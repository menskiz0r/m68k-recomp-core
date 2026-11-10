/*
 * code_generator.c — 68K → C code emitter.
 *
 * Emits void func_XXXXXX(void) for each discovered 68K function, split
 * across GENESIS_SPLIT_PART_COUNT balanced-size translation units
 * (<prefix>_part00.c .. _part{N-1}.c) sharing one declarations header
 * (<prefix>_decls.h), plus a dispatch table file (<prefix>_dispatch.c)
 * for call_by_address().
 */
#include "code_generator.h"
#include "m68k_timing.h"
#include "codegen_diag.h"
#include "m68k_decoder.h"
#include "m68k_validator.h"
#include "function_finder.h"
#include "annotations.h"
#include "game_config.h"
#include "portable_io.h"
#include "rom_parser.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdbool.h>
#include <stdint.h>
#include <ctype.h>

/* Current-instruction context for diagnostics, set at the top of
 * emit_instr and read by helpers (e.g., emit_ea_store_ex) so they can
 * attribute diagnostics to the right ROM PC and containing function
 * without threading params through every helper signature. Codegen is
 * single-threaded. */
static const char      *s_diag_func_name = NULL;
static uint32_t         s_diag_func_addr = 0;
static const M68KInstr *s_diag_instr     = NULL;
/* Active only while emitting a proven unobservable register span. Ordinary
 * instruction emission retains every architectural flag write. */
static bool s_span_flags = false;
static unsigned s_span_live_flags = 31;

/* =========================================================================
 * AddrSet — simple sorted dynamic array of uint32_t addresses
 * ========================================================================= */

typedef struct {
    uint32_t *addrs;
    int       count;
    int       cap;
} AddrSet;

static void addrset_init(AddrSet *s) {
    s->addrs = NULL; s->count = 0; s->cap = 0;
}

static void addrset_free(AddrSet *s) {
    free(s->addrs); s->addrs = NULL; s->count = 0; s->cap = 0;
}

static bool addrset_contains(const AddrSet *s, uint32_t a) {
    for (int i = 0; i < s->count; i++)
        if (s->addrs[i] == a) return true;
    return false;
}

static void addrset_insert(AddrSet *s, uint32_t a) {
    if (addrset_contains(s, a)) return;
    if (s->count >= s->cap) {
        s->cap = s->cap ? s->cap * 2 : 16;
        s->addrs = realloc(s->addrs, s->cap * sizeof(uint32_t));
    }
    s->addrs[s->count++] = a;
}

static void addrset_sort(AddrSet *s) {
    /* Insertion sort — functions are small */
    for (int i = 1; i < s->count; i++) {
        uint32_t key = s->addrs[i];
        int j = i - 1;
        while (j >= 0 && s->addrs[j] > key) {
            s->addrs[j + 1] = s->addrs[j];
            j--;
        }
        s->addrs[j + 1] = key;
    }
}

/* =========================================================================
 * JMP-table dispatch audit
 *
 * Every JMP-table site we emit gets recorded with its classification. At
 * the end of codegen we write `<game>_dispatch_audit.log` grouping sites
 * by kind. The danger category is `interior_unresolved`: a `JMP (PC,Dn.W)`
 * whose base lands on an interior PC of the containing function but my
 * Duff's-device probe didn't find enough uniform-instruction targets to
 * emit a switch. After my codegen fix landed in the previous commit this
 * category should be empty; if a new pattern shows up there in a future
 * regen, it's a Sonic-2-CPZ-style silent-failure waiting to happen.
 * ========================================================================= */

typedef enum {
    JMPAUDIT_STATIC_TARGET = 0,      /* JMP with statically-known target */
    JMPAUDIT_IN_FUNCTION_SWITCH,     /* (PC,Dn.W) resolved to in-function switch+goto */
    JMPAUDIT_FALLBACK_HYBRID,        /* (PC,Dn.W) punted to hybrid_jmp_interpret */
    JMPAUDIT_DYNAMIC_REGISTER,       /* JMP (An) / JMP (d16,An) / similar — not table */
    JMPAUDIT_UNSUPPORTED,            /* Decode succeeded but emitter couldn't handle */
} JmpAuditKind;

typedef struct {
    uint32_t     jmp_addr;
    uint32_t     func_addr;
    uint32_t     base;        /* for (PC,Dn.W); 0 otherwise */
    JmpAuditKind kind;
    int          n_targets;   /* for IN_FUNCTION_SWITCH */
} JmpAuditEntry;

static JmpAuditEntry *s_jmp_audit_arr = NULL;
static int            s_jmp_audit_count = 0;
static int            s_jmp_audit_cap   = 0;

static void audit_reset(void) { s_jmp_audit_count = 0; }

static void audit_record(uint32_t jmp_addr, uint32_t func_addr, uint32_t base,
                         JmpAuditKind kind, int n_targets)
{
    if (s_jmp_audit_count == s_jmp_audit_cap) {
        s_jmp_audit_cap = s_jmp_audit_cap ? s_jmp_audit_cap * 2 : 64;
        s_jmp_audit_arr = (JmpAuditEntry *)realloc(s_jmp_audit_arr,
                              (size_t)s_jmp_audit_cap * sizeof(JmpAuditEntry));
    }
    JmpAuditEntry *e = &s_jmp_audit_arr[s_jmp_audit_count++];
    e->jmp_addr  = jmp_addr;
    e->func_addr = func_addr;
    e->base      = base;
    e->kind      = kind;
    e->n_targets = n_targets;
}

/* =========================================================================
 * ExtReader — sequential walker over instruction extension words
 * ========================================================================= */

typedef struct {
    const M68KInstr *instr;
    int      wi;   /* index into instr->words[], starts at 1 */
    uint32_t bp;   /* byte offset from instr->addr for words[wi], starts at 2 */
} ExtReader;

static void er_init(ExtReader *er, const M68KInstr *instr) {
    er->instr = instr;
    er->wi    = 1;
    er->bp    = 2;
}

static void er_init_at(ExtReader *er, const M68KInstr *instr, int wi_start) {
    er->instr = instr;
    er->wi    = wi_start;
    er->bp    = (uint32_t)(wi_start * 2);
}

static uint16_t er_next(ExtReader *er) {
    uint16_t v = er->instr->words[er->wi];
    er->wi++;
    er->bp += 2;
    return v;
}

/* Read a long (32-bit) word from the extension stream — high word first. */
static uint32_t er_next_dword(ExtReader *er) {
    uint16_t hi = er_next(er);
    uint16_t lo = er_next(er);
    return ((uint32_t)hi << 16) | lo;
}

/* Read a size-tagged immediate from the extension stream:
 * .B → 1 word, low byte; .W → 1 word; .L → 2 words. */
static uint32_t er_next_imm(ExtReader *er, M68KSize sz) {
    if (sz == M68K_SIZE_L) return er_next_dword(er);
    uint16_t w = er_next(er);
    return (sz == M68K_SIZE_B) ? (uint32_t)(w & 0xFFu) : (uint32_t)w;
}

/* =========================================================================
 * ea_ext_words_count — mirrors m68k_decoder.c logic
 * ========================================================================= */

static int ea_ext_words_count(int mode, int reg, M68KSize size) {
    switch (mode) {
    case 0: case 1: case 2: case 3: case 4: return 0;
    case 5: return 1; /* (d16,An) */
    case 6: return 1; /* (d8,An,Xn) brief ext */
    case 7:
        switch (reg) {
        case 0: return 1; /* abs.W */
        case 1: return 2; /* abs.L */
        case 2: return 1; /* (d16,PC) */
        case 3: return 1; /* (d8,PC,Xn) */
        case 4: return (size == M68K_SIZE_L) ? 2 : 1; /* #imm */
        default: return 0;
        }
    default: return 0;
    }
}

/* =========================================================================
 * Size helpers
 * ========================================================================= */

static int size_bytes(M68KSize sz) {
    switch (sz) {
    case M68K_SIZE_B: return 1;
    case M68K_SIZE_W: return 2;
    case M68K_SIZE_L: return 4;
    default: return 2;
    }
}

static const char *size_ctype(M68KSize sz) {
    switch (sz) {
    case M68K_SIZE_B: return "uint8_t";
    case M68K_SIZE_W: return "uint16_t";
    case M68K_SIZE_L: return "uint32_t";
    default: return "uint16_t";
    }
}

static const char *size_read_fn(M68KSize sz) {
    switch (sz) {
    case M68K_SIZE_B: return "m68k_read8";
    case M68K_SIZE_W: return "m68k_read16";
    case M68K_SIZE_L: return "m68k_read32";
    default: return "m68k_read16";
    }
}

/* Tier-1 reverse-debugger switch. Set once at codegen_emit() entry. When
 * true, each func_XXXXXX body begins with `g_rdb_current_func = 0x……u;`
 * so the rdb_record bus-tap callback can attribute every write to its
 * source 68K function. We don't replace m68k_write* with wrappers —
 * recording happens at the shared bus-callback layer (works in both
 * native and oracle targets). When false, emission is byte-for-byte
 * identical to the pre-Tier-1 baseline. */
static bool s_reverse_debug = false;
/* Set by codegen_emit so emit_instr can probe the offset-table pattern
 * without dragging the whole GameConfig into every emit signature. */
static const uint32_t *s_extra_seeds      = NULL;
static int             s_extra_seed_count = 0;
/* Set by scan_function for ownership planning. A host whose unbounded CFG
 * touches an illegal encoding is not allowed to absorb later entries: that is
 * the classic code-running-into-data shape, not proof of overlap. */
static bool            s_scan_hit_invalid = false;
/* Set by codegen_emit after boundary splitting so JSR emission can verify
 * that the target is in the function table. Targets not present fall back
 * to recomp_call_addr() to avoid undeclared-identifier build errors. */
static const uint32_t *s_all_func_addrs = NULL;
static int             s_all_func_count = 0;

/* Widescreen (16:9) injection sites — set by codegen_emit from the GameConfig.
 * emit_instr looks each instruction's address up here and, when matched, emits
 * a margin-widened variant (reading the runtime g_ws_margin global; 0 =>
 * byte-identical vanilla). See game_config.h WsSite / the [[widescreen_site]]
 * TOML. This is the post-patch widening layer: the ROM is recompiled
 * unmodified and the widening lives entirely in the emitted C. */
static const WsSite *s_ws_sites = NULL;
static int           s_ws_site_count = 0;
static const WsSite *ws_site_for(uint32_t addr) {
    for (int i = 0; i < s_ws_site_count; i++)
        if (s_ws_sites[i].addr == addr) return &s_ws_sites[i];
    return NULL;
}
/* Kind-aware lookup: return the first site at `addr` whose kind is k0 or k1.
 * Lets MULTIPLE transforms of different kinds share one instruction address —
 * each codegen spot fetches the site of ITS OWN kind (e.g. a `subreg` register
 * adjust AND an `addimm` moveq-immediate widen both at the same moveq). */
static const WsSite *ws_site_for_kind(uint32_t addr, WsSiteKind k0, WsSiteKind k1) {
    for (int i = 0; i < s_ws_site_count; i++)
        if (s_ws_sites[i].addr == addr &&
            (s_ws_sites[i].kind == k0 || s_ws_sites[i].kind == k1))
            return &s_ws_sites[i];
    return NULL;
}

/* WS_SITE_ADDMEM helper: emit the wrapper that widens a memory-sourced word
 * value by +(g_ws_margin>>shift). Declares `uint16_t _wsv<addr> = <src_expr>;`
 * and, when g_ws_margin > 0, adds the margin — capped, if site->base != 0, at
 * the word `base` bytes after the source operand (camera min-bound clamp:
 * (a2) = Camera_Min_X_pos, cap = Camera_Max_X_pos at +2; never below the
 * original value either, so a boss lock with Min == Max stays authentic).
 * Word-size (An) and abs.W sources are supported (abs.W: the player
 * level-bound reads `move.w (Camera_Min_X_pos).w,d0` — cap address is the
 * absolute word + base) — anything else gets a diagnostic and no wrapper.
 * Returns 1 and writes the wrapped C expression into `out` when emitted;
 * returns 0 otherwise (caller keeps src_expr).
 * margin 0 => the wrapper leaves the value untouched (identical behavior). */
static int ws_emit_addmem_wrap(FILE *f, const WsSite *site, uint32_t addr,
                               const M68KInstr *instr, int src_ea, M68KSize sz,
                               const char *src_expr, char *out, size_t outsz)
{
    int smode = (src_ea >> 3) & 7;
    int sreg  = src_ea & 7;
    int is_absw = (smode == 7 && sreg == 0);
    if ((smode != 2 && !is_absw) || sz != M68K_SIZE_W) {
        fprintf(stderr, "[widescreen] addmem @%06X: only word-size (An) or "
                "abs.W sources are supported — site ignored\n", addr);
        return 0;
    }
    fprintf(f, "  /* [widescreen] addmem: src + (g_ws_margin>>%u)%s%s */\n",
            site->shift, site->base ? ", capped" : "",
            site->gate ? ", gated" : "");
    fprintf(f, "  uint16_t _wsv%06X = (uint16_t)(%s);\n", addr, src_expr);
    if (site->gate)
        /* gate: widen only while the RAM byte reads 0 (e.g. the game's
         * boss-active flag — boss arenas keep the authentic playfield) */
        fprintf(f, "  if (g_ws_margin && m68k_read8(0x%08Xu) == 0) {\n",
                site->gate);
    else
        fprintf(f, "  if (g_ws_margin) {\n");
    fprintf(f, "    uint32_t _wsc = (uint32_t)_wsv%06X + (uint32_t)(g_ws_margin >> %u);\n",
            addr, site->shift);
    if (site->base && is_absw) {
        /* abs.W source: ext word 1 holds the sign-extended operand address */
        uint32_t absaddr = (uint32_t)(int32_t)(int16_t)instr->words[1];
        fprintf(f, "    uint16_t _wscap = m68k_read16(0x%08Xu);\n",
                absaddr + (uint32_t)site->base);
        fprintf(f, "    if (_wsc > (uint32_t)_wscap) _wsc = _wscap;\n");
        fprintf(f, "    if (_wsc < (uint32_t)_wsv%06X) _wsc = _wsv%06X;\n", addr, addr);
    } else if (site->base) {
        fprintf(f, "    uint16_t _wscap = m68k_read16((uint32_t)(g_cpu.A[%d] + %uu));\n",
                sreg, (unsigned)site->base);
        fprintf(f, "    if (_wsc > (uint32_t)_wscap) _wsc = _wscap;\n");
        fprintf(f, "    if (_wsc < (uint32_t)_wsv%06X) _wsc = _wsv%06X;\n", addr, addr);
    }
    fprintf(f, "    _wsv%06X = (uint16_t)_wsc;\n", addr);
    fprintf(f, "  }\n");
    snprintf(out, outsz, "(uint16_t)(_wsv%06X)", addr);
    return 1;
}

/* Optional diagnostic: when set (via --dump-functions), codegen_emit writes
 * the final post-boundary-split function-entry set (one hex address per line)
 * to this path. Powers the heuristic-coverage exercise: diff the dump from a
 * disasm-seeded run against a no-seed (pure-heuristic) run, and against the
 * disasm label set, to read off heuristic misses (T\H) and false positives
 * (H\T) without per-entry provenance plumbing. */
static const char *s_dump_functions_path = NULL;
static uint32_t   *s_candidate_owners = NULL;
static int         s_candidate_owner_count = 0;
void codegen_set_dump_functions_path(const char *path) {
    s_dump_functions_path = path;
}

/*
 * Set by the per-instruction emit loop just before processing a Bcc
 * that's part of a hardware-flag spin idiom (tst.X mem; bcc self). The
 * Bcc handler then emits glue_yield_for_interrupt_poll() inside the goto
 * branch so the spin yields once per actual loop iteration without
 * paying yield cost on the fall-through path. Reset by the Bcc handler
 * after consuming. Module-global rather than parameter so the existing
 * emit_instr signature stays unchanged.
 */
static bool g_yield_in_next_bne = false;

static const char *size_write_fn(M68KSize sz) {
    switch (sz) {
    case M68K_SIZE_B: return "m68k_write8";
    case M68K_SIZE_W: return "m68k_write16";
    case M68K_SIZE_L: return "m68k_write32";
    default: return "m68k_write16";
    }
}

static uint32_t size_mask(M68KSize sz) {
    switch (sz) {
    case M68K_SIZE_B: return 0xFFFFFF00u;
    case M68K_SIZE_W: return 0xFFFF0000u;
    case M68K_SIZE_L: return 0x00000000u;
    default: return 0xFFFF0000u;
    }
}

static int size_bits(M68KSize sz) {
    switch (sz) {
    case M68K_SIZE_B: return 8;
    case M68K_SIZE_W: return 16;
    case M68K_SIZE_L: return 32;
    default: return 16;
    }
}

/* Size-qualified write back to a data register from a result variable that is
 * already typed as size_ctype(sz). For .L: full overwrite. For .B/.W: preserve
 * the unmodified upper bits via size_mask. The `indent` string lets callers
 * inside `{ ... }` blocks (e.g. shifts) match their surrounding indentation. */
static void emit_store_dn(FILE *f, const char *indent,
                          int dreg, const char *res, M68KSize sz) {
    if (sz == M68K_SIZE_L)
        fprintf(f, "%sg_cpu.D[%d] = (uint32_t)%s;\n", indent, dreg, res);
    else
        fprintf(f, "%sg_cpu.D[%d] = (g_cpu.D[%d] & 0x%08Xu) | (uint32_t)((%s)%s);\n",
                indent, dreg, dreg, size_mask(sz), size_ctype(sz), res);
}

/* =========================================================================
 * emit_ea_load — emit pre-statements and fill out_expr with C rvalue
 * ========================================================================= */

static void emit_ea_load_ex(FILE *f, const M68KInstr *instr, int ea, M68KSize sz,
                            ExtReader *er, const char *tmp, char *out_expr,
                            int rmw) {
    int mode = (ea >> 3) & 7;
    int reg  = ea & 7;
    const char *ct = size_ctype(sz);
    const char *rf = size_read_fn(sz);
    int sb = reg==7 && sz==M68K_SIZE_B ? 2 : size_bytes(sz);

    switch (mode) {
    case 0: /* Dn */
        snprintf(out_expr, 256, "(%s)g_cpu.D[%d]", ct, reg);
        break;
    case 1: /* An */
        snprintf(out_expr, 256, "g_cpu.A[%d]", reg);
        break;
    case 2: /* (An) */
        fprintf(f, "  %s %s = %s(g_cpu.A[%d]);\n", ct, tmp, rf, reg);
        snprintf(out_expr, 256, "%s", tmp);
        break;
    case 3: /* (An)+ */
        if (rmw) {
            /* RMW: read without increment — emit_ea_store will handle it */
            fprintf(f, "  %s %s = %s(g_cpu.A[%d]);\n",
                    ct, tmp, rf, reg);
        } else {
            fprintf(f, "  %s %s = %s(g_cpu.A[%d]); g_cpu.A[%d] += %d;\n",
                    ct, tmp, rf, reg, reg, sb);
        }
        snprintf(out_expr, 256, "%s", tmp);
        break;
    case 4: /* -(An) */
        fprintf(f, "  g_cpu.A[%d] -= %d; %s %s = %s(g_cpu.A[%d]);\n",
                reg, sb, ct, tmp, rf, reg);
        snprintf(out_expr, 256, "%s", tmp);
        break;
    case 5: { /* (d16,An) */
        uint16_t ext = er_next(er);
        int16_t  d16 = (int16_t)ext;
        fprintf(f, "  %s %s = %s((uint32_t)(g_cpu.A[%d] + (int32_t)%d));\n",
                ct, tmp, rf, reg, (int)d16);
        snprintf(out_expr, 256, "%s", tmp);
        break;
    }
    case 6: { /* (d8,An,Xn) */
        uint16_t ext = er_next(er);
        int      xreg  = (ext >> 12) & 7;
        int8_t   d8    = (int8_t)(ext & 0xFF);
        fprintf(f, "  %s %s = %s((uint32_t)(g_cpu.A[%d] + "
                "m68k_brief_index_value(0x%04Xu, g_cpu.D[%d], g_cpu.A[%d]) + (%d)));\n",
                ct, tmp, rf, reg, ext, xreg, xreg, (int)d8);
        snprintf(out_expr, 256, "%s", tmp);
        break;
    }
    case 7:
        switch (reg) {
        case 0: { /* abs.W */
            uint16_t ext = er_next(er);
            fprintf(f, "  %s %s = %s((uint32_t)(int32_t)(int16_t)0x%04X);\n",
                    ct, tmp, rf, ext);
            snprintf(out_expr, 256, "%s", tmp);
            break;
        }
        case 1: { /* abs.L */
            uint16_t hi = er_next(er);
            uint16_t lo = er_next(er);
            uint32_t addr = ((uint32_t)hi << 16) | lo;
            fprintf(f, "  %s %s = %s(0x%08X);\n", ct, tmp, rf, addr);
            snprintf(out_expr, 256, "%s", tmp);
            break;
        }
        case 2: { /* (d16,PC) */
            uint32_t pc_addr = instr->addr + er->bp; /* bp BEFORE er_next */
            uint16_t ext = er_next(er);
            int16_t  d16 = (int16_t)ext;
            uint32_t eff = (uint32_t)((int32_t)pc_addr + (int32_t)d16);
            fprintf(f, "  %s %s = %s(0x%08X);\n", ct, tmp, rf, eff);
            snprintf(out_expr, 256, "%s", tmp);
            break;
        }
        case 3: { /* (d8,PC,Xn) */
            uint32_t pc_addr = instr->addr + er->bp;
            uint16_t ext = er_next(er);
            int      xreg  = (ext >> 12) & 7;
            int8_t   d8    = (int8_t)(ext & 0xFF);
            fprintf(f, "  %s %s = %s((uint32_t)(0x%08X + "
                    "m68k_brief_index_value(0x%04Xu, g_cpu.D[%d], g_cpu.A[%d]) + (%d)));\n",
                    ct, tmp, rf, pc_addr, ext, xreg, xreg, (int)d8);
            snprintf(out_expr, 256, "%s", tmp);
            break;
        }
        case 4: { /* #imm */
            if (sz == M68K_SIZE_L) {
                uint16_t hi = er_next(er);
                uint16_t lo = er_next(er);
                uint32_t imm = ((uint32_t)hi << 16) | lo;
                snprintf(out_expr, 256, "0x%08Xu", imm);
            } else {
                uint16_t ext = er_next(er);
                if (sz == M68K_SIZE_B)
                    snprintf(out_expr, 256, "0x%02Xu", ext & 0xFF);
                else
                    snprintf(out_expr, 256, "0x%04Xu", ext);
            }
            break;
        }
        default:
            snprintf(out_expr, 256, "0 /* unknown EA 7/%d */", reg);
            codegen_diag_record(CGD_EA_FALLBACK,
                                s_diag_instr ? s_diag_instr->addr : 0,
                                s_diag_instr ? s_diag_instr->words[0] : 0,
                                s_diag_instr ? s_diag_instr->mnemonic : MN_OTHER,
                                s_diag_func_name, s_diag_func_addr);
            break;
        }
        break;
    default:
        snprintf(out_expr, 256, "0 /* unknown mode %d */", mode);
        codegen_diag_record(CGD_EA_FALLBACK,
                            s_diag_instr ? s_diag_instr->addr : 0,
                            s_diag_instr ? s_diag_instr->words[0] : 0,
                            s_diag_instr ? s_diag_instr->mnemonic : MN_OTHER,
                            s_diag_func_name, s_diag_func_addr);
        break;
    }
}

/* =========================================================================
 * emit_ea_addr — fill addr_expr with the address (no read)
 *
 * Used by LEA/PEA (u_suffix=false) and by JSR/JMP/BSR (u_suffix=true), which
 * historically formatted the mode 7/3 PC-relative literal slightly
 * differently. The flag picks `0x%08X` vs `0x%08Xu` to keep both call paths
 * byte-for-byte identical to their pre-refactor output.
 * ========================================================================= */

static void emit_ea_addr_ex(FILE *f, const M68KInstr *instr, int ea,
                            ExtReader *er, char *out_expr, bool u_suffix) {
    int mode = (ea >> 3) & 7;
    int reg  = ea & 7;
    (void)f;

    switch (mode) {
    case 2:
        snprintf(out_expr, 256, "g_cpu.A[%d]", reg);
        break;
    case 5: {
        uint16_t ext = er_next(er);
        int16_t d16 = (int16_t)ext;
        snprintf(out_expr, 256, "(uint32_t)(g_cpu.A[%d] + (int32_t)%d)", reg, (int)d16);
        break;
    }
    case 6: {
        uint16_t ext = er_next(er);
        int xreg  = (ext >> 12) & 7;
        int8_t d8 = (int8_t)(ext & 0xFF);
        snprintf(out_expr, 256,
                 "(uint32_t)(g_cpu.A[%d] + "
                 "m68k_brief_index_value(0x%04Xu, g_cpu.D[%d], g_cpu.A[%d]) + (%d))",
                 reg, ext, xreg, xreg, (int)d8);
        break;
    }
    case 7:
        switch (reg) {
        case 0: {
            uint16_t ext = er_next(er);
            snprintf(out_expr, 256, "(uint32_t)(int32_t)(int16_t)0x%04X", ext);
            break;
        }
        case 1: {
            uint32_t addr = er_next_dword(er);
            snprintf(out_expr, 256, "0x%08Xu", addr);
            break;
        }
        case 2: {
            uint32_t pc_addr = instr->addr + er->bp;
            uint16_t ext = er_next(er);
            int16_t d16 = (int16_t)ext;
            uint32_t eff = (uint32_t)((int32_t)pc_addr + (int32_t)d16);
            snprintf(out_expr, 256, "0x%08Xu", eff);
            break;
        }
        case 3: {
            uint32_t pc_addr = instr->addr + er->bp;
            uint16_t ext = er_next(er);
            int xreg  = (ext >> 12) & 7;
            int8_t d8 = (int8_t)(ext & 0xFF);
            snprintf(out_expr, 256,
                     u_suffix
                       ? "(uint32_t)(0x%08Xu + m68k_brief_index_value(0x%04Xu, g_cpu.D[%d], g_cpu.A[%d]) + (%d))"
                       : "(uint32_t)(0x%08X + m68k_brief_index_value(0x%04Xu, g_cpu.D[%d], g_cpu.A[%d]) + (%d))",
                     pc_addr, ext, xreg, xreg, (int)d8);
            break;
        }
        default:
            snprintf(out_expr, 256, "0 /* unknown EA addr 7/%d */", reg);
            codegen_diag_record(CGD_EA_FALLBACK,
                                s_diag_instr ? s_diag_instr->addr : 0,
                                s_diag_instr ? s_diag_instr->words[0] : 0,
                                s_diag_instr ? s_diag_instr->mnemonic : MN_OTHER,
                                s_diag_func_name, s_diag_func_addr);
            break;
        }
        break;
    default:
        snprintf(out_expr, 256, "0 /* cannot take addr of mode %d */", mode);
        codegen_diag_record(CGD_EA_FALLBACK,
                            s_diag_instr ? s_diag_instr->addr : 0,
                            s_diag_instr ? s_diag_instr->words[0] : 0,
                            s_diag_instr ? s_diag_instr->mnemonic : MN_OTHER,
                            s_diag_func_name, s_diag_func_addr);
        break;
    }
}

/* LEA/PEA wrapper: preserves the no-suffix mode 7/3 literal formatting. */
static void emit_ea_addr(FILE *f, const M68KInstr *instr, int ea,
                         ExtReader *er, char *out_expr) {
    emit_ea_addr_ex(f, instr, ea, er, out_expr, false);
}

/* Non-RMW wrapper — preserves old signature for all existing callers */
static void emit_ea_load(FILE *f, const M68KInstr *instr, int ea, M68KSize sz,
                         ExtReader *er, const char *tmp, char *out_expr) {
    emit_ea_load_ex(f, instr, ea, sz, er, tmp, out_expr, 0);
}

/* =========================================================================
 * emit_ea_store — emit the write statement
 * ========================================================================= */

static void emit_ea_store_ex(FILE *f, const M68KInstr *instr, int ea, M68KSize sz,
                             ExtReader *er, const char *val_expr, int rmw) {
    int mode = (ea >> 3) & 7;
    int reg  = ea & 7;
    const char *ct  = size_ctype(sz);
    const char *wf  = size_write_fn(sz);
    uint32_t    msk = size_mask(sz);
    int         sb  = reg==7 && sz==M68K_SIZE_B ? 2 : size_bytes(sz);
    (void)instr;

    switch (mode) {
    case 0: /* Dn */
        if (sz == M68K_SIZE_L)
            fprintf(f, "  g_cpu.D[%d] = (uint32_t)(%s)(%s);\n", reg, ct, val_expr);
        else
            fprintf(f, "  g_cpu.D[%d] = (g_cpu.D[%d] & 0x%08Xu) | (uint32_t)((%s)(%s));\n",
                    reg, reg, msk, ct, val_expr);
        break;
    case 1: /* An */
        fprintf(f, "  g_cpu.A[%d] = (uint32_t)(%s);\n", reg, val_expr);
        break;
    case 2: /* (An) */
        fprintf(f, "  %s(g_cpu.A[%d], (%s)(%s));\n", wf, reg, ct, val_expr);
        break;
    case 3: /* (An)+ — for both RMW and non-RMW, write to An and increment.
             * In RMW mode, emit_ea_load_ex suppressed the load's increment,
             * so the store does it. In non-RMW, the load already incremented
             * but the store gets a fresh er/address, so it also increments. */
        fprintf(f, "  %s(g_cpu.A[%d], (%s)(%s)); g_cpu.A[%d] += %d;\n",
                wf, reg, ct, val_expr, reg, sb);
        break;
    case 4: /* -(An) */
        if (rmw) {
            /* RMW: emit_ea_load already decremented An. Write to current
             * An (same address that was read). Don't decrement again. */
            fprintf(f, "  %s(g_cpu.A[%d], (%s)(%s));\n",
                    wf, reg, ct, val_expr);
        } else {
            fprintf(f, "  g_cpu.A[%d] -= %d; %s(g_cpu.A[%d], (%s)(%s));\n",
                    reg, sb, wf, reg, ct, val_expr);
        }
        break;
    case 5: { /* (d16,An) */
        uint16_t ext = er_next(er);
        int16_t d16 = (int16_t)ext;
        fprintf(f, "  %s((uint32_t)(g_cpu.A[%d] + (int32_t)%d), (%s)(%s));\n",
                wf, reg, (int)d16, ct, val_expr);
        break;
    }
    case 6: { /* (d8,An,Xn) */
        uint16_t ext = er_next(er);
        int xreg  = (ext >> 12) & 7;
        int8_t d8 = (int8_t)(ext & 0xFF);
        fprintf(f, "  %s((uint32_t)(g_cpu.A[%d] + "
                "m68k_brief_index_value(0x%04Xu, g_cpu.D[%d], g_cpu.A[%d]) + (%d)), (%s)(%s));\n",
                wf, reg, ext, xreg, xreg, (int)d8, ct, val_expr);
        break;
    }
    case 7:
        switch (reg) {
        case 0: {
            uint16_t ext = er_next(er);
            fprintf(f, "  %s((uint32_t)(int32_t)(int16_t)0x%04X, (%s)(%s));\n",
                    wf, ext, ct, val_expr);
            break;
        }
        case 1: {
            uint16_t hi = er_next(er);
            uint16_t lo = er_next(er);
            uint32_t addr = ((uint32_t)hi << 16) | lo;
            fprintf(f, "  %s(0x%08Xu, (%s)(%s));\n", wf, addr, ct, val_expr);
            break;
        }
        default:
            codegen_diag_record(CGD_INVALID_STORE_EA,
                                s_diag_instr ? s_diag_instr->addr : 0,
                                s_diag_instr ? s_diag_instr->words[0] : 0,
                                s_diag_instr ? s_diag_instr->mnemonic : MN_OTHER,
                                s_diag_func_name, s_diag_func_addr);
            fprintf(f, "  /* cannot store to EA 7/%d */\n", reg);
            break;
        }
        break;
    default:
        codegen_diag_record(CGD_INVALID_STORE_EA,
                            s_diag_instr ? s_diag_instr->addr : 0,
                            s_diag_instr ? s_diag_instr->words[0] : 0,
                            s_diag_instr ? s_diag_instr->mnemonic : MN_OTHER,
                            s_diag_func_name, s_diag_func_addr);
        fprintf(f, "  /* cannot store to mode %d */\n", mode);
        break;
    }
}

/* Non-RMW wrapper — default for MOVE and other non-RMW stores */
static void emit_ea_store(FILE *f, const M68KInstr *instr, int ea, M68KSize sz,
                          ExtReader *er, const char *val_expr) {
    emit_ea_store_ex(f, instr, ea, sz, er, val_expr, 0);
}

/* =========================================================================
 * Flag helpers
 * ========================================================================= */

#define SR_C  "(1u<<0)"
#define SR_V  "(1u<<1)"
#define SR_Z  "(1u<<2)"
#define SR_N  "(1u<<3)"
#define SR_X  "(1u<<4)"

static void emit_flags_logic(FILE *f, const char *expr, M68KSize sz) {
    /* MOVE-like: set N,Z; clear V,C.  Do NOT clear X (extend). */
    int bits = size_bits(sz);
    if (s_span_flags) {
        unsigned mask = s_span_live_flags & 15u;
        if (mask)
            fprintf(f, "  { uint%d_t _fv=(uint%d_t)(%s); g_cpu.SR=(uint16_t)((g_cpu.SR&~%uu)|"
                       "(((!_fv?4u:0u)|((_fv>>%d)?8u:0u))&%uu)); }\n",
                    bits, bits, expr, mask, bits-1, mask);
        return;
    }
    fprintf(f,
        "  { uint%d_t _fv = (uint%d_t)(%s);\n"
        "    g_cpu.SR &= ~(0x0Fu);\n"
        "    if (!_fv)             g_cpu.SR |= %s;\n"
        "    if (_fv >> %d)        g_cpu.SR |= %s; }\n",
        bits, bits, expr,
        SR_Z,
        bits - 1, SR_N);
}

static void emit_span_flags_arith(FILE *f, const char *a, const char *b,
                                  const char *res, M68KSize sz, bool subtract,
                                  unsigned written)
{
    unsigned mask=s_span_live_flags&written;
    if (!mask) return;
    int bits=size_bits(sz);
    uint32_t sign=bits==32?0x80000000u:1u<<(bits-1);
    uint32_t top=bits==32?0xffffffffu:(1u<<bits)-1u;
    fprintf(f,"  { uint%d_t _fa=(uint%d_t)(%s), _fb=(uint%d_t)(%s), _fr=(uint%d_t)(%s);\n",
            bits,bits,a,bits,b,bits,res);
    if(subtract) fputs("    unsigned _fc=(uint32_t)_fb>(uint32_t)_fa;\n",f);
    else fprintf(f,"    unsigned _fc=(uint64_t)_fa+(uint64_t)_fb>0x%08Xu;\n",top);
    fprintf(f,"    unsigned _fv=%s((_fa^_fb)&0x%08Xu)&&((_fa^_fr)&0x%08Xu);\n",
            subtract?"":"!",sign,sign);
    fprintf(f,"    g_cpu.SR=(uint16_t)((g_cpu.SR&~%uu)|(((!_fr?4u:0u)|"
              "((_fr>>%d)?8u:0u)|(_fc?%uu:0u)|(_fv?2u:0u))&%uu)); }\n",
            mask,bits-1,(written&16u)?17u:1u,mask);
}

static void emit_flags_add(FILE *f, const char *a, const char *b,
                            const char *res, M68KSize sz) {
    if(s_span_flags){emit_span_flags_arith(f,a,b,res,sz,false,31);return;}
    int bits = size_bits(sz);
    /* Carry is detected by widening to 64-bit before addition; a 32-bit
     * sum wraps so the previous "(uint32_t)_fa + (uint32_t)_fb > 0xFFFFFFFFu"
     * compare could never fire. Found by L3 oracle on Hud_TimeRingBonus. */
    fprintf(f,
        "  { uint%d_t _fa = (uint%d_t)(%s), _fb = (uint%d_t)(%s), _fr = (uint%d_t)(%s);\n"
        "    g_cpu.SR &= ~(0x1Fu);\n"
        "    if (!_fr)                        g_cpu.SR |= %s;\n"
        "    if (_fr >> %d)                   g_cpu.SR |= %s;\n"
        "    if ((uint64_t)_fa + (uint64_t)_fb > 0x%08Xu) { g_cpu.SR |= %s; g_cpu.SR |= %s; }\n"
        "    if (!((_fa^_fb) & 0x%08Xu) && ((_fa^_fr) & 0x%08Xu)) g_cpu.SR |= %s; }\n",
        bits, bits, a, bits, b, bits, res,
        SR_Z,
        bits - 1, SR_N,
        (bits == 32) ? 0xFFFFFFFFu : (bits == 16 ? 0xFFFFu : 0xFFu), SR_C, SR_X,
        (bits == 32) ? 0x80000000u : (bits == 16 ? 0x8000u : 0x80u),
        (bits == 32) ? 0x80000000u : (bits == 16 ? 0x8000u : 0x80u),
        SR_V);
}

static void emit_flags_sub(FILE *f, const char *a, const char *b,
                            const char *res, M68KSize sz) {
    if(s_span_flags){emit_span_flags_arith(f,a,b,res,sz,true,31);return;}
    int bits = size_bits(sz);
    fprintf(f,
        "  { uint%d_t _fa = (uint%d_t)(%s), _fb = (uint%d_t)(%s), _fr = (uint%d_t)(%s);\n"
        "    g_cpu.SR &= ~(0x1Fu);\n"
        "    if (!_fr)                   g_cpu.SR |= %s;\n"
        "    if (_fr >> %d)              g_cpu.SR |= %s;\n"
        "    if ((uint32_t)_fb > (uint32_t)_fa) { g_cpu.SR |= %s; g_cpu.SR |= %s; }\n"
        "    if (((_fa^_fb) & 0x%08Xu) && ((_fa^_fr) & 0x%08Xu)) g_cpu.SR |= %s; }\n",
        bits, bits, a, bits, b, bits, res,
        SR_Z,
        bits - 1, SR_N,
        SR_C, SR_X,
        (bits == 32) ? 0x80000000u : (bits == 16 ? 0x8000u : 0x80u),
        (bits == 32) ? 0x80000000u : (bits == 16 ? 0x8000u : 0x80u),
        SR_V);
}

/* CMP: same as SUB flags but does NOT affect X (extend). */
static void emit_flags_cmp(FILE *f, const char *a, const char *b,
                            const char *res, M68KSize sz) {
    if(s_span_flags){emit_span_flags_arith(f,a,b,res,sz,true,15);return;}
    int bits = size_bits(sz);
    fprintf(f,
        "  { uint%d_t _fa = (uint%d_t)(%s), _fb = (uint%d_t)(%s), _fr = (uint%d_t)(%s);\n"
        "    g_cpu.SR &= ~(0x0Fu);\n"
        "    if (!_fr)                   g_cpu.SR |= %s;\n"
        "    if (_fr >> %d)              g_cpu.SR |= %s;\n"
        "    if ((uint32_t)_fb > (uint32_t)_fa) { g_cpu.SR |= %s; }\n"
        "    if (((_fa^_fb) & 0x%08Xu) && ((_fa^_fr) & 0x%08Xu)) g_cpu.SR |= %s; }\n",
        bits, bits, a, bits, b, bits, res,
        SR_Z,
        bits - 1, SR_N,
        SR_C,
        (bits == 32) ? 0x80000000u : (bits == 16 ? 0x8000u : 0x80u),
        (bits == 32) ? 0x80000000u : (bits == 16 ? 0x8000u : 0x80u),
        SR_V);
}

/* =========================================================================
 * Per-mnemonic emission helpers
 *
 * These collapse the 5 ADD/SUB and 5 AND/OR/EOR mirror copies, plus the
 * 5 ADDI/SUBI/ANDI/ORI/EORI immediate-RMW mirror copies, plus the 3
 * BCHG/BCLR/BSET mirror copies, into per-family helpers parameterized by
 * operator string and (for arith) flag-update function pointer. Format
 * strings preserved verbatim so generated output is byte-identical.
 * ========================================================================= */

typedef void (*EmitFlagsArithFn)(FILE *, const char *, const char *,
                                 const char *, M68KSize);

/* ADD/SUB: dir=0 is EA→Dn, dir=1 is Dn→EA. Outer cast (`(ct)((ct)x op (ct)y)`)
 * matches arithmetic flag semantics. emit_flags is called BEFORE storing to
 * Dn so it sees the original Dn value, not the result. */
static void emit_alu_arith(FILE *f, const M68KInstr *instr, M68KSize sz,
                           ExtReader *er, const char *tmp, uint32_t addr,
                           const char *op,
                           EmitFlagsArithFn emit_flags) {
    int dir  = (instr->words[0] >> 8) & 1;
    int dreg = instr->reg;
    const char *ct = size_ctype(sz);
    char src_expr[256];
    char res[64];
    snprintf(res, sizeof(res), "_%06Xr", addr);

    if (dir == 0) {
        emit_ea_load(f, instr, instr->src_ea, sz, er, tmp, src_expr);
        fprintf(f, "  %s %s = (%s)((%s)g_cpu.D[%d] %s (%s)(%s));\n",
                ct, res, ct, ct, dreg, op, ct, src_expr);
        char da[256], db[256];
        snprintf(da, sizeof(da), "(%s)((%s)g_cpu.D[%d])", ct, ct, dreg);
        snprintf(db, sizeof(db), "(%s)(%s)", ct, src_expr);
        emit_flags(f, da, db, res, sz);
        emit_store_dn(f, "  ", dreg, res, sz);
    } else {
        ExtReader er_save = *er;
        emit_ea_load_ex(f, instr, instr->src_ea, sz, er, tmp, src_expr, 1);
        fprintf(f, "  %s %s = (%s)((%s)(%s) %s (%s)g_cpu.D[%d]);\n",
                ct, res, ct, ct, src_expr, op, ct, dreg);
        char da[256], db[256];
        snprintf(da, sizeof(da), "(%s)(%s)", ct, src_expr);
        snprintf(db, sizeof(db), "(%s)g_cpu.D[%d]", ct, dreg);
        emit_flags(f, da, db, res, sz);
        *er = er_save;
        emit_ea_store_ex(f, instr, instr->src_ea, sz, er, res, 1);
    }
}

/* AND/OR/EOR: logic ops have no outer cast and no operand-order swap-related
 * flag dependency. dir=0 (EA→Dn) emits store-then-flags; dir=1 (Dn→EA) emits
 * flags-then-store. Pass dir=1 from EOR (which has no Dn-destination form). */
static void emit_alu_logic(FILE *f, const M68KInstr *instr, M68KSize sz,
                           ExtReader *er, const char *tmp, uint32_t addr,
                           int dir, const char *op) {
    int dreg = instr->reg;
    const char *ct = size_ctype(sz);
    char src_expr[256];
    char res[64];
    snprintf(res, sizeof(res), "_%06Xr", addr);

    if (dir == 0) {
        emit_ea_load(f, instr, instr->src_ea, sz, er, tmp, src_expr);
        fprintf(f, "  %s %s = (%s)g_cpu.D[%d] %s (%s)(%s);\n",
                ct, res, ct, dreg, op, ct, src_expr);
        emit_store_dn(f, "  ", dreg, res, sz);
        emit_flags_logic(f, res, sz);
    } else {
        ExtReader er_save = *er;
        emit_ea_load_ex(f, instr, instr->src_ea, sz, er, tmp, src_expr, 1);
        fprintf(f, "  %s %s = (%s)(%s) %s (%s)g_cpu.D[%d];\n",
                ct, res, ct, src_expr, op, ct, dreg);
        emit_flags_logic(f, res, sz);
        *er = er_save;
        emit_ea_store_ex(f, instr, instr->src_ea, sz, er, res, 1);
    }
}

/* ADDI/SUBI: immediate-RMW on EA, with arithmetic flag semantics. Caller
 * has already consumed the immediate words via er_next_imm. The store walks
 * a fresh ExtReader at words[1 + imm_words] so the EA extension is re-read. */
static void emit_alui_arith(FILE *f, const M68KInstr *instr, M68KSize sz,
                            ExtReader *er, const char *tmp, uint32_t addr,
                            uint32_t imm, const char *op,
                            EmitFlagsArithFn emit_flags) {
    const char *ct = size_ctype(sz);
    char src_expr[256];
    char res[64];
    snprintf(res, sizeof(res), "_%06Xr", addr);

    emit_ea_load_ex(f, instr, instr->src_ea, sz, er, tmp, src_expr, 1);
    fprintf(f, "  %s %s = (%s)((%s)(%s) %s (%s)0x%Xu);\n",
            ct, res, ct, ct, src_expr, op, ct, imm);
    char da[256], db[256];
    snprintf(da, sizeof(da), "(%s)(%s)", ct, src_expr);
    snprintf(db, sizeof(db), "(%s)0x%Xu", ct, imm);
    emit_flags(f, da, db, res, sz);
    int imm_words = (sz == M68K_SIZE_L) ? 2 : 1;
    ExtReader er3;
    er_init_at(&er3, instr, 1 + imm_words);
    emit_ea_store_ex(f, instr, instr->src_ea, sz, &er3, res, 1);
}

/* ANDI/ORI/EORI RMW path (the EA-target case, NOT the SR/CCR special case
 * — caller handles that inline). Logic flag semantics, no outer cast. */
static void emit_alui_logic(FILE *f, const M68KInstr *instr, M68KSize sz,
                            ExtReader *er, const char *tmp, uint32_t addr,
                            uint32_t imm, const char *op) {
    const char *ct = size_ctype(sz);
    char src_expr[256];
    char res[64];
    snprintf(res, sizeof(res), "_%06Xr", addr);

    emit_ea_load_ex(f, instr, instr->src_ea, sz, er, tmp, src_expr, 1);
    fprintf(f, "  %s %s = (%s)(%s) %s (%s)0x%Xu;\n",
            ct, res, ct, src_expr, op, ct, imm);
    emit_flags_logic(f, res, sz);
    int imm_words = (sz == M68K_SIZE_L) ? 2 : 1;
    ExtReader er3;
    er_init_at(&er3, instr, 1 + imm_words);
    emit_ea_store_ex(f, instr, instr->src_ea, sz, &er3, res, 1);
}

/* SR-update tail shared by LSL/LSR (with_v=false) and ASL/ASR (with_v=true).
 * Both shift families end with the same N/Z/C/X update, gated on the
 * count-zero exception (preserve X when register-counted shift sees count=0).
 * ASL/ASR additionally sets V if the sign bit changed during the shift. */
static void emit_shift_sr_update(FILE *f, const char *res, int bits,
                                 bool reg_count, bool with_v) {
    if (reg_count) {
        fprintf(f, "    if (_cnt == 0) {\n");
        fprintf(f, "      g_cpu.SR &= ~(0x0Fu);  /* preserve X */\n");
        fprintf(f, "      if (!%s) g_cpu.SR |= (1u<<2);\n", res);
        fprintf(f, "      if ((uint32_t)%s >> %d) g_cpu.SR |= (1u<<3);\n", res, bits - 1);
        fprintf(f, "    } else {\n");
        fprintf(f, "      g_cpu.SR &= ~(0x1Fu);\n");
        fprintf(f, "      if (!%s) g_cpu.SR |= (1u<<2);\n", res);
        fprintf(f, "      if ((uint32_t)%s >> %d) g_cpu.SR |= (1u<<3);\n", res, bits - 1);
        fprintf(f, "      if (_c) { g_cpu.SR |= (1u<<0); g_cpu.SR |= (1u<<4); }\n");
        if (with_v) fprintf(f, "      if (_v) g_cpu.SR |= (1u<<1);\n");
        fprintf(f, "    }\n");
    } else {
        fprintf(f, "    g_cpu.SR &= ~(0x1Fu);\n");
        fprintf(f, "    if (!%s) g_cpu.SR |= (1u<<2);\n", res);
        fprintf(f, "    if ((uint32_t)%s >> %d) g_cpu.SR |= (1u<<3);\n", res, bits - 1);
        fprintf(f, "    if (_c) { g_cpu.SR |= (1u<<0); g_cpu.SR |= (1u<<4); }\n");
        if (with_v) fprintf(f, "    if (_v) g_cpu.SR |= (1u<<1);\n");
    }
}

/* BCHG/BCLR/BSET: identical except for the bit-modify operator string
 * (`"^"`, `"& ~"`, `"|"`). BTST stays inline since it has no RMW/result-var. */
static void emit_bitop_modify(FILE *f, const M68KInstr *instr, M68KSize sz,
                              ExtReader *er, const char *tmp, uint32_t addr,
                              const char *modify_op) {
    int dreg    = instr->reg;
    int is_imm  = (dreg < 0);
    int ea      = instr->src_ea;
    int ea_mode = (ea >> 3) & 7;
    int bit_mask = (ea_mode == 0) ? 31 : 7;
    /* 68K: bit ops on data registers operate on all 32 bits; memory
     * destinations are always byte-sized. */
    M68KSize bsz = (ea_mode == 0) ? M68K_SIZE_L : M68K_SIZE_B;
    const char *ct = size_ctype(bsz);

    char bit_expr[64];
    if (is_imm) {
        uint32_t imm = instr->imm32 & (uint32_t)bit_mask;
        snprintf(bit_expr, sizeof(bit_expr), "%uu", imm);
        er_init_at(er, instr, 2);
    } else {
        snprintf(bit_expr, sizeof(bit_expr), "(uint32_t)g_cpu.D[%d] & %uu", dreg, (unsigned)bit_mask);
    }
    char src_expr[256];
    ExtReader er_save = *er;
    emit_ea_load_ex(f, instr, ea, bsz, er, tmp, src_expr, 1);
    char res[64];
    snprintf(res, sizeof(res), "_%06Xr", addr);
    fprintf(f, "  %s %s = 0;\n", ct, res);   /* declare outside block */
    fprintf(f,
        "  { uint32_t _bn = %s;\n"
        "    g_cpu.SR = (g_cpu.SR & ~(1u<<2)) | (!((uint32_t)(%s) & (1u<<_bn)) ? (1u<<2) : 0u);\n"
        "    %s = (%s)((%s)(%s) %s(%s)(1u<<_bn)); }\n",
        bit_expr, src_expr, res, ct, ct, src_expr, modify_op, ct);
    *er = er_save;
    emit_ea_store_ex(f, instr, ea, bsz, er, res, 1);
}

/* =========================================================================
 * Branch condition helper
 * ========================================================================= */

static const char *bcc_cond_expr(int cond) {
    switch (cond & 0xF) {
    case 0x0: return "1";                                                        /* T */
    case 0x1: return "0";                                                        /* F */
    case 0x2: return "!(g_cpu.SR & ((1u<<0)|(1u<<2)))";                         /* HI */
    case 0x3: return "(g_cpu.SR & ((1u<<0)|(1u<<2)))";                          /* LS */
    case 0x4: return "!(g_cpu.SR & (1u<<0))";                                   /* CC */
    case 0x5: return "(g_cpu.SR & (1u<<0))";                                    /* CS */
    case 0x6: return "!(g_cpu.SR & (1u<<2))";                                   /* NE */
    case 0x7: return "(g_cpu.SR & (1u<<2))";                                    /* EQ */
    case 0x8: return "!(g_cpu.SR & (1u<<1))";                                   /* VC */
    case 0x9: return "(g_cpu.SR & (1u<<1))";                                    /* VS */
    case 0xA: return "!(g_cpu.SR & (1u<<3))";                                   /* PL */
    case 0xB: return "(g_cpu.SR & (1u<<3))";                                    /* MI */
    case 0xC: return "(!!(g_cpu.SR&(1u<<3)) == !!(g_cpu.SR&(1u<<1)))";          /* GE */
    case 0xD: return "(!!(g_cpu.SR&(1u<<3)) != !!(g_cpu.SR&(1u<<1)))";          /* LT */
    case 0xE: return "!(g_cpu.SR&(1u<<2)) && (!!(g_cpu.SR&(1u<<3))==!!(g_cpu.SR&(1u<<1)))"; /* GT */
    case 0xF: return "(g_cpu.SR&(1u<<2)) || (!!(g_cpu.SR&(1u<<3))!=!!(g_cpu.SR&(1u<<1)))";  /* LE */
    default:  return "0";
    }
}

static void emit_cycle_accounting(FILE *f, const char *indent, int cycles)
{
    if (cycles < 0)
        return;
    fprintf(f, "%sg_native_insn_count++; g_cycle_accumulator += %d;"
               " g_audio_cycle_counter += %d;"
               " if (g_cycle_accumulator >= g_vblank_threshold)"
               " glue_check_vblank();\n", indent, cycles, cycles);
    /* Differential co-sim per-instruction checkpoint (no-op unless GENESIS_COSIM;
     * mirrors interp_account_cycles in m68k_interp.c). */
    fprintf(f, "%sGEN_COSIM_TICK(%d);\n", indent, cycles);
}

static bool func_is_known(uint32_t addr);

/* Discovery may promote an external/RAM target into the function table.
 * Membership alone cannot bypass live RAM trampoline/stub resolution. */
static bool func_is_native_rom(const GenesisRom *rom,uint32_t addr)
{
    return rom && rom->rom_data && !rom->read8_override && rom->rom_size>=2 &&
           !(addr&1u) && addr<=rom->rom_size-2u && func_is_known(addr);
}

static void emit_static_tail_target(FILE *f,const GenesisRom *rom,const char *indent,uint32_t addr)
{
    if(func_is_native_rom(rom,addr))
        fprintf(f,"%sRECOMP_TAIL_NATIVE(0x%06Xu,func_%06X);\n",indent,addr,addr);
    else fprintf(f,"%srecomp_tail_call(0x%06Xu);\n",indent,addr);
}

static void emit_split_tail_call(FILE *f, const GenesisRom *rom,const char *indent,
                                 uint32_t target_addr, bool carry_sp_adjust,
                                 int cycles_before) {
    emit_cycle_accounting(f, indent, cycles_before);
    if (carry_sp_adjust) {
        fprintf(f, "%s{ g_split_sp_popped += _sp_popped; _sp_popped = 0;\n", indent);
        emit_static_tail_target(f,rom,indent,target_addr);
        fprintf(f, "%s  return;\n", indent);
        fprintf(f, "%s}\n", indent);
    } else {
        emit_static_tail_target(f,rom,indent,target_addr);
        fprintf(f,"%sreturn;\n",indent);
    }
}

static void emit_split_tail_call_expr(FILE *f, const char *indent,
                                      const char *addr_expr,
                                      bool carry_sp_adjust,
                                      int cycles_before) {
    emit_cycle_accounting(f, indent, cycles_before);
    if (carry_sp_adjust) {
        fprintf(f, "%s{ g_split_sp_popped += _sp_popped; _sp_popped = 0;\n", indent);
        fprintf(f, "%s  recomp_tail_call(%s);\n", indent, addr_expr);
        fprintf(f, "%s  return;\n", indent);
        fprintf(f, "%s}\n", indent);
    } else {
        fprintf(f, "%srecomp_tail_call(%s); return;\n", indent, addr_expr);
    }
}

/* func_is_known — binary search in s_all_func_addrs for a JSR target. */
static bool func_is_known(uint32_t addr) {
    if (!s_all_func_addrs || s_all_func_count == 0) return false;
    int lo = 0, hi = s_all_func_count - 1;
    while (lo <= hi) {
        int mid = (lo + hi) / 2;
        if (s_all_func_addrs[mid] == addr) return true;
        if (s_all_func_addrs[mid] < addr) lo = mid + 1;
        else                              hi = mid - 1;
    }
    return false;
}

/* =========================================================================
 * scan_function — discover all instruction addresses and branch-target labels
 * ========================================================================= */

/* addr_belongs_to_other_function — returns true if `addr` falls within the
 * address range of a function OTHER than `my_start`.
 *
 * `sorted_funcs` is a sorted array of `nfuncs` function entry points.
 * A target belongs to another function if the greatest entry point <= addr
 * is not `my_start`. */
static bool addr_belongs_to_other_function(uint32_t addr, uint32_t my_start,
                                           const uint32_t *sorted_funcs, int nfuncs) {
    if (nfuncs == 0) return false;
    /* Binary search for the largest entry point <= addr */
    int lo = 0, hi = nfuncs - 1, best = -1;
    while (lo <= hi) {
        int mid = (lo + hi) / 2;
        if (sorted_funcs[mid] <= addr) {
            best = mid;
            lo = mid + 1;
        } else {
            hi = mid - 1;
        }
    }
    if (best < 0) return false;
    /* If the owning function is not us, this address is in another function */
    return sorted_funcs[best] != my_start;
}

/* addr_is_function_entry — exact-match membership in the sorted entry set. */
static bool addr_is_function_entry(uint32_t addr, const uint32_t *sorted_funcs,
                                   int nfuncs) {
    int lo = 0, hi = nfuncs - 1;
    while (lo <= hi) {
        int mid = (lo + hi) / 2;
        if (sorted_funcs[mid] == addr) return true;
        if (sorted_funcs[mid] < addr) lo = mid + 1;
        else                          hi = mid - 1;
    }
    return false;
}

/* Exact-match index lookup in a sorted entry array. */
static int function_entry_index(uint32_t addr, const uint32_t *sorted_funcs,
                                int nfuncs) {
    int lo = 0, hi = nfuncs - 1;
    while (lo <= hi) {
        int mid = (lo + hi) / 2;
        if (sorted_funcs[mid] == addr) return mid;
        if (sorted_funcs[mid] < addr) lo = mid + 1;
        else                          hi = mid - 1;
    }
    return -1;
}

/* Report (once per entry per run) a discovered function entry that lands
 * MID-INSTRUCTION relative to a decoded stream — a data-shadowed / falsely
 * discovered entry. The stream decodes through it (see the linear-scan rule
 * below); the entry itself stays dispatchable as its own function. */
#define MISALIGNED_REPORT_CAP 1024
static uint32_t s_misaligned_reported[MISALIGNED_REPORT_CAP];
static int      s_misaligned_reported_count = 0;
static void report_misaligned_entries_in_range(uint32_t pc, uint32_t len,
                                               uint16_t opcode, M68KMnemonic mn,
                                               uint32_t enclosing_func,
                                               const uint32_t *sorted_funcs,
                                               int nfuncs) {
    for (uint32_t a = pc + 2; a < pc + len; a += 2) {
        if (!addr_is_function_entry(a, sorted_funcs, nfuncs)) continue;
        bool seen = false;
        for (int i = 0; i < s_misaligned_reported_count; i++)
            if (s_misaligned_reported[i] == a) { seen = true; break; }
        if (seen) continue;
        if (s_misaligned_reported_count < MISALIGNED_REPORT_CAP)
            s_misaligned_reported[s_misaligned_reported_count++] = a;
        codegen_diag_record(CGD_MISALIGNED_FUNC_ENTRY, a, opcode, mn,
                            NULL, enclosing_func);
        fprintf(stderr, "[Codegen] WARN: function entry $%06X lands mid-instruction "
                        "(inside $%06X..$%06X of func $%06X) — data-shadowed entry; "
                        "stream decodes through it\n",
                a, pc, pc + len - 2, enclosing_func);
    }
}

/* =========================================================================
 * probe_pc_idx_targets — find interior-label dispatch targets of a
 * `JMP (d8, PC, Xn)` instruction.
 *
 * Pattern: code like
 *     add.w  d2,d2
 *     jmp    .doPartialLineBlock(pc,d2.w)
 *   .doPartialLineBlock:
 *     rept 16
 *         move.l d0,(a1)+        ; 16 identical 2-byte instructions
 *     endm
 *     addq.b #1,d4
 *     dbf    d1,.doFullLineBlock
 *     rts
 *
 * The JMP lands at base + Dn (Dn is a byte offset). With a uniform-instruction
 * "Duff's device" tail like the 16x move.l above, Dn picks WHICH instruction
 * in the sequence to start at. Each landing point is an INTERIOR PC of the
 * current function — never a function entry, so runtime call_by_address fails
 * and the dispatch is silently dropped (see runner/glue.c interior-label
 * silencer). The fix is to emit an in-function switch at codegen time.
 *
 * Heuristic for "this is a Duff's device" (vs. e.g. a bra.w jump table):
 *  - Stop on the first probe address NOT in `instrs` (out of function).
 *  - Stop on the first opcode that doesn't match the base instruction's
 *    opcode + byte_length. (Bra.w tables have 4-byte entries with
 *    non-instruction displacement words between them, so the first probe
 *    at base+2 fails the `addrset_contains` check and we exit with n=1,
 *    correctly signalling "not a Duff's device — caller should fall back
 *    to hybrid_jmp_interpret + bra.w-trampoline path".)
 *
 * Returns the number of targets written to `out_targets[]`. Caller decides
 * whether the result is "enough" to emit a switch (>= 2).
 * ========================================================================= */
static int probe_pc_idx_targets(const GenesisRom *rom,
                                 const M68KInstr *jmp_instr,
                                 const AddrSet *instrs,
                                 uint32_t *out_targets,
                                 int max_targets)
{
    if (max_targets <= 0) return 0;

    /* Re-decode the JMP extension word for d8 and the index register.
     * For `JMP (d8, PC, Xn)`, words[1] is the brief-format extension word:
     *   bit 15:  0=Dn / 1=An
     *   bits 14-12: register
     *   bit 11:  0=W (sign-extended low word) / 1=L
     *   bits  7-0: d8 (signed displacement)
     * PC value used for the EA is the address of this extension word,
     * which is `jmp_instr->addr + 2` (opcode word is at +0). */
    if (jmp_instr->word_count < 2) return 0;
    uint16_t ext   = jmp_instr->words[1];
    int8_t   d8    = (int8_t)(ext & 0xFF);
    uint32_t base  = (uint32_t)(jmp_instr->addr + 2 + (int32_t)d8);

    /* Anchor: the instruction at `base` defines the uniform-sequence
     * signature. If `base` isn't even in this function's instruction set,
     * the dispatch isn't an interior-label one and we bail. */
    if (!addrset_contains(instrs, base)) return 0;

    M68KInstr first;
    if (!m68k_decode(rom, base, &first)) return 0;
    uint16_t first_op  = first.words[0];
    int      first_len = first.byte_length;
    if (first_len < 2) return 0;

    int n = 0;
    /* Probe at every 2-byte boundary — M68K instructions are word-aligned and
     * `JMP (PC,Dn.W)` uses Dn as a byte offset, so Dn=0,2,4,... are the only
     * plausible indices for a uniform sequence of 2-byte instructions. For
     * 4-byte (bra.w) entries the second probe address falls inside the prior
     * instruction's displacement word, fails `addrset_contains`, and we exit
     * with n <= 1. */
    for (int i = 0; i < max_targets; i++) {
        uint32_t t = (uint32_t)(base + (uint32_t)i * 2u);
        if (!addrset_contains(instrs, t)) break;
        M68KInstr probe;
        if (!m68k_decode(rom, t, &probe)) break;
        if (probe.words[0] != first_op)  break;
        if (probe.byte_length != first_len) break;
        out_targets[n++] = t;
    }
    return n;
}

/* =========================================================================
 * probe_offset_table_targets — decode a `dc.w (target - base)` offset table.
 *
 * Sister probe to probe_pc_idx_targets. Where that one handles Duff's-device
 * patterns (JMP into the start of a uniform instruction sequence), this one
 * handles the standard Sonic `move.w table(pc,Dn.W),Dn / jmp table(pc,Dn.W)`
 * dispatch where the table contains signed 16-bit offsets to interior labels
 * of the same function (e.g. ObjB2_* in Sonic 2 at $03AD0C / $03AD2A,
 * Elev_Types / Circ_Types / SStom_Move in Sonic 1).
 *
 * Filter is "target is in this function's instrs". For that to be a strong
 * signal, the caller (scan_function) must have already seeded the target
 * via disasm extra_seeds OR via auto-discovery from the JMP base itself
 * (see seed_pc_idx_dispatch_targets). Cross-function offset tables (entries
 * resolving to function entries in OTHER functions) are out of scope for
 * this probe — those continue through hybrid_jmp_interpret + call_by_address,
 * which already works for function-entry targets.
 *
 * Outputs the OFFSET VALUES used by the consumer's switch cases (the
 * runtime expression is `Dn == loaded_offset_value`, NOT byte index).
 *
 * Returns count; caller emits a switch with case constants = out_offsets.
 * ========================================================================= */
static int probe_offset_table_targets(const GenesisRom *rom,
                                       const M68KInstr *jmp_instr,
                                       const AddrSet *instrs,
                                       int32_t  *out_offsets,
                                       uint32_t *out_targets,
                                       int max_targets)
{
    if (max_targets <= 0)              return 0;
    if (jmp_instr->word_count < 2)     return 0;

    uint16_t ext  = jmp_instr->words[1];
    int8_t   d8   = (int8_t)(ext & 0xFF);
    uint32_t base = (uint32_t)(jmp_instr->addr + 2 + (int32_t)d8);

    int n = 0;
    for (int i = 0; i < max_targets; i++) {
        uint32_t a = base + (uint32_t)i * 2u;
        if (!rom || a + 1 >= rom->rom_size) break;
        int16_t off = (int16_t)(((uint16_t)rom->rom_data[a] << 8)
                              | rom->rom_data[a + 1]);
        uint32_t t = (uint32_t)((int32_t)base + (int32_t)off);
        if (!addrset_contains(instrs, t)) break;
        out_offsets[n] = (int32_t)off;
        out_targets[n] = t;
        n++;
    }
    return n;
}

/* =========================================================================
 * seed_pc_idx_dispatch_targets — discover JMP(PC,Dn.W) dispatch targets at
 * scan time, without depending on a disasm-generated label list.
 *
 * Adds interior PCs to the CFG-walker worklist for two patterns:
 *
 *   (1) Duff's device — base is the first of a uniform sequence of 2-byte
 *       instructions. Threshold: 8+ consecutive identical opcode words.
 *       Seeds base+0, base+2, ..., base+2*(N-1).
 *
 *   (2) Offset table — `dc.w (target - base)` rows, target = base + offset,
 *       all targets within [start_addr, plausible_end) and decode as valid
 *       M68K instructions. Seeds the resolved targets (NOT the table bytes).
 *
 * `plausible_end` is the next-larger entry in sorted_funcs, or
 * start_addr + 0x1000 as a defensive cap. This bounds the heuristic so it
 * can't seed targets that belong to entirely different functions.
 *
 * Safety: false-positive risk is low because:
 *   - The Duff's-device threshold (8+ identical 2-byte opcodes) is rare
 *     outside the actual pattern. Common multi-instruction sequences like
 *     bra.w trampolines fail at the second probe (different displacement
 *     word at base+2 vs the bra.w opcode at base+0).
 *   - The offset-table walk stops on the first entry that's out-of-range
 *     or fails to decode, so it can't "run away" into garbage data.
 * ========================================================================= */
static void seed_pc_idx_dispatch_targets(const GenesisRom *rom,
                                         const M68KInstr *jmp_instr,
                                         AddrSet *worklist,
                                         uint32_t start_addr,
                                         const uint32_t *sorted_funcs,
                                         int nfuncs)
{
    if (!jmp_instr || jmp_instr->word_count < 2) return;
    /* Only (d8, PC, Xn): src_ea encoding 7<<3 | 3 = 0x3B. */
    if (jmp_instr->src_ea != 0x3B) return;

    uint16_t ext  = jmp_instr->words[1];
    int8_t   d8   = (int8_t)(ext & 0xFF);
    uint32_t base = (uint32_t)(jmp_instr->addr + 2 + (int32_t)d8);
    if (!rom || base + 1 >= rom->rom_size) return;

    /* Duff's-device probe runs FIRST without function-range bounds. The
     * 8+ uniform-opcode threshold is self-bounding, and the dispatched
     * targets often extend past the next adjacent function entry (e.g.
     * Sonic 1's Deform_SLZ JMP at $00647C dispatches into the body of
     * the loc_6480 function — boundary-split will promote each landing
     * point separately, but we need to seed them all first). */
    uint16_t op0 = ((uint16_t)rom->rom_data[base] << 8) | rom->rom_data[base + 1];
    int n_same = 1;
    for (int i = 1; i < 32; i++) {
        uint32_t a = base + (uint32_t)i * 2u;
        if (a + 1 >= rom->rom_size) break;
        uint16_t w = ((uint16_t)rom->rom_data[a] << 8) | rom->rom_data[a + 1];
        if (w != op0) break;
        n_same++;
    }
    if (n_same >= 8) {
        /* Seed every Duff's-device target. Each falls naturally into either
         * the current function's instrs (if base is interior to start_addr)
         * or extern_targets (if base is past the next adjacent function),
         * driven by the worklist loop's `addr_belongs_to_other_function`
         * check. The boundary-splitter promotes the extern_targets to
         * function entries on the next discovery iteration, after which
         * call_by_address dispatches the JMP at runtime. */
        for (int i = 0; i < n_same; i++)
            addrset_insert(worklist, base + (uint32_t)i * 2u);
        return;
    }

    /* Offset-table probe needs an upper bound — the table is followed by
     * arbitrary data/code and we have to know when to stop reading. Use
     * the next function entry as plausible_end (offset-table targets are
     * typically interior PCs of the SAME function, by convention). If
     * base itself is past plausible_end, the JMP isn't an in-function
     * offset table — leave it for the hybrid_jmp_interpret fallback. */
    uint32_t plausible_end = start_addr + 0x1000u;
    for (int i = 0; i < nfuncs; i++) {
        if (sorted_funcs[i] > start_addr && sorted_funcs[i] < plausible_end)
            plausible_end = sorted_funcs[i];
    }
    if (base < start_addr || base >= plausible_end) return;

    for (int i = 0; i < 32; i++) {
        uint32_t a = base + (uint32_t)i * 2u;
        if (a + 1 >= rom->rom_size) break;
        int16_t off = (int16_t)(((uint16_t)rom->rom_data[a] << 8) | rom->rom_data[a + 1]);
        uint32_t t = (uint32_t)((int32_t)base + (int32_t)off);
        if (t < start_addr || t >= plausible_end) break;
        M68KInstr probe;
        if (!m68k_decode(rom, t, &probe)) break;
        addrset_insert(worklist, t);
    }
}

static void scan_function(const GenesisRom *rom, uint32_t start_addr,
                           AddrSet *instrs, AddrSet *labels,
                           const uint32_t *sorted_funcs, int nfuncs,
                           const uint32_t *all_entries, int nentries,
                           AddrSet *extern_targets,
                          const uint32_t *extra_seeds, int extra_seed_count,
                          const GameConfig *cfg) {
    /* Worklist-based CFG walk */
    s_scan_hit_invalid = false;
    AddrSet worklist;
    addrset_init(&worklist);
    addrset_insert(&worklist, start_addr);
    M68KValidatorOptions vopts = {0};
    vopts.allow_68020_branch = cfg ? cfg->allow_68020_branch : false;

    /* Disasm-extracted interior PCs that the CFG walker would otherwise
     * miss — e.g. local labels reached only via `JMP (PC,Dn.W)` (Sonic 2
     * CPZ Duff's-device buffer-fill loops). Only seed entries that
     * plausibly belong to THIS function (between start_addr and the next
     * function's start); cross-function seeds get filtered by the
     * `addr_belongs_to_other_function` check inside the walk anyway. */
    if (extra_seeds && extra_seed_count > 0) {
        uint32_t next_func_start = 0xFFFFFFFFu;
        for (int i = 0; i < nfuncs; i++) {
            if (sorted_funcs[i] > start_addr && sorted_funcs[i] < next_func_start)
                next_func_start = sorted_funcs[i];
        }
        for (int i = 0; i < extra_seed_count; i++) {
            uint32_t s = extra_seeds[i];
            if (s > start_addr && s < next_func_start)
                addrset_insert(&worklist, s);
        }
    }

    while (worklist.count > 0) {
        uint32_t pc = worklist.addrs[--worklist.count];

        /* Don't follow addresses that belong to another function */
        if (pc != start_addr &&
            addr_belongs_to_other_function(pc, start_addr, sorted_funcs, nfuncs)) {
            if (extern_targets) addrset_insert(extern_targets, pc);
            continue;
        }

        /* Scan linearly from pc until terminator or already-visited */
        while (pc < rom->rom_size) {
            if (addrset_contains(instrs, pc)) break;

            /* Stop the linear scan ONLY at another function's EXACT entry
             * point — the end-of-function fall-through logic emits the
             * boundary tail call there. A function entry that lands
             * MID-INSTRUCTION relative to this stream (territory test true,
             * but no entry coincides with an instruction start) is a
             * data-shadowed / falsely-discovered entry: severing the stream
             * there silently truncated the enclosing function with no
             * dispatch miss (RKA's $693E scroll-table builder lost its two
             * per-frame fill loops to bogus entry $697A → frozen background).
             * Decode through it and record the diagnostic instead. */
            if (pc != start_addr &&
                addr_is_function_entry(pc, sorted_funcs, nfuncs))
                break;

            M68KInstr instr;
            if (!m68k_decode(rom, pc, &instr)) break;

            /* The decoder is intentionally permissive; legality is the proof
             * that a speculative CFG path is still code.  The finder already
             * applies this gate, but codegen historically did not, allowing a
             * branch/table seed to walk arbitrary data and manufacture later
             * boundaries. */
            if (m68k_validate(&instr, &vopts) != M68K_LEGAL) {
                s_scan_hit_invalid = true;
                break;
            }

            if (all_entries && nentries > 0)
                report_misaligned_entries_in_range(pc, instr.byte_length,
                                                   instr.words[0], instr.mnemonic,
                                                   start_addr, all_entries, nentries);

            addrset_insert(instrs, pc);

            switch (instr.mnemonic) {
            case MN_RTS:
            case MN_RTE:
            case MN_RTR:
            case MN_STOP:
            case MN_ILLEGAL:
                goto next_work; /* terminate this path */

            case MN_BRA:
                if (instr.has_target && instr.target_addr != pc)
                    addrset_insert(&worklist, instr.target_addr);
                goto next_work;

            case MN_JMP:
                if (instr.has_target && instr.target_addr != pc) {
                    addrset_insert(&worklist, instr.target_addr);
                } else {
                    /* Computed dispatch (no static target). If this is a
                     * (d8,PC,Xn) JMP, try to discover Duff's-device or
                     * offset-table targets at the JMP base and seed them
                     * so the codegen probes find them in instrs. */
                    seed_pc_idx_dispatch_targets(rom, &instr, &worklist,
                                                 start_addr, sorted_funcs, nfuncs);
                }
                goto next_work;

            case MN_Bcc:
                if (instr.has_target)
                    addrset_insert(&worklist, instr.target_addr);
                /* fall through: continue linear scan */
                break;

            case MN_DBcc:
                if (instr.has_target)
                    addrset_insert(&worklist, instr.target_addr);
                break;

            case MN_BSR:
            case MN_JSR:
                /* FunctionFinder's linear walk stops at computed JMPs, while
                 * this CFG walk can prove and enter their case bodies. Close a
                 * direct call found there only with independent evidence:
                 * either the target is a disassembly-provided local seed (the
                 * historical path), or a trusted runtime oracle observed BOTH
                 * the call instruction and its static target. Requiring the
                 * executed edge prevents speculative/data-shaped CFG paths
                 * from cascading into false function entries. */
                if (instr.has_target && extern_targets) {
                    bool proven = false;
                    if (extra_seeds) {
                        for (int s = 0; s < extra_seed_count; s++) {
                            if (extra_seeds[s] == instr.target_addr) {
                                proven = true;
                                break;
                            }
                        }
                    }
                    if (!proven && game_config_has_runtime_oracle(cfg)) {
                        proven = game_config_runtime_observed(cfg, instr.addr) &&
                                 game_config_runtime_observed(cfg, instr.target_addr);
                    }
                    if (proven)
                        addrset_insert(extern_targets, instr.target_addr);
                }
                break;

            default:
                break;
            }

            pc += instr.byte_length;
        }
        next_work:;
    }

    /* Mark targets that land within this function as labels */
    for (int i = 0; i < instrs->count; i++) {
        uint32_t ipc = instrs->addrs[i];
        M68KInstr instr;
        if (!m68k_decode(rom, ipc, &instr)) continue;
        if ((instr.mnemonic == MN_Bcc || instr.mnemonic == MN_DBcc ||
             instr.mnemonic == MN_BRA || instr.mnemonic == MN_JMP) &&
             instr.has_target && addrset_contains(instrs, instr.target_addr)) {
            addrset_insert(labels, instr.target_addr);
        }
    }

    addrset_free(&worklist);
}

/* A callable address is not necessarily a new function boundary. Shared
 * epilogues and branch-entered suffixes can be both reachable inside a host
 * routine and valid dispatch entries. Treating every
 * such address as a hard boundary truncates the host. psxrecomp models these
 * as overlapping aliases; this is the 68000 counterpart.
 *
 * Walk every entry without entry boundaries, then select as an alias host the
 * reachable entry with the largest CFG. A strict size improvement is required
 * (equal-size cycles use the lower address as a deterministic tie break).
 * Unrelated adjacent routines separated by RTS/JMP never overlap and remain
 * hard boundaries. */
static uint32_t *build_entry_owners(const GenesisRom *rom,
                                    const AddrSet *all_funcs,
                                    const GameConfig *cfg,
                                    AddrSet *hard_boundaries,
                                    bool verbose) {
    int n = all_funcs->count;
    uint32_t *owners = (uint32_t *)malloc((size_t)n * sizeof(uint32_t));
    int *sizes = (int *)calloc((size_t)n, sizeof(int));
    int *best_sizes = (int *)calloc((size_t)n, sizeof(int));
    bool *safe = (bool *)calloc((size_t)n, sizeof(bool));
    if (!owners || !sizes || !best_sizes || !safe) {
        free(owners); free(sizes); free(best_sizes); free(safe);
        return NULL;
    }

    /* Pass 1: establish each entry's own unbounded reachable-CFG size. */
    for (int i = 0; i < n; i++) {
        AddrSet instrs, labels;
        addrset_init(&instrs); addrset_init(&labels);
        scan_function(rom, all_funcs->addrs[i], &instrs, &labels,
                      NULL, 0, NULL, 0, NULL, NULL, 0, cfg);
        sizes[i] = instrs.count;
        safe[i] = !s_scan_hit_invalid;
        best_sizes[i] = instrs.count;
        owners[i] = all_funcs->addrs[i];
        addrset_free(&instrs); addrset_free(&labels);
    }

    /* Pass 2: every exact entry reached by a larger CFG is an alias candidate. */
    for (int i = 0; i < n; i++) {
        if (!safe[i]) continue;
        AddrSet instrs, labels;
        addrset_init(&instrs); addrset_init(&labels);
        scan_function(rom, all_funcs->addrs[i], &instrs, &labels,
                      NULL, 0, NULL, 0, NULL, NULL, 0, cfg);
        for (int k = 0; k < instrs.count; k++) {
            int j = function_entry_index(instrs.addrs[k], all_funcs->addrs, n);
            if (j < 0 || j == i) continue;
            /* Mere sequential decoding across an entry is not proof that the
             * earlier routine owns it: some ROMs place data or a new routine
             * after code with no syntactic terminator. Require an actual
             * intra-CFG branch/JMP edge to the entry. scan_function records
             * those exact static targets in labels. */
            if (!addrset_contains(&labels, instrs.addrs[k])) continue;
            bool larger = sizes[i] > sizes[j];
            bool equal_tie = sizes[i] == sizes[j]
                          && all_funcs->addrs[i] < all_funcs->addrs[j];
            if (!larger && !equal_tie) continue;
            if (sizes[i] > best_sizes[j]
                    || (sizes[i] == best_sizes[j]
                        && all_funcs->addrs[i] < owners[j])) {
                owners[j] = all_funcs->addrs[i];
                best_sizes[j] = sizes[i];
            }
        }
        addrset_free(&instrs); addrset_free(&labels);
    }

    /* Collapse chains so every alias names the canonical host directly. */
    for (int i = 0; i < n; i++) {
        uint32_t owner = owners[i];
        for (int guard = 0; guard < n; guard++) {
            int oi = function_entry_index(owner, all_funcs->addrs, n);
            if (oi < 0 || owners[oi] == owner) break;
            owner = owners[oi];
        }
        owners[i] = owner;
    }

    addrset_init(hard_boundaries);
    for (int i = 0; i < n; i++) {
        if (owners[i] == all_funcs->addrs[i])
            addrset_insert(hard_boundaries, all_funcs->addrs[i]);
    }
    addrset_sort(hard_boundaries);

    /* Removing aliases from the boundary set can expose a host CFG, but other
     * canonical boundaries may still cut that walk before a proposed alias.
     * Prove every final host->entry route under the actual boundary policy;
     * promote any unreachable proposal back to a canonical function. Repeat
     * because each promotion can introduce a new boundary for another host. */
    for (;;) {
        bool changed = false;
        for (int h = 0; h < n; h++) {
            uint32_t host = all_funcs->addrs[h];
            if (owners[h] != host) continue;
            AddrSet instrs, labels;
            addrset_init(&instrs); addrset_init(&labels);
            scan_function(rom, host, &instrs, &labels,
                          hard_boundaries->addrs, hard_boundaries->count,
                          NULL, 0, NULL, NULL, 0, cfg);
            for (int j = 0; j < n; j++) {
                if (owners[j] != host || j == h) continue;
                if (!addrset_contains(&instrs, all_funcs->addrs[j])) {
                    owners[j] = all_funcs->addrs[j];
                    addrset_insert(hard_boundaries, all_funcs->addrs[j]);
                    changed = true;
                }
            }
            addrset_free(&instrs); addrset_free(&labels);
        }
        if (!changed) break;
        addrset_sort(hard_boundaries);
    }

    int aliases = n - hard_boundaries->count;
    bool enabled = cfg && cfg->function_aliases;
    if (verbose) {
        free(s_candidate_owners);
        s_candidate_owners = (uint32_t *)malloc((size_t)n * sizeof(uint32_t));
        s_candidate_owner_count = s_candidate_owners ? n : 0;
        if (s_candidate_owners)
            memcpy(s_candidate_owners, owners, (size_t)n * sizeof(uint32_t));
    }
    if (!enabled) {
        /* Analysis is useful before rollout, but candidate aliases must not
         * perturb a proven game until its runtime suite accepts them. */
        for (int i = 0; i < n; i++) owners[i] = all_funcs->addrs[i];
        addrset_free(hard_boundaries);
        addrset_init(hard_boundaries);
        for (int i = 0; i < n; i++)
            addrset_insert(hard_boundaries, all_funcs->addrs[i]);
        addrset_sort(hard_boundaries);
    }
    if (verbose) {
        if (enabled)
            printf("[Codegen] Entry ownership: %d canonical functions, %d "
                   "overlapping aliases (aliases do not split hosts)\n",
                   hard_boundaries->count, aliases);
        else
            printf("[Codegen] Entry ownership audit: %d branch-proven alias "
                   "candidates (disabled; established boundaries retained)\n",
                   aliases);
    }

    free(sizes);
    free(best_sizes);
    free(safe);
    return owners;
}

/* =========================================================================
 * Emit one instruction — big switch
 * ========================================================================= */

/* =========================================================================
 * Cycle-accurate VBlank: per-instruction 68K cycle cost.
 *
 * Values derived from the Motorola 68000 Programmer's Reference Manual
 * (Appendix B, "Instruction Timing"), cross-checked against the
 * interpreter's cost code in
 *   clownmdemu-core/libraries/clown68000/source/interpreter/clown68000.c
 * lines 399-463 (EA-mode costs) and per-instruction microcode.
 *
 * Data-dependent costs (MULx/DIVx result magnitude, Dn-register shift
 * counts, BTST on memory with dynamic bit index) use averages near the
 * mid-range of the PRM spec. Structural costs (size, addressing mode,
 * MOVEM register count, immediate shift count) are exact.
 *
 * Callers emit `g_cycle_accumulator += N;` once per non-terminator
 * instruction; the accumulator fires glue_check_vblank when it crosses
 * g_vblank_threshold (109,312 cycles = scanline 224).
 * ========================================================================= */


/* One nominal timing policy is shared by generated code and the live floor. */
static int estimate_cycles_prm(const M68KInstr *instr)
{return (int)m68k_68000_nominal_cycles(instr);}

/* Per-address record of the EXACT cost the generated code was stamped with.
 * Emitted as <prefix>_cycles.c so the Tier-3 interpreter floor charges the
 * SAME cost the recompiled code does — otherwise the two disagree on
 * g_audio_cycle_counter, which drives audio-stamp pacing. Indexed by addr>>1
 * (68K instructions are word-aligned); 0 = not recorded. */
static uint16_t *g_insn_cost_by_addr = NULL;   /* [GENESIS_ROM_MAX_SIZE / 2] */
static void insn_cost_record(uint32_t addr, int cost) {
    if (!g_insn_cost_by_addr)
        g_insn_cost_by_addr = (uint16_t *)calloc(GENESIS_ROM_MAX_SIZE / 2, sizeof(uint16_t));
    if (g_insn_cost_by_addr && addr < GENESIS_ROM_MAX_SIZE && cost > 0 && cost < 0x10000)
        g_insn_cost_by_addr[addr >> 1] = (uint16_t)cost;
}
/* Emit the sorted (addr,cost) table (called from main after codegen). */
void emit_insn_cost_table(FILE *f) {
    fprintf(f, "/* AUTO-GENERATED per-instruction cycle costs — do not edit.\n"
               " * The EXACT costs the recompiled code was stamped with by the\n"
               " * clean-room timing model. game_cycles.c looks these up so the\n"
               " * Tier-3 interpreter floor paces identically. */\n");
    fprintf(f, "#include \"game_cycles.h\"\n\n");
    fprintf(f, "const GameInsnCost g_game_insn_costs[] = {\n");
    size_t n = 0;
    if (g_insn_cost_by_addr) {
        for (uint32_t i = 0; i < GENESIS_ROM_MAX_SIZE / 2; i++) {
            if (g_insn_cost_by_addr[i]) {
                fprintf(f, "{0x%06Xu,%u},", i << 1, g_insn_cost_by_addr[i]);
                if ((++n & 7u) == 0) fprintf(f, "\n");
            }
        }
    }
    fprintf(f, "\n};\nconst size_t g_game_insn_cost_count = %zuu;\n", n);
}

/* --- Cycle-model census (always available, opt-in at runtime) -------------
 * Set GENESIS_CYCLE_DIAG=<path> to have every estimate_cycles() call append
 * one CSV row. The recompiler already visits every instruction, so the log is
 * a complete census of the codegen run rather than a sampled window — no
 * arming, no timing window to miss.
 *
 * Columns: addr,opcode,mnemonic,size,cost -- cost is what was emitted.
 * Diffing two censuses is how a change to the timing model is reviewed now
 * that there is no interpreter to compare against. The census never
 * influences the emitted cost, so enabling it cannot change generated code. */
static FILE *g_cycle_diag_f    = NULL;
static int   g_cycle_diag_init = 0;

static FILE *cycle_diag_file(void)
{
    if (!g_cycle_diag_init) {
        const char *path = getenv("GENESIS_CYCLE_DIAG");
        g_cycle_diag_init = 1;
        if (path && *path) {
            g_cycle_diag_f = m68k_fopen(path, "w");
            if (g_cycle_diag_f)
                fprintf(g_cycle_diag_f, "addr,opcode,mnemonic,size,cost\n");
        }
    }
    return g_cycle_diag_f;
}

/* Sole cycle-cost entry point. The clean-room model IS the cost, so codegen is
 * deterministic and reproducible from the ROM and config alone. */
static int estimate_cycles(const M68KInstr *instr)
{
    int cost = estimate_cycles_prm(instr);

    FILE *diag = cycle_diag_file();
    if (diag) {
        fprintf(diag, "0x%06X,0x%04X,%d,%d,%d\n",
                instr->addr, instr->words[0], (int)instr->mnemonic,
                (int)instr->size, cost);
    }

    insn_cost_record(instr->addr, cost);
    return cost;
}

/* emit_mem_shift — the 68K memory shift/rotate forms (opcode size field == 11,
 * instr->mem_shift set by the decoder). These always shift a single 16-bit
 * memory operand by exactly 1 bit; the destination EA is in src_ea. Emitted as
 * an RMW on the EA (load word → shift/rotate by 1 → store word → set flags),
 * mirroring the NEG/NOT <ea> RMW pattern. Count is always 1, so the
 * register-shift count==0 exception never applies here. */
static void emit_mem_shift(FILE *f, const M68KInstr *instr,
                           uint32_t addr, ExtReader *er) {
    char src_expr[256];
    char res[64];
    char tmp[32];
    snprintf(res, sizeof(res), "_%06Xr", addr);
    snprintf(tmp, sizeof(tmp), "_t%06X", addr);

    ExtReader er_save = *er;
    emit_ea_load_ex(f, instr, instr->src_ea, M68K_SIZE_W, er, tmp, src_expr, 1);

    fprintf(f, "  { uint16_t _sv = (uint16_t)(%s);\n", src_expr);
    fprintf(f, "    uint16_t %s; uint32_t _c;\n", res);

    switch (instr->mnemonic) {
    case MN_ASR:
        fprintf(f, "    %s = (uint16_t)((int16_t)_sv >> 1);\n", res);
        fprintf(f, "    _c = _sv & 1u;\n");
        break;
    case MN_ASL:
        fprintf(f, "    %s = (uint16_t)(_sv << 1);\n", res);
        fprintf(f, "    _c = (_sv >> 15) & 1u;\n");
        break;
    case MN_LSR:
        fprintf(f, "    %s = (uint16_t)(_sv >> 1);\n", res);
        fprintf(f, "    _c = _sv & 1u;\n");
        break;
    case MN_LSL:
        fprintf(f, "    %s = (uint16_t)(_sv << 1);\n", res);
        fprintf(f, "    _c = (_sv >> 15) & 1u;\n");
        break;
    case MN_ROR:
        fprintf(f, "    %s = (uint16_t)((_sv >> 1) | (_sv << 15));\n", res);
        fprintf(f, "    _c = _sv & 1u;\n");
        break;
    case MN_ROL:
        fprintf(f, "    %s = (uint16_t)((_sv << 1) | (_sv >> 15));\n", res);
        fprintf(f, "    _c = (_sv >> 15) & 1u;\n");
        break;
    case MN_ROXR:
        fprintf(f, "    uint32_t _x = (g_cpu.SR >> 4) & 1u;\n");
        fprintf(f, "    %s = (uint16_t)((_sv >> 1) | (_x << 15));\n", res);
        fprintf(f, "    _c = _sv & 1u;\n");
        break;
    case MN_ROXL:
        fprintf(f, "    uint32_t _x = (g_cpu.SR >> 4) & 1u;\n");
        fprintf(f, "    %s = (uint16_t)((_sv << 1) | _x);\n", res);
        fprintf(f, "    _c = (_sv >> 15) & 1u;\n");
        break;
    default:
        break;
    }

    /* Flags. ROL/ROR do NOT affect X (clear N,Z,V,C; keep X). All others
     * (ASd/LSd/ROXd) set X = C. ASL additionally sets V if the sign bit
     * changed during the 1-bit shift; all other forms clear V. */
    if (instr->mnemonic == MN_ROL || instr->mnemonic == MN_ROR) {
        fprintf(f, "    g_cpu.SR &= ~(0x0Fu);\n");
        fprintf(f, "    if (!%s) g_cpu.SR |= (1u<<2);\n", res);
        fprintf(f, "    if (%s >> 15) g_cpu.SR |= (1u<<3);\n", res);
        fprintf(f, "    if (_c) g_cpu.SR |= (1u<<0);\n");
    } else {
        fprintf(f, "    g_cpu.SR &= ~(0x1Fu);\n");
        fprintf(f, "    if (!%s) g_cpu.SR |= (1u<<2);\n", res);
        fprintf(f, "    if (%s >> 15) g_cpu.SR |= (1u<<3);\n", res);
        if (instr->mnemonic == MN_ASL)
            fprintf(f, "    if ((uint16_t)(_sv ^ %s) >> 15) g_cpu.SR |= (1u<<1);\n", res);
        fprintf(f, "    if (_c) { g_cpu.SR |= (1u<<0); g_cpu.SR |= (1u<<4); }\n");
    }

    *er = er_save;
    emit_ea_store_ex(f, instr, instr->src_ea, M68K_SIZE_W, er, res, 1);
    fprintf(f, "  }\n");
}

static unsigned step_operand_cost(unsigned ea,bool is_long);

static void emit_instr(FILE *f, const GenesisRom *rom,
                        const M68KInstr *instr,
                        const AddrSet *instrs,
                        bool *skip_until_label,
                        int *has_sp_adjust,
                        const char *func_name,
                        uint32_t func_addr, bool step_runtime) {
    uint32_t addr = instr->addr;
    M68KSize sz   = instr->size;
    s_diag_func_name = func_name;
    s_diag_func_addr = func_addr;
    s_diag_instr     = instr;

    /* Unique temp-var suffix based on address */
    char tmp[32];
    snprintf(tmp, sizeof(tmp), "_t%06X", addr);

    ExtReader er;
    er_init(&er, instr);

    char src_expr[256], addr_expr[256];

    if (ws_site_for_kind(addr, WS_SITE_GAME_HOOK, WS_SITE_GAME_HOOK))
        fprintf(f, "  if (genesis_game_instruction_hook(0x%06Xu)) return; /* game-owned extension */\n", addr);

    /* [widescreen] post-patch widening: when this instruction's address is a
     * configured add/sub-margin site, emit a word-sized adjustment of the named
     * data register by (g_ws_margin >> shift) BEFORE the instruction's own C.
     * g_ws_margin is 0 unless the runner has armed widescreen for this frame, so
     * the adjustment is a no-op (byte-identical 4:3) when off. (mask10 sites are
     * handled in the MN_ANDI case — they widen the mask immediate directly.) */
    {
        const WsSite *_ws = ws_site_for_kind(addr, WS_SITE_ADDREG, WS_SITE_SUBREG);
        if (_ws && (_ws->kind == WS_SITE_ADDREG || _ws->kind == WS_SITE_SUBREG)) {
            const char *op = (_ws->kind == WS_SITE_ADDREG) ? "+" : "-";
            unsigned sc = _ws->scale ? _ws->scale : 1;
            fprintf(f, "  /* [widescreen] D%u %s= %u*(g_ws_margin>>%u) */\n",
                    _ws->reg, op, sc, _ws->shift);
            fprintf(f, "  g_cpu.D[%u] = (g_cpu.D[%u] & 0xFFFF0000u) | "
                       "(uint16_t)((int16_t)g_cpu.D[%u] %s (int16_t)((g_ws_margin >> %u) * %u));\n",
                    _ws->reg, _ws->reg, _ws->reg, op, _ws->shift, sc);
        }
    }

    switch (instr->mnemonic) {

    /* ------------------------------------------------------------------ */
    case MN_NOP:
        fprintf(f, "  /* NOP */\n");
        break;

    /* ------------------------------------------------------------------ */
    case MN_RTS:
        /* A stack skip can discard MORE than one return slot (SMPS's
         * stop-track command uses addq.w #8,sp). Carry the complete count
         * through the C callers; a boolean loses the second unwind and
         * resumes code the guest deliberately skipped. Tail edges do not
         * consume this count; each actual JSR/BSR caller consumes one. */
        if (*has_sp_adjust) {
            fprintf(f, "  if (_sp_popped >= 4) { g_rte_pending = _sp_popped / 4; _sp_popped = 0; }\n");
            fprintf(f, "  else if (g_split_sp_popped >= 4) { g_rte_pending = g_split_sp_popped / 4; g_split_sp_popped = 0; }\n");
        } else {
            fprintf(f, "  if (g_split_sp_popped >= 4) { g_rte_pending = g_split_sp_popped / 4; g_split_sp_popped = 0; }\n");
        }
        emit_cycle_accounting(f, "  ", estimate_cycles(instr));
        fprintf(f, "  return;\n");
        *skip_until_label = true;
        break;

    /* ------------------------------------------------------------------ */
    case MN_RTE:
        /* Restore exception frame from supervisor stack (SR then PC, per 68K ABI).
         * glue_service_vblank() pushes the frame before calling the handler, so
         * this pop is always balanced.  g_rte_pending unwinds the C call chain.
         *
         * NOTE: This exception frame push/pop was added for verification consistency
         * (to eliminate stack-offset divergences in dual-execution mode).  In Sonic 1,
         * no game code inside the VBlank/HBlank handlers reads the exception frame
         * bytes directly, so the frame is semantically inert for correct execution.
         * Once the native recompilation is fully verified and dual-execution mode is
         * retired, this push (in glue_service_vblank) and these pops could be removed
         * and replaced with the simpler original: `g_rte_pending = 1; return;`
         * The manual `g_cpu.SR = saved_sr` restore in glue_service_vblank would then
         * need to be reinstated as the sole SR restore mechanism. */
        fprintf(f, "  g_cpu.SR = (uint16_t)m68k_read16(g_cpu.A[7]); g_cpu.A[7] += 2; /* RTE: pop SR */\n");
        fprintf(f, "  g_cpu.PC = m68k_read32(g_cpu.A[7]);            g_cpu.A[7] += 4; /* RTE: pop PC */\n");
        emit_cycle_accounting(f, "  ", estimate_cycles(instr));
        fprintf(f, "  g_rte_pending = 1; return; /* RTE */\n");
        *skip_until_label = true;
        break;

    /* ------------------------------------------------------------------ */
    case MN_STOP:
        /* STOP #imm: load imm into SR, halt until an interrupt of higher
         * priority than I-mask. genesis_stop_until_interrupt is the
         * runtime hook that yields control until the next VBlank /
         * HBlank service runs (which raises the relevant IRQ).
         *
         * Real-hardware behaviour after the interrupt RTEs is to resume
         * at the instruction following STOP. Our flat call model can't
         * cleanly express that — function_finder still treats STOP as a
         * static terminator and the post-STOP bytes typically aren't in
         * the codegen instr set. So we yield and return, matching the
         * prior (comment-only) emission's control-flow shape but adding
         * real SR + yield semantics. */
        fprintf(f, "  g_cpu.SR = (uint16_t)0x%04Xu;\n",
                (unsigned)(instr->imm32 & 0xFFFFu));
        emit_cycle_accounting(f, "  ", estimate_cycles(instr));
        fprintf(f, "  genesis_stop_until_interrupt((uint16_t)0x%04Xu);\n",
                (unsigned)(instr->imm32 & 0xFFFFu));
        fprintf(f, "  return; /* STOP — yield+return, see comment above */\n");
        *skip_until_label = true;
        break;

    /* ------------------------------------------------------------------ */
    case MN_TRAP: {
        /* TRAP #N (vectors 0x20..0x2F). Games such as Phantasy Star IV use
         * TRAPs as subroutine calls: the handler is ordinary ROM code that
         * RTEs back to the next instruction. Model it as a call, like
         * JSR/BSR: build the 68000 exception frame (PC, then SR; SR ends at
         * the lower address), set S and clear T (the I mask is unchanged),
         * call the handler, then consume the RTE signal its RTE raises and
         * continue inline. The handler's generated RTE pops this frame and
         * restores SR, so A7 and SR come back exactly as on hardware.
         *
         * Supervisor-only, like the rest of this model (RTE does not swap
         * stacks either): Genesis games run with S=1, so A7 is the SSP.
         *
         * Only a discovered handler is called directly (discovery registers
         * every ROM trap handler; see function_finder_trap_handler). The
         * Tier-3 framed capsule cannot stand in for one: it runs to a depth-0
         * RTS, so it would execute the handler's RTE and then the caller's
         * own continuation. Anything else — a vector into RAM, a garbage
         * vector, a blacklisted handler — still aborts loudly at runtime. */
        unsigned trap_num = (unsigned)(instr->imm32 & 0xF);
        uint32_t handler;
        if (function_finder_trap_handler(rom, trap_num, &handler) &&
            func_is_known(handler)) {
            /* Cycles are charged by the per-instruction tail after this
             * case, as for JSR; charging here too would double-count. */
            fprintf(f, "  { /* TRAP #%u -> $%06X */\n", trap_num, handler);
            fprintf(f, "    uint16_t _trap_sr = g_cpu.SR;\n");
            fprintf(f, "    g_cpu.A[7] -= 4; m68k_write32(g_cpu.A[7], 0x%06Xu); /* push PC */\n",
                    instr->addr + instr->byte_length);
            fprintf(f, "    g_cpu.A[7] -= 2; m68k_write16(g_cpu.A[7], _trap_sr); /* push SR */\n");
            fprintf(f, "    g_cpu.SR = (uint16_t)((_trap_sr | 0x2000u) & 0x7FFFu); /* S=1, T=0 */\n");
            fprintf(f, "    int _saved_split_sp_popped = g_split_sp_popped; g_split_sp_popped = 0;\n");
            fprintf(f, "    recomp_call_func(func_%06X);\n", handler);
            fprintf(f, "    g_split_sp_popped = _saved_split_sp_popped;\n");
            fprintf(f, "    if (g_rte_pending) --g_rte_pending; /* consume the handler's RTE */\n");
            fprintf(f, "  }\n");
        } else {
            emit_cycle_accounting(f, "  ", estimate_cycles(instr));
            fprintf(f, "  m68k_trap_vector(0x%02Xu); return;\n", 0x20u + trap_num);
            *skip_until_label = true;
        }
        break;
    }

    /* ------------------------------------------------------------------ */
    case MN_TRAPV:
        /* Vector 7 — only fires when V is set. Falls through otherwise. */
        fprintf(f, "  if (g_cpu.SR & %s) {\n", SR_V);
        emit_cycle_accounting(f, "    ", estimate_cycles(instr));
        fprintf(f, "    m68k_trap_vector(7u); return;\n");
        fprintf(f, "  }\n");
        break;

    /* ------------------------------------------------------------------ */
    case MN_RTR:
        /* Pop CCR (low byte of pushed word) then PC, like RTE but only
         * the user-visible CCR bits get restored. Mirrors the RTE
         * propagation idiom so unwind reaches the original caller. */
        fprintf(f, "  { uint16_t _ccrw = (uint16_t)m68k_read16(g_cpu.A[7]); g_cpu.A[7] += 2;\n");
        fprintf(f, "    g_cpu.SR = (uint16_t)((g_cpu.SR & 0xFF00u) | (_ccrw & 0x00FFu)); }\n");
        fprintf(f, "  g_cpu.PC = m68k_read32(g_cpu.A[7]); g_cpu.A[7] += 4;\n");
        emit_cycle_accounting(f, "  ", estimate_cycles(instr));
        fprintf(f, "  g_rte_pending = 1; return; /* RTR */\n");
        *skip_until_label = true;
        break;

    /* ------------------------------------------------------------------ */
    case MN_RESET:
        /* RESET pulses the external /RESET line; CPU registers are
         * unaffected. The runtime hook decides what (if anything) to
         * re-init — for Sonic 1 the runner already brought devices up
         * in runtime_init() before this instruction can execute, so the
         * hook is empty. Calling through it (rather than emitting a
         * comment) keeps the codegen behaviour honest with the rule
         * that every site has real semantics. */
        fprintf(f, "  genesis_reset_devices();\n");
        break;

    /* ------------------------------------------------------------------ */
    case MN_ILLEGAL:
        /* 0x4AFC, A-line, F-line — runtime picks the right vector. */
        emit_cycle_accounting(f, "  ", estimate_cycles(instr));
        fprintf(f, "  m68k_illegal_trap(0x%06Xu, 0x%04Xu); return;\n",
                addr, (unsigned)instr->words[0]);
        *skip_until_label = true;
        break;

    /* ------------------------------------------------------------------ */
    case MN_BSR:
    case MN_JSR: {
        int ea   = instr->src_ea;
        int mode = (ea >> 3) & 7;
        int reg  = ea & 7;
        uint32_t ret_addr = instr->addr + instr->byte_length;

        /* [widescreen] call_widen: preset the row-block count and retarget the
         * call to a sibling entry that skips the callee's own count reset, so
         * only THIS caller widens (not every caller of the shared callee). The
         * ret-address push/pop below is unchanged. margin 0 => preset == base,
         * target gets the same count it would have set => byte-identical 4:3. */
        uint32_t bsr_target = instr->target_addr;
        {
            const WsSite *_wsc = ws_site_for_kind(addr, WS_SITE_CALL_WIDEN, WS_SITE_CALL_WIDEN);
            if (instr->has_target && _wsc && _wsc->kind == WS_SITE_CALL_WIDEN) {
                fprintf(f, "  /* [widescreen] call_widen: D%u = %u + (g_ws_margin>>%u); "
                           "retarget 0x%06X -> 0x%06X */\n",
                        _wsc->reg, _wsc->base, _wsc->shift, instr->target_addr, _wsc->target);
                fprintf(f, "  g_cpu.D[%u] = (uint32_t)((int32_t)%u + (int32_t)(g_ws_margin >> %u));\n",
                        _wsc->reg, _wsc->base, _wsc->shift);
                bsr_target = _wsc->target;
            }
        }

        /* Obj_WaitOffscreen idiom: the callee unconditionally pops our pushed
         * return address off the stack (`move.l (sp)+,$34(a0)`) and repurposes
         * it as an object code pointer, so its eventual rts returns to OUR
         * caller — never to ret_addr. Emit a non-returning tail transfer: push
         * the return (so the callee's `(sp)+` reads it), call, then return.
         * Do NOT pop again (the callee already did — a second pop would
         * double-adjust A7) and do NOT fall through to ret_addr (that address,
         * when it is code, is a separate dispatch entry reached later via the
         * object's restored code pointer, not by linear fall-through). Without
         * this the recompiled caller runs ret_addr a frame early, corrupting
         * the object's state machine (e.g. the AIZ MonkeyDude body). */
        if (instr->has_target &&
            function_finder_pops_return_unconditionally(rom, instr->target_addr)) {
            fprintf(f, "  recomp_push_return(0x%06Xu); /* JSR push (callee captures return) */\n",
                    ret_addr);
            fprintf(f, "  { int _saved_split_sp_popped = g_split_sp_popped; g_split_sp_popped = 0;\n");
            if (func_is_native_rom(rom,instr->target_addr))
                fprintf(f, "    RECOMP_CALL_NATIVE(func_%06X);\n", instr->target_addr);
            else
                fprintf(f, "    recomp_call_addr(0x%06Xu);\n", instr->target_addr);
            fprintf(f, "    g_split_sp_popped = _saved_split_sp_popped;\n");
            fprintf(f, "  }\n");
            fprintf(f, "  g_rte_pending = 0; /* callee captured our return; handled here */\n");
            emit_cycle_accounting(f, "  ", estimate_cycles(instr));
            fprintf(f, "  return; /* callee captured return addr: no pop, no fall-through */\n");
            *skip_until_label = true;
            break;
        }

        /* Simulate JSR/BSR stack: push the return address, then remember the
         * actual slot address. recomp_push_return() may first canonicalize a
         * sign-extended A7 to the Genesis' 24-bit RAM address. */
        fprintf(f, "  uint32_t _jsr_pre_sp_%06X = g_cpu.A[7];\n", addr);
        fprintf(f, "  recomp_push_return(0x%06Xu); /* JSR push */\n", ret_addr);
        fprintf(f, "  uint32_t _jsr_slot_sp_%06X = g_cpu.A[7];\n", addr);

        if (instr->has_target) {
            fprintf(f, "  { int _saved_split_sp_popped = g_split_sp_popped; g_split_sp_popped = 0;\n");
            if (func_is_native_rom(rom,bsr_target))
                fprintf(f, "    RECOMP_CALL_NATIVE(func_%06X);\n", bsr_target);
            else
                fprintf(f, "    recomp_call_addr(0x%06Xu); /* JSR target not in func table */\n",
                        bsr_target);
            fprintf(f, "    g_split_sp_popped = _saved_split_sp_popped;\n");
            fprintf(f, "  }\n");
        } else if (mode == 2 || mode == 5 || mode == 6 ||
                   (mode == 7 && reg <= 3)) {
            char ae[256];
            emit_ea_addr_ex(f, instr, ea, &er, ae, true);
            fprintf(f, "  { int _saved_split_sp_popped = g_split_sp_popped; g_split_sp_popped = 0;\n");
            fprintf(f, "    recomp_call_addr(%s);\n", ae);
            fprintf(f, "    g_split_sp_popped = _saved_split_sp_popped;\n");
            fprintf(f, "  }\n");
        } else {
            codegen_diag_record(CGD_TODO_DYNAMIC_JSR_UNSUPPORTED, addr,
                                instr->words[0], instr->mnemonic,
                                func_name, func_addr);
            fprintf(f, "  /* TODO: dynamic JSR/BSR EA %d/%d */\n", mode, reg);
        }

        /* A normal callee leaves this wrapper's return slot in place. A nested
         * skip-return may consume it before unwinding its generated C frames,
         * leaving A7 at slot_sp + 4; that is also valid and the wrapper must
         * not synthesize a second pop below. */
        fprintf(f,
                "  if (!g_rte_pending && g_cpu.A[7] != "
                "_jsr_slot_sp_%06X && "
                "g_cpu.A[7] != (uint32_t)(_jsr_slot_sp_%06X + 4u) && "
                "getenv(\"GENESIS_STRICT_JSR_STACK\")) {\n",
                addr, addr);
        if (instr->has_target) {
            fprintf(f,
                    "    fprintf(stderr, \"JSR stack mismatch at $%06X -> "
                    "$%06X: pre=$%%08X slot=$%%08X post=$%%08X\\n\", "
                    "_jsr_pre_sp_%06X, _jsr_slot_sp_%06X, g_cpu.A[7]);\n",
                    addr, bsr_target, addr, addr);
        } else {
            fprintf(f,
                    "    fprintf(stderr, \"dynamic JSR stack mismatch at "
                    "$%06X: pre=$%%08X slot=$%%08X post=$%%08X\\n\", "
                    "_jsr_pre_sp_%06X, _jsr_slot_sp_%06X, g_cpu.A[7]);\n",
                    addr, addr, addr);
        }
        fprintf(f, "    exit(3);\n");
        fprintf(f, "  }\n");

        /* Pop return address from 68K stack.
         * Check g_rte_pending BEFORE the pop: when the callee used the
         * `addq.l #4,sp; rts` skip idiom, the game's own addq already
         * adjusted A7 and SJ's rts popped the slot this wrapper pushed.
         * Doing our pop here would double-adjust A7 by +4. Skipping the
         * pop keeps A7 in sync with hardware. Consume one skipped return
         * slot; additional skipped slots continue through outer callers. */
        fprintf(f, "  if (g_rte_pending) { --g_rte_pending;\n");
        emit_cycle_accounting(f, "    ", estimate_cycles(instr));
        fprintf(f, "    return; } /* RTE/skip propagation (pre-pop) */\n");
        fprintf(f,
                "  if (g_cpu.A[7] != (uint32_t)(_jsr_slot_sp_%06X + 4u))\n"
                "    g_cpu.A[7] += 4; /* normal JSR pop */\n"
                "  else\n"
                "    ; /* nested skip-return already consumed this slot */\n",
                addr);
        break;
    }

    /* ------------------------------------------------------------------ */
    case MN_JMP: {
        int ea   = instr->src_ea;
        int mode = (ea >> 3) & 7;
        int reg  = ea & 7;
        if (instr->has_target) {
            audit_record(instr->addr, func_addr, instr->target_addr,
                         JMPAUDIT_STATIC_TARGET, 0);
            if (addrset_contains(instrs, instr->target_addr)) {
                emit_cycle_accounting(f, "  ", estimate_cycles(instr));
                fprintf(f, "  goto label_%06X;\n", instr->target_addr);
            } else {
                emit_split_tail_call(f, rom,"  ", instr->target_addr, *has_sp_adjust != 0,
                                     estimate_cycles(instr));
            }
        } else if (mode == 2 || mode == 5 || mode == 6 ||
                   (mode == 7 && (reg == 0 || reg == 1))) {
            audit_record(instr->addr, func_addr, 0,
                         JMPAUDIT_DYNAMIC_REGISTER, 0);
            char ae[256];
            emit_ea_addr_ex(f, instr, ea, &er, ae, true);
            emit_split_tail_call_expr(f, "  ", ae, *has_sp_adjust != 0,
                                      estimate_cycles(instr));
        } else if (mode == 7 && reg == 3) {
            /* JMP (d8,PC,Xn) — indexed jump.  Three patterns we recognise:
             *   (a) Duff's device: the table base is the first of a uniform
             *       sequence of in-function instructions (CPZ/HPZ scroll).
             *   (b) Offset table to interior labels: `dc.w (target - base)`
             *       entries point to anonymous local labels of the same
             *       function (ObjB2_* DEZ-boss state machines).
             *   (c) Anything else (e.g. bra.w-trampoline / function-entry
             *       tables, where the target IS a registered function):
             *       runtime dispatch via hybrid_jmp_interpret. */
            uint32_t pc_addr = instr->addr + er.bp;
            uint16_t ext = er_next(&er);
            int xreg  = (ext >> 12) & 7;
            int xtype = (ext >> 15) & 1;
            int8_t d8 = (int8_t)(ext & 0xFF);
            const char *xr = xtype ? "g_cpu.A" : "g_cpu.D";
            uint32_t base = pc_addr + (int32_t)d8;

            uint32_t pc_targets[32];
            int npc = probe_pc_idx_targets(rom, instr, instrs, pc_targets,
                                           (int)(sizeof(pc_targets) / sizeof(pc_targets[0])));
            int32_t  ot_offsets[32];
            uint32_t ot_targets[32];
            int not_ = 0;
            if (npc < 2) {
                /* Try the offset-table pattern only if the Duff's-device
                 * probe didn't find a uniform sequence. */
                not_ = probe_offset_table_targets(rom, instr, instrs,
                                                  ot_offsets, ot_targets,
                                                  (int)(sizeof(ot_targets) / sizeof(ot_targets[0])));
            }
            if (npc >= 2) {
                /* Case (a): Duff's-device-style in-function switch. */
                audit_record(instr->addr, func_addr, base,
                             JMPAUDIT_IN_FUNCTION_SWITCH, npc);
                fprintf(f, "  /* JMP table at $%06X: in-function dispatch — base $%06X + %s[%d], %d targets (Duff's device) */\n",
                        instr->addr, base, xr + 6 /* skip "g_cpu." */, xreg, npc);
                emit_cycle_accounting(f, "  ", estimate_cycles(instr));
                fprintf(f, "  switch ((int32_t)m68k_brief_index_value(0x%04Xu, "
                        "g_cpu.D[%d], g_cpu.A[%d])) {\n", ext, xreg, xreg);
                { int32_t seen_offsets[512]; int seen_count = 0;
                  for (int t = 0; t < npc; t++) {
                    int32_t off = (int32_t)(pc_targets[t] - base);
                    int dup = 0;
                    for (int s = 0; s < seen_count; s++) if (seen_offsets[s] == off) { dup = 1; break; }
                    if (dup) continue;
                    seen_offsets[seen_count++] = off;
                    fprintf(f, "    case %d: goto label_%06X;\n", off, pc_targets[t]);
                } }
                fprintf(f, "    default: hybrid_jmp_interpret(0x%08Xu + "
                        "m68k_brief_index_value(0x%04Xu, g_cpu.D[%d], g_cpu.A[%d])); return;\n",
                        base, ext, xreg, xreg);
                fprintf(f, "  }\n");
            } else if (not_ >= 1) {
                /* Case (b): offset-table dispatch — `dc.w (target - base)`
                 * rows pointing to interior labels (anonymous `+:` / `-:`
                 * in asm68k). Only emitted when EVERY discovered target is
                 * in the disasm's seed list (strict filter — see
                 * probe_offset_table_targets). */
                audit_record(instr->addr, func_addr, base,
                             JMPAUDIT_IN_FUNCTION_SWITCH, not_);
                fprintf(f, "  /* JMP table at $%06X: in-function dispatch — base $%06X + %s[%d], %d targets (offset table) */\n",
                        instr->addr, base, xr + 6 /* skip "g_cpu." */, xreg, not_);
                emit_cycle_accounting(f, "  ", estimate_cycles(instr));
                fprintf(f, "  switch ((int32_t)m68k_brief_index_value(0x%04Xu, "
                        "g_cpu.D[%d], g_cpu.A[%d])) {\n", ext, xreg, xreg);
                { int seen_offsets[512]; int seen_count = 0;
                  for (int t = 0; t < not_; t++) {
                    int dup = 0;
                    for (int s = 0; s < seen_count; s++) if (seen_offsets[s] == ot_offsets[t]) { dup = 1; break; }
                    if (dup) continue;
                    seen_offsets[seen_count++] = ot_offsets[t];
                    fprintf(f, "    case %d: goto label_%06X;\n",
                            ot_offsets[t], ot_targets[t]);
                } }
                fprintf(f, "    default: hybrid_jmp_interpret(0x%08Xu + "
                        "m68k_brief_index_value(0x%04Xu, g_cpu.D[%d], g_cpu.A[%d])); return;\n",
                        base, ext, xreg, xreg);
                fprintf(f, "  }\n");
            } else {
                /* Case (c): nothing recognised — fall back to runtime dispatch. */
                audit_record(instr->addr, func_addr, base,
                             JMPAUDIT_FALLBACK_HYBRID, 0);
                fprintf(f, "  /* JMP table at $%06X: interpret handler at base $%06X + %s[%d] */\n",
                        instr->addr, base, xr + 6 /* skip "g_cpu." */, xreg);
                emit_cycle_accounting(f, "  ", estimate_cycles(instr));
                fprintf(f, "  hybrid_jmp_interpret(0x%08Xu + "
                        "m68k_brief_index_value(0x%04Xu, g_cpu.D[%d], g_cpu.A[%d]));\n",
                        base, ext, xreg, xreg);
                fprintf(f, "  return;\n");
            }
        } else {
            audit_record(instr->addr, func_addr, 0,
                         JMPAUDIT_UNSUPPORTED, 0);
            codegen_diag_record(CGD_TODO_DYNAMIC_JMP_UNSUPPORTED, addr,
                                instr->words[0], MN_JMP,
                                func_name, func_addr);
            emit_cycle_accounting(f, "  ", estimate_cycles(instr));
            fprintf(f, "  /* TODO: dynamic JMP mode %d/%d */ return;\n", mode, reg);
        }
        *skip_until_label = true;
        break;
    }

    /* ------------------------------------------------------------------ */
    case MN_BRA:
        if (instr->has_target) {
            if (addrset_contains(instrs, instr->target_addr)) {
                emit_cycle_accounting(f, "  ", estimate_cycles(instr));
                fprintf(f, "  goto label_%06X;\n", instr->target_addr);
            } else {
                emit_split_tail_call(f, rom,"  ", instr->target_addr, *has_sp_adjust != 0,
                                     estimate_cycles(instr));
            }
        } else {
            codegen_diag_record(CGD_BRANCH_WITHOUT_TARGET, addr,
                                instr->words[0], MN_BRA,
                                func_name, func_addr);
            emit_cycle_accounting(f, "  ", estimate_cycles(instr));
            fprintf(f, "  /* BRA with no target */ return;\n");
        }
        *skip_until_label = true;
        break;

    /* ------------------------------------------------------------------ */
    case MN_Bcc: {
        int cond = (instr->words[0] >> 8) & 0xF;
        const char *ce = bcc_cond_expr(cond);
        /* [widescreen] cull_left: widen a left-edge `bmi` so it fires at
         * (int16)D[reg] < -(g_ws_margin>>shift) instead of < 0. D[reg] still
         * holds the value the bmi's flags reflect (set by the preceding
         * add.w/sub.w), so at margin 0 this is byte-identical to the original
         * bmi (N flag). Non-mutating, so a right-edge cmpi sharing the register
         * still sees the unmodified value. Only valid on `bmi` (MI == 11). */
        char ws_cull_cond[200];
        {
            const WsSite *_wsc = ws_site_for_kind(addr, WS_SITE_CULL_LEFT, WS_SITE_CULL_WINDOW_LEFT);
            if (_wsc && _wsc->kind == WS_SITE_CULL_LEFT) {
                if (cond == 0xB) {   /* MI */
                    snprintf(ws_cull_cond, sizeof ws_cull_cond,
                             "((int16_t)g_cpu.D[%u] < -(int16_t)(g_ws_margin >> %u))",
                             _wsc->reg, _wsc->shift);
                    ce = ws_cull_cond;
                } else {
                    fprintf(f, "  /* [widescreen] cull_left @%06X ignored: "
                               "Bcc cond %d is not bmi(MI) */\n", addr, cond);
                }
            } else if (_wsc && _wsc->kind == WS_SITE_CULL_WINDOW_LEFT) {
                /* [widescreen] cull_window_left: extend a left-window clamp. MUTATE
                 * D[reg] -= (margin>>shift) (the rest of the routine uses the
                 * widened edge) and REPLACE the `bhi` with a SIGNED `> 0` test
                 * (the mutate destroys the borrow `bhi` used; `bgt` is the correct
                 * equivalent — matches the disasm). margin 0 => unchanged + bgt==bhi. */
                if (cond == 0x2) {   /* HI */
                    fprintf(f, "  /* [widescreen] cull_window_left: D%u -= (g_ws_margin>>%u); bhi->bgt */\n",
                            _wsc->reg, _wsc->shift);
                    fprintf(f, "  g_cpu.D[%u] = (g_cpu.D[%u] & 0xFFFF0000u) | "
                               "(uint16_t)((int16_t)g_cpu.D[%u] - (int16_t)(g_ws_margin >> %u));\n",
                            _wsc->reg, _wsc->reg, _wsc->reg, _wsc->shift);
                    snprintf(ws_cull_cond, sizeof ws_cull_cond,
                             "((int16_t)g_cpu.D[%u] > 0)", _wsc->reg);
                    ce = ws_cull_cond;
                } else {
                    fprintf(f, "  /* [widescreen] cull_window_left @%06X ignored: "
                               "Bcc cond %d is not bhi(HI) */\n", addr, cond);
                }
            }
        }
        if (instr->has_target) {
            if (g_yield_in_next_bne) {
                /* IRQ-flag-spin loop-back path: the previous tst set
                 * the polled-flag's Z bit; we're about to branch back
                 * to retest. Yield first so the runner can advance
                 * clownmdemu and let the IRQ handler clear the flag.
                 * Falls through naturally when the flag is clear. */
                if (addrset_contains(instrs, instr->target_addr)) {
                    fprintf(f, "  if (%s) {\n", ce);
                    emit_cycle_accounting(f, "    ", estimate_cycles(instr));
                    fprintf(f, "    glue_yield_for_interrupt_poll(); goto label_%06X;\n",
                            instr->target_addr);
                    fprintf(f, "  }\n");
                } else {
                    fprintf(f, "  if (%s) {\n", ce);
                    emit_cycle_accounting(f, "    ", estimate_cycles(instr));
                    fprintf(f, "    glue_yield_for_interrupt_poll();\n");
                    emit_split_tail_call(f, rom,"    ", instr->target_addr, *has_sp_adjust != 0,
                                         -1);
                    fprintf(f, "  }\n");
                }
                g_yield_in_next_bne = false;
            } else if (addrset_contains(instrs, instr->target_addr)) {
                fprintf(f, "  if (%s) {\n", ce);
                emit_cycle_accounting(f, "    ", estimate_cycles(instr));
                fprintf(f, "    goto label_%06X;\n", instr->target_addr);
                fprintf(f, "  }\n");
            } else {
                fprintf(f, "  if (%s) {\n", ce);
                emit_split_tail_call(f, rom,"    ", instr->target_addr, *has_sp_adjust != 0,
                                     estimate_cycles(instr));
                fprintf(f, "  }\n");
            }
        } else {
            codegen_diag_record(CGD_BRANCH_WITHOUT_TARGET, addr,
                                instr->words[0], MN_Bcc,
                                func_name, func_addr);
            fprintf(f, "  /* Bcc no target */\n");
        }
        break;
    }

    /* ------------------------------------------------------------------ */
    case MN_DBcc: {
        int cond = (instr->words[0] >> 8) & 0xF;
        int dreg = instr->words[0] & 7;
        const char *ce = bcc_cond_expr(cond);
        fprintf(f, "  if (!(%s)) {\n", ce);
        /* Truncate subtraction to uint16_t before widening — prevents
         * 0x0000 - 1 = 0xFFFFFFFF from clobbering the high word. */
        fprintf(f, "    g_cpu.D[%d] = (g_cpu.D[%d] & 0xFFFF0000u) | (uint32_t)((uint16_t)((uint16_t)(g_cpu.D[%d]) - 1u));\n",
                dreg, dreg, dreg);
        fprintf(f, "    if ((int16_t)g_cpu.D[%d] != -1) {\n", dreg);
        if (instr->has_target) {
            if (addrset_contains(instrs, instr->target_addr)) {
                emit_cycle_accounting(f, "      ", estimate_cycles(instr));
                fprintf(f, "      goto label_%06X;\n", instr->target_addr);
            } else {
                emit_split_tail_call(f, rom,"      ", instr->target_addr, *has_sp_adjust != 0,
                                     estimate_cycles(instr));
            }
        }
        fprintf(f, "    }\n  }\n");
        break;
    }

    /* ------------------------------------------------------------------ */
    case MN_MOVEQ: {
        uint32_t imm = instr->imm32; /* pre-sign-extended to 32 */
        int dreg = instr->reg;
        char expr[96];
        /* [widescreen] addimm/subimm: widen the loaded immediate by
         * +/-(g_ws_margin>>shift) in place (tile-load column seed / row-block
         * count). margin 0 => identical. */
        const WsSite *_wsi = ws_site_for_kind(addr, WS_SITE_ADDIMM, WS_SITE_SUBIMM);
        if (_wsi && (_wsi->kind == WS_SITE_ADDIMM || _wsi->kind == WS_SITE_SUBIMM)) {
            const char *op = (_wsi->kind == WS_SITE_ADDIMM) ? "+" : "-";
            fprintf(f, "  /* [widescreen] moveq #imm %s (g_ws_margin>>%u) */\n",
                    op, _wsi->shift);
            fprintf(f, "  g_cpu.D[%d] = (uint32_t)((int32_t)0x%08Xu %s "
                       "(int32_t)(g_ws_margin >> %u));\n",
                    dreg, imm, op, _wsi->shift);
            snprintf(expr, sizeof(expr),
                     "(uint32_t)((int32_t)0x%08Xu %s (int32_t)(g_ws_margin >> %u))",
                     imm, op, _wsi->shift);
        } else {
            fprintf(f, "  g_cpu.D[%d] = 0x%08Xu;\n", dreg, imm);
            snprintf(expr, sizeof(expr), "(uint32_t)0x%08Xu", imm);
        }
        /* flags: N,Z; clear V,C */
        emit_flags_logic(f, expr, M68K_SIZE_L);
        break;
    }

    /* ------------------------------------------------------------------ */
    case MN_MOVE: {
        /* words[1..]: src EA ext, then dst EA ext */
        int src_ea  = instr->src_ea;
        int dst_ea  = instr->dst_ea;
        int src_mode = (src_ea >> 3) & 7;
        int src_reg  = src_ea & 7;
        int src_ext  = ea_ext_words_count(src_mode, src_reg, sz);

        /* ExtReader for source starting at wi=1 */
        ExtReader er_src;
        er_init(&er_src, instr);

        /* ExtReader for dest starting right after src extension words */
        ExtReader er_dst;
        er_init_at(&er_dst, instr, 1 + src_ext);

        char stmp[32];
        snprintf(stmp, sizeof(stmp), "_ts%06X", addr);

        emit_ea_load(f, instr, src_ea, sz, &er_src, stmp, src_expr);

        /* [widescreen] addmem: widen a memory-sourced moved value by
         * +(g_ws_margin>>shift), capped at the word `base` bytes after it —
         * the store half of the camera min-bound clamp (must produce the SAME
         * capped value the paired cmp addmem compared against). */
        const WsSite *_wsam = ws_site_for_kind(addr, WS_SITE_ADDMEM, WS_SITE_ADDMEM);
        char wsmv[64];
        if (_wsam && ws_emit_addmem_wrap(f, _wsam, addr, instr, src_ea, sz,
                                         src_expr, wsmv, sizeof(wsmv))) {
            emit_ea_store(f, instr, dst_ea, sz, &er_dst, wsmv);
            emit_flags_logic(f, wsmv, sz);
            break;
        }
        /* [widescreen] addimm/subimm: widen the moved immediate by
         * +/-(g_ws_margin>>shift) before the store (e.g. move.w #320,d5 ->
         * right-edge tile-load column seed). margin 0 => identical. */
        const WsSite *_wsm = ws_site_for_kind(addr, WS_SITE_ADDIMM, WS_SITE_SUBIMM);
        if (_wsm && (_wsm->kind == WS_SITE_ADDIMM || _wsm->kind == WS_SITE_SUBIMM)) {
            const char *op = (_wsm->kind == WS_SITE_ADDIMM) ? "+" : "-";
            char wmov[300];
            snprintf(wmov, sizeof(wmov),
                     "(uint32_t)((int32_t)(%s) %s (int32_t)(g_ws_margin >> %u))",
                     src_expr, op, _wsm->shift);
            fprintf(f, "  /* [widescreen] move #imm %s (g_ws_margin>>%u) */\n",
                    op, _wsm->shift);
            emit_ea_store(f, instr, dst_ea, sz, &er_dst, wmov);
            emit_flags_logic(f, wmov, sz);
        } else {
            emit_ea_store(f, instr, dst_ea, sz, &er_dst, src_expr);
            /* Update N,Z; clear V,C */
            emit_flags_logic(f, src_expr, sz);
        }
        if (*has_sp_adjust) {
            /* A7 advances by two even for a byte operand. Track bytes so
             * two word data pushes balance one longword data pop. */
            int stack_bytes = sz == M68K_SIZE_L ? 4 : 2;
            if (src_ea == ((EA_An_POST << 3) | 7))
                fprintf(f, "  _sp_popped += %d; /* MOVE (SP)+ bytes */\n", stack_bytes);
            if (dst_ea == ((EA_An_PRE << 3) | 7))
                fprintf(f, "  _sp_popped -= %d; /* MOVE -(SP) bytes */\n", stack_bytes);
        }
        break;
    }

    /* ------------------------------------------------------------------ */
    case MN_MOVEA: {
        /* Sign-extend .W source to 32; no flags */
        int areg = instr->reg;
        emit_ea_load(f, instr, instr->src_ea, sz, &er, tmp, src_expr);
        if (sz == M68K_SIZE_W) {
            fprintf(f, "  g_cpu.A[%d] = (uint32_t)(int32_t)(int16_t)(%s);\n", areg, src_expr);
        } else {
            fprintf(f, "  g_cpu.A[%d] = (uint32_t)(%s);\n", areg, src_expr);
        }
        if (*has_sp_adjust
                && instr->src_ea == ((EA_An_POST << 3) | 7))
            fprintf(f, "  _sp_popped += %d; /* MOVEA (SP)+ bytes */\n",
                    sz == M68K_SIZE_L ? 4 : 2);
        break;
    }

    /* ------------------------------------------------------------------ */
    case MN_LEA: {
        int areg = instr->reg;
        emit_ea_addr(f, instr, instr->src_ea, &er, addr_expr);
        fprintf(f, "  g_cpu.A[%d] = %s;\n", areg, addr_expr);
        break;
    }

    /* ------------------------------------------------------------------ */
    case MN_PEA: {
        emit_ea_addr(f, instr, instr->src_ea, &er, addr_expr);
        fprintf(f, "  g_cpu.A[7] -= 4; m68k_write32(g_cpu.A[7], %s);\n", addr_expr);
        if (*has_sp_adjust)
            fprintf(f, "  _sp_popped -= 4; /* PEA pushes one longword */\n");
        break;
    }

    /* ------------------------------------------------------------------ */
    case MN_ADD:
        emit_alu_arith(f, instr, sz, &er, tmp, addr, "+", emit_flags_add);
        break;

    /* ------------------------------------------------------------------ */
    case MN_ADDA: {
        int areg = instr->reg;
        emit_ea_load(f, instr, instr->src_ea, sz, &er, tmp, src_expr);
        if (sz == M68K_SIZE_W)
            fprintf(f, "  g_cpu.A[%d] += (uint32_t)(int32_t)(int16_t)(%s);\n", areg, src_expr);
        else
            fprintf(f, "  g_cpu.A[%d] += (uint32_t)(%s);\n", areg, src_expr);
        if (areg == 7 && instr->src_ea == ((7 << 3) | 4) && *has_sp_adjust)
            fprintf(f, "  _sp_popped += (int32_t)(%s%s); /* ADDA immediate stack bytes */\n",
                    sz == M68K_SIZE_W ? "(int16_t)" : "", src_expr);
        break;
    }

    /* ------------------------------------------------------------------ */
    case MN_ADDQ: {
        uint32_t imm = instr->imm32;
        int ea   = instr->src_ea;
        int mode = (ea >> 3) & 7;
        int reg  = ea & 7;
        const char *ct = size_ctype(sz);

        if (mode == 1) {
            /* ADDQ to An: no flags */
            fprintf(f, "  g_cpu.A[%d] += %uu;\n", reg, imm);
            /* Account data releases as well as whole return-slot skips. */
            if (reg == 7 && imm > 0 && *has_sp_adjust) {
                fprintf(f, "  _sp_popped += %u;\n", imm);
            }
        } else {
            /* RMW: use emit_ea_load_ex with rmw=1 so (An)+ doesn't
             * double-increment (read suppresses increment, store does it) */
            emit_ea_load_ex(f, instr, ea, sz, &er, tmp, src_expr, 1);
            char res[64];
            snprintf(res, sizeof(res), "_%06Xr", addr);
            fprintf(f, "  %s %s = (%s)((%s)(%s) + (%s)%uu);\n",
                    ct, res, ct, ct, src_expr, ct, imm);
            char da[256], db[256];
            snprintf(da, sizeof(da), "(%s)(%s)", ct, src_expr);
            snprintf(db, sizeof(db), "(%s)%uu", ct, imm);
            emit_flags_add(f, da, db, res, sz);
            ExtReader er2;
            er_init(&er2, instr);
            emit_ea_store_ex(f, instr, ea, sz, &er2, res, 1);
        }
        break;
    }

    /* ------------------------------------------------------------------ */
    case MN_ADDI: {
        uint32_t imm = er_next_imm(&er, sz);
        emit_alui_arith(f, instr, sz, &er, tmp, addr, imm, "+", emit_flags_add);
        break;
    }

    /* ------------------------------------------------------------------ */
    case MN_SUB:
        emit_alu_arith(f, instr, sz, &er, tmp, addr, "-", emit_flags_sub);
        break;

    /* ------------------------------------------------------------------ */
    case MN_SUBA: {
        int areg = instr->reg;
        emit_ea_load(f, instr, instr->src_ea, sz, &er, tmp, src_expr);
        if (sz == M68K_SIZE_W)
            fprintf(f, "  g_cpu.A[%d] -= (uint32_t)(int32_t)(int16_t)(%s);\n", areg, src_expr);
        else
            fprintf(f, "  g_cpu.A[%d] -= (uint32_t)(%s);\n", areg, src_expr);
        if (areg == 7 && instr->src_ea == ((7 << 3) | 4) && *has_sp_adjust)
            fprintf(f, "  _sp_popped -= (int32_t)(%s%s); /* SUBA immediate stack bytes */\n",
                    sz == M68K_SIZE_W ? "(int16_t)" : "", src_expr);
        break;
    }

    /* ------------------------------------------------------------------ */
    case MN_SUBQ: {
        uint32_t imm = instr->imm32;
        int ea   = instr->src_ea;
        int mode = (ea >> 3) & 7;
        int reg  = ea & 7;
        const char *ct = size_ctype(sz);

        if (mode == 1) {
            fprintf(f, "  g_cpu.A[%d] -= %uu;\n", reg, imm);
            /* Reverse of the ADDQ early-exit pattern: pushing onto the stack
             * cancels a pending early return level. */
            if (reg == 7 && imm > 0 && *has_sp_adjust) {
                fprintf(f, "  _sp_popped -= %u;\n", imm);
            }
        } else {
            /* RMW: suppress (An)+ increment on read */
            emit_ea_load_ex(f, instr, ea, sz, &er, tmp, src_expr, 1);
            char res[64];
            snprintf(res, sizeof(res), "_%06Xr", addr);
            fprintf(f, "  %s %s = (%s)((%s)(%s) - (%s)%uu);\n",
                    ct, res, ct, ct, src_expr, ct, imm);
            char da[256], db[256];
            snprintf(da, sizeof(da), "(%s)(%s)", ct, src_expr);
            snprintf(db, sizeof(db), "(%s)%uu", ct, imm);
            emit_flags_sub(f, da, db, res, sz);
            ExtReader er2;
            er_init(&er2, instr);
            emit_ea_store_ex(f, instr, ea, sz, &er2, res, 1);
        }
        break;
    }

    /* ------------------------------------------------------------------ */
    case MN_SUBI: {
        uint32_t imm = er_next_imm(&er, sz);
        emit_alui_arith(f, instr, sz, &er, tmp, addr, imm, "-", emit_flags_sub);
        break;
    }

    /* ------------------------------------------------------------------ */
    case MN_AND:
        emit_alu_logic(f, instr, sz, &er, tmp, addr,
                       (instr->words[0] >> 8) & 1, "&");
        break;

    /* ------------------------------------------------------------------ */
    case MN_OR:
        emit_alu_logic(f, instr, sz, &er, tmp, addr,
                       (instr->words[0] >> 8) & 1, "|");
        break;

    /* ------------------------------------------------------------------ */
    case MN_EOR:
        /* EOR has only the Dn → EA form (no Dn-destination variant). */
        emit_alu_logic(f, instr, sz, &er, tmp, addr, 1, "^");
        break;

    /* ------------------------------------------------------------------ */
    case MN_ORI: {
        uint32_t imm = er_next_imm(&er, sz);
        emit_alui_logic(f, instr, sz, &er, tmp, addr, imm, "|");
        break;
    }

    /* ------------------------------------------------------------------ */
    case MN_ANDI: {
        uint32_t imm = er_next_imm(&er, sz);
        /* [widescreen] mask10: widen the mask one low bit ($1FF -> $3FF) so a
         * 9-bit sprite-X clips past 512 instead of wrapping into the left edge.
         * Unconditional (not g_ws_margin-gated) is byte-identical at 4:3 because
         * the masked sprite-X never sets the new high bit there (4:3 max ~448 <
         * 512) — proven by the earlier 4:3 parity validation. Precondition: only
         * mark sites whose masked value can't set bit `imm+1` at 4:3. */
        const WsSite *_ws = ws_site_for_kind(addr, WS_SITE_MASK10, WS_SITE_MASK10);
        if (_ws && _ws->kind == WS_SITE_MASK10)
            imm = (imm << 1) | 1u;
        emit_alui_logic(f, instr, sz, &er, tmp, addr, imm, "&");
        break;
    }

    /* ------------------------------------------------------------------ */
    case MN_EORI: {
        uint32_t imm = er_next_imm(&er, sz);
        emit_alui_logic(f, instr, sz, &er, tmp, addr, imm, "^");
        break;
    }

    /* ------------------------------------------------------------------ */
    /* Immediate-to-CCR / -to-SR (Phase 3B).
     * CCR forms touch only the low byte of SR; SR forms touch the full
     * word. Privilege-violation modeling for SR forms is out of scope
     * (this recompiler doesn't track supervisor mode separately yet).
     * The mask forced on ANDI #imm,CCR keeps the upper byte set so we
     * don't wipe supervisor + interrupt-mask bits — same rationale as
     * the SMPS-audio fix that previously guarded the inline branch. */
    case MN_ORI_TO_CCR:
        fprintf(f, "  g_cpu.SR |= 0x%02Xu; /* ORI #imm,CCR */\n",
                (unsigned)(instr->imm32 & 0xFFu));
        break;
    case MN_ORI_TO_SR:
        fprintf(f, "  g_cpu.SR |= 0x%04Xu; /* ORI #imm,SR */\n",
                (unsigned)(instr->imm32 & 0xFFFFu));
        break;
    case MN_ANDI_TO_CCR:
        fprintf(f, "  g_cpu.SR &= 0x%04Xu; /* ANDI #imm,CCR */\n",
                (unsigned)(0xFF00u | (instr->imm32 & 0xFFu)));
        break;
    case MN_ANDI_TO_SR:
        /* Lowering the mask can make a pending V-int takeable before the
         * next instruction: glue_sr_written() delivers it there. */
        fprintf(f, "  g_cpu.SR &= 0x%04Xu; /* ANDI #imm,SR */\n"
                   "  glue_sr_written();\n",
                (unsigned)(instr->imm32 & 0xFFFFu));
        break;
    case MN_EORI_TO_CCR:
        fprintf(f, "  g_cpu.SR ^= 0x%02Xu; /* EORI #imm,CCR */\n",
                (unsigned)(instr->imm32 & 0xFFu));
        break;
    case MN_EORI_TO_SR:
        fprintf(f, "  g_cpu.SR ^= 0x%04Xu; /* EORI #imm,SR */\n"
                   "  glue_sr_written();\n",
                (unsigned)(instr->imm32 & 0xFFFFu));
        break;

    /* ------------------------------------------------------------------ */
    case MN_CMP: {
        int dreg = instr->reg;
        const char *ct = size_ctype(sz);
        emit_ea_load(f, instr, instr->src_ea, sz, &er, tmp, src_expr);
        /* [widescreen] addmem: widen the memory-sourced compare value by
         * +(g_ws_margin>>shift), capped at the word `base` bytes after it
         * (camera min-bound clamp). margin 0 => identical. */
        char wsv[64];
        const char *csrc = src_expr;
        const WsSite *_wsam = ws_site_for_kind(addr, WS_SITE_ADDMEM, WS_SITE_ADDMEM);
        if (_wsam && ws_emit_addmem_wrap(f, _wsam, addr, instr, instr->src_ea, sz,
                                         src_expr, wsv, sizeof(wsv)))
            csrc = wsv;
        char res[64];
        snprintf(res, sizeof(res), "_%06Xr", addr);
        fprintf(f, "  %s %s = (%s)((%s)g_cpu.D[%d] - (%s)(%s));\n",
                ct, res, ct, ct, dreg, ct, csrc);
        char da[256], db[256];
        snprintf(da, sizeof(da), "(%s)g_cpu.D[%d]", ct, dreg);
        snprintf(db, sizeof(db), "(%s)(%s)", ct, csrc);
        emit_flags_cmp(f, da, db, res, sz);
        break;
    }

    /* ------------------------------------------------------------------ */
    case MN_CMPA: {
        int areg = instr->reg;
        emit_ea_load(f, instr, instr->src_ea, sz, &er, tmp, src_expr);
        /* Always 32-bit comparison; sign-extend .W source */
        const char *sext = (sz == M68K_SIZE_W) ?
            "(uint32_t)(int32_t)(int16_t)" : "(uint32_t)";
        fprintf(f, "  { uint32_t _cmp_b = %s(%s);\n", sext, src_expr);
        fprintf(f, "    uint32_t _cmp_r = g_cpu.A[%d] - _cmp_b;\n", areg);
        /* CMPA does not affect X flag */
        fprintf(f, "    g_cpu.SR &= ~(0x0Fu);\n");
        fprintf(f, "    if (!_cmp_r) g_cpu.SR |= (1u<<2);\n");
        fprintf(f, "    if (_cmp_r >> 31) g_cpu.SR |= (1u<<3);\n");
        fprintf(f, "    if ((uint32_t)_cmp_b > (uint32_t)g_cpu.A[%d]) { g_cpu.SR |= (1u<<0); }\n", areg);
        fprintf(f, "    if (((g_cpu.A[%d]^_cmp_b) & 0x80000000u) && ((g_cpu.A[%d]^_cmp_r) & 0x80000000u)) g_cpu.SR |= (1u<<1);\n", areg, areg);
        fprintf(f, "  }\n");
        break;
    }

    /* ------------------------------------------------------------------ */
    case MN_CMPM: {
        /* CMPM (Ay)+,(Ax)+ — read/increment source, then read/increment
         * destination. This order matters when Ax and Ay are the same.
         * Compute destination - source as CMP; X is unchanged.
         *
         * 68K quirk: byte-size post-increment on A7 increments by 2
         * to keep the supervisor stack aligned. CMPM (A7)+,(A7)+ is
         * legal but rare. */
        int ay = instr->src_ea & 7;             /* source register   */
        int ax = instr->reg;                    /* destination Ax    */
        int sb = size_bytes(sz);
        int ay_inc = (ay == 7 && sz == M68K_SIZE_B) ? 2 : sb;
        int ax_inc = (ax == 7 && sz == M68K_SIZE_B) ? 2 : sb;
        const char *ct = size_ctype(sz);
        const char *rf = size_read_fn(sz);
        char res[64];
        snprintf(res, sizeof(res), "_%06Xr", addr);
        fprintf(f,
            "  { %s _cmpm_s = (%s)%s(g_cpu.A[%d]);\n"
            "    g_cpu.A[%d] += %d;\n"
            "    %s _cmpm_d = (%s)%s(g_cpu.A[%d]);\n"
            "    g_cpu.A[%d] += %d;\n"
            "    %s %s = (%s)(_cmpm_d - _cmpm_s);\n",
            ct, ct, rf, ay,
            ay, ay_inc,
            ct, ct, rf, ax,
            ax, ax_inc,
            ct, res, ct);
        char da[64], db[64];
        snprintf(da, sizeof(da), "_cmpm_d");
        snprintf(db, sizeof(db), "_cmpm_s");
        emit_flags_cmp(f, da, db, res, sz);
        fprintf(f,"  }\n");
        break;
    }

    /* ------------------------------------------------------------------ */
    case MN_CMPI: {
        uint32_t imm = er_next_imm(&er, sz);
        const char *ct = size_ctype(sz);
        emit_ea_load(f, instr, instr->src_ea, sz, &er, tmp, src_expr);
        char res[64];
        snprintf(res, sizeof(res), "_%06Xr", addr);
        fprintf(f, "  %s %s = (%s)((%s)(%s) - (%s)0x%Xu);\n",
                ct, res, ct, ct, src_expr, ct, imm);
        char da[256], db[256];
        snprintf(da, sizeof(da), "(%s)(%s)", ct, src_expr);
        snprintf(db, sizeof(db), "(%s)0x%Xu", ct, imm);
        emit_flags_cmp(f, da, db, res, sz);
        break;
    }

    /* ------------------------------------------------------------------ */
    case MN_CLR: {
        /* Write 0 to EA. Per 68K spec: Z=1, N=V=C=0, **X unchanged**.
         * Earlier emission cleared X too, which broke any code path that
         * relied on the X bit set by an earlier arithmetic op surviving
         * across a CLR. Notably the SMPS sound driver: PSG track update
         * does CLR.B SMPS_Track.VolEnvIndex(a5) inside FinishTrackUpdate,
         * silently zeroing the X flag set by the earlier subi.b in
         * PSGSetFreq — corrupting downstream Bcc paths that read X
         * (squelched notes, drift). */
        /* The original 68000 reads memory CLR operands before clearing them.
         * Emit both phases as one RMW so (An)+ / -(An) update once, and use
         * matching extension readers so each phase resolves the same EA. */
        ExtReader read_er; er_init(&read_er, instr);
        char discarded[256];
        emit_ea_load_ex(f, instr, instr->src_ea, sz, &read_er, tmp, discarded, 1);
        ExtReader write_er; er_init(&write_er, instr);
        emit_ea_store_ex(f, instr, instr->src_ea, sz, &write_er, "0", 1);
        fprintf(f, "  g_cpu.SR = (g_cpu.SR & ~0x0Fu) | (1u<<2);\n");
        break;
    }

    /* ------------------------------------------------------------------ */
    case MN_NEG: {
        const char *ct = size_ctype(sz);
        emit_ea_load_ex(f, instr, instr->src_ea, sz, &er, tmp, src_expr, 1);
        char res[64];
        snprintf(res, sizeof(res), "_%06Xr", addr);
        fprintf(f, "  %s %s = (%s)(0 - (%s)(%s));\n",
                ct, res, ct, ct, src_expr);
        emit_flags_sub(f, "0", src_expr, res, sz);
        {
            ExtReader er2; er_init(&er2, instr);
            emit_ea_store_ex(f, instr, instr->src_ea, sz, &er2, res, 1);
        }
        break;
    }

    /* ------------------------------------------------------------------ */
    case MN_NOT: {
        const char *ct = size_ctype(sz);
        emit_ea_load_ex(f, instr, instr->src_ea, sz, &er, tmp, src_expr, 1);
        char res[64];
        snprintf(res, sizeof(res), "_%06Xr", addr);
        fprintf(f, "  %s %s = (%s)(~(%s)(%s));\n",
                ct, res, ct, ct, src_expr);
        emit_flags_logic(f, res, sz);
        {
            ExtReader er2; er_init(&er2, instr);
            emit_ea_store_ex(f, instr, instr->src_ea, sz, &er2, res, 1);
        }
        break;
    }

    /* ------------------------------------------------------------------ */
    case MN_TST: {
        emit_ea_load(f, instr, instr->src_ea, sz, &er, tmp, src_expr);
        emit_flags_logic(f, src_expr, sz);
        break;
    }

    /* ------------------------------------------------------------------ */
    case MN_BTST: {
        /* Static (#n): reg==-1, bit number in imm32, EA ext at words[2].
         * Dynamic (Dn): reg>=0, bit number in D[reg], EA ext at words[1]. */
        int dreg    = instr->reg;
        int is_imm  = (dreg < 0);
        int ea      = instr->src_ea;
        int ea_mode = (ea >> 3) & 7;
        /* Bit count: 32 for Dn dest, 8 for memory */
        int bit_mask = (ea_mode == 0) ? 31 : 7;
        /* Memory BTST is always byte-wide on 68K, even if instruction word implies word */
        M68KSize btst_sz = (ea_mode == 0) ? M68K_SIZE_L : M68K_SIZE_B;

        char bit_expr[64];
        if (is_imm) {
            uint32_t imm = instr->imm32 & (uint32_t)bit_mask;
            snprintf(bit_expr, sizeof(bit_expr), "%uu", imm);
            er_init_at(&er, instr, 2); /* skip bit-number extension word */
        } else {
            snprintf(bit_expr, sizeof(bit_expr), "(uint32_t)g_cpu.D[%d] & %uu", dreg, (unsigned)bit_mask);
        }
        emit_ea_load(f, instr, ea, btst_sz, &er, tmp, src_expr);
        fprintf(f,
            "  { uint32_t _bn = %s;\n"
            "    g_cpu.SR = (g_cpu.SR & ~(1u<<2)) | (!((uint32_t)(%s) & (1u<<_bn)) ? (1u<<2) : 0u); }\n",
            bit_expr, src_expr);
        break;
    }

    /* ------------------------------------------------------------------ */
    case MN_BCHG:
        emit_bitop_modify(f, instr, sz, &er, tmp, addr, "^ ");
        break;

    /* ------------------------------------------------------------------ */
    case MN_BCLR:
        emit_bitop_modify(f, instr, sz, &er, tmp, addr, "& ~");
        break;

    /* ------------------------------------------------------------------ */
    case MN_BSET:
        emit_bitop_modify(f, instr, sz, &er, tmp, addr, "| ");
        break;

    /* ------------------------------------------------------------------ */
    case MN_SWAP: {
        int dreg = instr->reg;
        fprintf(f,
            "  g_cpu.D[%d] = (g_cpu.D[%d] >> 16) | (g_cpu.D[%d] << 16);\n",
            dreg, dreg, dreg);
        char expr[64];
        snprintf(expr, sizeof(expr), "g_cpu.D[%d]", dreg);
        emit_flags_logic(f, expr, M68K_SIZE_L);
        break;
    }

    /* ------------------------------------------------------------------ */
    case MN_EXT: {
        int dreg = instr->reg;
        if (sz == M68K_SIZE_W) {
            /* sign-extend byte to word */
            fprintf(f,
                "  g_cpu.D[%d] = (g_cpu.D[%d] & 0xFFFF0000u) | (uint32_t)(uint16_t)(int16_t)(int8_t)(g_cpu.D[%d]);\n",
                dreg, dreg, dreg);
            char expr[64];
            snprintf(expr, sizeof(expr), "(uint16_t)g_cpu.D[%d]", dreg);
            emit_flags_logic(f, expr, M68K_SIZE_W);
        } else {
            /* sign-extend word to long */
            fprintf(f,
                "  g_cpu.D[%d] = (uint32_t)(int32_t)(int16_t)g_cpu.D[%d];\n",
                dreg, dreg);
            char expr[64];
            snprintf(expr, sizeof(expr), "g_cpu.D[%d]", dreg);
            emit_flags_logic(f, expr, M68K_SIZE_L);
        }
        break;
    }

    /* ------------------------------------------------------------------ */
    case MN_LSL:
    case MN_LSR: {
        if (instr->mem_shift) { emit_mem_shift(f, instr, addr, &er); break; }
        int dreg  = instr->reg;
        bool left = (instr->mnemonic == MN_LSL);
        bool reg_count = (instr->src_ea >= 0);
        const char *ct = size_ctype(sz);
        int bits = size_bits(sz);
        char res[64];
        snprintf(res, sizeof(res), "_%06Xr", addr);

        if (reg_count) {
            /* Register-counted shift: count from Dn at runtime */
            int creg = instr->src_ea;
            fprintf(f, "  { %s _sv = (%s)g_cpu.D[%d];\n", ct, ct, dreg);
            fprintf(f, "    int _cnt = (int)(g_cpu.D[%d] & 63u);\n", creg);
            if (left) {
                fprintf(f, "    %s %s = (_cnt > 0 && _cnt < %d) ? (_sv << _cnt) : (_cnt == 0 ? _sv : (%s)0);\n",
                        ct, res, bits, ct);
                fprintf(f, "    uint32_t _c = (_cnt > 0 && _cnt <= %d) ? ((_sv >> (%d - _cnt)) & 1u) : 0u;\n",
                        bits, bits);
            } else {
                fprintf(f, "    %s %s = (_cnt > 0 && _cnt < %d) ? (_sv >> _cnt) : (_cnt == 0 ? _sv : (%s)0);\n",
                        ct, res, bits, ct);
                fprintf(f, "    uint32_t _c = (_cnt > 0 && _cnt <= %d) ? ((_sv >> (_cnt - 1)) & 1u) : 0u;\n",
                        bits);
            }
            /* V flag for LSL/LSR is always 0 */
        } else {
            /* Immediate-counted shift */
            int count = (int)(instr->imm32 & 63);
            fprintf(f, "  { %s _sv = (%s)g_cpu.D[%d];\n", ct, ct, dreg);
            if (left) {
                fprintf(f, "    %s %s = (%d > 0 && %d < %d) ? (_sv << %d) : (%d == 0 ? _sv : (%s)0);\n",
                        ct, res, count, count, bits, count, count, ct);
                if (count > 0 && count <= bits)
                    fprintf(f, "    uint32_t _c = (%d > 0 && %d <= %d) ? ((_sv >> (%d - %d)) & 1u) : 0u;\n",
                            count, count, bits, bits, count);
                else
                    fprintf(f, "    uint32_t _c = 0u;\n");
            } else {
                fprintf(f, "    %s %s = (%d > 0 && %d < %d) ? (_sv >> %d) : (%d == 0 ? _sv : (%s)0);\n",
                        ct, res, count, count, bits, count, count, ct);
                if (count > 0 && count <= bits)
                    fprintf(f, "    uint32_t _c = (%d <= %d) ? ((_sv >> (%d - 1)) & 1u) : 0u;\n",
                            count, bits, count);
                else
                    fprintf(f, "    uint32_t _c = 0u;\n");
            }
        }
        /* Update Dn */
        emit_store_dn(f, "    ", dreg, res, sz);
        /* Flags. LSL/LSR with shift count == 0 leaves X UNCHANGED; only
         * count > 0 sets X = C = last bit shifted out. Register-counted
         * shifts can hit count == 0 at runtime; immediate-count shifts
         * encode 0 as 8, so they always shift. */
        emit_shift_sr_update(f, res, bits, reg_count, false);
        fprintf(f, "  }\n");
        break;
    }

    /* ------------------------------------------------------------------ */
    case MN_ASL:
    case MN_ASR: {
        if (instr->mem_shift) { emit_mem_shift(f, instr, addr, &er); break; }
        int dreg  = instr->reg;
        bool asr_reg_count = (instr->src_ea >= 0);
        int count = asr_reg_count ? 0 : (int)(instr->imm32 & 63);
        bool left = (instr->mnemonic == MN_ASL);
        const char *ct = size_ctype(sz);
        int bits = size_bits(sz);
        char res[64];
        snprintf(res, sizeof(res), "_%06Xr", addr);

        if (asr_reg_count) {
            /* Register-counted ASL/ASR */
            int creg = instr->src_ea;
            if (left) {
                fprintf(f, "  { %s _sv = (%s)g_cpu.D[%d];\n", ct, ct, dreg);
                fprintf(f, "    int _cnt = (int)(g_cpu.D[%d] & 63u);\n", creg);
                fprintf(f, "    %s %s = (_cnt > 0 && _cnt < %d) ? (_sv << _cnt) : (_cnt == 0 ? _sv : (%s)0);\n",
                        ct, res, bits, ct);
                fprintf(f, "    uint32_t _c = (_cnt > 0 && _cnt <= %d) ? (((uint32_t)_sv >> (%d - _cnt)) & 1u) : 0u;\n",
                        bits, bits);
                /* V = sign bit changed at ANY point during the shift (hardware):
                 * the top (_cnt+1) bits of the source are neither all-0 nor all-1.
                 * The old initial-vs-final-MSB compare missed even-count sign
                 * oscillations. (_sv is unsigned size-width here.) */
                fprintf(f,
                    "    uint32_t _v = 0u;\n"
                    "    if (_cnt > 0) {\n"
                    "      if (_cnt >= %d) _v = ((uint32_t)_sv != 0u) ? 1u : 0u;\n"
                    "      else { uint32_t _top = (uint32_t)_sv >> (%d - 1 - _cnt);\n"
                    "             uint32_t _allm = (_cnt + 1u >= 32u) ? 0xFFFFFFFFu : ((1u << (_cnt + 1u)) - 1u);\n"
                    "             _v = (_top != 0u && _top != _allm) ? 1u : 0u; }\n"
                    "    }\n",
                    bits, bits);
            } else {
                fprintf(f, "  { int%d_t _sv = (int%d_t)(%s)g_cpu.D[%d];\n",
                        bits, bits, ct, dreg);
                fprintf(f, "    int _cnt = (int)(g_cpu.D[%d] & 63u);\n", creg);
                fprintf(f, "    %s %s = (%s)((_cnt > 0 && _cnt < %d) ? (_sv >> _cnt) : (_cnt == 0 ? _sv : (_sv < 0 ? (%s)~(%s)0 : (%s)0)));\n",
                        ct, res, ct, bits, ct, ct, ct);
                /* C = last bit shifted out; once _cnt >= bits the value is all-sign,
                 * so C is the sign bit (hardware), not 0. */
                fprintf(f, "    uint32_t _c = (_cnt == 0) ? 0u : ((_cnt < %d) ? (((uint32_t)_sv >> (_cnt - 1)) & 1u) : (((uint32_t)_sv >> %d) & 1u));\n",
                        bits, bits - 1);
                fprintf(f, "    uint32_t _v = 0u;\n");
            }
        } else if (left) {
            fprintf(f, "  { %s _sv = (%s)g_cpu.D[%d];\n", ct, ct, dreg);
            fprintf(f, "    %s %s = (%d > 0 && %d < %d) ? (_sv << %d) : (%d == 0 ? _sv : (%s)0);\n",
                    ct, res, count, count, bits, count, count, ct);
            fprintf(f, "    uint32_t _c = (%d > 0 && %d <= %d) ? (((uint32_t)_sv >> (%d - %d)) & 1u) : 0u;\n",
                    count, count, bits, bits, count);
            fprintf(f, "    uint32_t _v = 0u;\n");
            /* V = sign changed at ANY point during the shift (hardware): the top
             * (count+1) bits of the source are neither all-0 nor all-1. count is
             * a compile-time constant here, so emit a constant mask. */
            if (count > 0) {
                if (count >= bits) {
                    fprintf(f, "    if ((uint32_t)_sv != 0u) _v = 1u;\n");
                } else {
                    uint32_t _allm = ((count + 1) >= 32) ? 0xFFFFFFFFu
                                                         : ((1u << (count + 1)) - 1u);
                    fprintf(f, "    { uint32_t _top = (uint32_t)_sv >> %d;\n"
                               "      if (_top != 0u && _top != 0x%Xu) _v = 1u; }\n",
                            bits - 1 - count, _allm);
                }
            }
        } else {
            /* ASR: arithmetic right shift */
            fprintf(f, "  { int%d_t _sv = (int%d_t)(%s)g_cpu.D[%d];\n",
                    bits, bits, ct, dreg);
            fprintf(f, "    %s %s = (%s)((%d > 0 && %d < %d) ? (_sv >> %d) : (%d == 0 ? _sv : (_sv < 0 ? (%s)~(%s)0 : (%s)0)));\n",
                    ct, res, ct, count, count, bits, count, count, ct, ct, ct);
            fprintf(f, "    uint32_t _c = (%d > 0 && %d <= %d) ? (((uint32_t)_sv >> (%d - 1)) & 1u) : 0u;\n",
                    count, count, bits, count);
            fprintf(f, "    uint32_t _v = 0u;\n");
        }
        /* Update Dn */
        emit_store_dn(f, "    ", dreg, res, sz);
        /* ASL/ASR with register count == 0 leaves X UNCHANGED (sets C=0, V=0).
         * Immediate count of 0 is decoded as 8, so only register-count form
         * can hit this case at runtime. Mirrors LSL/LSR's _cnt==0 handling. */
        emit_shift_sr_update(f, res, bits, asr_reg_count, true);
        fprintf(f, "  }\n");
        break;
    }

    /* ------------------------------------------------------------------ */
    case MN_ROL:
    case MN_ROR: {
        if (instr->mem_shift) { emit_mem_shift(f, instr, addr, &er); break; }
        int dreg  = instr->reg;
        bool rot_reg_count = (instr->src_ea >= 0);
        int count = rot_reg_count ? 0 : (int)(instr->imm32 & 63);
        bool left = (instr->mnemonic == MN_ROL);
        const char *ct = size_ctype(sz);
        int bits = size_bits(sz);
        int c = count % bits;
        char res[64];
        snprintf(res, sizeof(res), "_%06Xr", addr);

        if (rot_reg_count) {
            int creg = instr->src_ea;
            fprintf(f, "  { %s _sv = (%s)g_cpu.D[%d];\n", ct, ct, dreg);
            fprintf(f, "    int _cnt = (int)(g_cpu.D[%d] & 63u) %% %d;\n", creg, bits);
            if (left) {
                fprintf(f, "    %s %s = _cnt ? ((_sv << _cnt) | (_sv >> (%d - _cnt))) : _sv;\n",
                        ct, res, bits);
                fprintf(f, "    uint32_t _c = (g_cpu.D[%d] & 63u) ? ((uint32_t)%s & 1u) : 0u;\n",
                        creg, res);
            } else {
                fprintf(f, "    %s %s = _cnt ? ((_sv >> _cnt) | (_sv << (%d - _cnt))) : _sv;\n",
                        ct, res, bits);
                fprintf(f, "    uint32_t _c = (g_cpu.D[%d] & 63u) ? ((uint32_t)%s >> %d) : 0u;\n",
                        creg, res, bits - 1);
            }
        } else {
        fprintf(f, "  { %s _sv = (%s)g_cpu.D[%d];\n", ct, ct, dreg);
        if (left) {
            if (c == 0)
                fprintf(f, "    %s %s = _sv;\n", ct, res);
            else
                fprintf(f, "    %s %s = (_sv << %d) | (_sv >> (%d - %d));\n",
                        ct, res, c, bits, c);
            fprintf(f, "    uint32_t _c = %s ? ((uint32_t)%s & 1u) : 0u;\n",
                    count ? "1" : "0", res);
        } else {
            if (c == 0)
                fprintf(f, "    %s %s = _sv;\n", ct, res);
            else
                fprintf(f, "    %s %s = (_sv >> %d) | (_sv << (%d - %d));\n",
                        ct, res, c, bits, c);
            fprintf(f, "    uint32_t _c = %s ? ((uint32_t)%s >> %d) : 0u;\n",
                    count ? "1" : "0", res, bits - 1);
        }
        } /* end !rot_reg_count */
        emit_store_dn(f, "    ", dreg, res, sz);
        fprintf(f, "    g_cpu.SR &= ~(0x0Fu);\n"); /* clear N,Z,V,C; leave X */
        fprintf(f, "    if (!%s) g_cpu.SR |= (1u<<2);\n", res);
        fprintf(f, "    if ((uint32_t)%s >> %d) g_cpu.SR |= (1u<<3);\n", res, bits - 1);
        fprintf(f, "    if (_c) g_cpu.SR |= (1u<<0);\n");
        fprintf(f, "  }\n");
        break;
    }

    /* ------------------------------------------------------------------ */
    case MN_ROXL:
    case MN_ROXR: {
        if (instr->mem_shift) { emit_mem_shift(f, instr, addr, &er); break; }
        int dreg  = instr->reg;
        bool reg_count = (instr->words[0] & 32u) != 0;
        int count = (int)(instr->imm32 & 63);
        bool left = (instr->mnemonic == MN_ROXL);
        const char *ct = size_ctype(sz);
        int bits = size_bits(sz);
        int c = count % (bits + 1); /* rotate through X: period = bits+1 */
        char res[64];
        snprintf(res, sizeof(res), "_%06Xr", addr);

        /* Rotate a (bits+1)-wide value (the operand + X) in 64-bit so the .L
         * case works — the old 32-bit form did `_x << 32` / `>> 33` (undefined,
         * and it dropped the X bit for .L). Matches the Tier-3 interpreter. */
        unsigned long long widemask = ((unsigned long long)1 << (bits + 1)) - 1ull;
        unsigned long long lowmask  = (bits == 32) ? 0xFFFFFFFFull
                                                   : (((unsigned long long)1 << bits) - 1ull);
        fprintf(f, "  { %s _sv = (%s)g_cpu.D[%d];\n", ct, ct, dreg);
        fprintf(f, "    uint64_t _x = (g_cpu.SR >> 4) & 1u;\n");
        fprintf(f, "    uint64_t _wide = ((uint64_t)_sv) | (_x << %d);\n", bits);
        if (reg_count) {
            fprintf(f, "    unsigned _cc = (g_cpu.D[%u] & 63u) %% %uu;\n",
                    (unsigned)instr->src_ea, (unsigned)(bits + 1));
            if (left)
                fprintf(f, "    uint64_t _rot = ((_wide << _cc) | (_wide >> (%u - _cc))) & 0x%llXull;\n",
                        (unsigned)(bits + 1), widemask);
            else
                fprintf(f, "    uint64_t _rot = ((_wide >> _cc) | (_wide << (%u - _cc))) & 0x%llXull;\n",
                        (unsigned)(bits + 1), widemask);
        } else if (c == 0) {
            fprintf(f, "    uint64_t _rot = _wide & 0x%llXull;\n", widemask);
        } else if (left) {
            fprintf(f, "    uint64_t _rot = ((_wide << %d) | (_wide >> %d)) & 0x%llXull;\n",
                    c, bits + 1 - c, widemask);
        } else {
            fprintf(f, "    uint64_t _rot = ((_wide >> %d) | (_wide << %d)) & 0x%llXull;\n",
                    c, bits + 1 - c, widemask);
        }
        fprintf(f, "    %s %s = (%s)(_rot & 0x%llXull);\n", ct, res, ct, lowmask);
        fprintf(f, "    uint32_t _c = (uint32_t)((_rot >> %d) & 1u);\n", bits);
        emit_store_dn(f, "    ", dreg, res, sz);
        fprintf(f, "    g_cpu.SR &= ~(0x1Fu);\n");
        fprintf(f, "    if (!%s) g_cpu.SR |= (1u<<2);\n", res);
        fprintf(f, "    if ((uint32_t)%s >> %d) g_cpu.SR |= (1u<<3);\n", res, bits - 1);
        fprintf(f, "    if (_c) { g_cpu.SR |= (1u<<0); g_cpu.SR |= (1u<<4); }\n");
        fprintf(f, "  }\n");
        break;
    }

    /* ------------------------------------------------------------------ */
    case MN_MULU: {
        int dreg = instr->reg;
        emit_ea_load(f, instr, instr->src_ea, M68K_SIZE_W, &er, tmp, src_expr);
        fprintf(f,
            "  g_cpu.D[%d] = (uint32_t)(uint16_t)g_cpu.D[%d] * (uint32_t)(uint16_t)(%s);\n",
            dreg, dreg, src_expr);
        char expr[64];
        snprintf(expr, sizeof(expr), "g_cpu.D[%d]", dreg);
        emit_flags_logic(f, expr, M68K_SIZE_L);
        break;
    }

    /* ------------------------------------------------------------------ */
    case MN_MULS: {
        int dreg = instr->reg;
        emit_ea_load(f, instr, instr->src_ea, M68K_SIZE_W, &er, tmp, src_expr);
        fprintf(f,
            "  g_cpu.D[%d] = (uint32_t)((int32_t)(int16_t)g_cpu.D[%d] * (int32_t)(int16_t)(%s));\n",
            dreg, dreg, src_expr);
        char expr[64];
        snprintf(expr, sizeof(expr), "g_cpu.D[%d]", dreg);
        emit_flags_logic(f, expr, M68K_SIZE_L);
        break;
    }

    /* ------------------------------------------------------------------ */
    case MN_DIVU: {
        int dreg = instr->reg;
        char tmp2[32], zero[192];
        if(step_runtime)snprintf(zero,sizeof zero,"m68k_step_exception(ctx,5,g_cpu.PC,%u); return;",38u+step_operand_cost((unsigned)instr->src_ea,false));
        else snprintf(zero,sizeof zero,"g_cpu.PC=0x%06Xu; m68k_trap_vector(5u); return;",addr);
        snprintf(tmp2, sizeof(tmp2), "_tv%06X", addr);
        emit_ea_load(f, instr, instr->src_ea, M68K_SIZE_W, &er, tmp2, src_expr);
        /* HW-accurate (matches clown68000 / the Tier-3 floor): on quotient
         * overflow set V+N, clear Z, leave Dn UNCHANGED. C always cleared.
         * On real inputs this is identical to a plain divide (no overflow). */
        fprintf(f,
            "  { uint16_t _dv = (uint16_t)(%s); uint32_t _dest = g_cpu.D[%d];\n"
            "    g_cpu.SR &= ~(1u<<0);\n"
            "    if (_dv == 0u) { %s }\n"
            "    else if ((uint32_t)_dv > (_dest >> 16)) {\n"
            "      uint32_t _quo = _dest / _dv, _rem = _dest %% _dv;\n"
            "      g_cpu.D[%d] = (_quo & 0xFFFFu) | ((_rem & 0xFFFFu) << 16);\n"
            "      g_cpu.SR &= ~((1u<<3)|(1u<<2)|(1u<<1));\n"
            "      if (_quo & 0x8000u) g_cpu.SR |= (1u<<3);\n"
            "      if (_quo == 0u)     g_cpu.SR |= (1u<<2);\n"
            "    } else { g_cpu.SR |= (1u<<1); g_cpu.SR |= (1u<<3); g_cpu.SR &= ~(1u<<2); }\n"
            "  }\n",
            src_expr, dreg, zero, dreg);
        break;
    }

    /* ------------------------------------------------------------------ */
    case MN_DIVS: {
        int dreg = instr->reg;
        char tmp2[32], zero[192];
        if(step_runtime)snprintf(zero,sizeof zero,"m68k_step_exception(ctx,5,g_cpu.PC,%u); return;",38u+step_operand_cost((unsigned)instr->src_ea,false));
        else snprintf(zero,sizeof zero,"g_cpu.PC=0x%06Xu; m68k_trap_vector(5u); return;",addr);
        snprintf(tmp2, sizeof(tmp2), "_tv%06X", addr);
        emit_ea_load(f, instr, instr->src_ea, M68K_SIZE_W, &er, tmp2, src_expr);
        /* HW-accurate signed divide (matches clown68000 / the Tier-3 floor):
         * absolute-value method + unsigned and signed overflow checks; on
         * overflow set V+N, clear Z, leave Dn unchanged. C always cleared. */
        fprintf(f,
            "  { int16_t _dv = (int16_t)(%s); uint32_t _dest = g_cpu.D[%d];\n"
            "    g_cpu.SR &= ~(1u<<0);\n"
            "    if (_dv == 0) { %s }\n"
            "    else {\n"
            "      int _sn = (_dv < 0), _dn = ((int32_t)_dest < 0); int _rn = (_sn != _dn);\n"
            "      uint32_t _asrc = _sn ? (uint32_t)(0 - (int32_t)_dv) : (uint32_t)_dv;\n"
            "      uint32_t _adst = _dn ? (0u - _dest) : _dest;\n"
            "      if (_asrc >= (_adst >> 16)) {\n"
            "        uint32_t _aq = _adst / _asrc;\n"
            "        if (_aq <= (_rn ? 0x8000u : 0x7FFFu)) {\n"
            "          uint32_t _ar = _adst %% _asrc;\n"
            "          uint32_t _quo = _rn ? (0u - _aq) : _aq;\n"
            "          uint32_t _rem = _dn ? (0u - _ar) : _ar;\n"
            "          g_cpu.D[%d] = (_quo & 0xFFFFu) | ((_rem & 0xFFFFu) << 16);\n"
            "          g_cpu.SR &= ~((1u<<3)|(1u<<2)|(1u<<1));\n"
            "          if (_quo & 0x8000u) g_cpu.SR |= (1u<<3);\n"
            "          if (_quo == 0u)     g_cpu.SR |= (1u<<2);\n"
            "        } else { g_cpu.SR |= (1u<<1); g_cpu.SR |= (1u<<3); g_cpu.SR &= ~(1u<<2); }\n"
            "      } else { g_cpu.SR |= (1u<<1); g_cpu.SR |= (1u<<3); g_cpu.SR &= ~(1u<<2); }\n"
            "    }\n"
            "  }\n",
            src_expr, dreg, zero, dreg);
        break;
    }

    /* ------------------------------------------------------------------ */
    case MN_LINK: {
        int areg = instr->reg;
        int16_t disp = (int16_t)instr->words[1];
        fprintf(f,
            "  g_cpu.A[7] -= 4; m68k_write32(g_cpu.A[7], g_cpu.A[%d]);\n"
            "  g_cpu.A[%d] = g_cpu.A[7];\n"
            "  g_cpu.A[7] += (int32_t)%d;\n",
            areg, areg, (int)disp);
        break;
    }

    /* ------------------------------------------------------------------ */
    case MN_UNLK: {
        int areg = instr->reg;
        fprintf(f,
            "  g_cpu.A[7] = g_cpu.A[%d];\n"
            "  g_cpu.A[%d] = m68k_read32(g_cpu.A[7]);\n"
            "  g_cpu.A[7] += 4;\n",
            areg, areg);
        break;
    }

    /* ------------------------------------------------------------------ */
    case MN_MOVEM: {
        /* words[0] bit 10 = direction: 0=reg→mem, 1=mem→reg */
        int dir  = (instr->words[0] >> 10) & 1;
        uint16_t mask = instr->words[1];
        int ea   = instr->src_ea;
        int mode = (ea >> 3) & 7;
        int reg  = ea & 7;

        /* Build ExtReader starting at words[2] for EA extension */
        ExtReader er2;
        er_init_at(&er2, instr, 2);

        char base_expr[128];
        /* Compute base address expression */
        switch (mode) {
        case 2:
            snprintf(base_expr, sizeof(base_expr), "g_cpu.A[%d]", reg);
            break;
        case 3:
            snprintf(base_expr, sizeof(base_expr), "g_cpu.A[%d]", reg);
            break;
        case 4:
            snprintf(base_expr, sizeof(base_expr), "g_cpu.A[%d]", reg);
            break;
        case 5: {
            uint16_t ext = er_next(&er2);
            int16_t d16 = (int16_t)ext;
            snprintf(base_expr, sizeof(base_expr),
                     "(uint32_t)(g_cpu.A[%d] + (int32_t)%d)", reg, (int)d16);
            break;
        }
        case 6: {
            uint16_t ext = er_next(&er2);
            int xreg  = (ext >> 12) & 7;
            int8_t d8 = (int8_t)(ext & 0xFF);
            snprintf(base_expr, sizeof(base_expr),
                     "(uint32_t)(g_cpu.A[%d] + "
                     "m68k_brief_index_value(0x%04Xu, g_cpu.D[%d], g_cpu.A[%d]) + (%d))",
                     reg, ext, xreg, xreg, (int)d8);
            break;
        }
        case 7:
            switch (reg) {
            case 0: {
                uint16_t ext = er_next(&er2);
                snprintf(base_expr, sizeof(base_expr),
                         "(uint32_t)(int32_t)(int16_t)0x%04X", ext);
                break;
            }
            case 1: {
                uint16_t hi = er_next(&er2);
                uint16_t lo = er_next(&er2);
                uint32_t a = ((uint32_t)hi << 16) | lo;
                snprintf(base_expr, sizeof(base_expr), "0x%08Xu", a);
                break;
            }
            case 2: {
                uint32_t pc_addr = instr->addr + er2.bp;
                uint16_t ext = er_next(&er2);
                int16_t d16 = (int16_t)ext;
                uint32_t eff = (uint32_t)((int32_t)pc_addr + d16);
                snprintf(base_expr, sizeof(base_expr), "0x%08Xu", eff);
                break;
            }
            case 3: {  /* (d8,PC,Xn) — PC-relative indexed */
                uint32_t pc_addr = instr->addr + er2.bp;
                uint16_t ext = er_next(&er2);
                int xreg  = (ext >> 12) & 7;
                int8_t d8 = (int8_t)(ext & 0xFF);
                snprintf(base_expr, sizeof(base_expr),
                         "(uint32_t)(0x%08X + "
                         "m68k_brief_index_value(0x%04Xu, g_cpu.D[%d], g_cpu.A[%d]) + (%d))",
                         pc_addr, ext, xreg, xreg, (int)d8);
                break;
            }
            default:
                snprintf(base_expr, sizeof(base_expr), "0 /* MOVEM unknown EA */");
                codegen_diag_record(CGD_EA_FALLBACK,
                                    s_diag_instr ? s_diag_instr->addr : 0,
                                    s_diag_instr ? s_diag_instr->words[0] : 0,
                                    s_diag_instr ? s_diag_instr->mnemonic : MN_OTHER,
                                    s_diag_func_name, s_diag_func_addr);
                break;
            }
            break;
        default:
            snprintf(base_expr, sizeof(base_expr), "0 /* MOVEM unknown mode */");
            codegen_diag_record(CGD_EA_FALLBACK,
                                s_diag_instr ? s_diag_instr->addr : 0,
                                s_diag_instr ? s_diag_instr->words[0] : 0,
                                s_diag_instr ? s_diag_instr->mnemonic : MN_OTHER,
                                s_diag_func_name, s_diag_func_addr);
            break;
        }

        /* Emit */
        if (dir == 0) {
            /* reg → mem */
            if (mode == 4) {
                /* Predecrement: reversed mask (bit0=A7..bit7=A0, bit8=D7..bit15=D0) */
                fprintf(f, "  { uint32_t _mbase = %s;\n", base_expr);
                for (int bit = 0; bit < 16; bit++) {
                    if (!(mask & (1u << bit))) continue;
                    /* bit 0..7 = A7..A0, bit 8..15 = D7..D0 */
                    int is_an = (bit < 8);
                    int ridx  = is_an ? (7 - bit) : (15 - bit);
                    const char *rname = is_an ? "A" : "D";
                    if (sz == M68K_SIZE_L) {
                        fprintf(f, "    _mbase -= 4; m68k_write32(_mbase, g_cpu.%s[%d]);\n",
                                rname, ridx);
                    } else {
                        fprintf(f, "    _mbase -= 2; m68k_write16(_mbase, (uint16_t)g_cpu.%s[%d]);\n",
                                rname, ridx);
                    }
                }
                fprintf(f, "    g_cpu.A[%d] = _mbase; }\n", reg);
            } else {
                /* Standard: bit0=D0..bit7=D7, bit8=A0..bit15=A7 */
                fprintf(f, "  { uint32_t _mbase = %s;\n", base_expr);
                for (int bit = 0; bit < 16; bit++) {
                    if (!(mask & (1u << bit))) continue;
                    int is_an = (bit >= 8);
                    int ridx  = is_an ? (bit - 8) : bit;
                    const char *rname = is_an ? "A" : "D";
                    if (sz == M68K_SIZE_L) {
                        fprintf(f, "    m68k_write32(_mbase, g_cpu.%s[%d]); _mbase += 4;\n",
                                rname, ridx);
                    } else {
                        fprintf(f, "    m68k_write16(_mbase, (uint16_t)g_cpu.%s[%d]); _mbase += 2;\n",
                                rname, ridx);
                    }
                }
                if (mode == 3)
                    fprintf(f, "    g_cpu.A[%d] = _mbase; }\n", reg);
                else
                    fprintf(f, "  }\n");
            }
        } else {
            /* mem → reg: always standard bit order */
            fprintf(f, "  { uint32_t _mbase = %s;\n", base_expr);
            for (int bit = 0; bit < 16; bit++) {
                if (!(mask & (1u << bit))) continue;
                int is_an = (bit >= 8);
                int ridx  = is_an ? (bit - 8) : bit;
                const char *rname = is_an ? "A" : "D";
                if (sz == M68K_SIZE_L) {
                    fprintf(f, "    g_cpu.%s[%d] = m68k_read32(_mbase); _mbase += 4;\n",
                            rname, ridx);
                } else {
                    if (is_an) {
                        fprintf(f, "    g_cpu.A[%d] = (uint32_t)(int32_t)(int16_t)m68k_read16(_mbase); _mbase += 2;\n",
                                ridx);
                    } else {
                        /* MOVEM.W mem->Dn sign-extends to 32 bits per 68K spec
                         * (unlike MOVE.W which preserves Dn's upper word).
                         * Found while hunting SMPS audio squelching. */
                        fprintf(f, "    g_cpu.D[%d] = (uint32_t)(int32_t)(int16_t)m68k_read16(_mbase); _mbase += 2;\n",
                                ridx);
                    }
                }
            }
            if (mode == 3)
                fprintf(f, "    g_cpu.A[%d] = _mbase; }\n", reg);
            else
                fprintf(f, "  }\n");
        }
        if (*has_sp_adjust && reg == 7) {
            int reg_count = 0;
            for (int bit = 0; bit < 16; bit++)
                if (mask & (1u << bit))
                    reg_count++;
            if (dir == 1 && mode == 3)
                fprintf(f, "  _sp_popped += %d; /* MOVEM (SP)+ bytes */\n",
                        reg_count * (sz == M68K_SIZE_L ? 4 : 2));
            else if (dir == 0 && mode == 4)
                fprintf(f, "  _sp_popped -= %d; /* MOVEM -(SP) bytes */\n",
                        reg_count * (sz == M68K_SIZE_L ? 4 : 2));
        }
        break;
    }

    /* ------------------------------------------------------------------ */
    case MN_MOVE_SR: {
        /* Direction comes from the decoder's dst_is_ea flag:
         *   dst_is_ea=false → MOVE <ea>,SR  (load EA → SR)
         *   dst_is_ea=true  → MOVE SR,<ea>  (store SR → EA) */
        if (!instr->dst_is_ea) {
            emit_ea_load(f, instr, instr->src_ea, M68K_SIZE_W, &er, tmp, src_expr);
            /* Mask to the valid 68000 SR bits (T,S,I2-0,X,N,Z,V,C = 0xA71F) —
             * unused bits read as 0 on hardware. */
            fprintf(f, "  g_cpu.SR = (uint16_t)((%s) & 0xA71Fu);\n", src_expr);
            fprintf(f, "  glue_sr_written();\n");
        } else {
            emit_ea_store(f, instr, instr->src_ea, M68K_SIZE_W, &er, "g_cpu.SR");
        }
        break;
    }

    /* ------------------------------------------------------------------ */
    case MN_MOVE_CCR: {
        /* Direction from decoder:
         *   dst_is_ea=false → MOVE <ea>,CCR  (load low byte of EA into CCR;
         *                     upper byte of SR is preserved per 68K spec)
         *   dst_is_ea=true  → MOVE CCR,<ea>  (read CCR as a word — low 8
         *                     bits are CCR, upper 8 bits are zero — and
         *                     store to EA as a word) */
        if (!instr->dst_is_ea) {
            emit_ea_load(f, instr, instr->src_ea, M68K_SIZE_W, &er, tmp, src_expr);
            /* CCR is only 5 bits (X,N,Z,V,C = 0x1F); bits 5-7 read as 0. */
            fprintf(f, "  g_cpu.SR = (g_cpu.SR & 0xFF00u) | (uint16_t)((%s) & 0x1Fu);\n", src_expr);
        } else {
            emit_ea_store(f, instr, instr->src_ea, M68K_SIZE_W, &er,
                          "(uint16_t)(g_cpu.SR & 0x001Fu)");
        }
        break;
    }

    /* ------------------------------------------------------------------ */
    case MN_MOVE_USP: {
        /* MOVE USP,An or MOVE An,USP — USP is a separate shadow register.
         * In supervisor mode, A7 is SSP. USP is only accessible via these
         * privileged instructions. */
        int areg = instr->reg;
        int dir  = (instr->words[0] >> 3) & 1; /* 0=An→USP, 1=USP→An */
        if (dir)
            fprintf(f, "  g_cpu.A[%d] = g_cpu.USP; /* MOVE USP,An */\n", areg);
        else
            fprintf(f, "  g_cpu.USP = g_cpu.A[%d]; /* MOVE An,USP */\n", areg);
        break;
    }

    /* ------------------------------------------------------------------ */
    case MN_Scc: {
        int cond = (instr->words[0] >> 8) & 0xF;
        const char *ce = bcc_cond_expr(cond);
        ExtReader er_save = er;
        /* Write 0xFF or 0x00 */
        fprintf(f, "  { uint8_t _sval = (%s) ? 0xFFu : 0x00u;\n", ce);
        emit_ea_store(f, instr, instr->src_ea, M68K_SIZE_B, &er_save, "_sval");
        fprintf(f, "  }\n");
        break;
    }

    /* ------------------------------------------------------------------ */
    case MN_NEGX: {
        /* NEGX: result = 0 - ea - X */
        const char *ct = size_ctype(sz);
        emit_ea_load_ex(f, instr, instr->src_ea, sz, &er, tmp, src_expr, 1);
        char res[64];
        snprintf(res, sizeof(res), "_%06Xr", addr);
        fprintf(f,
            "  { uint32_t _x = (g_cpu.SR >> 4) & 1u;\n"
            "    %s %s = (%s)(0 - (%s)(%s) - (%s)_x);\n",
            ct, res, ct, ct, src_expr, ct);
        emit_flags_sub(f, "0", src_expr, res, sz);
        ExtReader er2; er_init(&er2, instr);
        emit_ea_store_ex(f, instr, instr->src_ea, sz, &er2, res, 1);
        fprintf(f, "  }\n");
        break;
    }

    /* ------------------------------------------------------------------ */
    case MN_CHK: {
        /* CHK <ea>,Dn — bounds check (signed word). Trap via vector 6
         * if Dn < 0 or Dn > <ea>. PRM:
         *   N is set if Dn < 0, cleared if Dn > <ea>, undefined otherwise.
         *   Z, V, C are undefined; X is unchanged.
         * On Sonic the check never trips in steady-state — m68k_trap_vector
         * aborts loud if it does. */
        int dn = instr->reg;
        emit_ea_load_ex(f, instr, instr->src_ea, M68K_SIZE_W, &er, tmp, src_expr, 1);
        fprintf(f,
            "  { int16_t _bound = (int16_t)(%s);\n"
            "    int16_t _val   = (int16_t)g_cpu.D[%d];\n"
            "    if (_val < 0)        { g_cpu.SR |= %s;\n",
            src_expr, dn, SR_N);
        emit_cycle_accounting(f, "      ", estimate_cycles(instr));
        fprintf(f,
            "      m68k_trap_vector(6u); return; }\n"
            "    if (_val > _bound)   { g_cpu.SR &= ~%s;\n",
            SR_N);
        emit_cycle_accounting(f, "      ", estimate_cycles(instr));
        fprintf(f,
            "      m68k_trap_vector(6u); return; }\n"
            "  }\n");
        break;
    }

    case MN_TAS:
        /* Test and Set: read EA, set N/Z, then set bit 7 */
        emit_ea_load_ex(f, instr, instr->src_ea, M68K_SIZE_B, &er, tmp, src_expr, 1);
        fprintf(f,
            "  { uint8_t _tasv = (uint8_t)(%s);\n"
            "    g_cpu.SR &= ~(0x0Fu);\n"
            "    if (!_tasv) g_cpu.SR |= (1u<<2);\n"
            "    if (_tasv >> 7) g_cpu.SR |= (1u<<3);\n",
            src_expr);
        {
            ExtReader er2; er_init(&er2, instr);
            char set_expr[64];
            snprintf(set_expr, sizeof(set_expr), "_tasv | 0x80u");
            emit_ea_store_ex(f, instr, instr->src_ea, M68K_SIZE_B, &er2, set_expr, 1);
        }
        fprintf(f, "  }\n");
        break;

    case MN_MOVEP: {
        /* MOVEP Dn, d16(An) and MOVEP d16(An), Dn — alternating-byte
         * transfer between a data register and memory at every other
         * byte starting at d16(An). Used by 8-bit-on-16-bit-bus glue
         * where each port lives at one half of a word lane.
         *
         * Encoding bits in words[0]:
         *   bit 7 (0x80):  0 = mem → Dn,  1 = Dn → mem
         *   bit 6 (0x40):  0 = .W (2 bytes),  1 = .L (4 bytes)
         * reg     = Dn ((w0 >> 9) & 7)        — populated by decoder
         * src_ea  = (5<<3)|An (d16(An) form)  — low 3 bits = An reg
         * words[1] = signed 16-bit displacement
         *
         * Memory bytes go: addr+0, addr+2, addr+4, addr+6 (most-
         * significant to least-significant). For .W only the low half
         * of Dn is touched; for .L the full 32 bits are read/written
         * with bit 31 at addr+0. */
        int dn   = instr->reg;
        int an   = instr->src_ea & 7;
        int dir  = (instr->words[0] >> 7) & 1;     /* 1 = Dn→mem */
        int isL  = (instr->words[0] >> 6) & 1;     /* 1 = .L     */
        int16_t d16 = (int16_t)instr->words[1];
        if (dir) {
            if (isL) {
                fprintf(f,
                    "  { uint32_t _ea = (uint32_t)(g_cpu.A[%d] + (int32_t)%d);\n"
                    "    uint32_t _v  = g_cpu.D[%d];\n"
                    "    m68k_write8(_ea + 0, (uint8_t)(_v >> 24));\n"
                    "    m68k_write8(_ea + 2, (uint8_t)(_v >> 16));\n"
                    "    m68k_write8(_ea + 4, (uint8_t)(_v >>  8));\n"
                    "    m68k_write8(_ea + 6, (uint8_t)(_v      ));\n"
                    "  }\n",
                    an, (int)d16, dn);
            } else {
                fprintf(f,
                    "  { uint32_t _ea = (uint32_t)(g_cpu.A[%d] + (int32_t)%d);\n"
                    "    uint32_t _v  = g_cpu.D[%d];\n"
                    "    m68k_write8(_ea + 0, (uint8_t)(_v >> 8));\n"
                    "    m68k_write8(_ea + 2, (uint8_t)(_v     ));\n"
                    "  }\n",
                    an, (int)d16, dn);
            }
        } else {
            if (isL) {
                fprintf(f,
                    "  { uint32_t _ea = (uint32_t)(g_cpu.A[%d] + (int32_t)%d);\n"
                    "    uint32_t _v  = ((uint32_t)m68k_read8(_ea + 0) << 24)\n"
                    "                 | ((uint32_t)m68k_read8(_ea + 2) << 16)\n"
                    "                 | ((uint32_t)m68k_read8(_ea + 4) <<  8)\n"
                    "                 | ((uint32_t)m68k_read8(_ea + 6)      );\n"
                    "    g_cpu.D[%d] = _v;\n"
                    "  }\n",
                    an, (int)d16, dn);
            } else {
                fprintf(f,
                    "  { uint32_t _ea = (uint32_t)(g_cpu.A[%d] + (int32_t)%d);\n"
                    "    uint16_t _v  = (uint16_t)(((uint16_t)m68k_read8(_ea + 0) << 8)\n"
                    "                            | (uint16_t)m68k_read8(_ea + 2));\n"
                    "    g_cpu.D[%d] = (g_cpu.D[%d] & 0xFFFF0000u) | _v;\n"
                    "  }\n",
                    an, (int)d16, dn, dn);
            }
        }
        break;
    }

    case MN_ABCD: {
        /* result = a + b + X, packed-BCD.
         *   low nibble: (a&0xF) + (b&0xF) + X; if >9, +6, low carry.
         *   high nibble: (a>>4) + (b>>4) + low_carry; if >9, +6, high carry.
         * SR: X = C; Z is "sticky" — cleared only when result != 0,
         *     preserved otherwise (multi-precision BCD chains rely on
         *     this: the chain reports overall zeroness, not per-byte).
         * N and V are undefined per PRM; we emit conservative values
         *     (N from result bit 7, V cleared) so generated code is
         *     deterministic. */
        int dst = instr->reg;
        int src = instr->src_ea & 7;
        if (instr->predec_mem_form) {
            int ay_dec = (src == 7) ? 2 : 1;
            int ax_dec = (dst == 7) ? 2 : 1;
            fprintf(f,
                "  { g_cpu.A[%d] -= %d;\n"
                "    uint8_t _b = (uint8_t)m68k_read8(g_cpu.A[%d]);\n"
                "    g_cpu.A[%d] -= %d;\n"
                "    uint8_t _a = (uint8_t)m68k_read8(g_cpu.A[%d]);\n"
                "    uint32_t _x = (g_cpu.SR >> 4) & 1u;\n"
                "    uint32_t _lo = (uint32_t)(_a & 0xF) + (uint32_t)(_b & 0xF) + _x;\n"
                "    uint32_t _adj_lo = (_lo > 9u) ? 6u : 0u;\n"
                "    uint32_t _hi = (uint32_t)(_a >> 4) + (uint32_t)(_b >> 4) + ((_lo + _adj_lo) >> 4);\n"
                "    uint32_t _adj_hi = (_hi > 9u) ? 6u : 0u;\n"
                "    uint32_t _full = (_hi << 4) + _adj_hi*16u + ((_lo + _adj_lo) & 0xFu);\n"
                "    uint8_t _r = (uint8_t)_full;\n"
                "    int _zold = (g_cpu.SR >> 2) & 1;\n"
                "    g_cpu.SR &= ~%s;\n"
                "    if (_r) { g_cpu.SR &= ~%s; } else if (_zold) { g_cpu.SR |= %s; }\n"
                "    g_cpu.SR &= ~(%s | %s | %s);\n"
                "    if (_r & 0x80u) g_cpu.SR |= %s;\n"
                "    if (_full & 0x100u) { g_cpu.SR |= %s; g_cpu.SR |= %s; }\n"
                "    m68k_write8(g_cpu.A[%d], _r);\n"
                "  }\n",
                src, ay_dec, src,
                dst, ax_dec, dst,
                SR_V, SR_Z, SR_Z,
                SR_C, SR_X, SR_N, SR_N, SR_C, SR_X,
                dst);
        } else {
            fprintf(f,
                "  { uint8_t _a = (uint8_t)g_cpu.D[%d];\n"
                "    uint8_t _b = (uint8_t)g_cpu.D[%d];\n"
                "    uint32_t _x = (g_cpu.SR >> 4) & 1u;\n"
                "    uint32_t _lo = (uint32_t)(_a & 0xF) + (uint32_t)(_b & 0xF) + _x;\n"
                "    uint32_t _adj_lo = (_lo > 9u) ? 6u : 0u;\n"
                "    uint32_t _hi = (uint32_t)(_a >> 4) + (uint32_t)(_b >> 4) + ((_lo + _adj_lo) >> 4);\n"
                "    uint32_t _adj_hi = (_hi > 9u) ? 6u : 0u;\n"
                "    uint32_t _full = (_hi << 4) + _adj_hi*16u + ((_lo + _adj_lo) & 0xFu);\n"
                "    uint8_t _r = (uint8_t)_full;\n"
                "    int _zold = (g_cpu.SR >> 2) & 1;\n"
                "    g_cpu.SR &= ~%s;\n"
                "    if (_r) { g_cpu.SR &= ~%s; } else if (_zold) { g_cpu.SR |= %s; }\n"
                "    g_cpu.SR &= ~(%s | %s | %s);\n"
                "    if (_r & 0x80u) g_cpu.SR |= %s;\n"
                "    if (_full & 0x100u) { g_cpu.SR |= %s; g_cpu.SR |= %s; }\n"
                "    g_cpu.D[%d] = (g_cpu.D[%d] & 0xFFFFFF00u) | _r;\n"
                "  }\n",
                dst, src,
                SR_V, SR_Z, SR_Z,
                SR_C, SR_X, SR_N, SR_N, SR_C, SR_X,
                dst, dst);
        }
        break;
    }

    case MN_SBCD: {
        /* result = a - b - X, packed-BCD. Borrow propagation mirrors the
         * carry path in ABCD; subtract the BCD adjustment instead of
         * adding it. Z is sticky like ABCD. */
        int dst = instr->reg;
        int src = instr->src_ea & 7;
        if (instr->predec_mem_form) {
            int ay_dec = (src == 7) ? 2 : 1;
            int ax_dec = (dst == 7) ? 2 : 1;
            fprintf(f,
                "  { g_cpu.A[%d] -= %d;\n"
                "    uint8_t _b = (uint8_t)m68k_read8(g_cpu.A[%d]);\n"
                "    g_cpu.A[%d] -= %d;\n"
                "    uint8_t _a = (uint8_t)m68k_read8(g_cpu.A[%d]);\n"
                "    uint32_t _x = (g_cpu.SR >> 4) & 1u;\n"
                "    int32_t _lo = (int32_t)(_a & 0xF) - (int32_t)(_b & 0xF) - (int32_t)_x;\n"
                "    int32_t _adj_lo = (_lo < 0) ? 6 : 0;\n"
                "    int32_t _hi = (int32_t)(_a >> 4) - (int32_t)(_b >> 4) - (_lo < 0 ? 1 : 0);\n"
                "    int32_t _adj_hi = (_hi < 0) ? 6 : 0;\n"
                "    int32_t _full = (_hi & 0xFF) * 16 - _adj_hi*16 + ((_lo - _adj_lo) & 0xF);\n"
                "    uint8_t _r = (uint8_t)_full;\n"
                "    int _zold = (g_cpu.SR >> 2) & 1;\n"
                "    g_cpu.SR &= ~%s;\n"
                "    if (_r) { g_cpu.SR &= ~%s; } else if (_zold) { g_cpu.SR |= %s; }\n"
                "    g_cpu.SR &= ~(%s | %s | %s);\n"
                "    if (_r & 0x80u) g_cpu.SR |= %s;\n"
                "    if (_hi < 0) { g_cpu.SR |= %s; g_cpu.SR |= %s; }\n"
                "    m68k_write8(g_cpu.A[%d], _r);\n"
                "  }\n",
                src, ay_dec, src,
                dst, ax_dec, dst,
                SR_V, SR_Z, SR_Z,
                SR_C, SR_X, SR_N, SR_N, SR_C, SR_X,
                dst);
        } else {
            fprintf(f,
                "  { uint8_t _a = (uint8_t)g_cpu.D[%d];\n"
                "    uint8_t _b = (uint8_t)g_cpu.D[%d];\n"
                "    uint32_t _x = (g_cpu.SR >> 4) & 1u;\n"
                "    int32_t _lo = (int32_t)(_a & 0xF) - (int32_t)(_b & 0xF) - (int32_t)_x;\n"
                "    int32_t _adj_lo = (_lo < 0) ? 6 : 0;\n"
                "    int32_t _hi = (int32_t)(_a >> 4) - (int32_t)(_b >> 4) - (_lo < 0 ? 1 : 0);\n"
                "    int32_t _adj_hi = (_hi < 0) ? 6 : 0;\n"
                "    int32_t _full = (_hi & 0xFF) * 16 - _adj_hi*16 + ((_lo - _adj_lo) & 0xF);\n"
                "    uint8_t _r = (uint8_t)_full;\n"
                "    int _zold = (g_cpu.SR >> 2) & 1;\n"
                "    g_cpu.SR &= ~%s;\n"
                "    if (_r) { g_cpu.SR &= ~%s; } else if (_zold) { g_cpu.SR |= %s; }\n"
                "    g_cpu.SR &= ~(%s | %s | %s);\n"
                "    if (_r & 0x80u) g_cpu.SR |= %s;\n"
                "    if (_hi < 0) { g_cpu.SR |= %s; g_cpu.SR |= %s; }\n"
                "    g_cpu.D[%d] = (g_cpu.D[%d] & 0xFFFFFF00u) | _r;\n"
                "  }\n",
                dst, src,
                SR_V, SR_Z, SR_Z,
                SR_C, SR_X, SR_N, SR_N, SR_C, SR_X,
                dst, dst);
        }
        break;
    }

    case MN_NBCD: {
        /* NBCD <ea>:  result = 0 - dst - X, packed-BCD. Same flag
         * semantics as SBCD (sticky Z, X = C). EA can be Dn, (An),
         * (An)+, -(An), d16(An), d8(An,Xn), abs.W, abs.L. */
        ExtReader er2; er_init(&er2, instr);
        emit_ea_load_ex(f, instr, instr->src_ea, M68K_SIZE_B, &er, tmp, src_expr, 1);
        fprintf(f,
            "  { uint8_t _a = (uint8_t)(%s);\n"
            "    uint32_t _x = (g_cpu.SR >> 4) & 1u;\n"
            "    int32_t _lo = -(int32_t)(_a & 0xF) - (int32_t)_x;\n"
            "    int32_t _adj_lo = (_lo < 0) ? 6 : 0;\n"
            "    int32_t _hi = -(int32_t)(_a >> 4) - (_lo < 0 ? 1 : 0);\n"
            "    int32_t _adj_hi = (_hi < 0) ? 6 : 0;\n"
            "    int32_t _full = (_hi & 0xFF) * 16 - _adj_hi*16 + ((_lo - _adj_lo) & 0xF);\n"
            "    uint8_t _r = (uint8_t)_full;\n"
            "    int _zold = (g_cpu.SR >> 2) & 1;\n"
            "    g_cpu.SR &= ~%s;\n"
            "    if (_r) { g_cpu.SR &= ~%s; } else if (_zold) { g_cpu.SR |= %s; }\n"
            "    g_cpu.SR &= ~(%s | %s | %s);\n"
            "    if (_r & 0x80u) g_cpu.SR |= %s;\n"
            "    if (_hi < 0) { g_cpu.SR |= %s; g_cpu.SR |= %s; }\n",
            src_expr,
            SR_V, SR_Z, SR_Z,
            SR_C, SR_X, SR_N, SR_N, SR_C, SR_X);
        {
            char res_expr[16];
            snprintf(res_expr, sizeof(res_expr), "_r");
            emit_ea_store_ex(f, instr, instr->src_ea, M68K_SIZE_B, &er2, res_expr, 1);
        }
        fprintf(f, "  }\n");
        break;
    }

    /* ------------------------------------------------------------------ */
    case MN_EXG: {
        /* Swap two 32-bit registers; no flags affected.
         * Encoding: 1100 Rx 1 opmode rrr  where opmode selects D-D, A-A,
         * or D-A form. Rx = bits 11-9, Ry = bits 2-0. */
        uint16_t w0 = instr->words[0];
        int rx = (w0 >> 9) & 7;
        int ry = w0 & 7;
        if ((w0 & 0xF1F8) == 0xC140) {
            fprintf(f, "  { uint32_t _t = g_cpu.D[%d]; g_cpu.D[%d] = g_cpu.D[%d]; g_cpu.D[%d] = _t; }\n",
                    rx, rx, ry, ry);
        } else if ((w0 & 0xF1F8) == 0xC148) {
            fprintf(f, "  { uint32_t _t = g_cpu.A[%d]; g_cpu.A[%d] = g_cpu.A[%d]; g_cpu.A[%d] = _t; }\n",
                    rx, rx, ry, ry);
        } else {
            /* 0xC188: EXG Dx,Ay */
            fprintf(f, "  { uint32_t _t = g_cpu.D[%d]; g_cpu.D[%d] = g_cpu.A[%d]; g_cpu.A[%d] = _t; }\n",
                    rx, rx, ry, ry);
        }
        break;
    }

    /* ------------------------------------------------------------------ */
    case MN_ADDX: {
        /* Dy/Dx → D-D form;  -(Ay),-(Ax) → memory predecrement form.
         * Z is cleared unless result==0 AND previous Z was set (for
         * multi-precision chains).  X = C. */
        uint16_t w0 = instr->words[0];
        int dst  = (w0 >> 9) & 7;
        int src  = w0 & 7;
        int bits = size_bits(sz);
        uint32_t sign_mask = (bits == 32) ? 0x80000000u : (bits == 16 ? 0x8000u : 0x80u);
        uint32_t low_mask  = (bits == 32) ? 0xFFFFFFFFu : (bits == 16 ? 0xFFFFu : 0xFFu);
        if (instr->predec_mem_form) {
            /* -(Ay),-(Ax): predec both, read both, compute (Ax) + (Ay) + X,
             * write back to (Ax). Byte size on A7 still increments by 2
             * to keep the supervisor stack aligned. */
            int sb = size_bytes(sz);
            int ay_dec = (src == 7 && sz == M68K_SIZE_B) ? 2 : sb;
            int ax_dec = (dst == 7 && sz == M68K_SIZE_B) ? 2 : sb;
            const char *rf = size_read_fn(sz);
            const char *wf = size_write_fn(sz);
            const char *ct = size_ctype(sz);
            fprintf(f,
                "  { g_cpu.A[%d] -= %d;\n"
                "    %s _fb = (%s)%s(g_cpu.A[%d]);\n"
                "    g_cpu.A[%d] -= %d;\n"
                "    %s _fa = (%s)%s(g_cpu.A[%d]);\n"
                "    uint32_t _fx = (g_cpu.SR >> 4) & 1u;\n"
                "    uint64_t _full = (uint64_t)(uint%d_t)_fa + (uint64_t)(uint%d_t)_fb + (uint64_t)_fx;\n"
                "    uint%d_t _fr = (uint%d_t)_full;\n"
                "    int _zold = (g_cpu.SR >> 2) & 1;\n"
                "    g_cpu.SR &= ~(0x1Fu);\n"
                "    if (!_fr && _zold)                              g_cpu.SR |= %s;\n"
                "    if (_fr >> %d)                                  g_cpu.SR |= %s;\n"
                "    if (_full >> %d)                                { g_cpu.SR |= %s; g_cpu.SR |= %s; }\n"
                "    if (!(((uint%d_t)_fa^(uint%d_t)_fb) & 0x%08Xu) && (((uint%d_t)_fa^_fr) & 0x%08Xu)) g_cpu.SR |= %s;\n"
                "    %s(g_cpu.A[%d], (%s)_fr);\n"
                "  }\n",
                src, ay_dec,
                ct, ct, rf, src,
                dst, ax_dec,
                ct, ct, rf, dst,
                bits, bits,
                bits, bits,
                SR_Z, bits - 1, SR_N, bits, SR_C, SR_X,
                bits, bits, sign_mask, bits, sign_mask, SR_V,
                wf, dst, ct);
        } else {
            fprintf(f,
                "  { uint%d_t _fa = (uint%d_t)g_cpu.D[%d];\n"
                "    uint%d_t _fb = (uint%d_t)g_cpu.D[%d];\n"
                "    uint32_t _fx = (g_cpu.SR >> 4) & 1u;\n"
                "    uint64_t _full = (uint64_t)_fa + (uint64_t)_fb + (uint64_t)_fx;\n"
                "    uint%d_t _fr = (uint%d_t)_full;\n"
                "    int _zold = (g_cpu.SR >> 2) & 1;\n"
                "    g_cpu.SR &= ~(0x1Fu);\n"
                "    if (!_fr && _zold)                              g_cpu.SR |= %s;\n"
                "    if (_fr >> %d)                                  g_cpu.SR |= %s;\n"
                "    if (_full >> %d)                                { g_cpu.SR |= %s; g_cpu.SR |= %s; }\n"
                "    if (!((_fa^_fb) & 0x%08Xu) && ((_fa^_fr) & 0x%08Xu)) g_cpu.SR |= %s;\n",
                bits, bits, dst, bits, bits, src, bits, bits,
                SR_Z, bits - 1, SR_N, bits, SR_C, SR_X,
                sign_mask, sign_mask, SR_V);
            if (sz == M68K_SIZE_L)
                fprintf(f, "    g_cpu.D[%d] = (uint32_t)_fr;\n", dst);
            else
                fprintf(f, "    g_cpu.D[%d] = (g_cpu.D[%d] & 0x%08Xu) | (uint32_t)_fr;\n",
                        dst, dst, (uint32_t)~low_mask);
            fprintf(f, "  }\n");
        }
        break;
    }

    /* ------------------------------------------------------------------ */
    case MN_SUBX: {
        /* Dy/Dx → D-D form;  -(Ay),-(Ax) → memory predecrement form.
         * Z-preserve semantics. X = C. */
        uint16_t w0 = instr->words[0];
        int dst  = (w0 >> 9) & 7;
        int src  = w0 & 7;
        int bits = size_bits(sz);
        uint32_t sign_mask = (bits == 32) ? 0x80000000u : (bits == 16 ? 0x8000u : 0x80u);
        uint32_t low_mask  = (bits == 32) ? 0xFFFFFFFFu : (bits == 16 ? 0xFFFFu : 0xFFu);
        if (instr->predec_mem_form) {
            int sb = size_bytes(sz);
            int ay_dec = (src == 7 && sz == M68K_SIZE_B) ? 2 : sb;
            int ax_dec = (dst == 7 && sz == M68K_SIZE_B) ? 2 : sb;
            const char *rf = size_read_fn(sz);
            const char *wf = size_write_fn(sz);
            const char *ct = size_ctype(sz);
            fprintf(f,
                "  { g_cpu.A[%d] -= %d;\n"
                "    %s _fb = (%s)%s(g_cpu.A[%d]);\n"
                "    g_cpu.A[%d] -= %d;\n"
                "    %s _fa = (%s)%s(g_cpu.A[%d]);\n"
                "    uint32_t _fx = (g_cpu.SR >> 4) & 1u;\n"
                "    uint64_t _full = (uint64_t)(uint%d_t)_fa - (uint64_t)(uint%d_t)_fb - (uint64_t)_fx;\n"
                "    uint%d_t _fr = (uint%d_t)_full;\n"
                "    int _zold = (g_cpu.SR >> 2) & 1;\n"
                "    g_cpu.SR &= ~(0x1Fu);\n"
                "    if (!_fr && _zold)                              g_cpu.SR |= %s;\n"
                "    if (_fr >> %d)                                  g_cpu.SR |= %s;\n"
                "    if ((_full >> 63) & 1u)                         { g_cpu.SR |= %s; g_cpu.SR |= %s; }\n"
                "    if ((((uint%d_t)_fa^(uint%d_t)_fb) & 0x%08Xu) && (((uint%d_t)_fa^_fr) & 0x%08Xu)) g_cpu.SR |= %s;\n"
                "    %s(g_cpu.A[%d], (%s)_fr);\n"
                "  }\n",
                src, ay_dec,
                ct, ct, rf, src,
                dst, ax_dec,
                ct, ct, rf, dst,
                bits, bits,
                bits, bits,
                SR_Z, bits - 1, SR_N, SR_C, SR_X,
                bits, bits, sign_mask, bits, sign_mask, SR_V,
                wf, dst, ct);
        } else {
            fprintf(f,
                "  { uint%d_t _fa = (uint%d_t)g_cpu.D[%d];\n"
                "    uint%d_t _fb = (uint%d_t)g_cpu.D[%d];\n"
                "    uint32_t _fx = (g_cpu.SR >> 4) & 1u;\n"
                "    uint64_t _full = (uint64_t)_fa - (uint64_t)_fb - (uint64_t)_fx;\n"
                "    uint%d_t _fr = (uint%d_t)_full;\n"
                "    int _zold = (g_cpu.SR >> 2) & 1;\n"
                "    g_cpu.SR &= ~(0x1Fu);\n"
                "    if (!_fr && _zold)                              g_cpu.SR |= %s;\n"
                "    if (_fr >> %d)                                  g_cpu.SR |= %s;\n"
                "    if ((_full >> 63) & 1u)                         { g_cpu.SR |= %s; g_cpu.SR |= %s; }\n"
                "    if (((_fa^_fb) & 0x%08Xu) && ((_fa^_fr) & 0x%08Xu)) g_cpu.SR |= %s;\n",
                bits, bits, dst, bits, bits, src, bits, bits,
                SR_Z, bits - 1, SR_N, SR_C, SR_X,
                sign_mask, sign_mask, SR_V);
            if (sz == M68K_SIZE_L)
                fprintf(f, "    g_cpu.D[%d] = (uint32_t)_fr;\n", dst);
            else
                fprintf(f, "    g_cpu.D[%d] = (g_cpu.D[%d] & 0x%08Xu) | (uint32_t)_fr;\n",
                        dst, dst, (uint32_t)~low_mask);
            fprintf(f, "  }\n");
        }
        break;
    }

    case MN_OTHER:
    default:
        codegen_diag_record(CGD_MN_OTHER, addr, instr->words[0],
                            instr->mnemonic, func_name, func_addr);
        fprintf(f, "  /* unimplemented opcode $%04X @ $%06X */\n",
                instr->words[0], addr);
        break;
    }
}

/* =========================================================================
 * Main codegen entry point
 * ========================================================================= */

bool codegen_emit_step_semantics(FILE *f, const GenesisRom *rom,
                                 const M68KInstr *ins)
{
    if (!f || !rom || !ins) return false;
    /* Deliberately explicit: adding a mnemonic to the legacy emitter does not
     * silently enroll a control/privilege/exception instruction in this ABI.
     * The step frontend owns PC, hardware exceptions and supervisor stacks. */
    switch (ins->mnemonic) {
    case MN_NOP: case MN_MOVE: case MN_MOVEA: case MN_MOVEQ:
    case MN_LEA: case MN_PEA: case MN_LINK: case MN_UNLK: case MN_MOVEM:
    case MN_ADD: case MN_ADDA: case MN_ADDQ: case MN_ADDI:
    case MN_SUB: case MN_SUBA: case MN_SUBQ: case MN_SUBI:
    case MN_AND: case MN_ANDI: case MN_OR: case MN_ORI: case MN_EOR: case MN_EORI:
    case MN_CMP: case MN_CMPA: case MN_CMPI: case MN_CMPM:
    case MN_TST: case MN_CLR: case MN_NEG: case MN_NEGX: case MN_NOT:
    case MN_SWAP: case MN_EXT:
    case MN_LSL: case MN_LSR: case MN_ASL: case MN_ASR:
    case MN_ROL: case MN_ROR: case MN_ROXL: case MN_ROXR:
    case MN_MULS: case MN_MULU: case MN_ABCD: case MN_SBCD: case MN_NBCD:
    case MN_BTST: case MN_BCHG: case MN_BCLR: case MN_BSET:
    case MN_MOVEP: case MN_TAS: case MN_EXG: case MN_ADDX: case MN_SUBX:
    case MN_Scc: case MN_MOVE_CCR:
    case MN_ORI_TO_CCR: case MN_ANDI_TO_CCR: case MN_EORI_TO_CCR:
        break;
    default:
        return false;
    }
    const WsSite *saved_sites = s_ws_sites;
    int saved_count = s_ws_site_count;
    bool saved_reverse = s_reverse_debug;
    const char *saved_name = s_diag_func_name;
    uint32_t saved_addr = s_diag_func_addr;
    const M68KInstr *saved_ins = s_diag_instr;
    s_ws_sites = NULL; s_ws_site_count = 0; s_reverse_debug = false;
    AddrSet instructions = {0};
    bool skip = false;
    int stack_accounting = 0;
    emit_instr(f, rom, ins, &instructions, &skip, &stack_accounting, "<step>", ins->addr, false);
    s_ws_sites = saved_sites; s_ws_site_count = saved_count;
    s_reverse_debug = saved_reverse;
    s_diag_func_name = saved_name; s_diag_func_addr = saved_addr; s_diag_instr = saved_ins;
    addrset_free(&instructions);
    return !skip && !ferror(f);
}

static unsigned step_operand_cost(unsigned ea, bool is_long)
{return m68k_68000_operand_cycles(ea,is_long);}

static unsigned step_jump_cost(unsigned ea, bool call)
{return m68k_68000_jump_cycles(ea,call);}

static bool emit_step_control(FILE *f,const GenesisRom *rom,const M68KInstr *ins)
{
    ExtReader er;er_init(&er,ins);
    char expr[256], tmp[32];snprintf(tmp,sizeof tmp,"_step%06X",ins->addr);
    uint32_t next=(ins->addr+2u*ins->word_count)&0xFFFFFFu;
    switch(ins->mnemonic) {
    case MN_RTS:
        fprintf(f,"  ctx->charge=16; g_cpu.PC=m68k_read32(g_cpu.A[7])&0xFFFFFFu; g_cpu.A[7]+=4;\n");return true;
    case MN_RTE:
        fprintf(f,"  ctx->charge=20; m68k_step_rte(ctx);\n");return true;
    case MN_RTR:
        fprintf(f,"  ctx->charge=20; { uint32_t sp=g_cpu.A[7]; uint16_t ccr=m68k_read16(sp);\n"
                  "    uint32_t pc=m68k_read32(sp+2); g_cpu.A[7]=sp+6;\n"
                  "    g_cpu.SR=(uint16_t)((g_cpu.SR&0xFF00u)|(ccr&31u)); g_cpu.PC=pc&0xFFFFFFu; }\n");return true;
    case MN_STOP:
        fprintf(f,"  ctx->charge=4; m68k_step_stop(ctx,0x%04Xu);\n",(unsigned)(ins->imm32&65535));return true;
    case MN_RESET:
        fprintf(f,"  ctx->charge=132; m68k_step_reset_devices(ctx);\n");return true;
    case MN_TRAP:
        fprintf(f,"  m68k_step_exception(ctx,%uu,g_cpu.PC,34);\n",32u+(unsigned)(ins->imm32&15));return true;
    case MN_TRAPV:
        fprintf(f,"  ctx->charge=4; if(g_cpu.SR&2u)m68k_step_exception(ctx,7,g_cpu.PC,34);\n");return true;
    case MN_ILLEGAL: case MN_MOVEC: {
        unsigned top=ins->words[0]>>12, vector=top==10?10u:top==15?11u:4u;
        fprintf(f,"  m68k_step_exception(ctx,%uu,0x%06Xu,34);\n",vector,ins->addr);return true;
    }
    case MN_BRA: case MN_BSR: case MN_Bcc: case MN_DBcc:
        if(!ins->has_target)return false;
        if(ins->mnemonic==MN_BRA) {
            fprintf(f,"  ctx->charge=10; g_cpu.PC=0x%06Xu;\n",ins->target_addr&0xFFFFFFu);
        } else if(ins->mnemonic==MN_BSR) {
            fprintf(f,"  ctx->charge=18; g_cpu.A[7]-=4; m68k_write32(g_cpu.A[7],0x%06Xu); g_cpu.PC=0x%06Xu;\n",next,ins->target_addr&0xFFFFFFu);
        } else if(ins->mnemonic==MN_Bcc) {
            fprintf(f,"  if(%s){ctx->charge=10;g_cpu.PC=0x%06Xu;}else ctx->charge=%u;\n",
                    bcc_cond_expr((ins->words[0]>>8)&15),ins->target_addr&0xFFFFFFu,ins->word_count==1?8u:12u);
        } else {
            fprintf(f,"  if(!(%s)){ uint16_t low=(uint16_t)(g_cpu.D[%u]-1u);\n"
                      "    g_cpu.D[%u]=(g_cpu.D[%u]&0xFFFF0000u)|low;\n"
                      "    if(low!=0xFFFFu){ctx->charge=10;g_cpu.PC=0x%06Xu;}else ctx->charge=14;\n"
                      "  }else ctx->charge=12;\n",bcc_cond_expr((ins->words[0]>>8)&15),
                      (unsigned)ins->reg,(unsigned)ins->reg,(unsigned)ins->reg,ins->target_addr&0xFFFFFFu);
        }
        return true;
    case MN_JMP: case MN_JSR: {
        bool call=ins->mnemonic==MN_JSR;
        unsigned cost=step_jump_cost((unsigned)ins->src_ea,call);
        if(!cost)return false;
        emit_ea_addr_ex(f,ins,ins->src_ea,&er,expr,true);
        fprintf(f,"  { uint32_t target=(%s)&0xFFFFFFu; ctx->charge=%u;\n",expr,cost);
        if(call)fprintf(f,"    g_cpu.A[7]-=4; m68k_write32(g_cpu.A[7],0x%06Xu);\n",next);
        fprintf(f,"    g_cpu.PC=target; }\n");return true;
    }
    case MN_MOVE_USP:
        fprintf(f,"  if(!m68k_step_supervisor(ctx))return; ctx->charge=4;\n");
        if(ins->words[0]&8)fprintf(f,"  g_cpu.A[%u]=g_cpu.USP;\n",(unsigned)ins->reg);
        else fprintf(f,"  g_cpu.USP=g_cpu.A[%u];\n",(unsigned)ins->reg);
        return true;
    case MN_MOVE_SR:
        if(!ins->dst_is_ea) {
            fprintf(f,"  if(!m68k_step_supervisor(ctx))return;\n");
            fprintf(f,"  ctx->charge=%u;\n",12u+step_operand_cost((unsigned)ins->src_ea,false));
            emit_ea_load(f,ins,ins->src_ea,M68K_SIZE_W,&er,tmp,expr);
            fprintf(f,"  m68k_step_set_sr(ctx,(uint16_t)(%s));\n",expr);
        } else {
            unsigned cost=(ins->src_ea>>3)==0?6u:8u+step_operand_cost((unsigned)ins->src_ea,false);
            fprintf(f,"  ctx->charge=%u;\n",cost);
            emit_ea_store(f,ins,ins->src_ea,M68K_SIZE_W,&er,"g_cpu.SR");
        }
        return true;
    case MN_MOVE_CCR:
        if(!ins->dst_is_ea)return false; /* MOVE to CCR is straight-line. */
        /* MOVE from CCR is a 68010 instruction, illegal on the CD's 68000. */
        fprintf(f,"  m68k_step_exception(ctx,4,0x%06Xu,34);\n",ins->addr);return true;
    case MN_ORI_TO_SR: case MN_ANDI_TO_SR: case MN_EORI_TO_SR: {
        const char *op=ins->mnemonic==MN_ORI_TO_SR?"|":ins->mnemonic==MN_ANDI_TO_SR?"&":"^";
        fprintf(f,"  if(!m68k_step_supervisor(ctx))return;\n"
                  "  ctx->charge=20;\n"
                  "  m68k_step_set_sr(ctx,(uint16_t)(g_cpu.SR%s0x%04Xu));\n",op,(unsigned)(ins->imm32&65535));return true;
    }
    case MN_DIVU: case MN_DIVS: {
        AddrSet instructions={0};bool skip=false;int stack_accounting=0;
        /* Nominal nonzero costs; data-dependent divide timing still needs
         * qualification. Zero division enters the real vector-five frame. */
        fprintf(f,"  ctx->charge=%u;\n",(ins->mnemonic==MN_DIVU?140u:158u)+step_operand_cost((unsigned)ins->src_ea,false));
        emit_instr(f,rom,ins,&instructions,&skip,&stack_accounting,"<step>",ins->addr,true);
        addrset_free(&instructions);return !skip;
    }
    case MN_CHK: {
        unsigned ea=step_operand_cost((unsigned)ins->src_ea,false);
        emit_ea_load(f,ins,ins->src_ea,M68K_SIZE_W,&er,tmp,expr);
        fprintf(f,"  ctx->charge=%u; { int16_t value=(int16_t)g_cpu.D[%u], bound=(int16_t)(%s);\n"
                  "    if(value<0){g_cpu.SR|=8u;m68k_step_exception(ctx,6,g_cpu.PC,%u);}\n"
                  "    else if(value>bound){g_cpu.SR&=(uint16_t)~8u;m68k_step_exception(ctx,6,g_cpu.PC,%u);} }\n",
                  10u+ea,(unsigned)ins->reg,expr,40u+ea,40u+ea);return true;
    }
    default:return false;
    }
}

bool codegen_emit_step_operation(FILE *f,const GenesisRom *rom,const M68KInstr *ins)
{
    if(!f || !rom || !ins || !ins->word_count)return false;
    const WsSite *saved_sites=s_ws_sites;
    int saved_count=s_ws_site_count;
    bool saved_reverse=s_reverse_debug;
    const char *saved_name=s_diag_func_name;
    uint32_t saved_addr=s_diag_func_addr;
    const M68KInstr *saved_ins=s_diag_instr;
    s_ws_sites=NULL;s_ws_site_count=0;s_reverse_debug=false;
    s_diag_func_name="<step>";s_diag_func_addr=ins->addr;s_diag_instr=ins;
    bool handled=emit_step_control(f,rom,ins);
    if(!handled) {
        switch(ins->mnemonic) {
        case MN_LSL: case MN_LSR: case MN_ASL: case MN_ASR:
        case MN_ROL: case MN_ROR: case MN_ROXL: case MN_ROXR:
            if(!ins->mem_shift && (ins->words[0]&32u))
                fprintf(f,"  ctx->charge=%u+2u*(g_cpu.D[%u]&63u);\n",
                        ins->size==M68K_SIZE_L?8u:6u,(unsigned)ins->src_ea);
            break;
        case MN_Scc:
            if((ins->src_ea>>3)==0)
                fprintf(f,"  ctx->charge=(%s)?6u:4u;\n",bcc_cond_expr((ins->words[0]>>8)&15));
            break;
        default:break;
        }
    }
    s_ws_sites=saved_sites;s_ws_site_count=saved_count;s_reverse_debug=saved_reverse;
    s_diag_func_name=saved_name;s_diag_func_addr=saved_addr;s_diag_instr=saved_ins;
    if(ferror(f))return false;
    return handled || codegen_emit_step_semantics(f,rom,ins);
}

bool codegen_owned_rmw_instruction(const M68KInstr *ins)
{
    if(!ins||ins->src_ea<0)return false;
    unsigned mode=(unsigned)ins->src_ea>>3,reg=(unsigned)ins->src_ea&7u;
    if(mode<2||mode>7||(mode==7&&reg>1))return false;
    switch(ins->mnemonic){
    case MN_ADD:case MN_SUB:case MN_AND:case MN_OR:
        return (ins->words[0]&0x100u)!=0;
    case MN_ADDI:case MN_SUBI:case MN_ANDI:case MN_ORI:case MN_EORI:case MN_EOR:
    case MN_ADDQ:case MN_SUBQ:case MN_CLR:case MN_NEG:case MN_NEGX:case MN_NOT:
    case MN_BCHG:case MN_BCLR:case MN_BSET:case MN_TAS:case MN_NBCD:return true;
    case MN_LSL:case MN_LSR:case MN_ASL:case MN_ASR:
    case MN_ROL:case MN_ROR:case MN_ROXL:case MN_ROXR:return ins->mem_shift;
    default:return false;
    }
}

typedef struct {size_t begin,end,args,close;unsigned bits;} OwnedRmwCall;
static bool owned_rmw_call(const char*body,const char*prefix,OwnedRmwCall*out)
{
    const char*p=strstr(body,prefix);if(!p||strstr(p+strlen(prefix),prefix))return false;
    const char*width=p+strlen(prefix);unsigned bits=0;
    if(!strncmp(width,"8(",2))bits=8;
    else if(!strncmp(width,"16(",3))bits=16;
    else if(!strncmp(width,"32(",3))bits=32;
    else return false;
    const char*open=strchr(width,'('),*end=open+1;unsigned depth=1;
    for(;*end&&depth;++end){if(*end=='(')++depth;else if(*end==')')--depth;}
    if(depth)return false;
    out->begin=(size_t)(p-body);out->end=(size_t)(end-body);
    out->args=(size_t)(open+1-body);out->close=(size_t)(end-1-body);out->bits=bits;return true;
}
static bool owned_rmw_same_ea(const char*body,size_t a,size_t a_end,size_t b,size_t b_end)
{
    while(a_end>a&&isspace((unsigned char)body[a_end-1]))--a_end;
    while(b_end>b&&isspace((unsigned char)body[b_end-1]))--b_end;
    while(a<a_end&&isspace((unsigned char)body[a]))++a;
    while(b<b_end&&isspace((unsigned char)body[b]))++b;
    /* Absolute-long load historically omits the literal's unsigned suffix. */
    if(a_end-a>2&&b_end-b>2&&body[a]=='0'&&body[a+1]=='x'&&body[b]=='0'&&body[b+1]=='x'){
        if(body[a_end-1]=='u'||body[a_end-1]=='U')--a_end;
        if(body[b_end-1]=='u'||body[b_end-1]=='U')--b_end;
    }
    return a_end-a==b_end-b&&!memcmp(body+a,body+b,a_end-a);
}
bool codegen_emit_owned_rmw_operation(FILE*out,const GenesisRom*rom,const M68KInstr*ins)
{
    if(!out||!rom||!codegen_owned_rmw_instruction(ins))return false;
    FILE*buffer=tmpfile();if(!buffer)return false;
    bool ok=codegen_emit_step_operation(buffer,rom,ins)&&!fflush(buffer);
    long size=ok?ftell(buffer):-1;char*body=NULL;bool emitted=false;
    if(size<=0||size>1048576||fseek(buffer,0,SEEK_SET))goto done;
    body=malloc((size_t)size+1u);if(!body)goto done;
    if(fread(body,1,(size_t)size,buffer)!=(size_t)size)goto done;body[size]=0;
    OwnedRmwCall read,write;
    if(!owned_rmw_call(body,"m68k_read",&read)||!owned_rmw_call(body,"m68k_write",&write)||
       read.bits!=write.bits||read.end>write.begin||strstr(body,"ctx->")||
       strstr(body,"m68k_step_")||strstr(body,"glue_")||strstr(body,"return"))goto done;
    size_t comma=write.args;unsigned depth=0;
    for(;comma<write.close;++comma){char ch=body[comma];if(ch=='(')++depth;else if(ch==')'){if(!depth)goto done;--depth;}else if(ch==','&&!depth)break;}
    if(comma==write.close||!owned_rmw_same_ea(body,read.args,read.close,write.args,comma))goto done;
    unsigned bytes=read.bits/8,mode=(unsigned)ins->src_ea>>3,reg=(unsigned)ins->src_ea&7u;
    fprintf(out,"  { M68kStepOwnedRmw _owned; uint32_t _owned_ea=(uint32_t)(%.*s)",
        (int)(read.close-read.args),body+read.args);
    if(mode==4)fprintf(out,"-%uu",reg==7&&bytes==1?2u:bytes);
    fprintf(out,";\n    if(m68k_step_owned_rmw(ctx,_owned_ea,%u,&_owned)){\n",bytes);
    fwrite(body,1,read.begin,out);fprintf(out,"m68k_step_owned_read%u(&_owned)",read.bits);
    fwrite(body+read.end,1,write.begin-read.end,out);
    fprintf(out,"m68k_step_owned_write%u(&_owned,%.*s)",write.bits,(int)(write.close-comma-1),body+comma+1);
    fwrite(body+write.end,1,(size_t)size-write.end,out);
    fputs("    }else{\n",out);fwrite(body,1,(size_t)size,out);fputs("    }\n  }\n",out);
    emitted=!ferror(out);
done:
    free(body);if(fclose(buffer))emitted=false;return emitted;
}

unsigned codegen_step_nominal_cycles(const M68KInstr *ins)
{
    return ins && ins->word_count ? (unsigned)estimate_cycles_prm(ins) : 0;
}

static bool span_value_ea(int ea)
{ return ea>=0 && (ea<16 || ea==0x3c); }

bool codegen_register_instruction(const M68KInstr *ins,unsigned *read,unsigned *written)
{
    unsigned r=0,w=0;
    if(!ins || !ins->word_count || m68k_validate(ins,NULL)!=M68K_LEGAL)return false;
    switch(ins->mnemonic) {
    case MN_NOP: break;
    case MN_MOVE:
        if(!span_value_ea(ins->src_ea) || ins->dst_ea<0 || ins->dst_ea>=8)return false;
        w=15;break;
    case MN_MOVEA: case MN_ADDA: case MN_SUBA:
        if(!span_value_ea(ins->src_ea))return false;
        break;
    case MN_MOVEQ: case MN_SWAP: case MN_EXT: w=15;break;
    case MN_LEA:
        /* Address arithmetic only: includes constant/PC-relative and brief
         * indexed EAs, never dereferences guest memory. */
        if((ins->src_ea>>3)<2 || (ins->src_ea>>3)==3 || (ins->src_ea>>3)==4 ||
           ins->src_ea>0x3b)return false;
        break;
    case MN_ADD: case MN_SUB:
        if(!span_value_ea(ins->src_ea) ||
           ((ins->words[0]&0x100u) && ins->src_ea>=8))return false;
        w=31;break;
    case MN_ADDQ: case MN_SUBQ:
        if(ins->src_ea<0 || ins->src_ea>=16)return false;
        w=ins->src_ea<8?31u:0u;break;
    case MN_ADDI: case MN_SUBI: case MN_NEG:
        if(ins->src_ea<0 || ins->src_ea>=8)return false;
        w=31;break;
    case MN_AND: case MN_OR: case MN_EOR:
        if(!span_value_ea(ins->src_ea) ||
           ((ins->words[0]&0x100u) && ins->src_ea>=8))return false;
        w=15;break;
    case MN_ANDI: case MN_ORI: case MN_EORI: case MN_CMPI:
    case MN_NOT: case MN_TST: case MN_CLR:
        if(ins->src_ea<0 || ins->src_ea>=8)return false;
        w=15;break;
    case MN_CMP: case MN_CMPA:
        if(!span_value_ea(ins->src_ea))return false;
        w=15;break;
    case MN_ADDX: case MN_SUBX:
        if(ins->predec_mem_form)return false;
        r=20;w=31;break; /* X and sticky Z are inputs, not dead writes. */
    case MN_NEGX:
        if(ins->src_ea<0 || ins->src_ea>=8)return false;
        r=20;w=31;break;
    case MN_ABCD: case MN_SBCD:
        if(ins->predec_mem_form)return false;
        r=31;break; /* Conservatively retain all incoming undefined flags. */
    case MN_NBCD:
        if(ins->src_ea<0 || ins->src_ea>=8)return false;
        r=31;break;
    case MN_EXG: break;
    default: return false;
    }
    if(read)*read=r;
    if(written)*written=w;
    return true;
}

/* Replace only canonical register tokens from the common emitter. No textual
 * expression optimization: the host compiler sees one straight-line SSA-like
 * region, so adjacent LEAs/address adds fold without repeating global stores.
 */
static unsigned span_register_token(const char *p,unsigned *length)
{
    if(strncmp(p,"g_cpu.",6))return 0;
    if((p[6]=='D'||p[6]=='A') && p[7]=='[' && p[8]>='0' && p[8]<='7' && p[9]==']') {
        *length=10;return 1u<<((p[6]=='D'?0:8)+(unsigned)(p[8]-'0'));
    }
    if(!strncmp(p+6,"SR",2)){*length=8;return 1u<<16;}
    return 0;
}
static void span_local_name(FILE *f,unsigned bit)
{
    unsigned index=0;while((1u<<index)!=bit)++index;
    if(index==16)fputs("_spanSR",f);
    else fprintf(f,"_span%c%u",index<8?'D':'A',index&7u);
}

bool codegen_emit_register_span(FILE *out,const GenesisRom *rom,const M68KInstr *ins,unsigned count)
{
    if(!out || !rom || !ins || count<2 || count>CODEGEN_REGISTER_SPAN_MAX)return false;
    unsigned live[CODEGEN_REGISTER_SPAN_MAX],need=31;
    for(unsigned n=count;n--;) {
        unsigned read,written;
        if(!codegen_register_instruction(&ins[n],&read,&written) ||
           (n && ins[n-1].addr+ins[n-1].byte_length!=ins[n].addr))return false;
        live[n]=need;need=(need&~written)|read;
    }
    FILE *buffer=tmpfile();if(!buffer)return false;
    bool old_active=s_span_flags;unsigned old_live=s_span_live_flags;
    s_span_flags=true;
    bool okay=true;
    for(unsigned n=0;n<count;++n) {
        s_span_live_flags=live[n];fputs("  {\n",buffer);
        if(!codegen_emit_step_semantics(buffer,rom,&ins[n])){okay=false;break;}
        fputs("  }\n",buffer);
    }
    s_span_flags=old_active;s_span_live_flags=old_live;
    if(fflush(buffer) || ferror(buffer))okay=false;
    long size=ftell(buffer);
    char *text=size>=0?malloc((size_t)size+1u):NULL;
    if(!text)okay=false;
    if(okay && (fseek(buffer,0,SEEK_SET) || fread(text,1,(size_t)size,buffer)!=(size_t)size))okay=false;
    if(fclose(buffer))okay=false;
    if(!okay){free(text);return false;}
    text[size]=0;
    unsigned used=0;
    for(const char *p=text;*p;) {
        unsigned length=0,bit=span_register_token(p,&length);
        used|=bit;p+=bit?length:1;
    }
    fputs("  { /* unobservable fixed-cycle register span */\n",out);
    for(unsigned n=0;n<17;++n)if(used&(1u<<n)) {
        fprintf(out,"    %s ",n==16?"uint16_t":"uint32_t");span_local_name(out,1u<<n);
        if(n==16)fputs("=g_cpu.SR;\n",out);
        else fprintf(out,"=g_cpu.%c[%u];\n",n<8?'D':'A',n&7u);
    }
    for(const char *p=text;*p;) {
        unsigned length=0,bit=span_register_token(p,&length);
        if(bit){span_local_name(out,bit);p+=length;}
        else fputc(*p++,out);
    }
    for(unsigned n=0;n<17;++n)if(used&(1u<<n)) {
        if(n==16)fputs("    g_cpu.SR=",out);
        else fprintf(out,"    g_cpu.%c[%u]=",n<8?'D':'A',n&7u);
        span_local_name(out,1u<<n);fputs(";\n",out);
    }
    fputs("  }\n",out);free(text);return !ferror(out);
}

bool codegen_flow_terminal(const M68KInstr *ins,unsigned *maximum)
{
    if(!ins || !ins->word_count || ins->word_count>M68K_MAX_WORDS ||
       ins->byte_length!=(unsigned)ins->word_count*2u ||
       (ins->addr&1u) || ins->addr>0xffffffu)return false;
    unsigned cycles;
    switch(ins->mnemonic) {
    case MN_BRA:if(!ins->has_target || ins->word_count>2)return false;cycles=10;break;
    case MN_Bcc:if(!ins->has_target || ins->word_count>2)return false;cycles=ins->word_count==1?10u:12u;break;
    case MN_DBcc:if(!ins->has_target || ins->word_count!=2)return false;cycles=14;break;
    case MN_JMP:
        if(ins->src_ea<0 || ins->src_ea>63)return false;
        cycles=step_jump_cost((unsigned)ins->src_ea,false);
        if(!cycles)return false;
        break;
    default:return false;
    }
    if(maximum)*maximum=cycles;
    return true;
}
bool codegen_emit_flow_span(FILE *f,const GenesisRom *rom,const M68KInstr *ins,unsigned count)
{
    if(!f || !rom || !ins || count<2 || count>CODEGEN_REGISTER_SPAN_MAX ||
       !codegen_flow_terminal(&ins[count-1],NULL))return false;
    for(unsigned n=0;n<count-1;++n)
        if(!codegen_register_instruction(&ins[n],NULL,NULL) ||
           ins[n].addr+ins[n].byte_length!=ins[n+1].addr)return false;
    /* Final prefix flags remain live for the control condition. Publishing
     * prefix locals before its exact terminal body also preserves DBcc and
     * register-indexed target dependencies. No observer can occur here. */
    return (count==2?codegen_emit_step_operation(f,rom,ins):
            codegen_emit_register_span(f,rom,ins,count-1)) &&
           codegen_emit_step_operation(f,rom,&ins[count-1]);
}

static void emit_decls_preamble(FILE *f) {
    fprintf(f, "#pragma once\n");
    fprintf(f, "/* <prefix>_decls.h — AUTO-GENERATED by GenesisRecomp. DO NOT EDIT.\n");
    fprintf(f, " * Shared includes + forward decls for the split <prefix>_partNN.c\n");
    fprintf(f, " * translation units (see cmake/GenesisRecompGenerated.cmake). */\n");
    fprintf(f, "#include \"genesis_runtime.h\"\n");
    fprintf(f, "#ifndef RECOMP_CALL_NATIVE\n#define RECOMP_CALL_NATIVE(fn) recomp_call_func(fn)\n#endif\n");
    fprintf(f, "#ifndef RECOMP_TAIL_NATIVE\n#define RECOMP_TAIL_NATIVE(addr,fn) recomp_tail_call(addr)\n#endif\n");
    fprintf(f, "#ifndef GEN_NATIVE_SPAN_RETIRED\n#define GEN_NATIVE_SPAN_RETIRED() ((void)0)\n#endif\n");
    fprintf(f, "#ifndef GEN_NATIVE_REGISTER_SPAN_READY\n#define GEN_NATIVE_REGISTER_SPAN_READY(cycles, count) (g_cycle_accumulator<g_vblank_threshold && (cycles)<g_vblank_threshold-g_cycle_accumulator)\n#endif\n");
    fprintf(f, "#include <stdio.h>\n");
    fprintf(f, "#include <stdlib.h>\n");
    if (s_reverse_debug) {
        /* Pull in the reverse-debugger API: g_rdb_current_func extern
         * (Tier 1) and rdb_on_block inline fast path (Tier 2). Header
         * is in runner/ which is on both targets' include path. */
        fprintf(f, "#include \"reverse_debug.h\"\n");
    }
    fprintf(f, "\n");
    fprintf(f, "/* Stack-skip levels carried across generated split-function tail calls.\n");
    fprintf(f, " * Real 68K JSR calls hide this value from callees; branch/JMP/fallthrough\n");
    fprintf(f, " * split calls preserve it until the next RTS consumes it. One file-scope\n");
    fprintf(f, " * definition lives in part00; every split TU links against this extern. */\n");
    fprintf(f, "extern int g_split_sp_popped;\n");
    fprintf(f, "\n");
}

/* =========================================================================
 * Per-function body buffering for size-balanced part-file distribution.
 *
 * Each function is fully emitted to an anonymous tmpfile() first so its
 * exact byte size is known; the buffered text is then copied verbatim into
 * whichever part file the greedy balancer assigns it to. This keeps the
 * ~4300 lines of per-instruction fprintf(f, ...) emission above completely
 * unaware of file splitting: callers just pass a different FILE* target.
 * ========================================================================= */

typedef struct {
    char   *data;
    size_t  size;
    uint32_t address;
} PartBuf;

static PartBuf *s_part_bufs      = NULL;
static int      s_part_buf_count = 0;
static int      s_part_buf_cap   = 0;

/* Reads back everything written to `tmp`, appends it as a new buffered
 * function body, and closes `tmp` (tmpfile()s are unlinked on close). */
static void part_buf_push(FILE *tmp,uint32_t address) {
    long sz = ftell(tmp);
    if (sz < 0) sz = 0;
    rewind(tmp);
    char *buf = (char *)malloc((size_t)(sz > 0 ? sz : 0)+1u);
    size_t rd = (sz > 0 && buf) ? fread(buf, 1, (size_t)sz, tmp) : 0;
    if(buf)buf[rd]=0;
    fclose(tmp);
    if (s_part_buf_count == s_part_buf_cap) {
        s_part_buf_cap = s_part_buf_cap ? s_part_buf_cap * 2 : 256;
        s_part_bufs = (PartBuf *)realloc(s_part_bufs,
                                         (size_t)s_part_buf_cap * sizeof(PartBuf));
    }
    s_part_bufs[s_part_buf_count].data = buf;
    s_part_bufs[s_part_buf_count].size = rd;
    s_part_bufs[s_part_buf_count].address = address;
    s_part_buf_count++;
}

typedef struct {int from,to;size_t target_size;} PartEdge;
typedef struct {int root;size_t size;uint32_t address;} PartGroup;
static int part_edge_compare(const void *a,const void *b)
{
    const PartEdge*x=a,*y=b;
    if(x->target_size!=y->target_size)return x->target_size<y->target_size?-1:1;
    if(x->from!=y->from)return x->from<y->from?-1:1;
    return x->to<y->to?-1:x->to!=y->to;
}
static int part_group_compare(const void *a,const void *b)
{
    const PartGroup*x=a,*y=b;
    if(x->size!=y->size)return x->size>y->size?-1:1;
    return x->address<y->address?-1:x->address!=y->address;
}
static int part_root(int *parent,int n)
{while(parent[n]!=n){parent[n]=parent[parent[n]];n=parent[n];}return n;}
static int part_find(uint32_t address)
{
    int lo=0,hi=s_part_buf_count;
    while(lo<hi){int mid=lo+(hi-lo)/2;if(s_part_bufs[mid].address<address)lo=mid+1;else hi=mid;}
    return lo<s_part_buf_count&&s_part_bufs[lo].address==address?lo:-1;
}
/* Direct native edges expose compiler inlining only when both definitions
 * share a TU. Keep complete canonical bodies/alias wrappers byte-identical,
 * cluster small callees within a bounded size, then balance whole clusters.
 * No profile, semantic substitution or unbounded monolithic TU is required.
 * Allocation failure retains the previous portable address-order layout. */
static bool part_buf_callgraph(FILE **parts,const AddrSet *functions,const uint32_t *owners)
{
    int count=s_part_buf_count;size_t edge_count=0,edge_capacity=0,total=0;
    PartEdge *edges=NULL;int *parent=malloc((size_t)count*sizeof*parent);
    int *head=malloc((size_t)count*sizeof*head),*next=malloc((size_t)count*sizeof*next);
    size_t *sizes=malloc((size_t)count*sizeof*sizes);
    PartGroup *groups=malloc((size_t)count*sizeof*groups);
    bool ready=false;
    if(!count || !parent || !head || !next || !sizes || !groups)goto done;
    for(int n=0;n<count;++n){parent[n]=n;head[n]=-1;sizes[n]=s_part_bufs[n].size;total+=sizes[n];}
    for(int n=0;n<count;++n)for(unsigned kind=0;kind<2;++kind){
        const char *marker=kind?"RECOMP_TAIL_NATIVE(":"RECOMP_CALL_NATIVE(";
        const char *at=s_part_bufs[n].data;
        while(at && (at=strstr(at,marker))!=NULL){
            at+=strlen(marker);const char *symbol=strstr(at,"func_");
            const char *end=strchr(at,')');
            if(!symbol || !end || symbol>end)continue;
            char *tail;uint32_t address=(uint32_t)strtoul(symbol+5,&tail,16);
            if(tail!=symbol+11)continue;
            int lo=0,hi=functions->count;
            while(lo<hi){int mid=lo+(hi-lo)/2;if(functions->addrs[mid]<address)lo=mid+1;else hi=mid;}
            if(lo==functions->count || functions->addrs[lo]!=address)continue;
            int target=part_find(owners[lo]);if(target<0 || target==n)continue;
            if(edge_count==edge_capacity){
                size_t capacity=edge_capacity?edge_capacity*2u:256u;
                PartEdge *grown=realloc(edges,capacity*sizeof*edges);if(!grown)goto done;
                edges=grown;edge_capacity=capacity;
            }
            edges[edge_count++]=(PartEdge){n,target,s_part_bufs[target].size};
        }
    }
    if(edge_count>1)qsort(edges,edge_count,sizeof*edges,part_edge_compare);
    size_t limit=total/(size_t)GENESIS_SPLIT_PART_COUNT*6u/5u;
    for(size_t e=0;e<edge_count;++e){
        int a=part_root(parent,edges[e].from),z=part_root(parent,edges[e].to);
        if(a!=z && sizes[a]+sizes[z]<=limit){parent[z]=a;sizes[a]+=sizes[z];}
    }
    int group_count=0;
    for(int n=count-1;n>=0;--n){int root=part_root(parent,n);next[n]=head[root];head[root]=n;}
    for(int n=0;n<count;++n)if(parent[n]==n)groups[group_count++]=(PartGroup){n,sizes[n],s_part_bufs[n].address};
    qsort(groups,(size_t)group_count,sizeof*groups,part_group_compare);
    size_t loads[GENESIS_SPLIT_PART_COUNT]={0};unsigned together=0;
    for(size_t e=0;e<edge_count;++e)if(part_root(parent,edges[e].from)==part_root(parent,edges[e].to))++together;
    for(int g=0;g<group_count;++g){
        unsigned bucket=0;for(unsigned p=1;p<GENESIS_SPLIT_PART_COUNT;++p)if(loads[p]<loads[bucket])bucket=p;
        for(int n=head[groups[g].root];n>=0;n=next[n])if(s_part_bufs[n].size)
            fwrite(s_part_bufs[n].data,1,s_part_bufs[n].size,parts[bucket]);
        loads[bucket]+=groups[g].size;
    }
    printf("[Codegen] Native callgraph: %zu edges, %u clustered, %d bounded groups across %u parts\n",edge_count,together,group_count,GENESIS_SPLIT_PART_COUNT);
    ready=true;
done:
    free(parent);free(head);free(next);free(sizes);free(groups);free(edges);return ready;
}

/* Frees any buffered-but-unflushed function bodies from a previous (e.g.
 * aborted) codegen_emit call, so repeated invocations in one process never
 * leak. */
static void part_buf_reset(void) {
    for (int i = 0; i < s_part_buf_count; i++)
        free(s_part_bufs[i].data);
    free(s_part_bufs);
    s_part_bufs = NULL;
    s_part_buf_count = 0;
    s_part_buf_cap = 0;
}

static void codegen_close_all(FILE *f_header, FILE **f_parts, int n_parts,
                              FILE *f_dispatch) {
    if (f_header) fclose(f_header);
    for (int i = 0; i < n_parts; i++)
        if (f_parts[i]) fclose(f_parts[i]);
    if (f_dispatch) fclose(f_dispatch);
}

bool codegen_emit(const GenesisRom *rom, const FunctionList *funcs,
                  const char *out_dir, const char *prefix,
                  const char *out_dispatch_path,
                  const AnnotationTable *at, const GameConfig *cfg,
                  bool reverse_debug) {
    s_reverse_debug = reverse_debug;
    free(s_candidate_owners);
    s_candidate_owners = NULL;
    s_candidate_owner_count = 0;
    s_extra_seeds      = cfg ? cfg->extra_seeds      : NULL;
    s_extra_seed_count = cfg ? cfg->extra_seed_count : 0;
    s_ws_sites      = cfg ? cfg->ws_sites      : NULL;
    s_ws_site_count = cfg ? cfg->ws_site_count : 0;
    if (s_ws_site_count)
        printf("[Codegen] [widescreen] %d injection sites armed (recompile-time)\n",
               s_ws_site_count);
    codegen_diag_reset();
    audit_reset();
    part_buf_reset();

    char header_path[1024];
    snprintf(header_path, sizeof(header_path), "%s/%s_decls.h", out_dir, prefix);
    FILE *f_header   = m68k_fopen(header_path, "w");
    FILE *f_dispatch = m68k_fopen(out_dispatch_path, "w");

    if (!f_header) {
        fprintf(stderr, "codegen: cannot open %s\n", header_path);
        if (f_dispatch) fclose(f_dispatch);
        return false;
    }
    if (!f_dispatch) {
        fprintf(stderr, "codegen: cannot open %s\n", out_dispatch_path);
        fclose(f_header);
        return false;
    }

    FILE *f_parts[GENESIS_SPLIT_PART_COUNT] = {0};
    char part_path[GENESIS_SPLIT_PART_COUNT][1024];
    bool parts_ok = true;
    for (int k = 0; k < GENESIS_SPLIT_PART_COUNT; k++) {
        snprintf(part_path[k], sizeof(part_path[k]), "%s/%s_part%02d.c",
                 out_dir, prefix, k);
        f_parts[k] = m68k_fopen(part_path[k], "w");
        if (!f_parts[k]) {
            fprintf(stderr, "codegen: cannot open %s\n", part_path[k]);
            parts_ok = false;
        }
    }
    if (!parts_ok) {
        codegen_close_all(f_header, f_parts, GENESIS_SPLIT_PART_COUNT, f_dispatch);
        return false;
    }

    emit_decls_preamble(f_header);
    for (int k = 0; k < GENESIS_SPLIT_PART_COUNT; k++) {
        fprintf(f_parts[k],
                "/* %s_part%02d.c — AUTO-GENERATED by GenesisRecomp. DO NOT EDIT. */\n",
                prefix, k);
        fprintf(f_parts[k], "#include \"%s_decls.h\"\n\n", prefix);
        if (k == 0) {
            fprintf(f_parts[k],
                "/* The one file-scope definition for the extern declared in\n"
                " * %s_decls.h — every other split TU links against this. */\n"
                "int g_split_sp_popped = 0; /* signed guest stack delta in bytes */\n\n", prefix);
        }
    }

    /* Build mutable sorted array of all function entry points for boundary
     * detection. Cross-function branches may discover mid-function targets
     * that need to become new function entries; iterate until stable. */
    AddrSet all_funcs;
    addrset_init(&all_funcs);
    for (int i = 0; i < funcs->count; i++)
        addrset_insert(&all_funcs, funcs->entries[i].addr);
    addrset_sort(&all_funcs);

    /* Discovery loop: scan all functions, collect external branch targets,
     * add them as new function entries, repeat until no new entries appear. */
    for (;;) {
        AddrSet extern_targets;
        addrset_init(&extern_targets);

        AddrSet hard_boundaries;
        uint32_t *iter_owners = NULL;
        if (cfg && cfg->function_aliases) {
            iter_owners = build_entry_owners(rom, &all_funcs, cfg,
                                             &hard_boundaries, false);
        } else {
            /* Default path: retain the established boundary set. Alias
             * candidates are audited once after this fixed point, not on
             * every discovery iteration. */
            iter_owners = (uint32_t *)malloc((size_t)all_funcs.count
                                             * sizeof(uint32_t));
            addrset_init(&hard_boundaries);
            if (iter_owners) {
                for (int i = 0; i < all_funcs.count; i++) {
                    iter_owners[i] = all_funcs.addrs[i];
                    addrset_insert(&hard_boundaries, all_funcs.addrs[i]);
                }
            }
        }
        if (!iter_owners) {
            addrset_free(&extern_targets);
            codegen_close_all(f_header, f_parts, GENESIS_SPLIT_PART_COUNT, f_dispatch);
            addrset_free(&all_funcs);
            return false;
        }

        /* Alias bodies are already reachable from their canonical host. Scan
         * canonical hosts only, and let only canonical entries bound them. */
        for (int i = 0; i < hard_boundaries.count; i++) {
            AddrSet instrs, labels;
            addrset_init(&instrs);
            addrset_init(&labels);
            scan_function(rom, hard_boundaries.addrs[i], &instrs, &labels,
                          hard_boundaries.addrs, hard_boundaries.count,
                          all_funcs.addrs, all_funcs.count, &extern_targets,
                          cfg ? cfg->extra_seeds : NULL,
                          cfg ? cfg->extra_seed_count : 0, cfg);
            addrset_free(&instrs);
            addrset_free(&labels);
        }
        free(iter_owners);
        addrset_free(&hard_boundaries);

        /* Add any external targets that aren't already function entries.
         * Skip addresses from game.toml [functions].blacklist —
         * useful for data labels the disasm never marks as code that
         * boundary-split would otherwise promote into bogus function
         * entries. */
        int added = 0, skipped_blacklist = 0, skipped_data = 0;
        for (int i = 0; i < extern_targets.count; i++) {
            uint32_t a = extern_targets.addrs[i];
            if (addrset_contains(&all_funcs, a)) continue;
            if (game_config_is_blacklisted(cfg, a)) {
                skipped_blacklist++;
                continue;
            }
            /* Data-gate: if a disasm code-address oracle is loaded, never
             * promote a target the disasm assembles as DATA. This kills the
             * data-as-code false-positive class (Eni_Decomp_Masks, sine
             * tables, art/mapping tables) that scan-time dispatch seeding and
             * mis-decoded function over-runs would otherwise create. No-op
             * when no code_addrs_file is configured (is_known_code => true). */
            if (!game_config_is_known_code(cfg, a)) {
                skipped_data++;
                continue;
            }
            addrset_insert(&all_funcs, a);
            added++;
        }
        addrset_free(&extern_targets);
        if (skipped_blacklist > 0)
            printf("[Codegen] Skipped %d blacklisted boundary-split entries\n",
                   skipped_blacklist);
        if (skipped_data > 0)
            printf("[Codegen] Data-gate: skipped %d boundary-split entries that "
                   "land on disasm data (not code)\n", skipped_data);

        if (added == 0) break;
        printf("[Codegen] Function boundary split: added %d new function entries, re-scanning...\n", added);
        addrset_sort(&all_funcs);
    }

    printf("[Codegen] Final function count after boundary splitting: %d\n", all_funcs.count);

    AddrSet hard_boundaries;
    uint32_t *entry_owners = build_entry_owners(rom, &all_funcs, cfg,
                                                &hard_boundaries, true);
    if (!entry_owners) {
        codegen_close_all(f_header, f_parts, GENESIS_SPLIT_PART_COUNT, f_dispatch);
        addrset_free(&all_funcs);
        return false;
    }

    if (s_dump_functions_path) {
        FILE *df = m68k_fopen(s_dump_functions_path, "w");
        if (df) {
            fprintf(df, "# Final function-entry set (post-boundary-split). "
                        "%d entries. One hex address per line.\n", all_funcs.count);
            for (int i = 0; i < all_funcs.count; i++)
                fprintf(df, "%06X\n", all_funcs.addrs[i]);
            fprintf(df, "# Branch-proven alias candidates (entry -> host).\n");
            if (s_candidate_owner_count == all_funcs.count) {
                for (int i = 0; i < all_funcs.count; i++)
                    if (s_candidate_owners[i] != all_funcs.addrs[i])
                        fprintf(df, "# candidate %06X -> %06X\n",
                                all_funcs.addrs[i], s_candidate_owners[i]);
            }
            fprintf(df, "# Overlapping entry aliases (entry -> canonical host).\n");
            for (int i = 0; i < all_funcs.count; i++)
                if (entry_owners[i] != all_funcs.addrs[i])
                    fprintf(df, "# alias %06X -> %06X\n",
                            all_funcs.addrs[i], entry_owners[i]);
            fclose(df);
            printf("[Codegen] Dumped %d function addresses to %s\n",
                   all_funcs.count, s_dump_functions_path);
        } else {
            fprintf(stderr, "[Codegen] could not open %s for --dump-functions\n",
                    s_dump_functions_path);
        }
    }

    /* Expose the final sorted function table to emit_instr so JSR emission
     * can distinguish known targets (recomp_call_func) from unknown ones
     * (recomp_call_addr fallback). */
    s_all_func_addrs = all_funcs.addrs;
    s_all_func_count = all_funcs.count;

    /* Forward declarations, written to the shared header so every part TU
     * can see every function regardless of which bucket it lands in. */
    for (int i = 0; i < all_funcs.count; i++)
        fprintf(f_header, "void func_%06X(void);\n", all_funcs.addrs[i]);
    /* Alias-group host bodies (func_body_%06X) are external too, so
     * bucketing never needs to keep a canonical host and its thin
     * func_%06X wrappers in the same part file. No-op when the game has
     * zero alias groups (e.g. Sonic 1 today), but handled generally since
     * the emitter is shared across every Genesis port. */
    for (int i = 0; i < all_funcs.count; i++) {
        if (entry_owners[i] != all_funcs.addrs[i]) continue; /* not a canonical host */
        int group_count = 0;
        for (int a = 0; a < all_funcs.count; a++)
            if (entry_owners[a] == all_funcs.addrs[i]) group_count++;
        if (group_count > 1)
            fprintf(f_header, "void func_body_%06X(uint32_t _entry);\n", all_funcs.addrs[i]);
    }
    fprintf(f_header, "\n");
    fclose(f_header);
    f_header = NULL;

    /* Emit each function body */
    for (int i = 0; i < all_funcs.count; i++) {
        uint32_t func_addr = all_funcs.addrs[i];
        uint32_t walk_start = entry_owners[i];
        if (walk_start != func_addr)
            continue; /* emitted by the canonical host's shared body below */
        int group_count = 0;
        for (int a = 0; a < all_funcs.count; a++)
            if (entry_owners[a] == func_addr) group_count++;
        bool has_aliases = group_count > 1;

        /* Buffer this function's full emission (through both possible exit
         * points below) so its exact byte size is known before deciding
         * which balanced part file it lands in. See part_buf_push(). */
        FILE *f_func = tmpfile();
        if (!f_func) {
            fprintf(stderr, "codegen: tmpfile() failed while emitting func_%06X\n",
                    func_addr);
            free(entry_owners);
            addrset_free(&hard_boundaries);
            addrset_free(&all_funcs);
            part_buf_reset();
            codegen_close_all(NULL, f_parts, GENESIS_SPLIT_PART_COUNT, f_dispatch);
            return false;
        }

        /* Annotation comment */
        const char *name = annotations_get_name(at, func_addr);
        if (name)
            fprintf(f_func, "/* %s */\n", name);

        /* Scan function to discover instruction addresses and branch labels */
        AddrSet instrs, labels;
        addrset_init(&instrs);
        addrset_init(&labels);
        scan_function(rom, walk_start, &instrs, &labels,
                      hard_boundaries.addrs, hard_boundaries.count,
                      all_funcs.addrs, all_funcs.count, NULL,
                      cfg ? cfg->extra_seeds : NULL,
                      cfg ? cfg->extra_seed_count : 0, cfg);

        /* Sort instruction addresses */
        addrset_sort(&instrs);

        /* Interior-dispatch pre-pass: any JMP (d8,PC,Xn) inside this function
         * whose targets land on in-function instructions needs `label_XXXXXX:;`
         * at each landing point so the MN_JMP emitter can emit a switch + goto
         * rather than punting to hybrid_jmp_interpret (which would silently
         * fail at runtime — see runner/glue.c interior-label silencer).
         *
         * Two patterns covered:
         *   probe_pc_idx_targets    — Duff's device: JMP into a uniform
         *                             sequence of in-function instructions
         *                             (e.g. CPZ/HPZ 16x move.l d0,(a1)+).
         *   probe_offset_table_targets — standard Sonic offset table where
         *                             entries are `dc.w (target - base)`
         *                             pointing to interior labels of the
         *                             same function (e.g. ObjB2_* dispatch
         *                             at $03AD0C / $03AD2A). */
        for (int j = 0; j < instrs.count; j++) {
            uint32_t pc = instrs.addrs[j];
            M68KInstr probe;
            if (!m68k_decode(rom, pc, &probe)) continue;
            if (probe.mnemonic != MN_JMP) continue;
            int pmode = (probe.src_ea >> 3) & 7;
            int preg  = probe.src_ea & 7;
            if (pmode != 7 || preg != 3) continue;   /* not (d8, PC, Xn) */
            uint32_t pc_targets[32];
            int npc = probe_pc_idx_targets(rom, &probe, &instrs, pc_targets,
                                           (int)(sizeof(pc_targets) / sizeof(pc_targets[0])));
            if (npc >= 2) {
                for (int t = 0; t < npc; t++)
                    addrset_insert(&labels, pc_targets[t]);
                continue;
            }
            int32_t  ot_offsets[32];
            uint32_t ot_targets[32];
            int not_ = probe_offset_table_targets(rom, &probe, &instrs,
                                                  ot_offsets, ot_targets,
                                                  (int)(sizeof(ot_targets) / sizeof(ot_targets[0])));
            if (not_ >= 1) {
                for (int t = 0; t < not_; t++)
                    addrset_insert(&labels, ot_targets[t]);
            }
        }

        /* Every alias wrapper enters this shared body through a label at its
         * exact instruction address. The canonical body is emitted once. */
        if (has_aliases) {
            for (int a = 0; a < all_funcs.count; a++)
                if (entry_owners[a] == func_addr && all_funcs.addrs[a] != func_addr)
                    addrset_insert(&labels, all_funcs.addrs[a]);
        }

        /* If the entry address is not the first sorted instruction (e.g. because
         * the function's CFG reaches backward addresses like NemDec callbacks),
         * emit a goto at function start so execution actually begins at func_addr.
         * Also ensure func_addr gets a label emitted when we reach it. */
        bool entry_not_first = (instrs.count > 0 && instrs.addrs[0] != func_addr);
        if (entry_not_first)
            addrset_insert(&labels, func_addr);

        if (has_aliases)
            /* External (not static): forward-declared in the shared header
             * so bucketing can place this host and its thin func_%06X
             * wrappers in different part files without an atomicity
             * constraint. */
            fprintf(f_func, "void func_body_%06X(uint32_t _entry) {\n",
                    func_addr);
        else
            fprintf(f_func, "void func_%06X(void) {\n", func_addr);
        if (s_reverse_debug) {
            if (has_aliases) {
                fprintf(f_func, "  g_rdb_current_func = _entry;\n");
                fprintf(f_func, "  rdb_on_block(_entry);\n");
            } else {
                fprintf(f_func, "  g_rdb_current_func = 0x%06Xu;\n", func_addr);
                fprintf(f_func, "  rdb_on_block(0x%06Xu);\n",        func_addr);
            }
        }

        /* Pre-scan for explicit stack operands of every width.
         * `_sp_popped` tracks the path-local net delta in BYTES. Besides explicit
         * ADDQ stack skips, this must include MOVE/MOVEM postincrement pops:
         * a helper may consume its JSR return slot on only one branch, which
         * cannot be classified as either an ordinary or an unconditional
         * return-capturing callee at the call site. */
        int has_sp_adjust = 0;
        for (int j = 0; j < instrs.count; j++) {
            M68KInstr pre;
            if (m68k_decode(rom, instrs.addrs[j], &pre)) {
                if ((pre.mnemonic == MN_ADDQ || pre.mnemonic == MN_SUBQ) &&
                    ((pre.src_ea >> 3) & 7) == 1 && (pre.src_ea & 7) == 7 &&
                    pre.imm32 > 0) {
                    has_sp_adjust = 1;
                    break;
                }
                if ((pre.mnemonic == MN_ADDA || pre.mnemonic == MN_SUBA) &&
                        pre.reg == 7 && pre.src_ea == ((7 << 3) | 4)) {
                    has_sp_adjust = 1;
                    break;
                }
                if ((pre.mnemonic == MN_MOVE || pre.mnemonic == MN_MOVEA)
                        && pre.src_ea == ((EA_An_POST << 3) | 7)) {
                    has_sp_adjust = 1;
                    break;
                }
                if (pre.mnemonic == MN_MOVE
                        && pre.dst_ea == ((EA_An_PRE << 3) | 7)) {
                    has_sp_adjust = 1;
                    break;
                }
                if (pre.mnemonic == MN_PEA) {
                    has_sp_adjust = 1;
                    break;
                }
                if (pre.mnemonic == MN_MOVEM) {
                    int dir = (pre.words[0] >> 10) & 1;
                    int mode = (pre.src_ea >> 3) & 7;
                    int reg = pre.src_ea & 7;
                    if (reg == 7
                            && ((dir == 1 && mode == 3)
                                || (dir == 0 && mode == 4))) {
                        has_sp_adjust = 1;
                        break;
                    }
                }
            }
        }
        if (has_sp_adjust) {
            /* A generated split-function tail call is one 68K control-flow
             * path, not a real JSR boundary.  Consume its carried net stack
             * delta into this function's path-local accounting before any
             * MOVEM/ADDQ adjustment changes it. */
            fprintf(f_func, "  int _sp_popped = g_split_sp_popped;\n");
            fprintf(f_func, "  g_split_sp_popped = 0;\n");
        }

        /* TEMPORARY debug counters for VBla chain tracing */
        if (func_addr == 0x000B64)
            fprintf(f_func, "  g_dbg_b64_count++;\n");
        else if (func_addr == 0x000B5E)
            fprintf(f_func, "  g_dbg_b5e_count++;\n");
        else if (func_addr == 0x000B88)
            fprintf(f_func, "  g_dbg_b88_count++;\n");

        /* VBlank yield override: emit yield call instead of normal body.
         *
         * The original 68K code is a spin loop: TST.B $F62A; BNE done; BRA loop.
         * In Step 2, VBlank only fires when the game fiber yields to the main
         * loop.  We MUST yield unconditionally so the main loop can run Iterate
         * and service VBlank (which sets $F62A).  After resuming, $F62A will
         * be non-zero and the game continues.
         *
         * Two ways this triggers:
         *   1. Explicit cfg directive: `vblank_yield <addr>` matches.
         *   2. Pattern detection (preferred): the function body is the
         *      4-instruction WaitForVint idiom every Genesis disasm uses:
         *
         *          move    #$XX00,sr           ; XX < $26 → VBlank allowed
         *          tst.b   <ram_byte>.w        ; poll a flag
         *          bne.s   self                ; loop back to tst
         *          rts
         *
         *      Same shape across Sonic 1's func_0029A8, Sonic 2's
         *      func_003384, and (by inspection) virtually every other
         *      Genesis disasm port. Detecting the shape statically means
         *      we don't need a per-game cfg directive for any future port. */
        bool yield_via_cfg = (!has_aliases && cfg->vblank_yield_addr &&
                              func_addr == cfg->vblank_yield_addr);
        bool yield_via_pattern = false;
        if (!has_aliases && !yield_via_cfg && instrs.count == 4) {
            M68KInstr di[4];
            bool ok = true;
            for (int k = 0; k < 4 && ok; k++) {
                if (!m68k_decode(rom, instrs.addrs[k], &di[k]))
                    ok = false;
            }
            if (ok &&
                /* move #imm,sr with VBlank-permitting mask */
                di[0].mnemonic == MN_MOVE_SR && !di[0].dst_is_ea &&
                di[0].src_ea == 0x3C &&
                ((di[0].imm32 & 0x0700) <= 0x0500) &&
                /* tst.b <mem> */
                di[1].mnemonic == MN_TST && di[1].size == M68K_SIZE_B &&
                /* bne back to the tst */
                di[2].mnemonic == MN_Bcc && di[2].has_target &&
                di[2].target_addr == instrs.addrs[1] &&
                /* rts */
                di[3].mnemonic == MN_RTS) {
                yield_via_pattern = true;
            }
        }
        if (yield_via_cfg || yield_via_pattern) {
            fprintf(f_func,
                "  /* WaitForVBlank — yield to main loop (%s) */\n"
                "  g_cpu.SR = 0x2300u;\n"
                "  glue_yield_for_vblank();\n"
                "}\n\n",
                yield_via_pattern ? "pattern-detected: move/tst.b/bne self/rts"
                                  : "game.toml: vblank_yield");
            part_buf_push(f_func,func_addr);
            addrset_free(&instrs);
            addrset_free(&labels);
            continue;
        }

        if (has_aliases) {
            fprintf(f_func, "  switch (_entry) {\n");
            for (int a = 0; a < all_funcs.count; a++) {
                uint32_t entry = all_funcs.addrs[a];
                if (entry_owners[a] == func_addr && entry != func_addr)
                    fprintf(f_func, "    case 0x%06Xu: goto label_%06X;\n",
                            entry, entry);
            }
            if (entry_not_first)
                fprintf(f_func, "    case 0x%06Xu: goto label_%06X;\n",
                        func_addr, func_addr);
            fprintf(f_func, "    default: break;\n  }\n");
        } else if (entry_not_first) {
            fprintf(f_func, "  goto label_%06X;\n", func_addr);
        }

        bool skip_until_label = false;
        uint32_t register_span_end = 0;

        for (int j = 0; j < instrs.count; j++) {
            uint32_t pc = instrs.addrs[j];

            /* Emit label if this address is a branch target */
            if (addrset_contains(&labels, pc)) {
                fprintf(f_func, "  label_%06X:;\n", pc);
                if (s_reverse_debug)
                    fprintf(f_func, "  rdb_on_block(0x%06Xu);\n", pc);
                skip_until_label = false;
            }

            if (skip_until_label)
                continue;

            /* Decode and emit */
            M68KInstr instr;
            if (!m68k_decode(rom, pc, &instr)) {
                fprintf(f_func, "  /* decode error @ $%06X */\n", pc);
                continue;
            }

            /* Ordinary labels/aliases remain entry points into the original
             * instruction stream. A fast span never crosses one, a game hook,
             * reverse-debug observation or stack-unwind bookkeeping. It owns
             * state only while the ENTIRE fixed-cycle span is before the next
             * interrupt/watchdog boundary. The original path handles crossings
             * and every co-simulation checkpoint at the precise instruction. */
            if(!s_reverse_debug && !has_sp_adjust && pc>=register_span_end) {
                M68KInstr span[CODEGEN_REGISTER_SPAN_MAX];
                unsigned count=0,total=0;uint32_t next=pc;
                while(count<CODEGEN_REGISTER_SPAN_MAX && j+(int)count<instrs.count) {
                    uint32_t at=instrs.addrs[j+(int)count];
                    M68KInstr candidate;
                    if(at!=next || (count && addrset_contains(&labels,at)) || ws_site_for(at) ||
                       !m68k_decode(rom,at,&candidate) || !codegen_register_instruction(&candidate,NULL,NULL))break;
                    int cost=estimate_cycles_prm(&candidate);if(cost<=0)break;
                    span[count++]=candidate;total+=(unsigned)cost;next=at+candidate.byte_length;
                }
                /* A real following instruction supplies the original label;
                 * no jump can bypass the function's fall-through tail call. */
                if(count>=2 && j+(int)count<instrs.count && instrs.addrs[j+(int)count]==next) {
                    fprintf(f_func,"#ifndef GENESIS_COSIM\n"
                        "  if(GEN_NATIVE_REGISTER_SPAN_READY(%uu,%uu)){\n",total,count);
                    if(!codegen_emit_register_span(f_func,rom,span,count))return false;
                    fprintf(f_func,"    g_native_insn_count+=%uu; g_cycle_accumulator+=%uu; g_audio_cycle_counter+=%uu; GEN_NATIVE_SPAN_RETIRED();\n"
                                   "    goto label_%06X;\n  }\n#endif\n",count,total,total,next);
                    addrset_insert(&labels,next);register_span_end=next;
                }
            }

            /* "Wait for IRQ-cleared flag" idiom — generalization of
             * the full WaitForVint pattern. The current instruction is
             * `tst.X (mem)` and the NEXT instruction is `bne self`
             * (i.e. branches to this tst). On real hardware the IRQ
             * handler clears the polled flag asynchronously; in our
             * cooperative-fiber model the game thread must yield to
             * let the runner advance clownmdemu (which fires the
             * H/V-Int handler that clears the flag).
             *
             * Mark the next bne so its emitter inserts
             * glue_yield_for_interrupt_poll() inside the loop-back branch
             * (NOT before the tst — yielding on the fall-through path
             * is unnecessary and would mark non-VBlank waits as frame
             * boundaries).
             *
             * Examples:
             *   Sonic 2 BuildSprites_P2 ($016A7A):
             *       tst.w (Hint_flag).w
             *       bne.s BuildSprites_P2 */
            if (j + 1 < instrs.count && instr.mnemonic == MN_TST) {
                M68KInstr next;
                if (m68k_decode(rom, instrs.addrs[j + 1], &next) &&
                    next.mnemonic == MN_Bcc &&
                    next.has_target &&
                    next.target_addr == pc) {
                    g_yield_in_next_bne = true;
                }
            }

            fprintf(f_func, "  /* $%06X */\n", pc);
            if (s_reverse_debug)
                fprintf(f_func, "  rdb_on_insn(0x%06Xu);\n", pc);
            emit_instr(f_func, rom, &instr, &instrs, &skip_until_label, &has_sp_adjust,
                       name, func_addr, false);

            /* Contextual recompiler: accumulate cycles and check for
             * pending VBlank.  The runtime maintains g_cycle_accumulator
             * which is checked against the VBlank threshold (~109312
             * 68K cycles from frame start = scanline 224).  This allows
             * the VBlank handler to fire between any two instructions,
             * matching the interpreter's interrupt-driven behavior. */
            {
                int cyc = estimate_cycles(&instr);
                emit_cycle_accounting(f_func, "  ", cyc);
            }

            /* Two valid entry streams can overlap in ROM. Sorted emission
             * interleaves their instruction starts, but linear execution
             * must continue at the byte after THIS instruction. Otherwise a
             * normal path runs the other stream's decoded extension words.
             * RKA $0289FA..$028A00 is one such case: falling through the
             * alternate $0289FC entry writes $02 into an object's type. */
            uint32_t next_pc = pc + instr.byte_length;
            if (j + 1 < instrs.count && instrs.addrs[j + 1] < next_pc &&
                addrset_contains(&instrs, next_pc)) {
                addrset_insert(&labels, next_pc);
                fprintf(f_func, "  goto label_%06X;\n", next_pc);
            }
        }

        /* Fall-through: if the last instruction in this function is not a
         * hard terminator (RTS/RTE/STOP/JMP/BRA) and the next address belongs
         * to a different function, emit a tail call so linear control flow
         * crosses the function boundary correctly.
         *
         * This covers both the JSR/BSR case (caller falls through to the
         * instruction after the return address) and plain data instructions
         * that fall through into an adjacent extracted function (e.g. when a
         * merge-point inside a loop body is split into its own function). */
        if (instrs.count > 0) {
            uint32_t last_pc = instrs.addrs[instrs.count - 1];
            M68KInstr last_instr;
            if (m68k_decode(rom, last_pc, &last_instr)) {
                bool is_terminator = (last_instr.mnemonic == MN_RTS     ||
                                      last_instr.mnemonic == MN_RTE     ||
                                      last_instr.mnemonic == MN_RTR     ||
                                      last_instr.mnemonic == MN_STOP    ||
                                      last_instr.mnemonic == MN_ILLEGAL ||
                                      last_instr.mnemonic == MN_JMP     ||
                                      last_instr.mnemonic == MN_BRA);
                /* A jsr/bsr whose callee unconditionally pops our return
                 * address (Obj_WaitOffscreen idiom) is emitted as a
                 * non-returning tail transfer above, so it does NOT fall
                 * through to the next instruction — treat it as a terminator
                 * here to suppress the boundary tail call. */
                if (!is_terminator && m68k_is_call(&last_instr) &&
                    last_instr.has_target &&
                    function_finder_pops_return_unconditionally(rom, last_instr.target_addr))
                    is_terminator = true;
                if (!is_terminator) {
                    uint32_t fall_through = last_pc + last_instr.byte_length;
                    /* Only emit the tail call if fall_through is the entry
                     * point of a known function (not just an interior address
                     * inside another function's range). */
                    if (fall_through != func_addr &&
                        addrset_contains(&all_funcs, fall_through)) {
                        emit_split_tail_call(f_func, rom,"  ", fall_through, has_sp_adjust != 0,
                                             -1);
                    }
                }
            }
        }

        fprintf(f_func, "}\n\n");

        if (has_aliases) {
            /* Thin dispatchable wrappers preserve every original entry while
             * sharing one host CFG/body. No wrapper changes the host extent. */
            for (int a = 0; a < all_funcs.count; a++) {
                uint32_t entry = all_funcs.addrs[a];
                if (entry_owners[a] != func_addr) continue;
                const char *alias_name = annotations_get_name(at, entry);
                if (alias_name)
                    fprintf(f_func, "/* %s */\n", alias_name);
                fprintf(f_func,
                        "void func_%06X(void) { func_body_%06X(0x%06Xu); }\n",
                        entry, func_addr, entry);
            }
            fprintf(f_func, "\n");
        }

        part_buf_push(f_func,func_addr);
        addrset_free(&instrs);
        addrset_free(&labels);
    }

    /* Keep complete bodies and alias groups intact. Native callgraph clusters
     * expose same-TU direct edges to the ordinary portable compiler. The old
     * address-order size balance remains an allocation-failure fallback. */
    {
        if(!part_buf_callgraph(f_parts,&all_funcs,entry_owners)) {
        size_t total_size = 0;
        for (int i = 0; i < s_part_buf_count; i++)
            total_size += s_part_bufs[i].size;
        size_t target_per_part = total_size / (size_t)GENESIS_SPLIT_PART_COUNT;

        int    cur_part      = 0;
        size_t cur_part_size = 0;
        for (int i = 0; i < s_part_buf_count; i++) {
            if (s_part_bufs[i].size && s_part_bufs[i].data)
                fwrite(s_part_bufs[i].data, 1, s_part_bufs[i].size, f_parts[cur_part]);
            cur_part_size += s_part_bufs[i].size;
            if (cur_part_size >= target_per_part && cur_part < GENESIS_SPLIT_PART_COUNT - 1) {
                cur_part++;
                cur_part_size = 0;
            }
        }
        }
        part_buf_reset();

        for (int k = 0; k < GENESIS_SPLIT_PART_COUNT; k++)
            fclose(f_parts[k]);
    }

    /* Dispatch table */
    fprintf(f_dispatch, "/* sonic_dispatch.c — AUTO-GENERATED by GenesisRecomp. DO NOT EDIT. */\n");
    fprintf(f_dispatch, "#include \"genesis_runtime.h\"\n");
    fprintf(f_dispatch, "#include \"game_spec.h\"\n");
    fprintf(f_dispatch, "#include <stddef.h>\n");
    fprintf(f_dispatch, "#include <stdio.h>\n");
    fprintf(f_dispatch, "#include <stdlib.h>\n\n");
    fprintf(f_dispatch, "typedef void (*FuncPtr)(void);\n\n");
    fprintf(f_dispatch,
        "typedef struct {\n"
        "    uint32_t addr;\n"
        "    FuncPtr  fn;\n"
        "} DispatchEntry;\n\n");

    /* Forward-declare all functions */
    for (int i = 0; i < all_funcs.count; i++)
        fprintf(f_dispatch, "void func_%06X(void);\n", all_funcs.addrs[i]);

    fprintf(f_dispatch, "\nstatic const DispatchEntry s_dispatch_table[] = {\n");
    for (int i = 0; i < all_funcs.count; i++)
        fprintf(f_dispatch, "    { 0x%06Xu, func_%06X },\n",
                all_funcs.addrs[i], all_funcs.addrs[i]);
    fprintf(f_dispatch, "    { 0u, NULL }\n};\n\n");

    fprintf(f_dispatch,
        "static FuncPtr recomp_find_func(uint32_t addr) {\n"
        "    int lo = 0, hi = %d;\n"
        "    while (lo < hi) {\n"
        "        int mid = lo + (hi - lo) / 2;\n"
        "        if (s_dispatch_table[mid].addr < addr) lo = mid + 1;\n"
        "        else hi = mid;\n"
        "    }\n"
        "    return (lo < %d && s_dispatch_table[lo].addr == addr)\n"
        "         ? s_dispatch_table[lo].fn : NULL;\n"
        "}\n\n",
        all_funcs.count, all_funcs.count);

    /* Table accessors for interior-label detection in genesis_log_dispatch_miss */
    fprintf(f_dispatch, "int game_dispatch_table_size(void) { return %d; }\n", all_funcs.count);
    fprintf(f_dispatch,
        "uint32_t game_dispatch_table_addr(int i) {\n"
        "    return (i >= 0 && i < %d) ? s_dispatch_table[i].addr : 0;\n"
        "}\n\n", all_funcs.count);

    /* game_hook sites, sorted, so the tier-3 interpreter can run the same
     * genesis_game_instruction_hook() callbacks as the generated code. */
    {
        uint32_t *hooks = NULL;
        int nhooks = 0;
        for (int i = 0; i < s_ws_site_count; i++)
            if (s_ws_sites[i].kind == WS_SITE_GAME_HOOK) {
                hooks = (uint32_t *)realloc(hooks, (size_t)(nhooks + 1) * sizeof *hooks);
                hooks[nhooks++] = s_ws_sites[i].addr & 0xFFFFFFu;
            }
        for (int i = 1; i < nhooks; i++)
            for (int j = i; j > 0 && hooks[j - 1] > hooks[j]; j--) {
                uint32_t t = hooks[j]; hooks[j] = hooks[j - 1]; hooks[j - 1] = t;
            }
        fprintf(f_dispatch, "static const uint32_t s_game_hook_sites[] = {");
        for (int i = 0; i < nhooks; i++)
            fprintf(f_dispatch, "%s0x%06Xu", i ? ", " : " ", hooks[i]);
        fprintf(f_dispatch, "%s0u };\n", nhooks ? ", " : " ");
        fprintf(f_dispatch,
            "int game_instruction_hook_site(uint32_t pc) {\n"
            "    int lo = 0, hi = %d;\n"
            "    while (lo < hi) {\n"
            "        int mid = lo + (hi - lo) / 2;\n"
            "        if (s_game_hook_sites[mid] < pc) lo = mid + 1;\n"
            "        else hi = mid;\n"
            "    }\n"
            "    return lo < %d && s_game_hook_sites[lo] == pc;\n"
            "}\n\n", nhooks, nhooks);
        free(hooks);
    }

    fprintf(f_dispatch,
        "#ifdef GENESIS_HAS_NATIVE_CALL_FRAME\n"
        "typedef GenesisNativeCallFrame RecompTailFrame;\n"
        "GenesisNativeCallFrame *g_recomp_native_frame = NULL;\n"
        "#define g_recomp_tail_frame g_recomp_native_frame\n"
        "#define RECOMP_FRAME_INIT {0,0,g_recomp_tail_frame,NULL}\n"
        "#else\n"
        "typedef struct RecompTailFrame {\n"
        "    int pending;\n"
        "    uint32_t addr;\n"
        "    struct RecompTailFrame *prev;\n"
        "} RecompTailFrame;\n\n"
        "static RecompTailFrame *g_recomp_tail_frame = NULL;\n"
        "#define RECOMP_FRAME_INIT {0,0,g_recomp_tail_frame}\n"
        "#endif\n\n"
        "/* The frame list lives on the game fiber's stack and its head is\n"
        " * execution state: fiber snapshots carry it (get/set) and rollback\n"
        " * digests hash it address-free (walk, innermost frame first). */\n"
        "void *recomp_tail_frame_get(void) {\n"
        "    return g_recomp_tail_frame;\n"
        "}\n\n"
        "void recomp_tail_frame_set(void *frame) {\n"
        "    g_recomp_tail_frame = (RecompTailFrame *)frame;\n"
        "}\n\n"
        "void recomp_tail_frame_walk(void (*visit)(int pending, uint32_t addr, void *user),\n"
        "                            void *user) {\n"
        "    for (const RecompTailFrame *f = g_recomp_tail_frame; f; f = f->prev)\n"
        "        visit(f->pending, f->addr, user);\n"
        "}\n\n"
        "void recomp_tail_call(uint32_t addr) {\n"
        "    if (!g_recomp_tail_frame) {\n"
        "        fprintf(stderr, \"recompiled tail call without dispatch frame at $%%06X\\n\", addr & 0xFFFFFFu);\n"
        "        exit(2);\n"
        "    }\n"
        "    g_recomp_tail_frame->addr = addr & 0xFFFFFFu;\n"
        "#ifdef GENESIS_HAS_NATIVE_CALL_FRAME\n"
        "    g_recomp_tail_frame->function = NULL;\n"
        "#endif\n"
        "    g_recomp_tail_frame->pending = 1;\n"
        "}\n\n"
        "static void recomp_dispatch_once(uint32_t addr) {\n"
        "    addr = recomp_resolve_ram_trampoline(addr);\n"
        "    if (recomp_dispatch_ram_stub(addr))\n"
        "        return;\n"
        "    FuncPtr fn = recomp_find_func(addr);\n"
        "    if (fn) {\n"
        "        fn();\n"
        "        return;\n"
        "    }\n"
        "    if (!g_game_spec.dispatch_override || !g_game_spec.dispatch_override(addr))\n"
        "        genesis_log_dispatch_miss(addr);\n"
        "}\n\n"
        "static void recomp_drain_tailcalls(RecompTailFrame *frame) {\n"
        "    unsigned guard = 0;\n"
        "    uint64_t guard_frame = g_frame_count;\n"
        "    while (frame->pending) {\n"
        "        uint32_t addr = frame->addr;\n"
        "        frame->pending = 0;\n"
        "#ifdef GENESIS_HAS_NATIVE_CALL_FRAME\n"
        "        RecompFuncPtr native = frame->function; frame->function = NULL;\n"
        "        if (native) native(); else recomp_dispatch_once(addr);\n"
        "#else\n"
        "        recomp_dispatch_once(addr);\n"
        "#endif\n"
        "        if (g_rte_pending)\n"
        "            break;\n"
        "        /* Native pause loops can span many yielded wall frames.\n"
        "         * Bound transfers without frame progress, not their lifetime. */\n"
        "        if (guard_frame != g_frame_count) {\n"
        "            guard_frame = g_frame_count; guard = 0;\n"
        "        }\n"
        "        if (++guard > 1000000u) {\n"
        "            fprintf(stderr, \"recompiled tail-dispatch runaway at $%%06X\\n\", addr);\n"
        "            exit(2);\n"
        "        }\n"
        "    }\n"
        "}\n\n"
        "#ifdef GENESIS_HAS_NATIVE_CALL_FRAME\n"
        "void recomp_native_drain(GenesisNativeCallFrame *frame) {\n"
        "    recomp_drain_tailcalls(frame);\n"
        "}\n"
        "#endif\n\n"
        "void recomp_call_func(RecompFuncPtr fn) {\n"
        "    if (!fn)\n"
        "        return;\n"
        "    RecompTailFrame frame = RECOMP_FRAME_INIT;\n"
        "    g_recomp_tail_frame = &frame;\n"
        "    fn();\n"
        "    recomp_drain_tailcalls(&frame);\n"
        "    g_recomp_tail_frame = frame.prev;\n"
        "}\n\n"
        "void recomp_call_addr(uint32_t addr) {\n"
        "    RecompTailFrame frame = RECOMP_FRAME_INIT;\n"
        "    g_recomp_tail_frame = &frame;\n"
        "    recomp_tail_call(addr);\n"
        "    recomp_drain_tailcalls(&frame);\n"
        "    g_recomp_tail_frame = frame.prev;\n"
        "}\n\n"
        "void call_by_address(uint32_t addr) {\n"
        "    recomp_call_addr(addr);\n"
        "}\n");

    /* JMP-table dispatch audit. Derive the audit path from the dispatch
     * path by swapping `_dispatch.c` -> `_dispatch_audit.log`. Skip the
     * write silently if the path doesn't follow that convention; the audit
     * is diagnostic, not load-bearing. */
    {
        char audit_path[512];
        size_t dl = strlen(out_dispatch_path);
        const char *suffix = "_dispatch.c";
        size_t sl = strlen(suffix);
        if (dl > sl && strcmp(out_dispatch_path + dl - sl, suffix) == 0) {
            snprintf(audit_path, sizeof(audit_path),
                     "%.*s_dispatch_audit.log",
                     (int)(dl - sl), out_dispatch_path);
        } else {
            snprintf(audit_path, sizeof(audit_path), "%s.audit.log", out_dispatch_path);
        }

        /* Subcategorize FALLBACK_HYBRID entries by what's at `base`:
         *   function_entry:      base IS a registered function entry
         *   bra_w_trampoline:    opcode at base is 0x6000 (bra.w) — runtime
         *                        miss becomes a [functions].extra lead
         *   offset_table:        base is the start of a `dc.w (target - base)`
         *                        table — at least 3 of the first 4 entries
         *                        decode to a registered function entry. This
         *                        is the standard Sonic `move.w table(pc,d.w),d
         *                        / jmp table(pc,d.w)` dispatch. Works at
         *                        runtime via call_by_address(base + offset).
         *   interior_unresolved: none of the above and base is interior to a
         *                        function — DANGER ZONE, the pre-fix CPZ class.
         *   external_unresolved: base outside any known function. */
        #define AUDIT_CLASSIFY_HYBRID(BASE, OUT_KIND) do {                       \
            uint32_t _b = (BASE);                                                \
            if (addrset_contains(&all_funcs, _b)) {                              \
                (OUT_KIND) = "function_entry";                                   \
            } else {                                                             \
                uint16_t _op = (rom && _b + 1 < rom->rom_size)                   \
                               ? ((uint16_t)rom->rom_data[_b] << 8) | rom->rom_data[_b + 1] \
                               : 0;                                              \
                if (_op == 0x6000u) {                                            \
                    (OUT_KIND) = "bra_w_trampoline";                             \
                } else {                                                         \
                    /* Offset-table probe: walk up to 16 words and count hits.
                     * A Duff's-device-style table (the real danger) has every
                     * entry being a code-as-offset garbage value; none resolve.
                     * A real `dc.w (target - base)` table has at least one
                     * entry resolving to a registered function. Threshold:
                     * 1+ unique resolved targets among the first 8 words
                     * classifies as offset_table (call_by_address resolves
                     * each at runtime); zero resolved is INTERIOR_UNRESOLVED.
                     * The risk of a false-safe (1-entry coincidence where
                     * a non-dispatch JMP happens to read a word that points
                     * to a real function) is real but small in practice —
                     * Sonic 1's SStom_Move is the smoking-gun safe case. */     \
                    int _hits = 0;                                               \
                    uint32_t _seen[8] = {0};                                     \
                    int _seen_n = 0;                                             \
                    for (int _w = 0; _w < 8; _w++) {                             \
                        uint32_t _a = _b + (uint32_t)_w * 2u;                    \
                        if (_a + 1 >= rom->rom_size) break;                      \
                        int16_t _off = (int16_t)(((uint16_t)rom->rom_data[_a] << 8) \
                                                | rom->rom_data[_a + 1]);        \
                        uint32_t _t = (uint32_t)((int32_t)_b + (int32_t)_off);   \
                        if (addrset_contains(&all_funcs, _t)) {                  \
                            int _dup = 0;                                        \
                            for (int _s = 0; _s < _seen_n; _s++)                 \
                                if (_seen[_s] == _t) { _dup = 1; break; }        \
                            if (!_dup) {                                         \
                                _seen[_seen_n++] = _t;                           \
                                _hits++;                                         \
                            }                                                    \
                        }                                                        \
                    }                                                            \
                    if (_hits >= 1) {                                            \
                        (OUT_KIND) = "offset_table";                             \
                    } else {                                                     \
                        uint32_t _own = 0;                                       \
                        for (int _k = 0; _k < all_funcs.count; _k++) {           \
                            uint32_t _fa = all_funcs.addrs[_k];                  \
                            if (_fa <= _b && _fa > _own) _own = _fa;             \
                        }                                                        \
                        (OUT_KIND) = (_own != 0 && _own != _b)                   \
                                     ? "INTERIOR_UNRESOLVED"                     \
                                     : "external_unresolved";                    \
                    }                                                            \
                }                                                                \
            }                                                                    \
        } while (0)

        int n_static = 0, n_switch = 0, n_dyn_reg = 0, n_unsupp = 0;
        int n_fb_func = 0, n_fb_bra = 0, n_fb_off = 0,
            n_fb_interior = 0, n_fb_external = 0;
        for (int i = 0; i < s_jmp_audit_count; i++) {
            switch (s_jmp_audit_arr[i].kind) {
                case JMPAUDIT_STATIC_TARGET:        n_static++; break;
                case JMPAUDIT_IN_FUNCTION_SWITCH:   n_switch++; break;
                case JMPAUDIT_DYNAMIC_REGISTER:     n_dyn_reg++; break;
                case JMPAUDIT_UNSUPPORTED:          n_unsupp++; break;
                case JMPAUDIT_FALLBACK_HYBRID: {
                    const char *sub = "?";
                    AUDIT_CLASSIFY_HYBRID(s_jmp_audit_arr[i].base, sub);
                    if      (strcmp(sub, "function_entry") == 0)      n_fb_func++;
                    else if (strcmp(sub, "bra_w_trampoline") == 0)    n_fb_bra++;
                    else if (strcmp(sub, "offset_table") == 0)        n_fb_off++;
                    else if (strcmp(sub, "INTERIOR_UNRESOLVED") == 0) n_fb_interior++;
                    else                                              n_fb_external++;
                    break;
                }
            }
        }

        FILE *fa = m68k_fopen(audit_path, "w");
        if (fa) {
            fprintf(fa, "# JMP-table dispatch audit\n");
            fprintf(fa, "# total sites: %d\n", s_jmp_audit_count);
            fprintf(fa, "#\n");
            fprintf(fa, "# Summary:\n");
            fprintf(fa, "#   static_target          %5d  (JMP with statically resolved target — safe)\n", n_static);
            fprintf(fa, "#   in_function_switch     %5d  (JMP(PC,Dn.W) compiled to in-function switch+goto — safe, this is the Duff's-device fix)\n", n_switch);
            fprintf(fa, "#   dynamic_register       %5d  (JMP (An)/(d,An)/(An,Xn) — runtime address from register, safe via call_by_address)\n", n_dyn_reg);
            fprintf(fa, "#   fallback_hybrid                — JMP(PC,Dn.W) routed through hybrid_jmp_interpret; subdivided:\n");
            fprintf(fa, "#     function_entry       %5d    (base IS a registered function — call_by_address resolves it directly)\n", n_fb_func);
            fprintf(fa, "#     bra_w_trampoline     %5d    (base opcode = 0x6000; runtime miss feedback works)\n", n_fb_bra);
            fprintf(fa, "#     offset_table         %5d    (base is a dc.w (target-base) table; 1+ entries decode to functions — runtime resolves it)\n", n_fb_off);
            fprintf(fa, "#     INTERIOR_UNRESOLVED  %5d    (DANGER: base is interior to a function, NOT one of the safe patterns above — silent failure class like pre-fix CPZ)\n", n_fb_interior);
            fprintf(fa, "#     external_unresolved  %5d    (base outside any known function — investigate)\n", n_fb_external);
            fprintf(fa, "#   unsupported            %5d  (decoder hit a JMP mode the emitter doesn't handle)\n", n_unsupp);
            fprintf(fa, "#\n");
            fprintf(fa, "# When `interior_unresolved` is non-zero, inspect each site — these are\n");
            fprintf(fa, "# Sonic-2-CPZ-style silent-failure candidates. Either the recompiler's\n");
            fprintf(fa, "# Duff's-device probe (probe_pc_idx_targets) didn't match, or the table\n");
            fprintf(fa, "# really is a new pattern that needs new codegen support.\n");
            fprintf(fa, "#\n");
            fprintf(fa, "# Format: <jmp_addr>  in func <func>  base <base>  kind=<kind>[ targets=N]\n\n");

            for (int i = 0; i < s_jmp_audit_count; i++) {
                JmpAuditEntry *e = &s_jmp_audit_arr[i];
                const char *kind = "?";
                char sub[40] = {0};
                switch (e->kind) {
                    case JMPAUDIT_STATIC_TARGET:      kind = "static_target"; break;
                    case JMPAUDIT_IN_FUNCTION_SWITCH: kind = "in_function_switch";
                        snprintf(sub, sizeof(sub), " targets=%d", e->n_targets); break;
                    case JMPAUDIT_DYNAMIC_REGISTER:   kind = "dynamic_register"; break;
                    case JMPAUDIT_UNSUPPORTED:        kind = "unsupported"; break;
                    case JMPAUDIT_FALLBACK_HYBRID: {
                        const char *cl = "?";
                        AUDIT_CLASSIFY_HYBRID(e->base, cl);
                        static char kbuf[64];
                        snprintf(kbuf, sizeof(kbuf), "fallback_hybrid/%s", cl);
                        kind = kbuf;
                        break;
                    }
                }
                fprintf(fa, "$%06X  in func $%06X  base $%06X  kind=%s%s\n",
                        e->jmp_addr, e->func_addr, e->base, kind, sub);
            }
            fclose(fa);
            printf("[Codegen] Dispatch audit: %d sites (%d static, %d switch, %d hybrid {fn=%d, bra.w=%d, offset_table=%d, interior=%d, ext=%d}, %d dyn_reg, %d unsupp)\n",
                   s_jmp_audit_count, n_static, n_switch,
                   n_fb_func + n_fb_bra + n_fb_off + n_fb_interior + n_fb_external,
                   n_fb_func, n_fb_bra, n_fb_off, n_fb_interior, n_fb_external,
                   n_dyn_reg, n_unsupp);
            if (n_fb_interior > 0)
                printf("[Codegen] WARNING: %d interior_unresolved JMP-table sites — see %s\n",
                       n_fb_interior, audit_path);
        }
    }

    free(entry_owners);
    free(s_candidate_owners);
    s_candidate_owners = NULL;
    s_candidate_owner_count = 0;
    addrset_free(&hard_boundaries);
    addrset_free(&all_funcs);
    /* f_header and every f_parts[k] were already closed once their content
     * was fully known (forward decls / balanced function bodies respectively);
     * only the dispatch TU is still open at this point. */
    fclose(f_dispatch);
    return true;
}
