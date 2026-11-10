/*
 * return_capture.c — bounded all-path proof for return-address consumers.
 */
#include "return_capture.h"

#include "m68k_decoder.h"

#define RETURN_CAPTURE_MAX_NODES 96

typedef enum {
    PROOF_VISITING,
    PROOF_TRUE,
    PROOF_FALSE,
} ProofState;

typedef struct {
    uint32_t pc;
    ProofState state;
} ProofNode;

typedef struct {
    const GenesisRom *rom;
    ProofNode nodes[RETURN_CAPTURE_MAX_NODES];
    int node_count;
} ProofContext;

static bool is_return_pop(const M68KInstr *ins)
{
    if (ins->size != M68K_SIZE_L
            || ins->src_ea != ((EA_An_POST << 3) | 7))
        return false;

    if (ins->mnemonic == MN_MOVE || ins->mnemonic == MN_MOVEA)
        return true;

    /*
     * MOVEM.L (A7)+,<regs> consumes the return slot just as surely as
     * MOVE.L (A7)+,<reg>.  Puyo's collision helper uses the one-register
     * form (`movem.l (sp)+,d0`) on only one branch, so recognizing the
     * instruction here is also important for correctly rejecting the whole
     * helper as merely conditional.
     */
    return ins->mnemonic == MN_MOVEM
        && ((ins->words[0] >> 10) & 1) != 0
        && ins->words[1] != 0;
}

static bool invalid_before_return_pop(const M68KInstr *ins)
{
    /*
     * Once a routine grows the stack, a later (A7)+ may merely rebalance its
     * own frame. Calls and MOVEM have the same ambiguity, so do not prove
     * through them.
     */
    return ins->dst_ea == ((EA_An_PRE << 3) | 7) /* -(A7) destination */
        || ins->mnemonic == MN_PEA
        || ins->mnemonic == MN_LINK
        || ins->mnemonic == MN_MOVEM
        || m68k_is_call(ins);
}

/*
 * A routine that pops the caller's return address is only a "capture and take
 * over" callee when it keeps that address and never rebuilds a normal frame.
 * A prologue/epilogue split looks identical at the capture instruction:
 *
 *     movea.l (a7)+,a0        ; capture
 *     link.w  a6,#0           ; ...but build an ordinary frame anyway
 *     movem.l d1/a1,-(a7)
 *     move.w  sr,-(a7)
 *     move.l  a0,-(a7)        ; and push the address straight back
 *     ...
 *     rts                     ; ordinary return, frame still live
 *
 * The shared epilogue later pops sr/movem/unlk and returns to the caller, so the
 * caller's own body must still be emitted. Treating that as a capture made the
 * caller emit `push return; call; return;` and drop everything after the call
 * (Shadowrun $052E4E is the reproducer; its six callers at $052EB0..$052FA0 were
 * truncated, leaking the pushed return slot). Reject any routine that, right
 * after capturing, sets up a frame or pushes to the stack again.
 */
static bool capture_is_takeover(const ProofContext *ctx, uint32_t pc)
{
    for (int i = 0; i < 8; i++) {
        M68KInstr ins;
        if (pc + 1 >= ctx->rom->rom_size || !m68k_decode(ctx->rom, pc, &ins))
            return false;
        if (ins.mnemonic == MN_LINK)
            return false;                            /* normal frame set up   */
        if (ins.dst_ea == ((EA_An_PRE << 3) | 7))
            return false;                            /* pushes again          */
        if (ins.mnemonic == MN_RTS)
            return false;                            /* ordinary return       */
        if (m68k_is_terminator(&ins) || ins.mnemonic == MN_JMP
                || ins.mnemonic == MN_BRA || ins.mnemonic == MN_Bcc
                || ins.mnemonic == MN_DBcc)
            return true;                             /* leaves this path      */
        pc += ins.byte_length;
    }
    return true;
}

static bool prove_from(ProofContext *ctx, uint32_t pc)
{
    int node_index = -1;
    for (int i = 0; i < ctx->node_count; i++) {
        if (ctx->nodes[i].pc != pc)
            continue;
        if (ctx->nodes[i].state == PROOF_TRUE)
            return true;
        if (ctx->nodes[i].state == PROOF_FALSE)
            return false;
        /*
         * A path that cycles before consuming the return address is not
         * proven. Reject it conservatively instead of treating "visited" as
         * success.
         */
        return false;
    }

    if (ctx->node_count >= RETURN_CAPTURE_MAX_NODES
            || pc + 1 >= ctx->rom->rom_size)
        return false;

    node_index = ctx->node_count++;
    ctx->nodes[node_index].pc = pc;
    ctx->nodes[node_index].state = PROOF_VISITING;

    M68KInstr ins;
    bool result = false;
    if (!m68k_decode(ctx->rom, pc, &ins))
        goto done;

    if (is_return_pop(&ins)) {
        result = capture_is_takeover(ctx, pc + ins.byte_length);
        goto done;
    }
    if (invalid_before_return_pop(&ins))
        goto done;

    uint32_t fallthrough = pc + ins.byte_length;
    switch (ins.mnemonic) {
    case MN_Bcc:
    case MN_DBcc:
        if (ins.has_target)
            result = prove_from(ctx, ins.target_addr)
                  && prove_from(ctx, fallthrough);
        break;
    case MN_BRA:
        if (ins.has_target)
            result = prove_from(ctx, ins.target_addr);
        break;
    default:
        if (!m68k_is_terminator(&ins))
            result = prove_from(ctx, fallthrough);
        break;
    }

done:
    ctx->nodes[node_index].state = result ? PROOF_TRUE : PROOF_FALSE;
    return result;
}

bool m68k_return_capture_is_unconditional(const GenesisRom *rom, uint32_t start)
{
    if (!rom)
        return false;
    ProofContext ctx = {0};
    ctx.rom = rom;
    return prove_from(&ctx, start);
}
