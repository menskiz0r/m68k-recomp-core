/* Synthetic instructions only: no game ROM or external consumer required. */
#include <stdio.h>
#include <string.h>

#include "return_capture.h"

static unsigned failures;
static unsigned checks;

uint16_t rom_read16(const GenesisRom *rom, uint32_t addr)
{
    if (addr >= rom->rom_size || rom->rom_size - addr < 2)
        return 0;
    return (uint16_t)(((uint16_t)rom->rom_data[addr] << 8)
                    | rom->rom_data[addr + 1]);
}

uint32_t rom_read32(const GenesisRom *rom, uint32_t addr)
{
    return ((uint32_t)rom_read16(rom, addr) << 16) | rom_read16(rom, addr + 2);
}

static void check(const char *name, const GenesisRom *rom, uint32_t start,
                  bool expected)
{
    bool actual = m68k_return_capture_is_unconditional(rom, start);
    checks++;
    if (actual != expected) {
        fprintf(stderr, "FAIL %s: expected %s, got %s\n", name,
                expected ? "proven" : "unproven", actual ? "proven" : "unproven");
        failures++;
    }
}

static void check_words(const char *name, const uint16_t *words, size_t count,
                        bool expected)
{
    uint8_t bytes[512];
    if (count > sizeof(bytes) / 2) {
        fprintf(stderr, "fixture too large: %s\n", name);
        failures++;
        return;
    }
    for (size_t i = 0; i < count; i++) {
        bytes[i * 2] = (uint8_t)(words[i] >> 8);
        bytes[i * 2 + 1] = (uint8_t)words[i];
    }
    GenesisRom rom = {bytes, (uint32_t)(count * 2)};
    check(name, &rom, 0, expected);
}

#define CASE(name, expected, ...) do { \
    const uint16_t words[] = {__VA_ARGS__}; \
    check_words(name, words, sizeof(words) / sizeof(words[0]), expected); \
} while (0)

int main(void)
{
    /* Genuine captures leave the slot consumed: the RTS skips the caller. */
    CASE("store return address then RTS", true,
         0x3140, 0x0024, 0x215F, 0x0002, 0x4E75);
    CASE("register capture then RTS", true, 0x205F, 0x4E75);
    CASE("MOVEM capture then RTS", true, 0x4CDF, 0x0001, 0x4E75);
    CASE("distinct captures on every conditional path", true,
         0x4A68, 0x0024, 0x6700, 0x000E, 0x5368, 0x0024, 0x6700, 0x0006,
         0x201F, 0x4E75, 0x215F, 0x0002, 0x4E75);
    CASE("ordinary return on one path", false,
         0x4A40, 0x6702, 0x4E75, 0x201F, 0x4E75);
    CASE("MOVEM capture on only one path", false,
         0x0800, 0x0000, 0x6602, 0x4E75, 0x4CDF, 0x0001, 0x4E75);

    /* Split prologue/epilogue: the first RTS returns normally into the caller
     * with a live frame. Its continuation must not be omitted by codegen. */
    CASE("split prologue and epilogue", false,
         0x205F, 0x4E56, 0x0000, 0x48E7, 0x4040, 0x40E7, 0x2F08, 0x4E75,
         0x46DF, 0x4CDF, 0x0202, 0x4E5E, 0x4E75);
    CASE("push captured slot straight back", false, 0x205F, 0x2F08, 0x4E75);
    CASE("same-instruction pop and push", false, 0x2F1F, 0x4E75);
    CASE("capture writes SP itself", false, 0x2E5F, 0x4E75);
    CASE("frame precedes apparent pop", false, 0x4E56, 0x0000, 0x201F, 0x4E75);
    CASE("call precedes apparent pop", false, 0x6102, 0x201F, 0x4E75);
    CASE("call after capture", false, 0x205F, 0x6102, 0x4E75, 0x4E75);
    CASE("PEA after capture", false, 0x205F, 0x4850, 0x4E75);
    CASE("MOVEM push after capture", false, 0x205F, 0x48E7, 0x4040, 0x4E75);
    CASE("UNLK after capture", false, 0x205F, 0x4E5E, 0x4E75);
    CASE("LEA resets SP after capture", false, 0x205F, 0x4FEF, 0xFFFC, 0x4E75);
    CASE("ADDA resets SP after capture", false, 0x205F, 0xDFFC, 0xFFFF, 0xFFFC, 0x4E75);
    CASE("SUBQ restores return slot", false, 0x205F, 0x598F, 0x2E88, 0x4E75);
    CASE("EXG resets SP after capture", false, 0x205F, 0xCF48, 0x4E75);
    CASE("MOVEM loads SP", false, 0x4CDF, 0x8001, 0x4E75);

    /* A branch is not evidence of takeover: inspect both reachable paths. */
    CASE("BRA reaches frame rebuild", false,
         0x205F, 0x6002, 0x4E71, 0x4E56, 0x0000, 0x4E75);
    CASE("conditional frame rebuild", false,
         0x205F, 0x6602, 0x4E75, 0x4E56, 0x0000, 0x4E75);
    CASE("conditional ordinary RTS after capture", true,
         0x205F, 0x6602, 0x4E75, 0x4E75);
    CASE("DBcc reaches frame rebuild", false,
         0x205F, 0x51C8, 0x0004, 0x4E75, 0x4E56, 0x0000, 0x4E75);
    CASE("DBcc paths both return after capture", true,
         0x205F, 0x51C8, 0x0004, 0x4E75, 0x4E75);
    CASE("shared RTS reached with and without capture", false,
         0x6602, 0x6002, 0x201F, 0x4E75);
    CASE("direct jump reaches RTS", true, 0x205F, 0x4EF8, 0x0006, 0x4E75);
    CASE("direct jump reaches frame rebuild", false,
         0x205F, 0x4EF8, 0x0006, 0x4E56, 0x0000, 0x4E75);
    CASE("indirect jump has unknown target", false, 0x205F, 0x4ED0);
    CASE("cycle before capture", false, 0x60FE);
    CASE("cycle after capture", false, 0x205F, 0x60FE);
    CASE("branch outside image", false, 0x205F, 0x6020);
    CASE("branch to odd address", false, 0x205F, 0x6001, 0x4E75);

    /* Neither the old eight-instruction lookahead nor the total proof budget
     * may turn an unexamined path into success. Boundary cases also ensure
     * the proof does not simply disable longer genuine capture routines. */
    uint16_t delayed[98];
    delayed[0] = 0x205F;
    for (size_t i = 1; i < 98; i++) delayed[i] = 0x4E71;
    delayed[10] = 0x2F08;
    delayed[11] = 0x4E75;
    check_words("restore beyond eight-instruction lookahead", delayed, 12, false);
    delayed[10] = delayed[11] = 0x4E71;
    delayed[95] = 0x4E75;
    check_words("genuine return at node budget", delayed, 96, true);
    delayed[95] = 0x4E71;
    delayed[96] = 0x4E75;
    check_words("genuine return beyond node budget is unproven", delayed, 97, false);
    delayed[96] = 0x2F08;
    delayed[97] = 0x4E75;
    check_words("restoration beyond node budget is unproven", delayed, 98, false);

    CASE("truncated capture destination extension", false, 0x215F);
    CASE("truncated branch extension", false, 0x205F, 0x6000);
    CASE("truncated LINK extension", false, 0x205F, 0x4E56);
    CASE("illegal instruction after capture", false, 0x205F, 0x4AFC);
    CASE("RTE after capture", false, 0x205F, 0x4E73);
    CASE("RTR after capture", false, 0x205F, 0x4E77);
    CASE("STOP after capture", false, 0x205F, 0x4E72, 0x2700);
    CASE("TRAP after capture", false, 0x205F, 0x4E40, 0x4E75);
    uint8_t bytes[] = {0x20, 0x5F, 0x4E, 0x75};
    GenesisRom rom = {bytes, sizeof(bytes)};
    check("odd entry", &rom, 1, false);
    check("entry at end", &rom, sizeof(bytes), false);
    check("overflowing entry", &rom, UINT32_MAX, false);
    rom.rom_size = 3;
    check("truncated final opcode", &rom, 0, false);
    check("null image", NULL, 0, false);

    printf("return_capture_test: %u checks, %u failures\n", checks, failures);
    return failures ? 1 : 0;
}
