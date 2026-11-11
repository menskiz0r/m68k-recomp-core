/* Minimal consumer-owned ROM interface for synthetic frontend tests. */
#pragma once
#include <stdint.h>

typedef struct {
    const uint8_t *rom_data;
    uint32_t rom_size;
} GenesisRom;

uint16_t rom_read16(const GenesisRom *rom, uint32_t addr);
uint32_t rom_read32(const GenesisRom *rom, uint32_t addr);
