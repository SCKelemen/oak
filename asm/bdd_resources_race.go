//go:build race

package asm

// Conservative scheduling estimate, not a hard bound on race-detector RSS.
const bddRaceMemoryFactor = 3
