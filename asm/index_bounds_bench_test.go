package asm

import "testing"

// An access in the first 256-element slice after stores in later slices of
// the same root. Offsets alone do not prove anything about the masked indices
// to the linear congruence shortcut.
func BenchmarkMemoryAtBoundedRegions(b *testing.B) {
	index := binaryTerm("and", paramTerm("read", 32), constTerm(255, 32))
	log := make([]*spanWrite, 128)
	for i := range log {
		at := binaryTerm("add", constTerm(uint64((i+1)*256), 32), binaryTerm("and", paramTerm("write", 32), constTerm(255, 32)))
		log[i] = &spanWrite{index: at, value: constTerm(uint64(i+1), 32)}
	}
	initial := paramTerm("initial", 32)
	b.ReportAllocs()
	for b.Loop() {
		if memoryAt(log, index, initial) != initial {
			b.Fatal("disjoint writes remained in the read")
		}
	}
}

func BenchmarkMemoryAtCommonBaseBoundedRegions(b *testing.B) {
	base := paramTerm("base", 32)
	index := binaryTerm("add", base, binaryTerm("and", paramTerm("read", 32), constTerm(255, 32)))
	log := make([]*spanWrite, 128)
	for i := range log {
		offset := binaryTerm("add", constTerm(uint64((i+1)*256), 32), binaryTerm("and", paramTerm("write", 32), constTerm(255, 32)))
		log[i] = &spanWrite{index: binaryTerm("add", base, offset), value: constTerm(uint64(i+1), 32)}
	}
	initial := paramTerm("initial", 32)
	b.ReportAllocs()
	for b.Loop() {
		memoryAt(log, index, initial)
	}
}
