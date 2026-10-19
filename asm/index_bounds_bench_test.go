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

func BenchmarkMemoryAtCommonBaseScaledRegions(b *testing.B) {
	base := paramTerm("base", 32)
	read := binaryTerm("shl", binaryTerm("and", paramTerm("read", 32), constTerm(63, 32)), constTerm(2, 32))
	index := binaryTerm("add", base, read)
	log := make([]*spanWrite, 128)
	for i := range log {
		scaled := binaryTerm("mul", constTerm(4, 32), binaryTerm("and", paramTerm("write", 32), constTerm(63, 32)))
		offset := binaryTerm("add", constTerm(uint64((i+1)*256), 32), scaled)
		log[i] = &spanWrite{index: binaryTerm("add", base, offset), value: constTerm(uint64(i+1), 32)}
	}
	initial := paramTerm("initial", 32)
	b.ReportAllocs()
	for b.Loop() {
		if memoryAt(log, index, initial) != initial {
			b.Fatal("disjoint scaled writes remained in the read")
		}
	}
}

// The benchmarks above reuse their term graph between analyses. These
// variants include fresh terms on every pass, so comparisons also measure
// cold analysis rather than only the benefit of a previously warmed graph.
func BenchmarkMemoryAtColdBoundedRegions(b *testing.B) {
	benchmarkMemoryAtColdBoundedRegions(b, false)
}

func BenchmarkMemoryAtColdCommonBaseBoundedRegions(b *testing.B) {
	benchmarkMemoryAtColdBoundedRegions(b, true)
}

func benchmarkMemoryAtColdBoundedRegions(b *testing.B, commonBase bool) {
	b.ReportAllocs()
	for b.Loop() {
		base := paramTerm("base", 32)
		index := binaryTerm("and", paramTerm("read", 32), constTerm(255, 32))
		if commonBase {
			index = binaryTerm("add", base, index)
		}
		log := make([]*spanWrite, 128)
		for i := range log {
			at := binaryTerm("add", constTerm(uint64((i+1)*256), 32), binaryTerm("and", paramTerm("write", 32), constTerm(255, 32)))
			if commonBase {
				at = binaryTerm("add", base, at)
			}
			log[i] = &spanWrite{index: at, value: constTerm(uint64(i+1), 32)}
		}
		initial := paramTerm("initial", 32)
		if memoryAt(log, index, initial) != initial {
			b.Fatal("disjoint writes remained in the read")
		}
	}
}
