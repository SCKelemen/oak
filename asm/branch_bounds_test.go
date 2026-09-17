package asm

import "testing"

func boundInstructions(t *testing.T, source string) []Instruction {
	t.Helper()
	unit, errs := ParseUnit("bounds.oakasm", "bounds: () -> u64 = {\n"+source+"\n}\n")
	if len(errs) != 0 {
		t.Fatal(errs)
	}
	var instructions []Instruction
	for _, item := range unit.Functions[0].Items {
		if instr, ok := item.(Instruction); ok {
			instructions = append(instructions, instr)
		}
	}
	return instructions
}

func TestBranchIndexBound(t *testing.T) {
	for _, tc := range []struct {
		name, setup, cond string
		wide              bool
		bound             uint64
		known, taken      bool
	}{
		{"below fallthrough", "cmp w9, #16", "hs", false, 16, true, false},
		{"below taken", "cmp w9, #16", "lo", false, 16, true, true},
		{"carry alias", "cmp w9, #16", "cc", false, 16, true, true},
		{"carry set alias", "cmp w9, #16", "cs", false, 16, true, false},
		{"inclusive fallthrough", "cmp w9, #15", "hi", false, 16, true, false},
		{"inclusive taken", "cmp w9, #15", "ls", false, 16, true, true},
		{"opposite hs", "cmp w9, #16", "hs", false, 0, false, true},
		{"opposite lo", "cmp w9, #16", "lo", false, 0, false, false},
		{"opposite hi", "cmp w9, #15", "hi", false, 0, false, true},
		{"opposite ls", "cmp w9, #15", "ls", false, 0, false, false},
		{"signed", "cmp w9, #16", "lt", false, 0, false, true},
		{"empty side", "cmp w9, #0", "lo", false, 0, true, true},
		{"wide", "cmp x9, #16", "lo", true, 16, true, true},
		{"upper half unknown", "cmp w9, #16", "lo", true, 0, false, true},
		{"stale index", "cmp w9, #16\nmov w9, #31", "lo", false, 0, false, true},
		{"unchanged value", "cmp w9, #16\nmov w9, w9", "lo", false, 16, true, true},
		{"new flags", "cmp w9, #16\ntst w9, #1", "lo", false, 0, false, true},
		{"conditional compare", "cmp w9, #16\nccmp w9, #8, #0, lo", "lo", false, 0, false, true},
		{"tightest bound", "cmp w9, #32", "lo", false, 8, true, true},
	} {
		t.Run(tc.name, func(t *testing.T) {
			value := paramTerm("index", 64)
			if !tc.wide {
				value = zeroExtend(paramTerm("index", 32), 64)
			}
			s := &symbolicState{arch: ArchArm64, regs: map[int]*term{9: value}}
			if tc.name == "tightest bound" {
				s.bounds = map[int]uint64{9: 8}
			}
			for _, instr := range boundInstructions(t, tc.setup) {
				if reason, ok := step(instr, s); !ok {
					t.Fatal(reason)
				}
			}
			s.noteBranchIndexBound(Instruction{Mnemonic: "b.", Cond: tc.cond}, tc.taken)
			if bound, known := s.bounds[9]; known != tc.known || known && bound != tc.bound {
				t.Fatalf("bound (%d, %v), want (%d, %v)", bound, known, tc.bound, tc.known)
			}
		})
	}
}

func TestBranchIndexBoundOverflow(t *testing.T) {
	// Test the boundary terms directly: the encoder does not admit these
	// constants in a single cmp immediate. The fact must still never wrap.
	for _, width := range []int{32, 64} {
		index := paramTerm("index", width)
		s := &symbolicState{
			regs:  map[int]*term{9: zeroExtend(index, 64)},
			flags: &flagsFact{left: index, right: constTerm(^uint64(0), width), width: width, indexReg: 9},
		}
		s.noteBranchIndexBound(Instruction{Mnemonic: "b.", Cond: "ls"}, true)
		bound, known := s.bounds[9]
		if width == 64 && known || width == 32 && (!known || bound != uint64(1)<<32) {
			t.Fatalf("width %d: bound (%d, %v)", width, bound, known)
		}
	}
}

func TestRV64BranchIndexBound(t *testing.T) {
	for _, mnemonic := range []string{"bgeu", "bltu"} {
		index := paramTerm("index", 64)
		s := &symbolicState{arch: ArchRV64, regs: map[int]*term{10: index, 11: constTerm(16, 64)}}
		instr := Instruction{Mnemonic: mnemonic, Operands: []Operand{
			Register{Class: ClassRV64X, Num: 10}, Register{Class: ClassRV64X, Num: 11}, Symbol{Name: "done"},
		}}
		taken, fall := s.clone(), s.clone()
		noteBranchBound(instr, taken, fall)
		bounded, other := fall, taken
		if mnemonic == "bltu" {
			bounded, other = taken, fall
		}
		if bounded.bounds[10] != 16 || bounded.termBounds[index] != 16 || len(other.bounds) != 0 || len(other.termBounds) != 0 || len(s.bounds) != 0 {
			t.Fatalf("%s: the bound must be private to the below side", mnemonic)
		}
		bounded.write(Register{Class: ClassRV64X, Num: 10}, binaryTerm("shl", index, constTerm(2, 64)))
		if len(bounded.bounds) != 0 || bounded.termBounds[index] != 16 {
			t.Fatalf("%s: scaling must clear the register fact and retain the original value's fact", mnemonic)
		}
	}
}
