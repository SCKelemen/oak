package asm

import (
	"testing"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/layout"
	"github.com/SCKelemen/oak/parser"
	"github.com/SCKelemen/oak/scanner"
)

// An argument bound must not constrain a returned value in the same
// physical register. Register-returning calls have separate invalidation
// paths from memory/unit/float returns, so exercise the actual summaries.
func TestCallClearsRegisterBounds(t *testing.T) {
	p := parser.New(layout.New(scanner.New(`Pair: type = struct { a: u64, b: u64 }
scalar: () -> u64 = u64(31)
pair: () -> Pair = Pair { a: u64(31), b: u64(32) }
vector: () -> simd.U8x16 = simd.splat_u8x16(u8(31))
`)))
	program := p.ParseProgram()
	if errs := p.Errors(); len(errs) != 0 {
		t.Fatal(errs)
	}
	callees := map[string]*ast.FunctionStatement{}
	records := map[string]*ast.RecordLiteral{}
	for _, stmt := range program.Statements {
		switch d := stmt.(type) {
		case *ast.FunctionStatement:
			callees[d.Name.Value] = d
		case *ast.ADTType:
			records[d.Name.Value] = d.Variants[0].Literal.(*ast.RecordLiteral)
		}
	}
	for _, arch := range []string{ArchArm64, ArchRV64} {
		for _, kind := range []string{"discard", "scalar", "pair", "vector"} {
			t.Run(arch+"/"+kind, func(t *testing.T) {
				registers, preserved, result, mnemonic := []int{0, 1, 9, 17, 19, 30}, 19, 0, "bl"
				if arch == ArchRV64 {
					registers, preserved, result, mnemonic = []int{1, 5, 8, 10, 11, 17, 28}, 8, 10, "call"
				}
				s := &symbolicState{arch: arch, regs: map[int]*term{}, bounds: map[int]uint64{}, notes: &pathNotes{}}
				for _, reg := range registers {
					s.regs[reg] = constTerm(0, 64)
					s.bounds[reg] = 16
				}
				oldIndex := s.regs[result]
				s.termBounds = map[*term]uint64{oldIndex: 16}
				x := &pathExecutor{arch: arch, declared: map[string]int{}, fn: &Function{
					Arch: arch, Callees: callees, Records: records,
					Composites: map[string]Composite{"Pair": {Size: 16, Fields: []CompositeField{
						{Name: "a", Offset: 0, Size: 8, Scalar: "u64"},
						{Name: "b", Offset: 8, Size: 8, Scalar: "u64"},
					}}},
				}}
				target := kind
				if kind == "vector" {
					target += VectorEntrySuffix(arch)
				}
				if kind == "discard" {
					x.forgetCallerSaved(s)
				} else if reason, ok := x.summarizeCall(Instruction{Mnemonic: mnemonic, Operands: []Operand{Symbol{Name: target}}}, s); !ok {
					t.Fatal(reason)
				}
				if len(s.bounds) != 1 || s.bounds[preserved] != 16 {
					t.Fatalf("only the preserved register may retain a bound: %v", s.bounds)
				}
				if s.termBounds[oldIndex] != 16 {
					t.Fatal("the immutable pre-call value lost its fact")
				}
				if kind == "scalar" || kind == "pair" {
					if value := s.regs[result]; value == nil || value.kind != termConst || value.value != 31 {
						t.Fatal("the return value was not installed")
					}
					s.noteVariableShift(result)
					if s.notes.shiftGuardMax != ^uint64(0) {
						t.Fatal("the new shift count inherited the pre-call bound")
					}
				}
			})
		}
	}
}
