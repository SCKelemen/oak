package asm

import (
	"fmt"
	"strings"
	"testing"
)

// Exercise the production admission + serialization path, not just the header
// constructor. Raw metadata is projected even when unused by constant words;
// the Lean checker must refuse it before returning any settled equality.
func TestNativeCNFReplayMetadataSettledMatchesLean(t *testing.T) {
	a, b := paramTerm("a", 8), paramTerm("b", 8)
	tests := []struct {
		name        string
		left, right *term
		mutate      func(*blaster)
		wantHeader  bool
		wantEqual   bool
	}{
		{name: "unused valid metadata", wantHeader: true, wantEqual: true},
		{name: "empty metadata", mutate: func(bl *blaster) {
			bl.params, bl.index, bl.widths = nil, nil, nil
		}, wantHeader: true, wantEqual: true},
		{name: "ordered named input", left: a, right: a, wantHeader: true, wantEqual: true},
		{name: "commuted named words", left: nativeWordBinary(8, "and", a, b),
			right: nativeWordBinary(8, "and", b, a), wantHeader: true, wantEqual: true},
		{name: "missing first index balanced by ghost", mutate: func(bl *blaster) {
			delete(bl.index, "b")
			bl.index["ghost"] = 0
		}},
		{name: "missing index", mutate: func(bl *blaster) { delete(bl.index, "a") }},
		{name: "extra index", mutate: func(bl *blaster) { bl.index["ghost"] = 2 }},
		{name: "swapped positions", mutate: func(bl *blaster) { bl.index["a"], bl.index["b"] = 0, 1 }},
		{name: "missing width balanced by ghost", mutate: func(bl *blaster) {
			delete(bl.widths, "b")
			bl.widths["ghost"] = 8
		}},
		{name: "missing width", mutate: func(bl *blaster) { delete(bl.widths, "a") }},
		{name: "extra width", mutate: func(bl *blaster) { bl.widths["ghost"] = 8 }},
		{name: "zero declared width", mutate: func(bl *blaster) { bl.widths["a"] = 0 }},
		{name: "oversized declared width", mutate: func(bl *blaster) { bl.widths["a"] = 65 }},
		{name: "empty name", mutate: func(bl *blaster) {
			bl.params, bl.index, bl.widths = []string{""}, map[string]int{"": 0}, map[string]int{"": 8}
		}},
		{name: "duplicate ordered name", mutate: func(bl *blaster) { bl.params[1] = "b" }},
		{name: "grouped mode", mutate: func(bl *blaster) { bl.grouped = true }},
		{name: "assumed mode", mutate: func(bl *blaster) { bl.assumed = true }},
		{name: "select abstraction", mutate: func(bl *blaster) { bl.selects = make([]selectAbstraction, 1) }},
		{name: "valid header cannot change a used declared width", left: a, right: a, wantHeader: true,
			mutate: func(bl *blaster) { bl.widths["a"] = 16 }},
		{name: "valid header cannot excuse unaccounted allocation", wantHeader: true,
			mutate: func(bl *blaster) { bl.cnf.variables++ }},
		{name: "valid header cannot excuse exceeded allocation", wantHeader: true,
			mutate: func(bl *blaster) { bl.cnf.exceeded = true }},
		{name: "valid header cannot settle true root", left: constTerm(42, 8), right: constTerm(43, 8), wantHeader: true},
		{name: "valid header cannot settle pending root", left: a, right: b, wantHeader: true},
		{name: "valid header cannot excuse unequal widths", left: constTerm(42, 8), right: constTerm(42, 16), wantHeader: true},
	}
	var pins []string
	for index, test := range tests {
		t.Run(test.name, func(t *testing.T) {
			// Parameter order deliberately differs from sorted map order.
			bl := newCNFBlaster([]string{"b", "a"}, map[string]int{"a": 8, "b": 8})
			if test.left == nil {
				test.left, test.right = constTerm(42, 8), constTerm(42, 8)
			}
			left, right := bl.blast(test.left), bl.blast(test.right)
			if test.mutate != nil {
				test.mutate(bl)
			}
			difference := bddFalse
			if len(left) == len(right) {
				for bit := range left {
					difference = bl.apply(opOr, difference, bl.apply(opXor, left[bit], right[bit]))
				}
			}
			// Isolate the header oracle with the exact same raw metadata but
			// empty allocation: the constructor also checks gate/memo state.
			headerOnly := nativeCNFHeaderBlaster(bl.params, bl.index, bl.widths,
				bl.grouped, bl.assumed, len(bl.selects))
			_, headerErr := newNativeCNFReplay(headerOnly)
			if (headerErr == nil) != test.wantHeader {
				t.Fatalf("production header acceptance = %t, want %t: %v", headerErr == nil, test.wantHeader, headerErr)
			}
			// Full replay and allocation must still pass after the header.
			accepted := false
			if err := validateNativeBitwiseRoots(bl, test.left, test.right, difference); err == nil {
				cnf, _, ok := serializeNativeBitwiseCNF(test.name, bl, difference)
				accepted = ok && cnf.Settled != nil && cnf.Settled.Kind == DecisionProven
			}
			if accepted != test.wantEqual {
				t.Fatalf("production settled equality = %t, want %t (root %d)", accepted, test.wantEqual, difference)
			}
			header, err := renderNativeCNFReplayHeader(bl)
			if err != nil {
				t.Fatal(err)
			}
			snapshot, err := renderCNFAllocationSnapshot(bl.cnf)
			if err != nil {
				t.Fatal(err)
			}
			leftTerm, err := renderNativeCNFWordTerm(test.left)
			if err != nil {
				t.Fatal(err)
			}
			rightTerm, err := renderNativeCNFWordTerm(test.right)
			if err != nil {
				t.Fatal(err)
			}
			expected := "none"
			if accepted {
				parameters, err := renderNativeCNFWordParameters(bl.params, bl.widths)
				if err != nil {
					t.Fatal(err)
				}
				expected = "some " + parameters
			}
			pin := fmt.Sprintf(`
namespace Case%d
def header : CNFReplayHeader.Snapshot := %s
def snapshot : CNFDenseAllocation.Snapshot := %s
def left : CNFWordProjection.WordTerm := %s
def right : CNFWordProjection.WordTerm := %s
example : (CNFReplayHeader.check header).isSome = %t := by decide +kernel
theorem decision : check header snapshot 1000000 left right = %s := by decide +kernel
`, index, header, snapshot, leftTerm, rightTerm, test.wantHeader, expected)
			if accepted {
				pin += `example (inputs : CNFWordInput.Inputs) :
    left.width = right.width ∧ (left.eval inputs).toNat = (right.eval inputs).toNat :=
  (check_sound decision inputs).2.2
`
			}
			pins = append(pins, pin+fmt.Sprintf("end Case%d\n", index))
		})
	}
	if t.Failed() {
		return
	}
	t.Run("kernel", func(t *testing.T) {
		source := "import Oak.CNFMetadataSettled\nnamespace Oak.CNFMetadataSettled\n" +
			"set_option maxRecDepth 4096\nset_option maxHeartbeats 4000000\n" +
			strings.Join(pins, "\n") + "\nend Oak.CNFMetadataSettled\n"
		checkNativeCNFLean(t, "NativeCNFMetadataSettledProductionPins.lean", source)
	})
}
