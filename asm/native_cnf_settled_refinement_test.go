package asm

import (
	"fmt"
	"strings"
	"testing"
)

// These bounded pins compare the production replay + allocator + settled
// decision with the equality-only model. Pending and true roots both refuse
// that model; neither refusal is interpreted as a proof of inequality.
func TestNativeCNFReplaySettledMatchesLean(t *testing.T) {
	a, b, c := paramTerm("a", 1), paramTerm("b", 1), paramTerm("c", 1)
	a8, b8 := paramTerm("a", 8), paramTerm("b", 8)
	wideByte := nativeWordParam(16, 8, "a")
	andAB := nativeWordBinary(8, "and", a8, b8)
	andBA := nativeWordBinary(8, "and", b8, a8)
	tests := []struct {
		name        string
		names       []string
		widths      map[string]int
		left, right *term
		mutate      func(*blaster)
		want        string
	}{
		{name: "one-bit identity", names: []string{"a"}, widths: map[string]int{"a": 1},
			left: a, right: a, want: "equal"},
		{name: "commuted gate word", names: []string{"b", "a"}, widths: map[string]int{"a": 8, "b": 8},
			left: andAB, right: andBA, want: "equal"},
		{name: "zero-extended parameter", names: []string{"a"}, widths: map[string]int{"a": 8},
			left: wideByte, right: nativeWordBinary(16, "or", a8, constTerm(0, 16)), want: "equal"},
		{name: "equal high-bit constants", left: constTerm(0x8000000000000001, 64),
			right: constTerm(0x8000000000000001, 64), want: "equal"},
		{name: "unequal high-bit constants", left: constTerm(0x8000000000000001, 64),
			right: constTerm(1, 64), want: "unequal"},
		{name: "complemented parameter", names: []string{"a"}, widths: map[string]int{"a": 8},
			left: a8, right: nativeWordBinary(8, "xor", a8, constTerm(0xff, 8)), want: "unequal"},
		{name: "nonconstant equal words still need a certificate", names: []string{"c", "a", "b"},
			widths: map[string]int{"a": 1, "b": 1, "c": 1},
			left:   nativeWordBinary(1, "and", a, nativeWordBinary(1, "or", b, c)),
			right:  nativeWordBinary(1, "or", nativeWordBinary(1, "and", a, b), nativeWordBinary(1, "and", a, c)),
			want:   "pending"},
		{name: "independent inputs", names: []string{"a", "b"}, widths: map[string]int{"a": 1, "b": 1},
			left: a, right: b, want: "pending"},
		{name: "unequal widths", left: constTerm(0, 8), right: constTerm(0, 16), want: "replay refusal"},
		{name: "empty widths", left: constTerm(0, 0), right: constTerm(0, 0), want: "replay refusal"},
		{name: "oversized widths", left: nativeWordConstant(65, 0), right: nativeWordConstant(65, 0), want: "replay refusal"},
		{name: "unnormalized constant", left: nativeWordConstant(8, 0x100), right: constTerm(0, 8), want: "replay refusal"},
		{name: "unaccounted variable behind false root", names: []string{"a"}, widths: map[string]int{"a": 1},
			left: a, right: a, mutate: func(bl *blaster) { bl.cnf.variables++ }, want: "allocation refusal"},
		{name: "consistent input alias behind false root", names: []string{"a", "b"}, widths: map[string]int{"a": 1, "b": 1},
			left: a, right: b, mutate: func(bl *blaster) {
				bl.cnf.inputs[1] = bl.cnf.inputs[0]
				bl.memo[b][0] = bl.memo[a][0]
			}, want: "allocation refusal"},
		{name: "corrupt memo behind false root", names: []string{"a", "b"}, widths: map[string]int{"a": 8, "b": 8},
			left: andAB, right: andBA, mutate: func(bl *blaster) {
				gate := bl.cnf.gates[0]
				bl.cnf.memo[cnfKey{op: gate.op, x: gate.x, y: gate.y, z: -1}] = gate.out + 1
			}, want: "replay refusal"},
		{name: "exceeded allocation behind constants", left: constTerm(0, 8), right: constTerm(0, 8),
			mutate: func(bl *blaster) { bl.cnf.exceeded = true }, want: "replay refusal"},
	}
	var pins []string
	for index, test := range tests {
		t.Run(test.name, func(t *testing.T) {
			bl := newCNFBlaster(test.names, test.widths)
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
			outcome := "replay refusal"
			if err := validateNativeBitwiseRoots(bl, test.left, test.right, difference); err == nil {
				cnf, reason, ok := serializeNativeBitwiseCNF(test.name, bl, difference)
				if !ok {
					if !strings.Contains(reason, "allocation check failed") {
						t.Fatalf("unexpected serialization refusal: %s", reason)
					}
					outcome = "allocation refusal"
				} else if cnf.Settled == nil {
					outcome = "pending"
				} else if cnf.Settled.Kind == DecisionProven {
					outcome = "equal"
				} else if cnf.Settled.Kind == DecisionRefuted {
					outcome = "unequal"
				} else {
					t.Fatalf("unexpected settled decision: %+v", cnf.Settled)
				}
			}
			if outcome != test.want {
				t.Fatalf("production outcome = %s, want %s (root %d)", outcome, test.want, difference)
			}
			snapshot, err := renderCNFAllocationSnapshot(bl.cnf)
			if err != nil {
				t.Fatal(err)
			}
			parameters, err := renderNativeCNFWordParameters(test.names, test.widths)
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
			pin := fmt.Sprintf(`
namespace Case%d
def snapshot : CNFDenseAllocation.Snapshot := %s
def parameters : List CNFWordInput.Parameter := %s
def left : CNFWordProjection.WordTerm := %s
def right : CNFWordProjection.WordTerm := %s
theorem decision : checkEqual snapshot parameters 1000000 left right = %t := by decide +kernel
`, index, snapshot, parameters, leftTerm, rightTerm, outcome == "equal")
			if outcome == "equal" {
				// Apply the theorem at arbitrary inputs, not just sample values.
				pin += `example (inputs : CNFWordInput.Inputs) :
    left.width = right.width ∧ (left.eval inputs).toNat = (right.eval inputs).toNat :=
  checkEqual_sound decision inputs
`
			}
			pins = append(pins, pin+fmt.Sprintf("end Case%d\n", index))
		})
	}
	if t.Failed() {
		return
	}
	t.Run("kernel", func(t *testing.T) {
		source := "import Oak.CNFWordSettled\nnamespace Oak.CNFWordSettled\n" +
			"set_option maxRecDepth 4096\nset_option maxHeartbeats 4000000\n" +
			strings.Join(pins, "\n") + "\nend Oak.CNFWordSettled\n"
		checkNativeCNFLean(t, "NativeCNFSettledProductionPins.lean", source)
	})
}
