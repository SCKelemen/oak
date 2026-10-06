package asm

import (
	"encoding/binary"
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
	"slices"
	"strings"
	"testing"
)

type rv64RelaxCandidate struct {
	limit  int64
	target int
}

func rv64RelaxLayout(units []rv64Piece) []bool {
	layout := make([]bool, len(units))
	for i, unit := range units {
		layout[i] = unit.size == 2
	}
	return layout
}

func rv64RelaxLeanLayout(layout []bool) string {
	values := make([]string, len(layout))
	for i, short := range layout {
		values[i] = fmt.Sprint(short)
	}
	return "[" + strings.Join(values, ", ") + "]"
}

// Candidates are supplied by the fixture, independently of the production
// eligibility code. Nil denotes a pinned pair, ineligible shape, or missing
// label. Small fixtures and real function cases share this trace checker.
func rv64CheckRelaxation(t *testing.T, units []rv64Piece, labels map[string]int,
	candidates []*rv64RelaxCandidate, capture bool) ([]string, int) {
	t.Helper()
	initial := rv64RelaxLayout(units)
	initialWide := 0
	candidateTerms := make([]string, len(candidates))
	for i, candidate := range candidates {
		if !initial[i] {
			initialWide++
		}
		candidateTerms[i] = "none"
		if candidate != nil {
			candidateTerms[i] = fmt.Sprintf("some ⟨%d, %d⟩", candidate.limit, candidate.target)
		}
	}
	model := "chooseCandidates [" + strings.Join(candidateTerms, ", ") + "]"
	var claims []string
	changes := 0
	for {
		before := rv64RelaxLayout(units)
		oldStarts, _ := rv64Offsets(units, labels)
		expected := slices.Clone(before)
		for i, candidate := range candidates {
			if candidate == nil {
				continue
			}
			delta := oldStarts[candidate.target] - oldStarts[i]
			if delta%2 == 0 && -candidate.limit <= delta && delta < candidate.limit {
				expected[i] = true
			}
		}
		changed := rv64RelaxPass(units, labels)
		after := rv64RelaxLayout(units)
		if !slices.Equal(after, expected) || changed == slices.Equal(before, after) {
			t.Fatalf("pass: before=%v after=%v expected=%v changed=%v", before, after, expected, changed)
		}
		newStarts, newLabels := rv64Offsets(units, labels)
		for name, index := range labels {
			if newLabels[name] != newStarts[index] {
				t.Fatalf("label %s lost its instruction boundary", name)
			}
		}
		for i, unit := range units {
			if unit.size != 2 && unit.size != 4 || newStarts[i+1]-newStarts[i] != unit.size || newStarts[i]%2 != 0 {
				t.Fatalf("invalid width/alignment at %d", i)
			}
			if unit.fromCall && before[i] != after[i] {
				t.Fatalf("relocation pair shrank at %d", i)
			}
			if candidate := candidates[i]; candidate != nil && after[i] {
				delta := newStarts[candidate.target] - newStarts[i]
				if delta < -candidate.limit || delta >= candidate.limit || delta%2 != 0 {
					t.Fatalf("admitted transfer at %d stopped fitting: %d", i, delta)
				}
			}
		}
		if capture {
			old := rv64RelaxLeanLayout(before)
			claims = append(claims, fmt.Sprintf("example : pass ((%s) %s) %s = %s := by decide", model, old, old, rv64RelaxLeanLayout(after)))
			for _, index := range []int{0, len(units) / 2, len(units)} {
				claims = append(claims, fmt.Sprintf("example : offset %s %d = %d := by decide", rv64RelaxLeanLayout(after), index, newStarts[index]))
			}
		}
		if !changed {
			break
		}
		changes++
		if changes > initialWide {
			t.Fatalf("relaxation exceeded %d changing passes", initialWide)
		}
	}
	if capture {
		claims = append(claims, fmt.Sprintf("example : relax (%s) %s = (%s, %d) := by apply relax_eq_of_fuel_eq (fuel := %d) <;> decide",
			model, rv64RelaxLeanLayout(initial), rv64RelaxLeanLayout(rv64RelaxLayout(units)), changes, initialWide+1))
	}
	return claims, changes
}

// Exhaust every short / wide eligible / wide blocked layout up to six units,
// with forward, backward, and self targets. The blocked variants exercise
// non-control instructions, nonzero link registers, non-prime branch registers,
// missing labels, and the production fromCall exclusion.
func rv64SmallRelaxations(t *testing.T, capture bool) []string {
	t.Helper()
	var claims []string
	for n, variants := 0, 1; n <= 6; n, variants = n+1, variants*3 {
		for encoded := 0; encoded < variants; encoded++ {
			for direction := 0; direction < 3; direction++ {
				units := make([]rv64Piece, n)
				candidates := make([]*rv64RelaxCandidate, n)
				labels := make(map[string]int)
				states := encoded
				for i := range units {
					state := states % 3
					states /= 3
					target := []int{n, 0, i}[direction]
					name := fmt.Sprintf("l%d", i)
					labels[name] = target
					mnemonic, rs, limit := "beq", 8, int64(256)
					if i%3 == 1 {
						mnemonic, rs = "bne", 15
					} else if i%3 == 2 {
						mnemonic, rs, limit = "jal", 0, 2048
					}
					instr := rv64ProofBranch(mnemonic, rs, 0)
					instr.Operands[len(instr.Operands)-1] = Symbol{Name: name}
					units[i] = rv64Piece{base: instr, size: 4}
					candidates[i] = &rv64RelaxCandidate{limit: limit, target: target}
					if state == 0 {
						units[i].size = 2
					} else if state == 2 {
						candidates[i] = nil
						switch (i + direction) % 5 {
						case 0:
							units[i].fromCall = true
						case 1:
							units[i].base = rv64ProofBranch("jal", 1, 0)
							units[i].base.Operands[1] = Symbol{Name: name}
						case 2:
							units[i].base = rv64ProofBranch("beq", 7, 0)
							units[i].base.Operands[2] = Symbol{Name: name}
						case 3:
							delete(labels, name)
						case 4:
							units[i].base = Instruction{Mnemonic: "nop"}
						}
					}
				}
				pins, _ := rv64CheckRelaxation(t, units, labels, candidates, capture && n <= 3)
				claims = append(claims, pins...)
			}
		}
	}
	return claims
}

// Two forward transfers initially sit exactly outside the compressed range.
// C shrinks in pass 1, B in pass 2, A and the backward edge in pass 3. This
// distinguishes one-snapshot passes from incrementally recomputed layouts.
func rv64CascadeRelaxation(t *testing.T, jump, capture bool) []string {
	t.Helper()
	mnemonic, rs, limit := "beq", 8, int64(256)
	if jump {
		mnemonic, rs, limit = "jal", 0, 2048
	}
	branch := func(mnemonic string, rs int, label string) Instruction {
		instr := rv64ProofBranch(mnemonic, rs, 0)
		instr.Operands[len(instr.Operands)-1] = Symbol{Name: label}
		return instr
	}
	reg := func(n int) Register { return Register{Class: ClassRV64X, Num: n, Lane: -1} }
	mul := Instruction{Mnemonic: "mul", Operands: []Operand{reg(5), reg(6), reg(7)}}
	fn := &Function{Name: "three_passes", Arch: ArchRV64, Compressed: true, Items: []Item{
		Label{Name: "start"}, branch(mnemonic, rs, "a"), branch(mnemonic, rs, "b"),
	}}
	filler := int((limit - 8) / 4)
	for i := 0; i < filler; i++ {
		fn.Items = append(fn.Items, mul)
	}
	fn.Items = append(fn.Items, Label{Name: "a"}, branch("jal", 0, "b"), Label{Name: "b"},
		branch(mnemonic, rs, "start"), branch("jal", 1, "start"),
		Instruction{Mnemonic: "addi", Operands: []Operand{reg(8), reg(8), Immediate{Value: 1}}})
	units, labels, err := rv64Expand(fn)
	if err != nil {
		t.Fatal(err)
	}
	units[len(units)-1].size = 2 // the non-control prepass compresses the tail
	candidates := make([]*rv64RelaxCandidate, len(units))
	candidates[0] = &rv64RelaxCandidate{limit: limit, target: labels["a"]}
	candidates[1] = &rv64RelaxCandidate{limit: limit, target: labels["b"]}
	candidates[labels["a"]] = &rv64RelaxCandidate{limit: 2048, target: labels["b"]}
	candidates[labels["b"]] = &rv64RelaxCandidate{limit: limit, target: labels["start"]}
	claims, changes := rv64CheckRelaxation(t, units, labels, candidates, capture)
	if changes != 3 {
		t.Fatalf("want three changing passes, got %d", changes)
	}
	code, relocs, err := encodeRV64Function(fn)
	starts, finalLabels := rv64Offsets(units, labels)
	if err != nil || len(relocs) != 0 || int64(len(code)) != starts[len(units)] {
		t.Fatalf("function writer: %d bytes, relocs=%v, error=%v", len(code), relocs, err)
	}
	if finalLabels["a"] != limit-4 || finalLabels["b"] != limit-2 {
		t.Fatalf("final label positions: %v", finalLabels)
	}
	for i, unit := range units {
		pc := starts[i]
		if unit.size == 2 {
			got := binary.LittleEndian.Uint16(code[pc:])
			want, ok := rvcEncode(unit.base, pc, finalLabels)
			if !ok || got != want {
				t.Fatalf("compressed writer at %d: %#x want %#x", pc, got, want)
			}
			if candidate := candidates[i]; candidate != nil && pc+rv64ProofCompressedDisplacement(unit.base.Mnemonic == "jal", got) != starts[candidate.target] {
				t.Fatalf("compressed edge at %d missed its label", pc)
			}
		} else {
			got := binary.LittleEndian.Uint32(code[pc:])
			want, err := encodeRV64Instruction(unit.base, pc, finalLabels)
			if err != nil || got != want {
				t.Fatalf("wide writer at %d: %#x want %#x (%v)", pc, got, want, err)
			}
		}
	}
	return claims
}

func TestRV64RelaxationPasses(t *testing.T) {
	rv64SmallRelaxations(t, false)
	rv64CascadeRelaxation(t, false, false)
	rv64CascadeRelaxation(t, true, false)
}

// A fixed point belongs to the existing snapshot policy; it is not a minimum
// code-size claim. The policy does not speculate that shortening this branch
// itself would bring a +256-byte displacement down to +254.
func TestRV64RelaxationConservativeEndpoint(t *testing.T) {
	units := make([]rv64Piece, 64)
	units[0] = rv64Piece{base: rv64ProofBranch("beq", 8, 0), size: 4}
	for i := 1; i < len(units); i++ {
		units[i] = rv64Piece{base: Instruction{Mnemonic: "mul"}, size: 4}
	}
	labels := map[string]int{"target": len(units)}
	if rv64RelaxPass(units, labels) || units[0].size != 4 {
		t.Fatal("the out-of-range branch must remain wide under snapshot admission")
	}
	units[0].size = 2
	starts, targets := rv64Offsets(units, labels)
	if _, ok := rvcEncode(units[0].base, starts[0], targets); !ok {
		t.Fatal("the counterfactual shorter layout should admit the branch")
	}
}

func TestRV64RelaxationMatchesLean(t *testing.T) {
	claims := rv64SmallRelaxations(t, true)
	claims = append(claims, rv64CascadeRelaxation(t, false, true)...)
	claims = append(claims, rv64CascadeRelaxation(t, true, true)...)
	source := "import Oak.RiscVRelaxation\nopen Oak.RiscVRelaxation\nset_option maxRecDepth 65536\nset_option maxHeartbeats 10000000\n" + strings.Join(claims, "\n") + "\n"
	lake, err := exec.LookPath("lake")
	if err != nil {
		if os.Getenv("OAK_REQUIRE_RV64_LEAN") != "" {
			t.Fatal("lake required for RV64 relaxation correspondence")
		}
		t.Skip("lake not on PATH; formal workflow requires this oracle")
	}
	path := filepath.Join(t.TempDir(), "RV64RelaxationProductionPins.lean")
	if err := os.WriteFile(path, []byte(source), 0600); err != nil {
		t.Fatal(err)
	}
	buildLeanImports(t, lake, path)
	cmd := exec.Command(lake, "env", "lean", path)
	cmd.Dir = filepath.Join("..", "spec", "lean")
	if out, err := cmd.CombinedOutput(); err != nil {
		t.Fatalf("RV64 relaxation correspondence: %v\n%s", err, out)
	}
	t.Logf("checked %d Lean production claims", len(claims))
}
