package asm

import (
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
	"sort"
	"strings"
	"testing"
)

// renderCNFAllocationSnapshot projects one nonnegative Go snapshot into the
// executable Lean model.  Map keys are sorted solely to make the generated
// kernel input deterministic; key uniqueness is intrinsic to the Go maps and
// is checked explicitly after projection by Lean.
func renderCNFAllocationSnapshot(builder *cnfBuilder) (string, error) {
	if builder == nil || builder.variables < 0 {
		return "", fmt.Errorf("the builder or variable count is outside the Nat projection")
	}
	inputSources := make([]int, 0, len(builder.inputs))
	for source, output := range builder.inputs {
		if source < 0 || output < 0 {
			return "", fmt.Errorf("input (%d, %d) is outside the Nat projection", source, output)
		}
		inputSources = append(inputSources, source)
	}
	sort.Ints(inputSources)
	inputs := make([]string, 0, len(inputSources))
	for _, source := range inputSources {
		inputs = append(inputs, fmt.Sprintf("⟨%d, %d⟩", source, builder.inputs[source]))
	}

	gates := make([]string, 0, len(builder.gates))
	for index, gate := range builder.gates {
		if gate.op < 0 || gate.x < 0 || gate.y < 0 || gate.z < 0 || gate.out < 0 {
			return "", fmt.Errorf("gate %d is outside the Nat projection", index)
		}
		gates = append(gates, fmt.Sprintf("⟨%d, %d, %d, %d, %d⟩",
			gate.op, gate.x, gate.y, gate.z, gate.out))
	}

	keys := make([]cnfKey, 0, len(builder.memo))
	for key, output := range builder.memo {
		if key.op < 0 || key.x < 0 || key.y < 0 || output < 0 {
			return "", fmt.Errorf("memo entry is outside the Nat projection")
		}
		if key.op == cnfIte {
			if key.z < 0 {
				return "", fmt.Errorf("ITE memo edge is outside the Nat projection")
			}
		} else if key.z != -1 {
			return "", fmt.Errorf("binary memo key does not carry the production z=-1 sentinel")
		}
		keys = append(keys, key)
	}
	sort.Slice(keys, func(i, j int) bool {
		left, right := keys[i], keys[j]
		if left.op != right.op {
			return left.op < right.op
		}
		if left.x != right.x {
			return left.x < right.x
		}
		if left.y != right.y {
			return left.y < right.y
		}
		return left.z < right.z
	})
	memo := make([]string, 0, len(keys))
	for _, key := range keys {
		var renderedKey string
		if key.op == cnfIte {
			renderedKey = fmt.Sprintf(".ite %d %d %d", key.x, key.y, key.z)
		} else {
			renderedKey = fmt.Sprintf(".binary %d %d %d", key.op, key.x, key.y)
		}
		memo = append(memo, fmt.Sprintf("⟨%s, %d⟩", renderedKey, builder.memo[key]))
	}

	return fmt.Sprintf("⟨%d, %t, [%s], [%s], [%s]⟩", builder.variables,
		builder.exceeded, strings.Join(inputs, ", "), strings.Join(gates, ", "),
		strings.Join(memo, ", ")), nil
}

// The production validator supplies each expected result.  The generated
// examples make Lean independently replay the same concrete snapshots, so a
// drift in header, density, gate-order/backward or memo decisions fails either
// this test or the kernel check.
func TestValidateCNFAllocationMatchesLean(t *testing.T) {
	type allocationCase struct {
		name   string
		mutate func(*cnfBuilder)
	}
	cases := []allocationCase{
		{name: "valid interleaved allocation"},
		{name: "exceeded", mutate: func(builder *cnfBuilder) { builder.exceeded = true }},
		{name: "input zero", mutate: func(builder *cnfBuilder) { builder.inputs[0] = 0 }},
		{name: "input alias", mutate: func(builder *cnfBuilder) {
			builder.inputs[1] = builder.inputs[0]
		}},
		{name: "input gate collision", mutate: func(builder *cnfBuilder) {
			builder.inputs[0] = builder.gates[0].out
		}},
		{name: "unaccounted variable", mutate: func(builder *cnfBuilder) { builder.variables++ }},
		{name: "backward operand", mutate: func(builder *cnfBuilder) {
			gate := &builder.gates[0]
			old := cnfKey{op: gate.op, x: gate.x, y: gate.y, z: -1}
			output := builder.memo[old]
			delete(builder.memo, old)
			gate.y = 2 * gate.out
			builder.memo[cnfKey{op: gate.op, x: gate.x, y: gate.y, z: -1}] = output
		}},
		{name: "folded identical operands", mutate: func(builder *cnfBuilder) {
			gate := &builder.gates[0]
			old := cnfKey{op: gate.op, x: gate.x, y: gate.y, z: -1}
			output := builder.memo[old]
			delete(builder.memo, old)
			gate.y = gate.x
			builder.memo[cnfKey{op: gate.op, x: gate.x, y: gate.y, z: -1}] = output
		}},
		{name: "memo output drift", mutate: func(builder *cnfBuilder) {
			for key, output := range builder.memo {
				builder.memo[key] = output + 1
				break
			}
		}},
		{name: "missing memo", mutate: func(builder *cnfBuilder) {
			for key := range builder.memo {
				delete(builder.memo, key)
				break
			}
		}},
		{name: "extra memo", mutate: func(builder *cnfBuilder) {
			builder.memo[cnfKey{op: 99, x: 2, y: 4, z: -1}] = 1
		}},
	}

	leanExamples := make([]string, 0, len(cases))
	for index, test := range cases {
		base, _, _ := validCNFTraceFixture()
		builder := cloneCNFTraceBuilder(base)
		if test.mutate != nil {
			test.mutate(builder)
		}
		_, validationErr := validateCNFAllocation(builder)
		snapshot, err := renderCNFAllocationSnapshot(builder)
		if err != nil {
			t.Fatalf("%s: rendering projection: %v", test.name, err)
		}
		leanExamples = append(leanExamples, fmt.Sprintf(
			"def snapshot%d : Snapshot := %s\nexample : (check snapshot%d).isSome = %t := by decide",
			index, snapshot, index, validationErr == nil))
	}

	lake, err := exec.LookPath("lake")
	if err != nil {
		t.Skip("lake not on PATH; the formal workflow runs this kernel oracle")
	}
	leanPath := filepath.Join(t.TempDir(), "CNFDenseAllocationProductionPins.lean")
	leanSource := "import Oak.CNFDenseAllocation\n\nnamespace Oak.CNFDenseAllocation\n\n" +
		strings.Join(leanExamples, "\n\n") + "\n\nend Oak.CNFDenseAllocation\n"
	if err := os.WriteFile(leanPath, []byte(leanSource), 0o600); err != nil {
		t.Fatal(err)
	}
	command := exec.Command(lake, "env", "lean", leanPath)
	command.Dir = filepath.Join("..", "spec", "lean")
	if output, err := command.CombinedOutput(); err != nil {
		t.Fatalf("kernel-checking production allocation pins: %v\n%s\n--- source ---\n%s",
			err, output, leanSource)
	}
}
