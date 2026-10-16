package asm

import (
	"context"
	"fmt"
	"os"
	"path/filepath"
	"strings"
	"testing"
)

// Produce exact Go decisions separately from the bounded Lean gate. No test
// starts a Lean process. The supplied snapshot includes every fold precedence,
// operand polarity and unmodified/refused memo case in a single small artifact.
func TestTypedCNFMuxPins(t *testing.T) {
	builder := newCNFBuilder()
	for i := 0; i < 3; i++ {
		builder.variable(i)
	}
	for c := 0; c < 8; c++ {
		for a := 0; a < 8; a++ {
			for b := 0; b < 8; b++ {
				builder.ite(c, a, b)
			}
		}
	}
	if _, err := validateCNFAllocation(builder); err != nil {
		t.Fatal(err)
	}
	snapshot, err := renderCNFAllocationSnapshot(builder)
	if err != nil {
		t.Fatal(err)
	}
	var pins strings.Builder
	pins.WriteString("import Oak.CNFReplayTerm\n\nnamespace Oak.CNFReplayApply\n\n")
	fmt.Fprintf(&pins, "def typedMuxSnapshot : CNFDenseAllocation.Snapshot := %s\n", snapshot)
	replay := func(builder *cnfBuilder, maxInt int) *typedCNFReplay {
		return &typedCNFReplay{nativeCNFReplay: &nativeCNFReplay{bl: &blaster{cnf: builder}, gateKeys: map[cnfKey]bool{}, maxInt: maxInt}, ctx: context.Background(), limit: typedCNFDiagnosticLimits}
	}
	r := replay(builder, 100000)
	for c := 0; c < 8; c++ {
		for a := 0; a < 8; a++ {
			for b := 0; b < 8; b++ {
				root, err := r.ite(c, a, b)
				if err != nil {
					t.Fatal(err)
				}
				// Compare actual Boolean truth on every input assignment, including negative
				// edges, against the requested if/then/else, independently of builder.ite.
				for mask := 0; mask < 8; mask++ {
					values := map[int]bool{1: mask&1 != 0, 2: mask&2 != 0, 3: mask&4 != 0}
					edge := func(e int) bool {
						if e < 2 {
							return e == 1
						}
						return values[e>>1] != (e&1 != 0)
					}
					for _, g := range builder.gates {
						switch g.op {
						case opAnd:
							values[g.out] = edge(g.x) && edge(g.y)
						case opOr:
							values[g.out] = edge(g.x) || edge(g.y)
						case opXor:
							values[g.out] = edge(g.x) != edge(g.y)
						case cnfIte:
							if edge(g.x) {
								values[g.out] = edge(g.y)
							} else {
								values[g.out] = edge(g.z)
							}
						}
					}
					want := edge(b)
					if edge(c) {
						want = edge(a)
					}
					if edge(root) != want {
						t.Fatalf("mux truth c=%d a=%d b=%d mask=%d", c, a, b, mask)
					}
				}
				fmt.Fprintf(&pins, "example : replayIte typedMuxSnapshot.variables 100000 typedMuxSnapshot.memo %d %d %d = some %d := by decide\n", c, a, b, root)
			}
		}
	}
	key := cnfKey{cnfIte, 2, 4, 6}
	for index, mode := range []string{"missing", "zero", "range", "maxInt"} {
		invalid := cloneCNFTraceBuilder(builder)
		maxInt := 100000
		switch mode {
		case "missing":
			delete(invalid.memo, key)
		case "zero":
			invalid.memo[key] = 0
		case "range":
			invalid.memo[key] = invalid.variables + 1
		case "maxInt":
			maxInt = 1
		}
		if _, err := replay(invalid, maxInt).ite(2, 4, 6); err == nil {
			t.Fatalf("accepted %s mux memo", mode)
		}
		supplied, err := renderCNFAllocationSnapshot(invalid)
		if err != nil {
			t.Fatal(err)
		}
		fmt.Fprintf(&pins, "def typedMuxRefusal%d : CNFDenseAllocation.Snapshot := %s\nexample : replayIte typedMuxRefusal%d.variables %d typedMuxRefusal%d.memo 2 4 6 = none := by decide\n", index, supplied, index, maxInt, index)
	}
	for _, triple := range [][3]int{{-1, 4, 6}, {2, -1, 6}, {2, 4, -1}} {
		if _, err := r.ite(triple[0], triple[1], triple[2]); err == nil {
			t.Fatal("negative edge accepted")
		}
	}
	root, err := r.ite(2, 5, 6)
	if err != nil {
		t.Fatal(err)
	}
	fmt.Fprintf(&pins, "example : CNFReplayTerm.replayTerm typedMuxSnapshot 100000 (.ite (.input 1) (.complement (.input 2)) (.input 3)) = some %d := by decide\n", root)
	pins.WriteString("end Oak.CNFReplayApply\n")
	if pins.Len() > 176<<10 {
		t.Fatalf("mux pins exceed structured output cap: %d", pins.Len())
	}
	if output := os.Getenv("OAK_TYPED_CNF_PIN_DIR"); output != "" {
		if err := os.WriteFile(filepath.Join(output, "TypedCNFMuxProductionPins.lean"), []byte(pins.String()), 0600); err != nil {
			t.Fatal(err)
		}
	}
	t.Logf("mux pins: 512 fold/polarity cases, 4 memo refusals, complement/ITE composition, bytes=%d SHA256=%s", pins.Len(), tcSHA([]byte(pins.String())))
}
