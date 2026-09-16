package asm

import (
	"context"
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
	"sort"
	"strconv"
	"strings"
	"testing"
	"time"
)

func TestNativeCNFReplayRefusesMissingFirstIndex(t *testing.T) {
	for _, test := range []struct {
		name string
		root *term
	}{
		{name: "first parameter used", root: paramTerm("a", 1)},
		{name: "first parameter unused by constant", root: constTerm(0, 1)},
	} {
		t.Run(test.name, func(t *testing.T) {
			bl := newCNFBlaster([]string{"a", "b"}, map[string]int{"a": 1, "b": 1})
			if roots := bl.blast(test.root); len(roots) != 1 {
				t.Fatalf("fixture root count = %d, want 1", len(roots))
			}
			delete(bl.index, "a")
			bl.index["ghost"] = 0
			if _, err := newNativeCNFReplay(bl); err == nil {
				t.Fatal("replay accepted a missing first parameter index replaced by an extra key")
			}
		})
	}
}

// TestNativeCNFReplayHeaderMatchesLean isolates constructor metadata from its
// separate gate-memo check by using builders with no gates. Map projections
// retain every raw key/value pair in sorted order; they do not fill a missing
// parameter key from the ordered parameter slice.
func TestNativeCNFReplayHeaderMatchesLean(t *testing.T) {
	type headerCase struct {
		name           string
		params         []string
		index          map[string]int
		widths         map[string]int
		grouped        bool
		assumed        bool
		selects        int
		wantAccepted   bool
		wantParameters string
		wantProjection bool
	}
	validIndex := map[string]int{"a": 0, "b": 1}
	validWidths := map[string]int{"a": 1, "b": 64}
	reversedIndex := make(map[string]int, 2)
	reversedIndex["b"] = 1
	reversedIndex["a"] = 0
	reversedWidths := make(map[string]int, 2)
	reversedWidths["b"] = 64
	reversedWidths["a"] = 1
	cases := []headerCase{
		{name: "empty", index: map[string]int{}, widths: map[string]int{}, wantAccepted: true, wantParameters: "[]", wantProjection: true},
		{name: "valid ordered", params: []string{"a", "b"}, index: validIndex, widths: validWidths, wantAccepted: true, wantParameters: "[⟨\"a\", 1⟩, ⟨\"b\", 64⟩]", wantProjection: true},
		{name: "valid reversed map insertion", params: []string{"a", "b"}, index: reversedIndex, widths: reversedWidths, wantAccepted: true, wantParameters: "[⟨\"a\", 1⟩, ⟨\"b\", 64⟩]", wantProjection: true},
		{name: "missing first index balanced by ghost", params: []string{"a", "b"}, index: map[string]int{"ghost": 0, "b": 1}, widths: validWidths, wantProjection: true},
		{name: "missing index", params: []string{"a", "b"}, index: map[string]int{"b": 1}, widths: validWidths, wantProjection: true},
		{name: "extra index", params: []string{"a", "b"}, index: map[string]int{"a": 0, "b": 1, "ghost": 2}, widths: validWidths, wantProjection: true},
		{name: "swapped positions", params: []string{"a", "b"}, index: map[string]int{"a": 1, "b": 0}, widths: validWidths, wantProjection: true},
		{name: "missing width balanced by ghost", params: []string{"a", "b"}, index: validIndex, widths: map[string]int{"ghost": 1, "b": 64}, wantProjection: true},
		{name: "missing width", params: []string{"a", "b"}, index: validIndex, widths: map[string]int{"b": 64}, wantProjection: true},
		{name: "extra width", params: []string{"a", "b"}, index: validIndex, widths: map[string]int{"a": 1, "b": 64, "ghost": 8}, wantProjection: true},
		{name: "zero width", params: []string{"a", "b"}, index: validIndex, widths: map[string]int{"a": 0, "b": 64}, wantProjection: true},
		{name: "width above 64", params: []string{"a", "b"}, index: validIndex, widths: map[string]int{"a": 65, "b": 64}, wantProjection: true},
		{name: "empty name", params: []string{""}, index: map[string]int{"": 0}, widths: map[string]int{"": 1}, wantProjection: true},
		{name: "duplicate ordered name", params: []string{"a", "a"}, index: map[string]int{"a": 0, "ghost": 1}, widths: map[string]int{"a": 1, "ghost": 1}, wantProjection: true},
		{name: "grouped", params: []string{"a", "b"}, index: validIndex, widths: validWidths, grouped: true, wantProjection: true},
		{name: "assumed", params: []string{"a", "b"}, index: validIndex, widths: validWidths, assumed: true, wantProjection: true},
		{name: "select abstraction", params: []string{"a", "b"}, index: validIndex, widths: validWidths, selects: 1, wantProjection: true},
		{name: "negative index projection refused", params: []string{"a", "b"}, index: map[string]int{"a": -1, "b": 1}, widths: validWidths},
		{name: "negative width projection refused", params: []string{"a", "b"}, index: validIndex, widths: map[string]int{"a": -1, "b": 64}},
	}

	leanExamples := make([]string, 0, len(cases))
	t.Run("decisions", func(t *testing.T) {
		for index, test := range cases {
			t.Run(test.name, func(t *testing.T) {
				bl := nativeCNFHeaderBlaster(test.params, test.index, test.widths,
					test.grouped, test.assumed, test.selects)
				_, constructorErr := newNativeCNFReplay(bl)
				accepted := constructorErr == nil
				if accepted != test.wantAccepted {
					t.Fatalf("accepted = %t, want %t: %v", accepted, test.wantAccepted, constructorErr)
				}
				rendered, projectionErr := renderNativeCNFReplayHeader(bl)
				projectable := projectionErr == nil
				if projectable != test.wantProjection {
					t.Fatalf("projectable = %t, want %t: %v", projectable, test.wantProjection, projectionErr)
				}
				if !projectable {
					return
				}
				expected := "none"
				if accepted {
					expected = "some " + test.wantParameters
				}
				leanExamples = append(leanExamples, fmt.Sprintf(
					"def header%d : Snapshot := %s\nexample : check header%d = %s := by decide",
					index, rendered, index, expected))
			})
		}
	})
	if t.Failed() {
		return
	}
	t.Run("kernel", func(t *testing.T) {
		runNativeCNFBookkeepingKernel(t, "Oak.CNFReplayHeader", "Oak.CNFReplayHeader",
			"NativeCNFReplayHeaderProductionPins.lean", leanExamples)
	})
}

// TestNativeCNFReplayFinishMatchesLean models exactly finish's count and
// snapshot comparison. Same-count substitutions are intentionally fabricated,
// unreachable maps: acceptance there demonstrates why finish alone is not a
// theorem about arbitrary term/input/gate map contents.
func TestNativeCNFReplayFinishMatchesLean(t *testing.T) {
	type finishCase struct {
		name           string
		complete       bool
		mutate         func(*nativeCNFReplay)
		wantAccepted   bool
		wantProjection bool
	}
	cases := []finishCase{
		{name: "legitimate complete replay", complete: true, wantAccepted: true, wantProjection: true},
		{name: "incomplete replay", wantProjection: true},
		{name: "missing term", complete: true, mutate: func(replay *nativeCNFReplay) {
			for key := range replay.terms {
				delete(replay.terms, key)
				break
			}
		}, wantProjection: true},
		{name: "extra term", complete: true, mutate: func(replay *nativeCNFReplay) {
			replay.terms[constTerm(0, 1)] = []int{0}
		}, wantProjection: true},
		{name: "missing input", complete: true, mutate: func(replay *nativeCNFReplay) {
			for source := range replay.inputs {
				delete(replay.inputs, source)
				break
			}
		}, wantProjection: true},
		{name: "extra input", complete: true, mutate: func(replay *nativeCNFReplay) {
			replay.inputs[999] = true
		}, wantProjection: true},
		{name: "missing gate key", complete: true, mutate: func(replay *nativeCNFReplay) {
			for key := range replay.gateKeys {
				delete(replay.gateKeys, key)
				break
			}
		}, wantProjection: true},
		{name: "extra gate key", complete: true, mutate: func(replay *nativeCNFReplay) {
			replay.gateKeys[cnfKey{op: 99, x: 2, y: 4, z: -1}] = true
		}, wantProjection: true},
		{name: "builder variables changed", complete: true, mutate: func(replay *nativeCNFReplay) {
			replay.bl.cnf.variables++
		}, wantProjection: true},
		{name: "builder clauses changed", complete: true, mutate: func(replay *nativeCNFReplay) {
			replay.bl.cnf.clauses = append(replay.bl.cnf.clauses, []int{1})
		}, wantProjection: true},
		{name: "builder inputs changed", complete: true, mutate: func(replay *nativeCNFReplay) {
			replay.bl.cnf.inputs[999] = replay.bl.cnf.variables
			replay.inputs[999] = true
		}, wantProjection: true},
		{name: "builder gates changed", complete: true, mutate: func(replay *nativeCNFReplay) {
			replay.bl.cnf.gates = append(replay.bl.cnf.gates, cnfGate{})
		}, wantProjection: true},
		{name: "builder gate memo changed", complete: true, mutate: func(replay *nativeCNFReplay) {
			key := cnfKey{op: 99, x: 2, y: 4, z: -1}
			replay.bl.cnf.memo[key] = replay.bl.cnf.variables
			replay.gateKeys[key] = true
		}, wantProjection: true},
		{name: "builder term memo changed", complete: true, mutate: func(replay *nativeCNFReplay) {
			key := constTerm(0, 1)
			replay.bl.memo[key] = []int{0}
			replay.terms[key] = []int{0}
		}, wantProjection: true},
		{name: "builder owners changed", complete: true, mutate: func(replay *nativeCNFReplay) {
			replay.bl.owners[999] = variableOwner{param: "a"}
		}, wantProjection: true},
		{name: "builder selects changed", complete: true, mutate: func(replay *nativeCNFReplay) {
			replay.bl.selects = append(replay.bl.selects, selectAbstraction{})
		}, wantProjection: true},
		{name: "builder exceeded changed", complete: true, mutate: func(replay *nativeCNFReplay) {
			replay.bl.cnf.exceeded = true
		}, wantProjection: true},
		{name: "same key term roots changed", complete: true, mutate: func(replay *nativeCNFReplay) {
			for _, roots := range replay.terms {
				roots[0] ^= 1
				break
			}
		}, wantAccepted: true, wantProjection: true},
		{name: "same count term substitution", complete: true, mutate: func(replay *nativeCNFReplay) {
			for key, roots := range replay.terms {
				delete(replay.terms, key)
				replay.terms[constTerm(1, 1)] = roots
				break
			}
		}, wantAccepted: true, wantProjection: true},
		{name: "same count input substitution", complete: true, mutate: func(replay *nativeCNFReplay) {
			for source := range replay.inputs {
				delete(replay.inputs, source)
				replay.inputs[999] = true
				break
			}
		}, wantAccepted: true, wantProjection: true},
		{name: "same count gate substitution", complete: true, mutate: func(replay *nativeCNFReplay) {
			for key := range replay.gateKeys {
				delete(replay.gateKeys, key)
				replay.gateKeys[cnfKey{op: 99, x: 2, y: 4, z: -1}] = true
				break
			}
		}, wantAccepted: true, wantProjection: true},
		{name: "negative start field projection refused", complete: true, mutate: func(replay *nativeCNFReplay) {
			replay.startShape.variables = -1
		}},
	}

	leanExamples := make([]string, 0, len(cases))
	t.Run("decisions", func(t *testing.T) {
		for index, test := range cases {
			t.Run(test.name, func(t *testing.T) {
				replay, root, err := newNativeCNFBookkeepingFixture()
				if err != nil {
					t.Fatal(err)
				}
				if test.complete {
					if _, err := replay.term(root); err != nil {
						t.Fatal(err)
					}
				}
				if test.mutate != nil {
					test.mutate(replay)
				}
				finishErr := replay.finish()
				accepted := finishErr == nil
				if accepted != test.wantAccepted {
					t.Fatalf("accepted = %t, want %t: %v", accepted, test.wantAccepted, finishErr)
				}
				current := snapshotCNFObligationCounts(replay.bl)
				startShape, startErr := renderNativeCNFReplayCoverageShape(replay.startShape)
				currentShape, currentErr := renderNativeCNFReplayCoverageShape(current)
				projectable := startErr == nil && currentErr == nil
				if projectable != test.wantProjection {
					t.Fatalf("projectable = %t, want %t: start=%v current=%v",
						projectable, test.wantProjection, startErr, currentErr)
				}
				if !projectable {
					return
				}
				leanExamples = append(leanExamples, fmt.Sprintf(
					"def start%d : Shape := %s\ndef current%d : Shape := %s\n"+
						"example : finish %d %d %d start%d current%d = %t := by decide",
					index, startShape, index, currentShape, len(replay.terms), len(replay.inputs),
					len(replay.gateKeys), index, index, accepted))
			})
		}
	})
	if t.Failed() {
		return
	}
	t.Run("kernel", func(t *testing.T) {
		runNativeCNFBookkeepingKernel(t, "Oak.CNFReplayCoverage", "Oak.CNFReplayCoverage",
			"NativeCNFReplayCoverageProductionPins.lean", leanExamples)
	})
}

func nativeCNFHeaderBlaster(params []string, index, widths map[string]int,
	grouped, assumed bool, selects int) *blaster {
	bl := newCNFBlaster(append([]string(nil), params...), cloneStringIntMap(widths))
	bl.index = cloneStringIntMap(index)
	bl.grouped = grouped
	bl.assumed = assumed
	if selects > 0 {
		bl.selects = make([]selectAbstraction, selects)
	}
	return bl
}

func cloneStringIntMap(source map[string]int) map[string]int {
	cloned := make(map[string]int, len(source))
	for key, value := range source {
		cloned[key] = value
	}
	return cloned
}

func renderNativeCNFReplayHeader(bl *blaster) (string, error) {
	if bl == nil {
		return "", fmt.Errorf("nil blaster")
	}
	params := make([]string, len(bl.params))
	for index, name := range bl.params {
		rendered, err := renderNativeCNFHeaderASCIIString(name)
		if err != nil {
			return "", err
		}
		params[index] = rendered
	}
	index, err := renderNativeCNFHeaderTable(bl.index)
	if err != nil {
		return "", err
	}
	widths, err := renderNativeCNFHeaderTable(bl.widths)
	if err != nil {
		return "", err
	}
	return fmt.Sprintf("⟨[%s], %s, %s, %t, %t, %d⟩", strings.Join(params, ", "),
		index, widths, bl.grouped, bl.assumed, len(bl.selects)), nil
}

func renderNativeCNFHeaderTable(table map[string]int) (string, error) {
	keys := make([]string, 0, len(table))
	for key := range table {
		keys = append(keys, key)
	}
	sort.Strings(keys)
	entries := make([]string, len(keys))
	for index, key := range keys {
		if table[key] < 0 {
			return "", fmt.Errorf("negative table value is outside the Nat projection")
		}
		name, err := renderNativeCNFHeaderASCIIString(key)
		if err != nil {
			return "", err
		}
		entries[index] = fmt.Sprintf("(%s, %d)", name, table[key])
	}
	return "[" + strings.Join(entries, ", ") + "]", nil
}

func renderNativeCNFHeaderASCIIString(value string) (string, error) {
	for _, character := range value {
		if (character < 'a' || character > 'z') && (character < 'A' || character > 'Z') &&
			(character < '0' || character > '9') && character != '_' {
			return "", fmt.Errorf("header name %q is outside fixed ASCII identifiers", value)
		}
	}
	return strconv.Quote(value), nil
}

func newNativeCNFBookkeepingFixture() (*nativeCNFReplay, *term, error) {
	a := paramTerm("a", 1)
	b := paramTerm("b", 1)
	root := &term{kind: termBinary, width: 1, op: "and", left: a, right: b}
	bl := newCNFBlaster([]string{"a", "b"}, map[string]int{"a": 1, "b": 1})
	if roots := bl.blast(root); len(roots) != 1 || roots[0] != 6 {
		return nil, nil, fmt.Errorf("unexpected bookkeeping fixture roots %v", roots)
	}
	replay, err := newNativeCNFReplay(bl)
	if err != nil {
		return nil, nil, err
	}
	return replay, root, nil
}

func renderNativeCNFReplayCoverageShape(shape cnfObligationCounts) (string, error) {
	values := []int{shape.variables, shape.clauses, shape.inputs, shape.gates,
		shape.gateMemo, shape.termMemo, shape.owners, shape.selects}
	for _, value := range values {
		if value < 0 {
			return "", fmt.Errorf("negative shape field is outside the Nat projection")
		}
	}
	return fmt.Sprintf("⟨%d, %d, %d, %d, %d, %d, %d, %d, %t⟩",
		shape.variables, shape.clauses, shape.inputs, shape.gates, shape.gateMemo,
		shape.termMemo, shape.owners, shape.selects, shape.exceeded), nil
}

func runNativeCNFBookkeepingKernel(t *testing.T, module, namespace, filename string,
	examples []string) {
	t.Helper()
	lake, err := exec.LookPath("lake")
	if err != nil {
		requireOracle(t, "lake not on PATH; the formal workflow runs this kernel oracle")
	}
	if len(examples) == 0 {
		t.Fatal("no production bookkeeping decisions were available for the kernel pin")
	}
	leanSource := "import " + module + "\n\nnamespace " + namespace + "\n\n" +
		strings.Join(examples, "\n\n") + "\n\nend " + namespace + "\n"
	leanPath := filepath.Join(t.TempDir(), filename)
	file, err := os.OpenFile(leanPath, os.O_WRONLY|os.O_CREATE|os.O_EXCL, 0o600)
	if err != nil {
		t.Fatal(err)
	}
	if _, err := file.WriteString(leanSource); err != nil {
		file.Close()
		t.Fatal(err)
	}
	if err := file.Close(); err != nil {
		t.Fatal(err)
	}
	ctx, cancel := context.WithTimeout(context.Background(), 90*time.Second)
	defer cancel()
	command := exec.CommandContext(ctx, lake, "env", "lean", leanPath)
	command.Dir = filepath.Join("..", "spec", "lean")
	if output, err := command.CombinedOutput(); err != nil {
		t.Fatalf("kernel-checking native CNF bookkeeping pins: %v (context: %v)\n%s\n--- source ---\n%s",
			err, ctx.Err(), output, leanSource)
	}
}
