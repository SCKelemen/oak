package asm

import (
	"context"
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
	"runtime"
	"slices"
	"strconv"
	"strings"
	"testing"
	"time"
)

// renderNativeCNFReplayWord projects syntax and allocated input slots, never
// producer memo roots or Boolean evaluation. Each child is projected at its
// own width before its parent truncates or zero-extends it. The resulting
// list is least-significant-bit first, as replay.term and resultWord require.
// This bounded test bridge is not a universal Go implementation refinement.
func renderNativeCNFReplayWord(bl *blaster, root *term) ([]string, error) {
	if bl == nil || bl.cnf == nil {
		return nil, fmt.Errorf("the CNF blaster is missing")
	}
	if bl.grouped || bl.assumed || len(bl.selects) != 0 {
		return nil, fmt.Errorf("ordering or abstraction is outside the word projection")
	}
	if len(bl.params) != len(bl.index) || len(bl.params) != len(bl.widths) {
		return nil, fmt.Errorf("ordered parameter tables disagree")
	}
	maxInt := int(^uint(0) >> 1)
	if len(bl.params) > maxInt-selectSlots {
		return nil, fmt.Errorf("parameter stride overflows int")
	}
	stride := len(bl.params) + selectSlots
	for position, name := range bl.params {
		index, indexed := bl.index[name]
		width, known := bl.widths[name]
		if name == "" || !indexed || index != position || !known || width < 1 || width > 64 {
			return nil, fmt.Errorf("invalid ordered parameter %d", position)
		}
	}
	if _, err := validateCNFAllocation(bl.cnf); err != nil {
		return nil, fmt.Errorf("input allocation: %w", err)
	}

	// Depth alone does not bound expanding a shared DAG into tree syntax.
	// Account for every rendered string before allocating the next one.
	const maxProjectionBytes = 1 << 20
	remaining := maxProjectionBytes
	charge := func(size int) bool {
		if size > remaining {
			return false
		}
		remaining -= size
		return true
	}
	memo := map[*term][]string{}
	heights := map[*term]int{}
	active := map[*term]bool{}
	var render func(*term, int) ([]string, error)
	render = func(current *term, depth int) ([]string, error) {
		if current == nil || depth > 64 || active[current] {
			return nil, fmt.Errorf("term is nil, cyclic, or exceeds the depth bound")
		}
		if bits, seen := memo[current]; seen {
			if depth+heights[current] > 64 {
				return nil, fmt.Errorf("shared term exceeds the depth bound")
			}
			return bits, nil
		}
		if current.width < 1 || current.width > 64 {
			return nil, fmt.Errorf("term width %d is outside 1..64", current.width)
		}
		active[current] = true
		defer delete(active, current)
		out := make([]string, current.width)
		switch current.kind {
		case termConst:
			if current.name != "" || current.op != "" || current.left != nil || current.right != nil ||
				current.cond != nil || current.declared != 0 || current.width < 64 && current.value>>uint(current.width) != 0 {
				return nil, fmt.Errorf("constant term is malformed")
			}
			for bit := range out {
				out[bit] = fmt.Sprintf(".constant %t", current.value>>uint(bit)&1 != 0)
			}
		case termParam:
			if current.name == "" || current.op != "" || current.left != nil || current.right != nil ||
				current.cond != nil || current.value != 0 || current.declared < 0 {
				return nil, fmt.Errorf("parameter term is malformed")
			}
			position, indexed := bl.index[current.name]
			declared, known := bl.widths[current.name]
			if !indexed || !known || current.declaredWidth() != declared {
				return nil, fmt.Errorf("parameter is absent or has a mismatched declared width")
			}
			for bit := range out {
				out[bit] = ".constant false"
				if bit >= declared {
					continue
				}
				if bit > (maxInt-position)/stride {
					return nil, fmt.Errorf("input bit index overflows int")
				}
				output, allocated := bl.cnf.inputs[bit*stride+position]
				if !allocated || output < 1 || output > bl.cnf.variables || output > maxInt/2 {
					return nil, fmt.Errorf("parameter %q bit %d has no valid allocated input output", current.name, bit)
				}
				out[bit] = fmt.Sprintf(".input %d", output)
			}
		case termBinary:
			if current.name != "" || current.value != 0 || current.declared != 0 || current.cond != nil ||
				current.left == nil || current.right == nil {
				return nil, fmt.Errorf("binary term is malformed")
			}
			// Literal tags belong to the formal model, independently of Go's
			// opAnd/opOr/opXor constants, whose correspondence the pins test.
			operation, known := map[string]int{"and": 0, "or": 1, "xor": 2}[current.op]
			if !known {
				return nil, fmt.Errorf("operation %q is outside the word projection", current.op)
			}
			left, err := render(current.left, depth+1)
			if err != nil {
				return nil, err
			}
			right, err := render(current.right, depth+1)
			if err != nil {
				return nil, err
			}
			heights[current] = 1 + max(heights[current.left], heights[current.right])
			at := func(bits []string, bit int) string {
				if bit >= len(bits) {
					return ".constant false"
				}
				return bits[bit]
			}
			for bit := range out {
				l, r := at(left, bit), at(right, bit)
				if !charge(len(l) + len(r) + len(".binary 0 () ()")) {
					return nil, fmt.Errorf("word projection exceeds the text budget")
				}
				out[bit] = fmt.Sprintf(".binary %d (%s) (%s)", operation, l, r)
			}
		default:
			return nil, fmt.Errorf("term kind %d is outside the word projection", current.kind)
		}
		if current.kind != termBinary {
			for _, bit := range out {
				if !charge(len(bit)) {
					return nil, fmt.Errorf("word projection exceeds the text budget")
				}
			}
		}
		memo[current] = out
		return out, nil
	}
	return render(root, 0)
}

func renderNativeCNFReplayPairs(bl *blaster, left, right *term) (string, error) {
	if left == nil || right == nil || left.width != right.width {
		return "", fmt.Errorf("result words are missing or have unequal widths")
	}
	l, err := renderNativeCNFReplayWord(bl, left)
	if err != nil {
		return "", err
	}
	r, err := renderNativeCNFReplayWord(bl, right)
	if err != nil {
		return "", err
	}
	pairs := make([]string, len(l))
	for bit := range pairs {
		pairs[bit] = fmt.Sprintf("((%s), (%s))", l[bit], r[bit])
	}
	return "[" + strings.Join(pairs, ", ") + "]", nil
}

// Whole-word pins exercise production memo replay, the independent syntax
// projection, and Lean's Boolean replay. Concrete value pins additionally
// bind source names and bit ordering to resultWord's original-input semantics.
func TestNativeCNFReplayWordPairsMatchesLean(t *testing.T) {
	binary := func(width int, op string, left, right *term) *term {
		return &term{kind: termBinary, width: width, op: op, left: left, right: right}
	}
	type wordCase struct {
		name        string
		names       []string
		widths      map[string]int
		left, right *term
		values      []uint64
		want        [2]uint64
	}
	var cases []wordCase
	for _, width := range []int{1, 8, 16, 32, 64} {
		a, b, c := paramTerm("a", width), paramTerm("b", width), paramTerm("c", width)
		if width >= 32 {
			// A single gate per bit keeps the kernel's quadratic snapshot
			// checks bounded while exercising every bit of full-width inputs.
			cases = append(cases, wordCase{
				name: fmt.Sprintf("commutativity_%d", width), names: []string{"b", "a"},
				widths: map[string]int{"a": width, "b": width},
				left:   binary(width, "xor", a, b), right: binary(width, "xor", b, a),
				values: []uint64{0x0123456789abcdef & mask(width), 0xa55aa55aa55aa55a & mask(width)},
				want:   [2]uint64{0xa479e03d2cf168b5 & mask(width), 0xa479e03d2cf168b5 & mask(width)},
			})
			continue
		}
		// c is deliberately in position zero. Blasting (a&b) first allocates
		// c after the first word's gates, not at a guessed dense input offset.
		left := binary(width, "or", binary(width, "and", a, b), binary(width, "and", a, c))
		right := binary(width, "and", a, binary(width, "or", b, c))
		cases = append(cases, wordCase{
			name: fmt.Sprintf("distributivity_%d", width), names: []string{"c", "a", "b"},
			widths: map[string]int{"a": width, "b": width, "c": width}, left: left, right: right,
			values: []uint64{0x8040201008040201 & mask(width), 0xa55aa55aa55aa55a & mask(width), 0x0123456789abcdef & mask(width)},
			want:   [2]uint64{0x81422552810a854a & mask(width), 0x81422552810a854a & mask(width)},
		})
	}
	narrow := paramTerm("byte", 8)
	widened := *narrow
	widened.width = 64
	truncated := *paramTerm("wide", 64)
	truncated.width = 8
	shared := binary(16, "xor", narrow, constTerm(0xa500, 16))
	cases = append(cases,
		wordCase{name: "parameter_zero_extension", names: []string{"byte"}, widths: map[string]int{"byte": 8},
			left: &widened, right: binary(64, "or", narrow, constTerm(0, 64)), values: []uint64{0x81}, want: [2]uint64{0x81, 0x81}},
		wordCase{name: "parameter_truncation", names: []string{"wide"}, widths: map[string]int{"wide": 64},
			left: &truncated, right: binary(8, "or", paramTerm("wide", 64), constTerm(0, 8)),
			values: []uint64{0x123456789abcdef1}, want: [2]uint64{0xf1, 0xf1}},
		wordCase{name: "truncate_then_extend", names: []string{"wide"}, widths: map[string]int{"wide": 64},
			left:   binary(64, "or", binary(8, "xor", paramTerm("wide", 64), constTerm(0x80, 8)), constTerm(0x100000000, 64)),
			right:  binary(64, "or", &truncated, constTerm(0x100000000, 64)),
			values: []uint64{0x123456789abcdef1}, want: [2]uint64{0x100000071, 0x1000000f1}},
		wordCase{name: "mixed_children_and_shared_dag", names: []string{"byte"}, widths: map[string]int{"byte": 8},
			left: binary(16, "and", shared, shared), right: binary(16, "or", constTerm(0xa500, 16), narrow),
			values: []uint64{0x81}, want: [2]uint64{0xa581, 0xa581}},
		wordCase{name: "unequal_high_bit", names: []string{"wide"}, widths: map[string]int{"wide": 64},
			left: binary(64, "xor", paramTerm("wide", 64), constTerm(0x8000000000000000, 64)), right: paramTerm("wide", 64),
			values: []uint64{0x123456789abcdef1}, want: [2]uint64{0x923456789abcdef1, 0x123456789abcdef1}},
		wordCase{name: "unequal_mask", names: []string{"a", "b"}, widths: map[string]int{"a": 8, "b": 8},
			left: binary(8, "and", paramTerm("a", 8), paramTerm("b", 8)), right: binary(8, "or", paramTerm("a", 8), paramTerm("b", 8)),
			values: []uint64{0x81, 0x42}, want: [2]uint64{0, 0xc3}},
		wordCase{name: "all_constant", widths: map[string]int{}, left: constTerm(0xfedcba9876543210, 64), right: constTerm(0xfedcba9876543210, 64),
			want: [2]uint64{0xfedcba9876543210, 0xfedcba9876543210}},
	)
	for _, test := range cases {
		t.Run(test.name, func(t *testing.T) {
			bl := newCNFBlaster(test.names, test.widths)
			left, right := bl.blast(test.left), bl.blast(test.right)
			difference := bddFalse
			for bit := range left {
				difference = bl.apply(opOr, difference, bl.apply(opXor, left[bit], right[bit]))
			}
			if err := validateNativeBitwiseRoots(bl, test.left, test.right, difference); err != nil {
				t.Fatalf("production replay: %v", err)
			}
			pairs, err := renderNativeCNFReplayPairs(bl, test.left, test.right)
			if err != nil {
				t.Fatal(err)
			}
			snapshot, err := renderCNFAllocationSnapshot(bl.cnf)
			if err != nil {
				t.Fatal(err)
			}
			roots := func(bits []int) string {
				values := make([]string, len(bits))
				for i, bit := range bits {
					values[i] = fmt.Sprintf("some %d", bit)
				}
				return "[" + strings.Join(values, ", ") + "]"
			}
			env := map[string]uint64{}
			for i, name := range test.names {
				env[name] = test.values[i]
			}
			if got := [2]uint64{test.left.eval(env), test.right.eval(env)}; got != test.want {
				t.Fatalf("production values = %x, want %x", got, test.want)
			}
			// Generate the assignment from names and input source indices, not
			// the producer's diagnostic owners map (which can drift separately).
			// The eight reserved select positions pin the current input layout
			// independently of the production selectSlots constant.
			var trueInputs []int
			for position, name := range test.names {
				for bit := 0; bit < test.widths[name]; bit++ {
					if output, exists := bl.cnf.inputs[bit*(len(test.names)+8)+position]; exists && env[name]>>uint(bit)&1 != 0 {
						trueInputs = append(trueInputs, output)
					}
				}
			}
			slices.Sort(trueInputs)
			indices := make([]string, len(trueInputs))
			for i, input := range trueInputs {
				indices[i] = strconv.Itoa(input)
			}
			source := fmt.Sprintf(`import Oak.CNFReplayCertificate

namespace Oak.CNFReplayTerm
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

def wordSnapshot : CNFDenseAllocation.Snapshot := %s
def pairs : List (Term × Term) := %s
def initial : RupCheck.Assignment := fun index => ([%s] : List Nat).contains index

example : (CNFDenseAllocation.check wordSnapshot).isSome = true := by decide +kernel
example : pairs.length = %d := by decide +kernel
example : pairs.map (fun pair => replayTerm wordSnapshot 100000 pair.1) = %s := by decide +kernel
example : pairs.map (fun pair => replayTerm wordSnapshot 100000 pair.2) = %s := by decide +kernel
example : replayTerm wordSnapshot 100000 (differenceTerm pairs) = some %d := by decide +kernel
example : (CNFReplayCertificate.resultWord pairs Prod.fst initial).toNat = %d := by decide +kernel
example : (CNFReplayCertificate.resultWord pairs Prod.snd initial).toNat = %d := by decide +kernel
end Oak.CNFReplayTerm
`, snapshot, pairs, strings.Join(indices, ", "), len(left), roots(left), roots(right), difference, test.want[0], test.want[1])
			t.Run("kernel", func(t *testing.T) {
				lake, err := exec.LookPath("lake")
				if err != nil {
					requireOracle(t, "lake not on PATH; the formal workflow runs this kernel oracle")
				}
				path := filepath.Join(t.TempDir(), "NativeCNFReplayWordProductionPins.lean")
				if err := os.WriteFile(path, []byte(source), 0o600); err != nil {
					t.Fatal(err)
				}
				ctx, cancel := context.WithTimeout(context.Background(), 90*time.Second)
				defer cancel()
				// Resolve Lake's environment, then run Lean directly: cancelling
				// a lake wrapper can leave its child evaluating after the deadline.
				environment := exec.CommandContext(ctx, lake, "env")
				environment.Dir = filepath.Join("..", "spec", "lean")
				environment.WaitDelay = 2 * time.Second
				envOutput, err := environment.Output()
				if err != nil {
					t.Fatalf("resolving Lean environment: %v", err)
				}
				variables := strings.Split(strings.TrimSuffix(string(envOutput), "\n"), "\n")
				var sysroot string
				for i, variable := range variables {
					variable = strings.TrimSuffix(variable, "\r")
					variables[i] = variable
					if value, found := strings.CutPrefix(variable, "LEAN_SYSROOT="); found {
						sysroot = value
					}
				}
				if sysroot == "" {
					t.Fatal("Lake did not report LEAN_SYSROOT")
				}
				lean := filepath.Join(sysroot, "bin", "lean")
				if runtime.GOOS == "windows" {
					lean += ".exe"
				}
				command := exec.CommandContext(ctx, lean, path)
				command.Dir = environment.Dir
				command.Env = append(os.Environ(), variables...)
				command.WaitDelay = 2 * time.Second
				if output, err := command.CombinedOutput(); err != nil {
					t.Fatalf("kernel-checking word replay: %v (context: %v)\n%s", err, ctx.Err(), output)
				}
			})
		})
	}
}
