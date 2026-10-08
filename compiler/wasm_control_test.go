package compiler

import (
	"context"
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"
	"time"

	"github.com/SCKelemen/oak/wasm/encoding"
)

// Expected values come from the source-level control scenarios, independently
// of Lean's label machine. Every case is also validated and run by a Wasm engine.
func wasmControlCases() []wasmExecutionCase {
	var cases []wasmExecutionCase
	ins := func(op byte, imm int64) encoding.Instruction { return encoding.Instruction{Opcode: op, Immediate: imm} }
	for _, width := range []int{32, 64} {
		resultType, add, sub, eq, ne := int64(127), byte(0x6a), byte(0x6b), byte(0x46), byte(0x47)
		if width == 64 {
			resultType, add, sub, eq, ne = 126, 0x7c, 0x7d, 0x51, 0x52
		}
		c := func(v uint64) encoding.Instruction { return wasmConstant(width, v) }
		appendCase := func(name string, plan []encoding.Instruction, want uint64, locals [2]uint64, fault string) {
			cases = append(cases, wasmExecutionCase{name: fmt.Sprintf("i%d/%s", width, name), width: width, resultWidth: width, plan: plan, want: want, locals: locals, fault: fault})
		}
		// The value below a block is isolated while executing its body, then restored.
		appendCase("block-fallthrough", []encoding.Instruction{c(10), ins(2, resultType), c(32), ins(11, 0), ins(add, 0)}, 42, [2]uint64{}, "")
		appendCase("loop-fallthrough", []encoding.Instruction{ins(3, 64), c(7), ins(0x21, 0), ins(11, 0), ins(0x20, 0)}, 7, [2]uint64{7, 0}, "")
		for depth := 0; depth <= 8; depth++ {
			plan := []encoding.Instruction{c(10), ins(2, resultType)}
			for i := 0; i < depth; i++ {
				plan = append(plan, c(77), ins(2, 64))
			}
			plan = append(plan, c(99), c(32), ins(12, int64(depth)), ins(0, 0))
			for i := 0; i < depth; i++ {
				plan = append(plan, ins(11, 0), ins(0x1a, 0))
			}
			plan = append(plan, ins(0, 0), ins(11, 0), ins(add, 0))
			appendCase(fmt.Sprintf("branch-depth-%d", depth), plan, 42, [2]uint64{}, "")
			// Both return and br to the implicit function label must unwind all labels.
			for _, op := range []byte{12, 15} {
				plan = []encoding.Instruction{}
				for i := 0; i < depth; i++ {
					plan = append(plan, ins(2, 64), ins(3, 64))
				}
				imm := int64(0)
				if op == 12 {
					imm = int64(2 * depth)
				}
				plan = append(plan, c(99), c(42), ins(op, imm), ins(0, 0))
				for i := 0; i < depth; i++ {
					plan = append(plan, ins(11, 0), ins(11, 0))
				}
				// A return inside a zero-result block does not make its outer continuation
				// statically unreachable, so finish that continuation with unreachable too.
				plan = append(plan, ins(0, 0))
				appendCase(fmt.Sprintf("function-exit-%d-depth-%d", op, depth), plan, 42, [2]uint64{}, "")
			}
		}
		for _, cond := range []uint64{0, 1, 2, 0x80000000, 0xffffffff} {
			choose := uint64(17)
			if cond != 0 {
				choose = 42
			}
			appendCase(fmt.Sprintf("if-%x", cond), []encoding.Instruction{wasmConstant(32, cond), ins(4, resultType), c(42), ins(5, 0), c(17), ins(11, 0)}, choose, [2]uint64{}, "")
			// br_if must preserve its result operand when the condition is false.
			want := uint64(43)
			if cond != 0 {
				want = 42
			}
			appendCase(fmt.Sprintf("br-if-%x", cond), []encoding.Instruction{ins(2, resultType), c(42), wasmConstant(32, cond), ins(13, 0), c(1), ins(add, 0), ins(11, 0)}, want, [2]uint64{}, "")
			local := uint64(0)
			if cond != 0 {
				local = 9
			}
			appendCase(fmt.Sprintf("if-no-else-%x", cond), []encoding.Instruction{wasmConstant(32, cond), ins(4, 64), c(9), ins(0x21, 0), ins(11, 0), ins(0x20, 0)}, local, [2]uint64{local, 0}, "")
			fault := ""
			if cond != 0 {
				fault = "unreachable"
			}
			appendCase(fmt.Sprintf("selected-trap-%x", cond), []encoding.Instruction{wasmConstant(32, cond), ins(4, resultType), ins(0, 0), ins(5, 0), c(17), ins(11, 0)}, 17, [2]uint64{}, fault)
			for _, inner := range []uint64{0, 1} {
				want = 23
				if cond != 0 {
					want = 17
					if inner != 0 {
						want = 42
					}
				}
				appendCase(fmt.Sprintf("nested-if-%x-%d", cond, inner), []encoding.Instruction{wasmConstant(32, cond), ins(4, resultType), wasmConstant(32, inner), ins(4, resultType), c(42), ins(5, 0), c(17), ins(11, 0), ins(5, 0), c(23), ins(11, 0)}, want, [2]uint64{}, "")
			}
		}
		// Restart an outer loop through intervening block labels. Saved stacks
		// belonging to those blocks must not leak into the next iteration.
		for depth := 1; depth <= 5; depth++ {
			for n := uint64(1); n <= 3; n++ {
				plan := []encoding.Instruction{c(n), ins(0x21, 0), c(10), ins(3, resultType), c(88)}
				for i := 0; i < depth; i++ {
					plan = append(plan, c(77), ins(2, 64))
				}
				plan = append(plan, c(99), ins(0x20, 0), c(1), ins(sub, 0), ins(0x22, 0), c(0), ins(ne, 0), ins(13, int64(depth)), ins(0x1a, 0))
				for i := 0; i < depth; i++ {
					plan = append(plan, ins(11, 0), ins(0x1a, 0))
				}
				plan = append(plan, ins(0x1a, 0), c(42), ins(11, 0), ins(add, 0))
				appendCase(fmt.Sprintf("outer-loop-%d-depth-%d", n, depth), plan, 52, [2]uint64{}, "")
			}
		}

		for n := uint64(0); n <= 10; n++ {
			// while n != 0 { sum += n; n -= 1 }; sum
			plan := []encoding.Instruction{c(n), ins(0x21, 0), ins(2, 64), ins(3, 64), ins(0x20, 0), c(0), ins(eq, 0), ins(13, 1), ins(0x20, 1), ins(0x20, 0), ins(add, 0), ins(0x21, 1), ins(0x20, 0), c(1), ins(sub, 0), ins(0x21, 0), ins(12, 0), ins(11, 0), ins(11, 0), ins(0x20, 1)}
			sum := n * (n + 1) / 2
			appendCase(fmt.Sprintf("sum-loop-%d", n), plan, sum, [2]uint64{0, sum}, "")
			if n > 0 {
				// A result-bearing loop still has a zero-arity branch target. Junk is
				// discarded on restart, but explicitly dropped on normal fallthrough.
				plan = []encoding.Instruction{c(n), ins(0x21, 0), ins(3, resultType), c(99), ins(0x20, 0), c(1), ins(sub, 0), ins(0x22, 0), c(0), ins(ne, 0), ins(13, 0), ins(0x1a, 0), c(42), ins(11, 0)}
				appendCase(fmt.Sprintf("result-loop-%d", n), plan, 42, [2]uint64{}, "")
			}
		}
	}
	return cases
}

func TestWasmControlEngine(t *testing.T)        { checkWasmExecutionCases(t, wasmControlCases(), nil) }
func TestE2ESelfHostedWasmControl(t *testing.T) { checkSelfHostedWasmExecution(t, wasmControlCases()) }

func TestWasmControlLean(t *testing.T) {
	lake := findLake()
	if lake == "" {
		if os.Getenv("OAK_REQUIRE_WASM_LEAN") == "1" {
			t.Fatal("OAK_REQUIRE_WASM_LEAN=1 requires lake")
		}
		t.Skip("lake unavailable; formal CI requires control execution checks")
	}
	root, err := filepath.Abs(filepath.Join("..", "spec", "lean"))
	if err != nil {
		t.Fatal(err)
	}
	run := func(args ...string) {
		t.Helper()
		ctx, cancel := context.WithTimeout(t.Context(), 4*time.Minute)
		defer cancel()
		cmd := exec.CommandContext(ctx, lake, args...)
		cmd.Dir = root
		if out, err := cmd.CombinedOutput(); err != nil {
			t.Fatalf("lake %v: %v\n%s", args, err, out)
		}
	}
	run("build", "Oak.WasmControl")
	var claims []string
	for _, tc := range wasmControlCases() {
		code, err := encoding.Assemble(tc.plan)
		if err != nil {
			t.Fatal(err)
		}
		bytes := append(append([]byte(nil), code...), 255, 128)
		expected := fmt.Sprintf(".ok (({stack := [.i%d %d], locals := #[.i%d %d, .i%d %d]} : State), [255,128])", tc.width, tc.want, tc.width, tc.locals[0], tc.width, tc.locals[1])
		if tc.fault != "" {
			expected = ".error (.scalar (.trap ." + tc.fault + "))"
		}
		claims = append(claims, fmt.Sprintf("-- %s\nexample : executeBytes %d 512 %s [.w%d] #[.i%d 0,.i%d 0] = %s := by decide +kernel\n", tc.name, len(tc.plan), strings.Replace(wasmLeanArray(bytes), "#[", "[", 1), tc.width, tc.width, tc.width, expected))
	}
	// Invalid-state diagnostics, full-body delimiter checking, fuel exhaustion,
	// and explicit call refusal are distinct from Core runtime traps.
	for _, tc := range []struct {
		code, results, expected string
		fuel                    int
	}{
		{"[(11,0)]", "[]", ".error .malformedControl", 32},
		{"[(5,0)]", "[]", ".error .malformedControl", 32},
		{"[(2,64)]", "[]", ".error .malformedControl", 32},
		{"[(2,64),(5,0),(11,0)]", "[]", ".error .malformedControl", 32},
		{"[(65,0),(4,64),(5,0),(5,0),(11,0)]", "[]", ".error .malformedControl", 32},
		{"[(0,0),(2,64)]", "[]", ".error .malformedControl", 32},
		{"[(12,1)]", "[]", ".error .labelOutOfBounds", 32},
		{"[(12,-1)]", "[]", ".error (.scalar .malformed)", 32},
		{"[(4,64),(11,0)]", "[]", ".error (.scalar .stackUnderflow)", 32},
		{"[(66,0),(4,64),(11,0)]", "[]", ".error (.scalar .typeMismatch)", 32},
		{"[(65,1),(2,127),(11,0)]", "[.w32]", ".error .resultMismatch", 32},
		{"[(2,127),(66,1),(11,0)]", "[.w32]", ".error (.scalar .typeMismatch)", 32},
		{"[(2,127),(65,1),(65,2),(11,0)]", "[.w32]", ".error .resultMismatch", 32},
		{"[(65,1),(2,64),(26,0),(11,0)]", "[]", ".error (.scalar .stackUnderflow)", 32},
		{"[(2,127),(12,0),(11,0)]", "[.w32]", ".error (.scalar .stackUnderflow)", 32},
		{"[(2,127),(66,1),(12,0),(11,0)]", "[.w32]", ".error (.scalar .typeMismatch)", 32},
		{"[(15,0)]", "[.w32]", ".error (.scalar .stackUnderflow)", 32},
		{"[(16,0)]", "[]", ".error (.scalar .unsupported)", 32},
		{"[(3,64),(12,0),(11,0)]", "[]", ".error .exhausted", 32},
		{"[]", "[]", ".error .exhausted", 0},
		{"[]", "[]", ".ok ({stack := [],locals := #[]} : State)", 1},
		{"[(0,0)]", "[]", ".error (.scalar (.trap .unreachable))", 1},
	} {
		claims = append(claims, fmt.Sprintf("example : execute %d %s %s #[] = %s := by decide +kernel\n", tc.fuel, tc.code, tc.results, tc.expected))
	}
	dir := t.TempDir()
	for start := 0; start < len(claims); start += 32 {
		end := min(start+32, len(claims))
		path := filepath.Join(dir, fmt.Sprintf("WasmControl%d.lean", start/32))
		source := "import Oak.WasmControl\nopen Oak.WasmExecution Oak.WasmControl\nderiving instance DecidableEq for Except\nset_option maxRecDepth 16384\nset_option maxHeartbeats 2000000\n" + strings.Join(claims[start:end], "\n")
		if err := os.WriteFile(path, []byte(source), 0600); err != nil {
			t.Fatal(err)
		}
		run("env", "lean", path)
		t.Logf("kernel checked control cases %d–%d of %d", start+1, end, len(claims))
	}
}
