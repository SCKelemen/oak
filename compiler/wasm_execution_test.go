package compiler

import (
	"bytes"
	"context"
	"encoding/base64"
	"encoding/json"
	"fmt"
	"math/big"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"
	"time"

	"github.com/SCKelemen/oak/internal/wasmtest"
	"github.com/SCKelemen/oak/wasm/check"
	"github.com/SCKelemen/oak/wasm/encoding"
)

// Shared by the Lean decoder/executor and an independent WebAssembly engine.
// Expected arithmetic uses mathematical integers, not the Lean opcode dispatch.
type wasmExecutionCase struct {
	name               string
	width, resultWidth int
	plan               []encoding.Instruction
	want               uint64
	fault              string
	locals             [2]uint64
}

func wasmSigned(v uint64, width int) *big.Int {
	x := new(big.Int).SetUint64(v)
	if v>>(width-1) != 0 {
		x.Sub(x, new(big.Int).Lsh(big.NewInt(1), uint(width)))
	}
	return x
}

func wasmConstant(width int, v uint64) encoding.Instruction {
	if width == 32 {
		return encoding.Instruction{Opcode: 0x41, Immediate: int64(int32(v))}
	}
	return encoding.Instruction{Opcode: 0x42, Immediate: int64(v)}
}

func wasmExecutionCases() []wasmExecutionCase {
	var cases []wasmExecutionCase
	for _, width := range []int{32, 64} {
		max := ^uint64(0)
		if width == 32 {
			max = 1<<32 - 1
		}
		min := uint64(1) << (width - 1)
		values := []uint64{0, 1, 2, 63, max, min, min - 1}
		binaryBase, compareBase := byte(0x6a), byte(0x46)
		if width == 64 {
			binaryBase, compareBase = 0x7c, 0x51
		}
		for _, a := range values {
			for _, b := range values {
				ua, ub := new(big.Int).SetUint64(a), new(big.Int).SetUint64(b)
				sa, sb := wasmSigned(a, width), wasmSigned(b, width)
				for kind := 0; kind < 10; kind++ {
					tc := wasmExecutionCase{name: fmt.Sprintf("i%d/binary%d/%x/%x", width, kind, a, b), width: width, resultWidth: width,
						plan: []encoding.Instruction{wasmConstant(width, a), wasmConstant(width, b), {Opcode: binaryBase + byte(kind)}}}
					v := new(big.Int)
					switch kind {
					case 0:
						v.Add(ua, ub)
					case 1:
						v.Sub(ua, ub)
					case 2:
						v.Mul(ua, ub)
					case 3, 4, 5, 6:
						if b == 0 {
							tc.fault = "divideByZero"
						} else if kind == 3 && a == min && b == max {
							tc.fault = "integerOverflow"
						} else {
							switch kind {
							case 3:
								v.Quo(sa, sb)
							case 4:
								v.Quo(ua, ub)
							case 5:
								v.Rem(sa, sb)
							case 6:
								v.Rem(ua, ub)
							}
						}
					case 7:
						v.And(ua, ub)
					case 8:
						v.Or(ua, ub)
					case 9:
						v.Xor(ua, ub)
					}
					tc.want = v.Mod(v, new(big.Int).Lsh(big.NewInt(1), uint(width))).Uint64()
					cases = append(cases, tc)
				}
				cs, cu := sa.Cmp(sb), ua.Cmp(ub)
				yes := []bool{cu == 0, cu != 0, cs < 0, cu < 0, cs > 0, cu > 0, cs <= 0, cu <= 0, cs >= 0, cu >= 0}
				for kind, ok := range yes {
					tc := wasmExecutionCase{name: fmt.Sprintf("i%d/compare%d/%x/%x", width, kind, a, b), width: width, resultWidth: 32,
						plan: []encoding.Instruction{wasmConstant(width, a), wasmConstant(width, b), {Opcode: compareBase + byte(kind)}}}
					if ok {
						tc.want = 1
					}
					cases = append(cases, tc)
				}
			}
		}
		for _, a := range values {
			if width == 32 {
				tc := wasmExecutionCase{name: fmt.Sprintf("eqz/%x", a), width: 32, resultWidth: 32, plan: []encoding.Instruction{wasmConstant(32, a), {Opcode: 0x45}}}
				if a == 0 {
					tc.want = 1
				}
				cases = append(cases, tc)
			}
			// set consumes, tee retains, get reloads; nop and drop frame the result.
			tc := wasmExecutionCase{name: fmt.Sprintf("locals/i%d/%x", width, a), width: width, resultWidth: width, want: a, locals: [2]uint64{a, a},
				plan: []encoding.Instruction{wasmConstant(width, a), {Opcode: 0x21, Immediate: 0}, {Opcode: 0x20, Immediate: 0}, {Opcode: 0x22, Immediate: 1},
					{Opcode: 0x1a}, {Opcode: 0x01}, {Opcode: 0x20, Immediate: 1}}}
			cases = append(cases, tc)
		}
		cases = append(cases, wasmExecutionCase{name: fmt.Sprintf("unreachable/i%d", width), width: width, resultWidth: width,
			fault: "unreachable", plan: []encoding.Instruction{{Opcode: 0}}})
	}
	return cases
}

func wasmExecutionModule(t *testing.T, tc wasmExecutionCase, code []byte) []byte {
	t.Helper()
	valType := byte(0x7f)
	if tc.width == 64 {
		valType = 0x7e
	}
	resultType := byte(0x7f)
	if tc.resultWidth == 64 {
		resultType = 0x7e
	}
	module := []byte{0, 97, 115, 109, 1, 0, 0, 0, 1, 5, 1, 0x60, 0, 1, resultType, 3, 2, 1, 0, 7, 8, 1, 4, 'm', 'a', 'i', 'n', 0, 0}
	body := append([]byte{1, 2, valType}, code...)
	body = append(body, 0x0b) // The function delimiter is outside the straight-line model.
	payload := encoding.AppendUnsigned([]byte{1}, uint64(len(body)))
	payload = append(payload, body...)
	module = encoding.AppendUnsigned(append(module, 10), uint64(len(payload)))
	module = append(module, payload...)
	if _, err := check.Validate(module); err != nil {
		t.Fatalf("%s: validator: %v", tc.name, err)
	}
	return module
}

func TestWasmExecutionEngine(t *testing.T) {
	checkWasmExecutionCases(t, wasmExecutionCases(), nil)
}

func checkWasmExecutionCases(t *testing.T, cases []wasmExecutionCase, bodies [][]byte) {
	t.Helper()
	engine := wasmtest.Require(t)
	type row struct {
		Name   string
		Module string
		Width  int
		Want   string
		Trap   bool
	}
	var rows []row
	for i, tc := range cases {
		code, err := encoding.Assemble(tc.plan)
		if err != nil {
			t.Fatal(err)
		}
		if bodies != nil {
			if !bytes.Equal(bodies[i], code) {
				t.Fatalf("%s: compiled Oak bytes %x, want %x", tc.name, bodies[i], code)
			}
			code = bodies[i]
		}
		module := wasmExecutionModule(t, tc, code)
		rows = append(rows, row{tc.name, base64.StdEncoding.EncodeToString(module), tc.resultWidth, fmt.Sprint(tc.want), tc.fault != ""})
	}
	data, err := json.Marshal(rows)
	if err != nil {
		t.Fatal(err)
	}
	path := filepath.Join(t.TempDir(), "cases.json")
	if err := os.WriteFile(path, data, 0600); err != nil {
		t.Fatal(err)
	}
	script := `const path=typeof Deno!=="undefined"?Deno.args[0]:process.argv[1];
const rows=JSON.parse(typeof Deno!=="undefined"?Deno.readTextFileSync(path):require('fs').readFileSync(path,'utf8'));
for(const r of rows){
 const bytes=Uint8Array.from(atob(r.Module),c=>c.charCodeAt(0));
 const f=new WebAssembly.Instance(new WebAssembly.Module(bytes),{}).exports.main;
 let value,trapped=false;
 try{value=f();}catch(e){if(!(e instanceof WebAssembly.RuntimeError))throw e;trapped=true;}
 if(trapped!==r.Trap)throw Error(r.Name+': trap mismatch');
 if(!trapped&&BigInt.asUintN(r.Width,BigInt(value))!==BigInt(r.Want))throw Error(r.Name+': value mismatch '+value);
}`
	ctx, cancel := context.WithTimeout(t.Context(), 60*time.Second)
	defer cancel()
	if out, err := engine.Command(ctx, script, path).CombinedOutput(); err != nil {
		t.Fatalf("Wasm engine: %v\n%s", err, out)
	}
	t.Logf("independently executed %d shared numeric/local/trap cases", len(rows))
}

// Exercise actual compiled Oak bytes for every modeled operation family and
// every modeled trap category. The larger Go/Lean corpus shares these cases.
func TestE2ESelfHostedWasmDecodedExecution(t *testing.T) {
	var cases []wasmExecutionCase
	seen := map[string]bool{}
	for _, tc := range wasmExecutionCases() {
		last := tc.plan[len(tc.plan)-1].Opcode
		key := fmt.Sprintf("%d/%d/%s", tc.width, last, tc.fault)
		if !seen[key] {
			seen[key] = true
			cases = append(cases, tc)
		}
	}
	core, err := os.ReadFile(filepath.Join("..", "asm", "selfhost", "wasm.oak"))
	if err != nil {
		t.Fatal(err)
	}
	var source strings.Builder
	source.Write(core)
	source.WriteString("\nputchar: (ch: c.Int): c.Int = c.extern(\"putchar\")\nmain: (): i32 {\n  bytes: [64]u8\n  count: u32 = 0\n  cursor: u32 = 0\n")
	var sizes []int
	for i, tc := range cases {
		code, err := encoding.Assemble(tc.plan)
		if err != nil {
			t.Fatal(err)
		}
		sizes = append(sizes, len(code))
		fmt.Fprintf(&source, "  plan_%d: [%d]WasmInstruction = [", i, len(tc.plan))
		for j, ins := range tc.plan {
			if j != 0 {
				source.WriteByte(',')
			}
			fmt.Fprintf(&source, "WasmInstruction { opcode: u32(%d), immediate: i64_bits_u64(u64(%d)) }", ins.Opcode, uint64(ins.Immediate))
		}
		source.WriteString("]\n")
		fmt.Fprintf(&source, "  true ? { dst: [*]u8 = span(&bytes)\n    r: WasmAssembly = wasm_assemble(dst, u32(0), view(&plan_%d))\n    assert(r.status == u32(0))\n    assert(r.size == u32(%d))\n    count = r.size\n  }\n", i, len(code))
		source.WriteString("  cursor = u32(0)\n  while cursor < count { putchar(c.Int(i32_bits_u32(u32(bytes[cursor])))); cursor = cursor + u32(1) }\n")
	}
	source.WriteString("  0\n}\n")
	out, exit, abnormal := buildAndRunOutput(t, "selfhost_wasm_decoded_execution", source.String())
	if abnormal || exit != 0 {
		t.Fatalf("compiled Oak: exit %d, abnormal %v", exit, abnormal)
	}
	var bodies [][]byte
	pos := 0
	for _, n := range sizes {
		if pos+n > len(out) {
			t.Fatal("compiled Oak output truncated")
		}
		bodies = append(bodies, []byte(out[pos:pos+n]))
		pos += n
	}
	if pos != len(out) {
		t.Fatal("compiled Oak emitted trailing bytes")
	}
	checkWasmExecutionCases(t, cases, bodies)
}

func TestWasmExecutionLean(t *testing.T) {
	lake := findLake()
	if lake == "" {
		if os.Getenv("OAK_REQUIRE_WASM_LEAN") == "1" {
			t.Fatal("OAK_REQUIRE_WASM_LEAN=1 requires lake")
		}
		t.Skip("lake unavailable; formal CI requires decoded execution checks")
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
	run("build", "Oak.WasmExecution")
	var claims []string
	for _, tc := range wasmExecutionCases() {
		code, err := encoding.Assemble(tc.plan)
		if err != nil {
			t.Fatal(err)
		}
		// An unparseable suffix and a deeper stack sentinel check the prefix/frame.
		bytes := append(append([]byte(nil), code...), 255, 128)
		input := fmt.Sprintf("({stack := [.i64 17], locals := #[.i%d 0, .i%d 0]} : State)", tc.width, tc.width)
		expected := fmt.Sprintf(".ok (({stack := [.i%d %d, .i64 17], locals := #[.i%d %d, .i%d %d]} : State), [255,128])",
			tc.resultWidth, tc.want, tc.width, tc.locals[0], tc.width, tc.locals[1])
		if tc.fault != "" {
			expected = ".error (.trap ." + tc.fault + ")"
		}
		claims = append(claims, fmt.Sprintf("-- %s\nexample : runBytes %d %s %s = %s := by decide +kernel\n", tc.name, len(tc.plan), strings.Replace(wasmLeanArray(bytes), "#[", "[", 1), input, expected))
	}
	// Error categories stay separate from runtime traps; none may execute control
	// delimiters as no-ops, coerce a mixed stack, or wrap a bad local index.
	claims = append(claims,
		"example : runBytes 1 [255] {} = .error .malformed := by decide +kernel\n",
		"example : runBytes 1 [65,128] {} = .error .malformed := by decide +kernel\n",
		"example : runBytes 1 [11] {} = .error .unsupported := by decide +kernel\n",
		"example : runBytes 1 [106] {} = .error .stackUnderflow := by decide +kernel\n",
		"example : runBytes 1 [106] {stack := [.i32 1,.i64 2]} = .error .typeMismatch := by decide +kernel\n",
		"example : runBytes 1 [32,0] {} = .error .localOutOfBounds := by decide +kernel\n",
		"example : runBytes 1 [33,0] {stack := [.i64 1],locals := #[.i32 0]} = .error .typeMismatch := by decide +kernel\n",
		"example : step (32,-1) {locals := #[.i32 0]} = .error .malformed := by decide +kernel\n",
		"example : step (106,1) {stack := [.i32 1,.i32 2]} = .error .malformed := by decide +kernel\n",
		"example : runBytes 2 [0,255] {} = .error (.trap .unreachable) := by decide +kernel\n",
	)
	dir := t.TempDir()
	for start := 0; start < len(claims); start += 64 {
		end := min(start+64, len(claims))
		path := filepath.Join(dir, fmt.Sprintf("WasmExecution%d.lean", start/64))
		source := "import Oak.WasmExecution\nopen Oak.WasmExecution\nderiving instance DecidableEq for Except\nset_option maxRecDepth 8192\n" + strings.Join(claims[start:end], "\n")
		if err := os.WriteFile(path, []byte(source), 0600); err != nil {
			t.Fatal(err)
		}
		run("env", "lean", path)
		t.Logf("kernel checked execution cases %d–%d of %d", start+1, end, len(claims))
	}
}
