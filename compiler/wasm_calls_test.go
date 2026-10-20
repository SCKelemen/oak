package compiler

import (
	"bytes"
	"context"
	"encoding/base64"
	"encoding/json"
	"fmt"
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

type wasmCallFunction struct {
	params, results, locals []int
	body                    []encoding.Instruction
}
type wasmCallCase struct {
	name  string
	funcs []wasmCallFunction
	width int
	want  uint64
	fault string
}

func wasmCallCases() []wasmCallCase {
	var cases []wasmCallCase
	i := func(op byte, v int64) encoding.Instruction { return encoding.Instruction{Opcode: op, Immediate: v} }
	for _, w := range []int{32, 64} {
		c := func(v uint64) encoding.Instruction { return wasmConstant(w, v) }
		add, sub, eq, mul := byte(0x6a), byte(0x6b), byte(0x46), byte(0x6c)
		bt := int64(127)
		if w == 64 {
			add, sub, eq, mul, bt = 0x7c, 0x7d, 0x51, 0x7e, 126
		}
		for _, a := range []uint64{0, 1, 17, 0x7fffffff, 0x80000000} {
			for _, b := range []uint64{0, 1, 7, 0xffffffff} {
				// Caller local 0 is seven; the callee overwrites its own parameter 0.
				// A zero-initialized extra local contributes zero to the result.
				callee := wasmCallFunction{params: []int{w, w}, results: []int{w}, locals: []int{w}, body: []encoding.Instruction{i(32, 0), i(32, 1), i(sub, 0), i(32, 2), i(add, 0), c(99), i(33, 0), i(15, 0), i(0, 0)}}
				main := wasmCallFunction{results: []int{w}, locals: []int{w}, body: []encoding.Instruction{c(7), i(33, 0), c(10), i(2, bt), c(a), c(b), i(16, 1), i(32, 0), i(add, 0), i(11, 0), i(add, 0)}}
				want := a - b + 17
				if w == 32 {
					want = uint64(uint32(want))
				}
				cases = append(cases, wasmCallCase{fmt.Sprintf("order-isolation/i%d/%d/%d", w, a, b), []wasmCallFunction{main, callee}, w, want, ""})
				wrapper := wasmCallFunction{params: []int{w, w}, results: []int{w}, body: []encoding.Instruction{i(32, 0), i(32, 1), i(16, 2)}}
				cases = append(cases, wasmCallCase{fmt.Sprintf("nested/i%d/%d/%d", w, a, b), []wasmCallFunction{main, wrapper, callee}, w, want, ""})
			}
		}
		for n := uint64(0); n <= 8; n++ {
			// factorial(n), including recursive argument and return transfer.
			rec := wasmCallFunction{params: []int{w}, results: []int{w}, body: []encoding.Instruction{i(32, 0), c(0), i(eq, 0), i(4, bt), c(1), i(5, 0), i(32, 0), i(32, 0), c(1), i(sub, 0), i(16, 1), i(mul, 0), i(11, 0)}}
			main := wasmCallFunction{results: []int{w}, body: []encoding.Instruction{c(n), i(16, 1)}}
			want := uint64(1)
			for k := uint64(1); k <= n; k++ {
				want *= k
			}
			cases = append(cases, wasmCallCase{fmt.Sprintf("recursive/i%d/%d", w, n), []wasmCallFunction{main, rec}, w, want, ""})
		}
		// Mutually recursive parity functions exercise non-self recursive lookup.
		for n := uint64(0); n <= 8; n++ {
			main := wasmCallFunction{results: []int{w}, body: []encoding.Instruction{c(n), i(16, 1)}}
			var fs []wasmCallFunction
			fs = append(fs, main)
			for k := 0; k < 2; k++ {
				fs = append(fs, wasmCallFunction{params: []int{w}, results: []int{w}, body: []encoding.Instruction{i(32, 0), c(0), i(eq, 0), i(4, bt), c(uint64(k)), i(5, 0), i(32, 0), c(1), i(sub, 0), i(16, int64(2-k)), i(11, 0)}})
			}
			cases = append(cases, wasmCallCase{fmt.Sprintf("mutual/i%d/%d", w, n), fs, w, n % 2, ""})
		}
		cases = append(cases, wasmCallCase{fmt.Sprintf("fresh-locals/i%d", w), []wasmCallFunction{
			{results: []int{w}, body: []encoding.Instruction{i(16, 1), i(16, 1), i(add, 0)}},
			{results: []int{w}, locals: []int{w}, body: []encoding.Instruction{i(32, 0), c(99), i(33, 0)}},
		}, w, 0, ""})

		for _, op := range []byte{15, 12} {
			// Return and br 0 in a callee exit that function, not the caller's block.
			main := wasmCallFunction{results: []int{w}, body: []encoding.Instruction{i(2, bt), i(16, 1), c(1), i(add, 0), i(11, 0)}}
			f := wasmCallFunction{results: []int{w}, body: []encoding.Instruction{c(99), c(41), i(op, 0), i(0, 0)}}
			cases = append(cases, wasmCallCase{fmt.Sprintf("callee-exit/i%d/%d", w, op), []wasmCallFunction{main, f}, w, 42, ""})
		}
		main := wasmCallFunction{results: []int{w}, body: []encoding.Instruction{i(16, 1)}}
		wrapper := wasmCallFunction{results: []int{w}, body: []encoding.Instruction{i(16, 2)}}
		for _, fault := range []string{"unreachable", "divideByZero", "integerOverflow"} {
			div := byte(0x6d)
			min := uint64(1) << 31
			minus := uint64(0xffffffff)
			if w == 64 {
				div = 0x7f
				min = uint64(1) << 63
				minus = ^uint64(0)
			}
			body := []encoding.Instruction{i(0, 0)}
			if fault == "divideByZero" {
				body = []encoding.Instruction{c(1), c(0), i(div, 0)}
			}
			if fault == "integerOverflow" {
				body = []encoding.Instruction{c(min), c(minus), i(div, 0)}
			}
			cases = append(cases, wasmCallCase{fmt.Sprintf("nested-trap/i%d/%s", w, fault), []wasmCallFunction{main, wrapper, {results: []int{w}, body: body}}, w, 0, fault})
		}
		// Void call mutates only its own fresh local; caller continues with a value.
		cases = append(cases, wasmCallCase{fmt.Sprintf("void/i%d", w), []wasmCallFunction{{results: []int{w}, body: []encoding.Instruction{i(16, 1), c(42)}}, {locals: []int{w}, body: []encoding.Instruction{c(99), i(33, 0)}}}, w, 42, ""})
	}
	// Mixed parameter widths catch reversal that homogeneous signatures can hide.
	for _, index := range []int64{0, 1, 2} {
		w := 32
		if index == 1 {
			w = 64
		}
		cases = append(cases, wasmCallCase{fmt.Sprintf("mixed/%d", index), []wasmCallFunction{{results: []int{w}, body: []encoding.Instruction{wasmConstant(32, 11), wasmConstant(64, 22), wasmConstant(32, 33), i(16, 1)}}, {params: []int{32, 64, 32}, results: []int{w}, body: []encoding.Instruction{i(32, index)}}}, w, uint64(index+1) * 11, ""})
	}
	return cases
}

func wasmCallModule(t *testing.T, tc wasmCallCase, bodies [][]byte) []byte {
	t.Helper()
	module := []byte{0, 97, 115, 109, 1, 0, 0, 0}
	section := func(id byte, p []byte) {
		module = encoding.AppendUnsigned(append(module, id), uint64(len(p)))
		module = append(module, p...)
	}
	vec := func(widths []int) []byte {
		b := encoding.AppendUnsigned(nil, uint64(len(widths)))
		for _, w := range widths {
			if w == 32 {
				b = append(b, 0x7f)
			} else {
				b = append(b, 0x7e)
			}
		}
		return b
	}
	types := encoding.AppendUnsigned(nil, uint64(len(tc.funcs)))
	fs := encoding.AppendUnsigned(nil, uint64(len(tc.funcs)))
	code := encoding.AppendUnsigned(nil, uint64(len(tc.funcs)))
	for j, f := range tc.funcs {
		types = append(types, 0x60)
		types = append(types, vec(f.params)...)
		types = append(types, vec(f.results)...)
		fs = encoding.AppendUnsigned(fs, uint64(j))
		b := encoding.AppendUnsigned(nil, uint64(len(f.locals)))
		for _, w := range f.locals {
			b = append(b, 1)
			if w == 32 {
				b = append(b, 0x7f)
			} else {
				b = append(b, 0x7e)
			}
		}
		expected, err := encoding.Assemble(f.body)
		if err != nil {
			t.Fatal(err)
		}
		if bodies != nil {
			if !bytes.Equal(expected, bodies[j]) {
				t.Fatalf("%s function %d: compiled bytes differ", tc.name, j)
			}
			expected = bodies[j]
		}
		b = append(b, expected...)
		b = append(b, 11)
		code = encoding.AppendUnsigned(code, uint64(len(b)))
		code = append(code, b...)
	}
	section(1, types)
	section(3, fs)
	section(7, []byte{1, 4, 'm', 'a', 'i', 'n', 0, 0})
	section(10, code)
	if _, err := check.Validate(module); err != nil {
		t.Fatalf("%s: %v", tc.name, err)
	}
	return module
}

func checkWasmCalls(t *testing.T, selfhost bool) {
	t.Helper()
	engine := wasmtest.Require(t)
	cases := wasmCallCases()
	var bodies [][]byte
	if selfhost {
		var flat []wasmExecutionCase
		for _, tc := range cases {
			for _, f := range tc.funcs {
				flat = append(flat, wasmExecutionCase{name: tc.name, plan: f.body})
			}
		}
		bodies = assembleSelfHostedWasmBodies(t, flat)
	}
	type row struct {
		Name, Module, Want string
		Width              int
		Trap               bool
	}
	var rows []row
	pos := 0
	for _, tc := range cases {
		var bs [][]byte
		if selfhost {
			bs = bodies[pos : pos+len(tc.funcs)]
			pos += len(tc.funcs)
		}
		rows = append(rows, row{tc.name, base64.StdEncoding.EncodeToString(wasmCallModule(t, tc, bs)), fmt.Sprint(tc.want), tc.width, tc.fault != ""})
	}
	data, err := json.Marshal(rows)
	if err != nil {
		t.Fatal(err)
	}
	path := filepath.Join(t.TempDir(), "calls.json")
	if err = os.WriteFile(path, data, 0600); err != nil {
		t.Fatal(err)
	}
	script := `const path=typeof Deno!=="undefined"?Deno.args[0]:process.argv[1];
const rows=JSON.parse(typeof Deno!=="undefined"?Deno.readTextFileSync(path):require('fs').readFileSync(path,'utf8'));
for(const r of rows){const f=new WebAssembly.Instance(new WebAssembly.Module(Uint8Array.from(atob(r.Module),c=>c.charCodeAt(0))),{}).exports.main;
let v,trap=false;try{v=f()}catch(e){if(!(e instanceof WebAssembly.RuntimeError))throw e;trap=true}
if(trap!==r.Trap)throw Error(r.Name+': trap mismatch');if(!trap&&BigInt.asUintN(r.Width,BigInt(v))!==BigInt(r.Want))throw Error(r.Name+': value '+v);}`
	ctx, cancel := context.WithTimeout(t.Context(), 60*time.Second)
	defer cancel()
	if out, err := engine.Command(ctx, script, path).CombinedOutput(); err != nil {
		t.Fatalf("engine: %v\n%s", err, out)
	}
	t.Logf("executed %d call scenarios; compiled Oak=%v", len(cases), selfhost)
}
func TestWasmCallsEngine(t *testing.T)        { checkWasmCalls(t, false) }
func TestE2ESelfHostedWasmCalls(t *testing.T) { checkWasmCalls(t, true) }

func TestWasmCallsLean(t *testing.T) {
	lake := findLake()
	if lake == "" {
		if os.Getenv("OAK_REQUIRE_WASM_LEAN") == "1" {
			t.Fatal("lake required")
		}
		t.Skip("lake unavailable")
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
	run("build", "Oak.WasmCalls")
	widths := func(ws []int) string {
		var xs []string
		for _, w := range ws {
			xs = append(xs, fmt.Sprintf(".w%d", w))
		}
		return "[" + strings.Join(xs, ",") + "]"
	}
	var claims []string
	for _, tc := range wasmCallCases() {
		var definitions []string
		for _, f := range tc.funcs {
			b, err := encoding.Assemble(f.body)
			if err != nil {
				t.Fatal(err)
			}
			b = append(b, 255, 128)
			metadata := fmt.Sprintf("({params := %s,results := %s,locals := %s} : Function)", widths(f.params), widths(f.results), widths(f.locals))
			definitions = append(definitions, fmt.Sprintf("do let (f,suffix) ← decodeFunction %s %d %s; if suffix = [255,128] then some f else none", metadata, len(f.body), strings.Replace(wasmLeanArray(b), "#[", "[", 1)))
		}
		var expr strings.Builder
		expr.WriteString("(do\n")
		for j, d := range definitions {
			fmt.Fprintf(&expr, "let f%d ← (%s)\n", j, d)
		}
		expr.WriteString("some #[")
		for j := range definitions {
			if j > 0 {
				expr.WriteByte(',')
			}
			fmt.Fprintf(&expr, "f%d", j)
		}
		expr.WriteString("])")
		expected := fmt.Sprintf(".ok [.i%d %d]", tc.width, tc.want)
		if tc.fault != "" {
			expected = ".error (.control (.scalar (.trap ." + tc.fault + ")))"
		}
		claims = append(claims, fmt.Sprintf("-- %s\nexample : (%s : Option (Array Function)).map (fun fs => (invoke fs 0 1024 []).map (fun s => s.stack)) = some (%s) := by decide +kernel\n", tc.name, expr.String(), expected))
	}
	for _, claim := range []string{
		"invoke #[] 0 10 [] = .error .functionOutOfBounds",
		"invoke #[{body := [(16,1)]}] 0 10 [] = .error .functionOutOfBounds",
		"invoke #[{body := [(16,-1)]}] 0 10 [] = .error (.control (.scalar .malformed))",
		"invoke #[{body := [(16,0)]}] 0 10 [] = .error (.control .exhausted)",
		"invoke #[{params := [.w32]}] 0 10 [] = .error (.control (.scalar .typeMismatch))",
		"invoke #[{body := [(16,1)]},{params := [.w32]}] 0 10 [] = .error (.control (.scalar .stackUnderflow))",
		"invoke #[{body := [(66,0),(16,1)]},{params := [.w32]}] 0 10 [] = .error (.control (.scalar .typeMismatch))",
		"invoke #[{body := [(2,64),(16,1),(11,0)]},{body := [(12,1)]}] 0 10 [] = .error (.control .labelOutOfBounds)",
		"invoke #[{body := [(16,1)]},{body := [(32,0)]}] 0 10 [] = .error (.control (.scalar .localOutOfBounds))",
		"invoke #[{body := [(16,1)]},{results := [.w32]}] 0 10 [] = .error (.control .resultMismatch)",
		"invoke #[{body := [(16,1)]},{body := [(2,64)]}] 0 10 [] = .error (.control .malformedControl)",
	} {
		claims = append(claims, "example : "+claim+" := by decide +kernel\n")
	}
	for start := 0; start < len(claims); start += 16 {
		end := min(start+16, len(claims))
		p := filepath.Join(t.TempDir(), "Calls.lean")
		s := "import Oak.WasmCalls\nopen Oak.WasmExecution Oak.WasmCalls\nderiving instance DecidableEq for Except\nset_option maxRecDepth 16384\nset_option maxHeartbeats 4000000\n" + strings.Join(claims[start:end], "\n")
		if err := os.WriteFile(p, []byte(s), 0600); err != nil {
			t.Fatal(err)
		}
		run("env", "lean", p)
		t.Logf("kernel checked calls %d–%d of %d", start+1, end, len(claims))
	}
}
