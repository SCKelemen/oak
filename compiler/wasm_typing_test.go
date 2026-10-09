package compiler

import (
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

type wasmTypingCase struct {
	name       string
	ins        encoding.Instruction
	stack, out []int // top first
	valid      bool
}

// Contract oracle independent of Lean's executable checker. Full binary
// validation below also compares these decisions with Go and Node/Deno.
func wasmTypingContract(ins encoding.Instruction, stack []int) ([]int, bool) {
	out := append([]int(nil), stack...)
	pop := func(w int) bool {
		if len(out) == 0 {
			return false
		}
		if w != 0 && out[0] != w {
			return false
		}
		out = out[1:]
		return true
	}
	push := func(w int) { out = append([]int{w}, out...) }
	op := ins.Opcode
	switch {
	case op == 0 || op == 1:
	case op == 26:
		if !pop(0) {
			return nil, false
		}
	case op >= 32 && op <= 34:
		if ins.Immediate < 0 || ins.Immediate > 1 {
			return nil, false
		}
		w := 32
		if ins.Immediate == 1 {
			w = 64
		}
		if op != 32 && !pop(w) {
			return nil, false
		}
		if op != 33 {
			push(w)
		}
	case op == 65:
		push(32)
	case op == 66:
		push(64)
	case op == 69:
		if !pop(32) {
			return nil, false
		}
		push(32)
	default:
		w, result := 32, 32
		if op >= 81 && op <= 90 {
			w = 64
		}
		if op >= 124 && op <= 133 {
			w, result = 64, 64
		}
		if !pop(w) || !pop(w) {
			return nil, false
		}
		push(result)
	}
	return out, true
}
func wasmTypingCases() []wasmTypingCase {
	var instructions []encoding.Instruction
	for _, op := range []byte{0, 1, 26, 65, 66, 69} {
		instructions = append(instructions, encoding.Instruction{Opcode: op})
	}
	for op := byte(32); op <= 34; op++ {
		for index := int64(0); index <= 2; index++ {
			instructions = append(instructions, encoding.Instruction{Opcode: op, Immediate: index})
		}
	}
	for _, interval := range [][2]byte{{70, 79}, {81, 90}, {106, 115}, {124, 133}} {
		for op := interval[0]; op <= interval[1]; op++ {
			instructions = append(instructions, encoding.Instruction{Opcode: op})
		}
	}
	var cases []wasmTypingCase
	for n := 0; n <= 3; n++ {
		for mask := 0; mask < 1<<n; mask++ {
			var stack []int
			for j := 0; j < n; j++ {
				w := 32
				if mask&(1<<j) != 0 {
					w = 64
				}
				stack = append(stack, w)
			}
			for _, ins := range instructions {
				out, valid := wasmTypingContract(ins, stack)
				cases = append(cases, wasmTypingCase{fmt.Sprintf("op%02x/imm%d/stack%v", ins.Opcode, ins.Immediate, stack), ins, stack, out, valid})
			}
		}
	}
	return cases
}

// One function with heterogeneous locals and a single i32 result. For accepted
// cases, storing every predicted result into a matching local verifies the
// complete output stack types, rather than hiding them behind untyped drops.
func wasmTypingModule(t *testing.T, plan []encoding.Instruction) []byte {
	t.Helper()
	code, err := encoding.Assemble(plan)
	if err != nil {
		t.Fatal(err)
	}
	module := []byte{0, 97, 115, 109, 1, 0, 0, 0, 1, 5, 1, 96, 0, 1, 127, 3, 2, 1, 0, 7, 8, 1, 4, 'm', 'a', 'i', 'n', 0, 0}
	body := append([]byte{2, 1, 127, 1, 126}, code...)
	body = append(body, 11)
	payload := encoding.AppendUnsigned([]byte{1}, uint64(len(body)))
	payload = append(payload, body...)
	module = encoding.AppendUnsigned(append(module, 10), uint64(len(payload)))
	return append(module, payload...)
}
func TestWasmTypingEngine(t *testing.T) {
	engine := wasmtest.Require(t)
	type row struct {
		Name, Module string
		Valid, Trap  bool
	}
	var rows []row
	for _, tc := range wasmTypingCases() {
		var plan []encoding.Instruction
		for j := len(tc.stack) - 1; j >= 0; j-- {
			plan = append(plan, wasmConstant(tc.stack[j], 0))
		}
		plan = append(plan, tc.ins)
		for _, w := range tc.out {
			index := int64(0)
			if w == 64 {
				index = 1
			}
			plan = append(plan, encoding.Instruction{Opcode: 33, Immediate: index})
		}
		plan = append(plan, wasmConstant(32, 42))
		module := wasmTypingModule(t, plan)
		_, err := check.Validate(module)
		if (err == nil) != tc.valid {
			t.Fatalf("%s: validator=%v, contract accepted=%v", tc.name, err, tc.valid)
		}
		op := tc.ins.Opcode
		trap := op == 0 || (op >= 109 && op <= 112) || (op >= 127 && op <= 130)
		rows = append(rows, row{tc.name, base64.StdEncoding.EncodeToString(module), tc.valid, trap})
	}
	// The reachable checker is intentionally conservative after unreachable;
	// the production validator still implements Core's polymorphic stack rule.
	boundary := wasmTypingModule(t, []encoding.Instruction{{Opcode: 0}, {Opcode: 106}})
	if _, err := check.Validate(boundary); err != nil {
		t.Fatal(err)
	}
	rows = append(rows, row{"unreachable-polymorphism-boundary", base64.StdEncoding.EncodeToString(boundary), true, true})
	data, err := json.Marshal(rows)
	if err != nil {
		t.Fatal(err)
	}
	path := filepath.Join(t.TempDir(), "typing.json")
	if err := os.WriteFile(path, data, 0600); err != nil {
		t.Fatal(err)
	}
	script := `const path=typeof Deno!=="undefined"?Deno.args[0]:process.argv[1];const rows=JSON.parse(typeof Deno!=="undefined"?Deno.readTextFileSync(path):require('fs').readFileSync(path,'utf8'));
for(const r of rows){const bytes=Uint8Array.from(atob(r.Module),c=>c.charCodeAt(0));if(WebAssembly.validate(bytes)!==r.Valid)throw Error(r.Name+': validation');if(!r.Valid)continue;
const f=new WebAssembly.Instance(new WebAssembly.Module(bytes),{}).exports.main;let v,trap=false;try{v=f()}catch(e){if(!(e instanceof WebAssembly.RuntimeError))throw e;trap=true}if(trap!==r.Trap||(!trap&&v!==42))throw Error(r.Name+': execution');}`
	ctx, cancel := context.WithTimeout(t.Context(), 60*time.Second)
	defer cancel()
	if out, err := engine.Command(ctx, script, path).CombinedOutput(); err != nil {
		t.Fatalf("engine: %v\n%s", err, out)
	}
	t.Logf("checked %d scalar stack contracts plus one unreachable boundary against Go and engine", len(rows)-1)
}

func TestWasmTypingLean(t *testing.T) {
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
	run("build", "Oak.WasmTyping")
	types := func(ws []int) string {
		var xs []string
		for _, w := range ws {
			xs = append(xs, fmt.Sprintf(".w%d", w))
		}
		return "[" + strings.Join(xs, ",") + "]"
	}
	var claims []string
	for _, tc := range wasmTypingCases() {
		expected := "none"
		if tc.valid {
			expected = "some " + types(tc.out)
		}
		claims = append(claims, fmt.Sprintf("-- %s\nexample : check #[.w32,.w64] (%d,%d) %s = %s := by decide +kernel\n", tc.name, tc.ins.Opcode, tc.ins.Immediate, types(tc.stack), expected))
	}
	seen := map[string]bool{}
	for _, tc := range wasmExecutionCases() {
		key := fmt.Sprintf("%d/%d/%s", tc.width, tc.plan[len(tc.plan)-1].Opcode, tc.fault)
		if seen[key] {
			continue
		}
		seen[key] = true
		var tokens []string
		for _, i := range tc.plan {
			tokens = append(tokens, fmt.Sprintf("(%d,%d)", i.Opcode, i.Immediate))
		}
		expected := fmt.Sprintf("[.w%d]", tc.resultWidth)
		if tc.fault == "unreachable" {
			expected = "[]"
		}
		claims = append(claims, fmt.Sprintf("example : checkSequence #[.w%d,.w%d] [%s] [] = some %s := by decide +kernel\n", tc.width, tc.width, strings.Join(tokens, ","), expected))
	}
	for _, claim := range []string{
		"check #[.w32] (32,-1) [] = none",
		"check #[.w32] (32,4294967296) [] = none",
		"check #[] (106,1) [.w32,.w32] = none",
		"check #[] (65,2147483648) [] = none",
		"check #[] (66,9223372036854775808) [] = none",
		"check #[] (255,0) [] = none",
		"check #[] (11,0) [] = none",
		"checkSequence #[] [(0,0),(106,0)] [] = none",
	} {
		claims = append(claims, "example : "+claim+" := by decide +kernel\n")
	}
	for start := 0; start < len(claims); start += 64 {
		end := min(start+64, len(claims))
		p := filepath.Join(t.TempDir(), "Typing.lean")
		source := "import Oak.WasmTyping\nopen Oak.WasmExecution Oak.WasmTyping\nset_option maxRecDepth 8192\n" + strings.Join(claims[start:end], "\n")
		if err := os.WriteFile(p, []byte(source), 0600); err != nil {
			t.Fatal(err)
		}
		run("env", "lean", p)
		t.Logf("kernel checked typing cases %d–%d of %d", start+1, end, len(claims))
	}
}
