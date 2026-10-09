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
	"github.com/SCKelemen/oak/optir"
	"github.com/SCKelemen/oak/wasm"
	"github.com/SCKelemen/oak/wasm/check"
	"github.com/SCKelemen/oak/wasm/encoding"
)

type wasmModuleCase struct {
	name   string
	bytes  []byte
	export string
	width  int
	want   uint64
	fault  string
	funcs  []wasmCallFunction // when present, independently assert all decoded metadata/tokens
}

type wasmTestSection struct {
	id   byte
	data []byte
}

func wasmTestU32(data []byte, pos *int) uint64 {
	var v uint64
	for shift := uint(0); ; shift += 7 {
		b := data[*pos]
		*pos++
		v |= uint64(b&127) << shift
		if b < 128 {
			return v
		}
	}
}
func wasmTestSections(data []byte) []wasmTestSection {
	var ss []wasmTestSection
	for pos := 8; pos < len(data); {
		id := data[pos]
		pos++
		n := int(wasmTestU32(data, &pos))
		ss = append(ss, wasmTestSection{id, append([]byte(nil), data[pos:pos+n]...)})
		pos += n
	}
	return ss
}
func wasmTestModule(ss []wasmTestSection, padded bool) []byte {
	out := []byte{0, 97, 115, 109, 1, 0, 0, 0}
	for _, s := range ss {
		out = append(out, s.id)
		n := encoding.AppendUnsigned(nil, uint64(len(s.data)))
		if padded {
			n[len(n)-1] |= 128
			n = append(n, 0)
		}
		out = append(out, n...)
		out = append(out, s.data...)
	}
	return out
}
func wasmModuleCases(t *testing.T) []wasmModuleCase {
	t.Helper()
	var cases []wasmModuleCase
	for _, tc := range wasmCallCases() {
		cases = append(cases, wasmModuleCase{tc.name, wasmCallModule(t, tc, nil), "main", tc.width, tc.want, tc.fault, tc.funcs})
	}
	// Permuted/reused type indices must resolve by index, not zip type/code order.
	tc := wasmCallCases()[1]
	ss := wasmTestSections(wasmCallModule(t, tc, nil))
	var types [][]byte
	pos := 0
	n := int(wasmTestU32(ss[0].data, &pos))
	for j := 0; j < n; j++ {
		start := pos
		pos++
		for k := 0; k < 2; k++ {
			count := int(wasmTestU32(ss[0].data, &pos))
			pos += count
		}
		types = append(types, ss[0].data[start:pos])
	}
	ss[0].data = encoding.AppendUnsigned(nil, uint64(n))
	ss[1].data = encoding.AppendUnsigned(nil, uint64(n))
	for j := n - 1; j >= 0; j-- {
		ss[0].data = append(ss[0].data, types[j]...)
	}
	for j := 0; j < n; j++ {
		ss[1].data = encoding.AppendUnsigned(ss[1].data, uint64(n-1-j))
	}
	cases = append(cases, wasmModuleCase{"permuted-types", wasmTestModule(ss, false), "main", tc.width, tc.want, tc.fault, tc.funcs})
	cases = append(cases, wasmModuleCase{"padded-section-lengths", wasmTestModule(ss, true), "main", tc.width, tc.want, tc.fault, tc.funcs})
	// Export a nonzero function under a UTF-8 name; two functions share one type.
	tc = wasmCallCase{name: "export-one", width: 32, want: 42, funcs: []wasmCallFunction{{results: []int{32}, body: []encoding.Instruction{{Opcode: 65, Immediate: 7}}}, {results: []int{32}, body: []encoding.Instruction{{Opcode: 65, Immediate: 42}}}}}
	ss = wasmTestSections(wasmCallModule(t, tc, nil))
	ss[0].data = []byte{1, 96, 0, 1, 127}
	ss[1].data = []byte{2, 0, 0}
	ss[2].data = []byte{1, 2, 0xcf, 0x80, 0, 1}
	cases = append(cases, wasmModuleCase{"shared-type-unicode-export", wasmTestModule(ss, false), "π", 32, 42, "", tc.funcs})
	// A grouped declaration is expanded into the exact local order.
	tc = wasmCallCase{name: "grouped-locals", width: 32, want: 42, funcs: []wasmCallFunction{{results: []int{32}, locals: []int{32, 32, 64}, body: []encoding.Instruction{{Opcode: 65, Immediate: 42}}}}}
	ss = wasmTestSections(wasmCallModule(t, tc, nil))
	ss[3].data = []byte{1, 8, 2, 2, 127, 1, 126, 65, 42, 11}
	cases = append(cases, wasmModuleCase{"grouped-locals", wasmTestModule(ss, false), "main", 32, 42, "", tc.funcs})
	// Complete binary artifacts from the production module emitter, not just
	// instruction bytes embedded in the test module envelope.
	for _, w := range []int{32, 64} {
		for _, v := range []int64{0, 42, -1} {
			typ := optir.Type(fmt.Sprintf("i%d", w))
			cfg := optir.CFG{Name: "main", Entry: 1, Results: []optir.Type{typ}, Blocks: []optir.Block{{ID: 1, Operations: []optir.Operation{{Code: optir.OpConstInt, Results: []optir.Value{{ID: 1, Type: typ}}, Attributes: []optir.Attribute{{Name: optir.AttributeValue, Value: fmt.Sprint(v)}}}}, Terminator: optir.Terminator{Kind: optir.TerminatorReturn, Values: []optir.ValueID{1}}}}}
			m, err := wasm.Emit([]optir.CFG{cfg})
			if err != nil {
				t.Fatal(err)
			}
			want := uint64(v)
			if w == 32 {
				want = uint64(uint32(v))
			}
			cases = append(cases, wasmModuleCase{fmt.Sprintf("production-module/i%d/%d", w, v), m.Bytes, "main", w, want, "", nil})
		}
	}
	return cases
}

func wasmModuleRefusals(t *testing.T) []wasmModuleCase {
	t.Helper()
	tc := wasmCallCase{name: "minimal", width: 32, funcs: []wasmCallFunction{{results: []int{32}, body: []encoding.Instruction{{Opcode: 65, Immediate: 42}}}}}
	base := wasmCallModule(t, tc, nil)
	var cases []wasmModuleCase
	for n := 0; n < len(base); n++ {
		cases = append(cases, wasmModuleCase{name: fmt.Sprintf("truncated-%d", n), bytes: base[:n]})
	}
	add := func(name string, section int, data []byte) {
		ss := wasmTestSections(base)
		ss[section].data = data
		cases = append(cases, wasmModuleCase{name: name, bytes: wasmTestModule(ss, false)})
	}
	add("type-index", 1, []byte{1, 1})
	add("empty-types", 0, []byte{0})
	add("no-functions", 1, []byte{0})
	add("code-count", 3, []byte{0})
	add("export-index", 2, []byte{1, 4, 'm', 'a', 'i', 'n', 0, 1})
	add("duplicate-exports", 2, []byte{2, 1, 'x', 0, 0, 1, 'x', 0, 0})
	add("empty-name", 2, []byte{1, 0, 0, 0})
	add("invalid-utf8", 2, []byte{1, 1, 255, 0, 0})
	add("nonfunction-export", 2, []byte{1, 1, 'x', 1, 0})
	add("extra-type-byte", 0, []byte{1, 96, 0, 1, 127, 0})
	add("float-type", 0, []byte{1, 96, 0, 1, 125})
	add("oversized-local-group", 3, []byte{1, 7, 1, 0xc2, 0x80, 1, 127, 11, 0})
	add("missing-body-end", 3, []byte{1, 3, 0, 65, 42})
	add("body-extra-end", 3, []byte{1, 5, 0, 65, 42, 11, 11})
	add("body-size-short", 3, []byte{1, 3, 0, 65, 42, 11})
	add("body-size-long", 3, []byte{1, 5, 0, 65, 42, 11})
	add("operand-truncated", 3, []byte{1, 2, 0, 65})
	add("unknown-instruction", 3, []byte{1, 3, 0, 255, 11})
	add("bad-nesting", 3, []byte{1, 5, 0, 2, 64, 0, 11})
	b := append([]byte(nil), base...)
	b[4] = 2
	cases = append(cases, wasmModuleCase{name: "version", bytes: b})
	cases = append(cases, wasmModuleCase{name: "trailing", bytes: append(append([]byte(nil), base...), 0)})
	ss := wasmTestSections(base)
	ss[0], ss[1] = ss[1], ss[0]
	cases = append(cases, wasmModuleCase{name: "section-order", bytes: wasmTestModule(ss, false)})
	ss = wasmTestSections(base)
	ss[1].id = 2
	cases = append(cases, wasmModuleCase{name: "import-section", bytes: wasmTestModule(ss, false)})
	return cases
}

func TestWasmModuleEngine(t *testing.T) {
	engine := wasmtest.Require(t)
	type row struct {
		Name, Module, Export, Want string
		Width                      int
		Trap                       bool
	}
	var rows []row
	for _, tc := range wasmModuleCases(t) {
		if _, err := check.Validate(tc.bytes); err != nil {
			t.Fatalf("%s: %v", tc.name, err)
		}
		rows = append(rows, row{tc.name, base64.StdEncoding.EncodeToString(tc.bytes), tc.export, fmt.Sprint(tc.want), tc.width, tc.fault != ""})
	}
	for _, tc := range wasmModuleRefusals(t) {
		if _, err := check.Validate(tc.bytes); err == nil {
			t.Fatalf("validator accepted %s", tc.name)
		}
	}
	data, err := json.Marshal(rows)
	if err != nil {
		t.Fatal(err)
	}
	path := filepath.Join(t.TempDir(), "modules.json")
	if err := os.WriteFile(path, data, 0600); err != nil {
		t.Fatal(err)
	}
	script := `const path=typeof Deno!=="undefined"?Deno.args[0]:process.argv[1];
const rows=JSON.parse(typeof Deno!=="undefined"?Deno.readTextFileSync(path):require('fs').readFileSync(path,'utf8'));
for(const r of rows){const f=new WebAssembly.Instance(new WebAssembly.Module(Uint8Array.from(atob(r.Module),c=>c.charCodeAt(0))),{}).exports[r.Export];let v,trap=false;
try{v=f()}catch(e){if(!(e instanceof WebAssembly.RuntimeError))throw e;trap=true}
if(trap!==r.Trap)throw Error(r.Name+': trap');if(!trap&&BigInt.asUintN(r.Width,BigInt(v))!==BigInt(r.Want))throw Error(r.Name+': value '+v);}`
	ctx, cancel := context.WithTimeout(t.Context(), 60*time.Second)
	defer cancel()
	if out, err := engine.Command(ctx, script, path).CombinedOutput(); err != nil {
		t.Fatalf("engine: %v\n%s", err, out)
	}
	t.Logf("executed %d complete modules; validator rejected %d structural corruptions", len(rows), len(wasmModuleRefusals(t)))
}

func TestWasmModuleLean(t *testing.T) {
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
	run("build", "Oak.WasmModule")
	list := func(b []byte) string { return strings.Replace(wasmLeanArray(b), "#[", "[", 1) }
	widths := func(ws []int) string {
		var xs []string
		for _, w := range ws {
			xs = append(xs, fmt.Sprintf(".w%d", w))
		}
		return "[" + strings.Join(xs, ",") + "]"
	}
	var claims []string
	for _, tc := range wasmModuleCases(t) {
		expected := fmt.Sprintf(".ok [.i%d %d]", tc.width, tc.want)
		if tc.fault != "" {
			expected = ".error (.control (.scalar (.trap ." + tc.fault + ")))"
		}
		claim := fmt.Sprintf("-- %s\nexample : ((invokeExport %s %s 2048 []).map (fun r => r.map (fun s => s.stack))) = some (%s) := by decide +kernel\n", tc.name, list(tc.bytes), list([]byte(tc.export)), expected)
		if tc.funcs != nil {
			var fs []string
			for _, f := range tc.funcs {
				var body []string
				for _, i := range f.body {
					body = append(body, fmt.Sprintf("(%d,%d)", i.Opcode, i.Immediate))
				}
				fs = append(fs, fmt.Sprintf("{params := %s, results := %s, locals := %s, body := [%s]}", widths(f.params), widths(f.results), widths(f.locals), strings.Join(body, ",")))
			}
			claim += fmt.Sprintf("example : (decode %s).map (fun m => m.functions) = some (#[%s] : Array Oak.WasmCalls.Function) := by decide +kernel\n", list(tc.bytes), strings.Join(fs, ","))
		}
		claims = append(claims, claim)
	}
	for _, tc := range wasmModuleRefusals(t) {
		claims = append(claims, fmt.Sprintf("-- %s\nexample : decode %s = none := by decide +kernel\n", tc.name, list(tc.bytes)))
	}
	// Structural acceptance is deliberately weaker than the production validator.
	// This well-framed but ill-typed body must decode and report a runtime-model
	// diagnostic; it must never be advertised as a validated executable module.
	tc := wasmModuleCases(t)[0]
	ss := wasmTestSections(tc.bytes)
	ss[3].data = []byte{2, 3, 0, 106, 11, 3, 0, 0, 11}
	badTyped := wasmTestModule(ss, false)
	if _, err := check.Validate(badTyped); err == nil {
		t.Fatal("validator accepted ill-typed boundary case")
	}
	claims = append(claims, fmt.Sprintf("example : invokeExport %s [109,97,105,110] 32 [] = some (.error (.control (.scalar .stackUnderflow))) := by decide +kernel\n", list(badTyped)))
	claims = append(claims, fmt.Sprintf("example : invokeExport %s [110,111] 32 [] = none := by decide +kernel\n", list(tc.bytes)))
	for start := 0; start < len(claims); start += 8 {
		end := min(start+8, len(claims))
		path := filepath.Join(t.TempDir(), "Module.lean")
		source := "import Oak.WasmModule\nopen Oak.WasmExecution Oak.WasmModule\nderiving instance DecidableEq for Except\nset_option maxRecDepth 32768\nset_option maxHeartbeats 4000000\n" + strings.Join(claims[start:end], "\n")
		if err := os.WriteFile(path, []byte(source), 0600); err != nil {
			t.Fatal(err)
		}
		run("env", "lean", path)
		t.Logf("kernel checked module rows %d–%d of %d", start+1, end, len(claims))
	}
}
