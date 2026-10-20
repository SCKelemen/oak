package compiler

import (
	"bytes"
	"context"
	"encoding/base64"
	"encoding/hex"
	"encoding/json"
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"
	"time"

	"github.com/SCKelemen/oak/internal/wasmtest"
)

type bitwiseModuleCase struct {
	name, symbol string
	source       string
	opcode       byte
	bytes        []byte
}

// This produces actual compiler output from source. Fixture agreement and the
// generated Lean claims are evidence for these exact artifacts, not a universal
// Go parser/lowering/emitter refinement or permission to enable -verified.
func bitwiseModuleCases(t *testing.T) []bitwiseModuleCase {
	t.Helper()
	cases := []bitwiseModuleCase{{name: "and", symbol: "&", opcode: 0x71}, {name: "or", symbol: "|", opcode: 0x72}, {name: "xor", symbol: "^", opcode: 0x73}}
	for i := range cases {
		tc := &cases[i]
		source := "bitwise: (x: u32, y: u32): u32 = x " + tc.symbol + " y\n"
		module, err := New().WithSource("bitwise.oak", source).EmitWasm().Get()
		if err != nil {
			t.Fatal(err)
		}
		if module.TranslationVerified || module.ByteValidation == nil || len(module.Exports) != 1 {
			t.Fatal("bitwise emission bypassed validation or claimed translation proof")
		}
		e := module.Exports[0]
		if e.Name != "bitwise" || len(e.Parameters) != 2 || e.Parameters[0] != "u32" || e.Parameters[1] != "u32" || e.Result != "u32" {
			t.Fatalf("wrong source-level signature: %+v", e)
		}
		want, err := hex.DecodeString("0061736d0100000001070160027f7f017f03020100070b01076269747769736500000a0901070020002001710b")
		if err != nil {
			t.Fatal(err)
		}
		want[len(want)-2] = tc.opcode
		if !bytes.Equal(module.Bytes, want) {
			t.Fatalf("%s production module changed: got %x, want %x", tc.name, module.Bytes, want)
		}
		tc.source = source
		tc.bytes = append([]byte(nil), module.Bytes...)
	}
	return cases
}

func TestWasmBitwiseModule(t *testing.T) {
	cases := bitwiseModuleCases(t)
	engine := wasmtest.Require(t)
	type row struct {
		Op    string `json:"op"`
		Bytes string `json:"bytes"`
	}
	var rows []row
	for _, tc := range cases {
		rows = append(rows, row{tc.name, base64.StdEncoding.EncodeToString(tc.bytes)})
	}
	data, err := json.Marshal(rows)
	if err != nil {
		t.Fatal(err)
	}
	script := `const arg=typeof Deno!=="undefined"?Deno.args[0]:process.argv[1];
const rows=JSON.parse(arg);
let seed=0x913be241;
const values=[0,1,2,0x7fffffff,0x80000000,0xffffffff,0xaaaaaaaa,0x55555555];
for(let i=0;i<64;i++){seed=(Math.imul(seed,1664525)+1013904223)>>>0;values.push(seed);}
for(const row of rows){
 const bytes=Uint8Array.from(atob(row.bytes),c=>c.charCodeAt(0));
 if(!WebAssembly.validate(bytes))throw Error("module validation failed");
 const module=new WebAssembly.Module(bytes);
 if(WebAssembly.Module.imports(module).length)throw Error("unexpected import");
 const exports=WebAssembly.Module.exports(module);
 if(exports.length!==1||exports[0].name!=="bitwise"||exports[0].kind!=="function")throw Error("wrong export");
 const fn=new WebAssembly.Instance(module,{}).exports.bitwise;
 for(const a of values)for(const b of values){
  const x=BigInt(a),y=BigInt(b);
  const want=Number(row.op==="and"?x&y:row.op==="or"?x|y:x^y);
  if((fn(a,b)>>>0)!==want)throw Error(row.op+" mismatch "+a+","+b);
 }
}`
	ctx, cancel := context.WithTimeout(t.Context(), 30*time.Second)
	defer cancel()
	if out, err := engine.Command(ctx, script, string(data)).CombinedOutput(); err != nil {
		t.Fatalf("bitwise module engine: %v\n%s", err, out)
	}
}

// Called by the existing required formal lane, not an optional new CI job.
func testWasmBitwiseModuleLean(t *testing.T) {
	t.Helper()
	lake := findLake()
	if lake == "" {
		t.Fatal("required bitwise module correspondence needs lake")
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
	run("build", "Oak.BitwiseSource")
	var source strings.Builder
	source.WriteString("import Oak.BitwiseSource\nopen Oak Oak.BitwiseFunction Oak.BitwiseModule\nset_option maxRecDepth 8192\n")
	for _, tc := range bitwiseModuleCases(t) {
		literal := strings.Replace(wasmLeanArray(tc.bytes), "#[", "[", 1)
		fmt.Fprintf(&source, "def actual_%s : List UInt8 := %s\n", tc.name, literal)
		original := strings.Replace(wasmLeanArray([]byte(tc.source)), "#[", "[", 1)
		fmt.Fprintf(&source, "def source_%s : List UInt8 := %s\n", tc.name, original)
		fmt.Fprintf(&source, "theorem actual_%s_source_bound (left right : BitVec 32) : BitwiseSource.Means source_%s (BitwiseSource.fixture .%s) left right (eval .%s left right) ∧ invokeModule entryName actual_%s left right = .ok (eval .%s left right) := by simpa only [BitwiseSource.fixture_name, BitwiseSource.fixture_op] using (BitwiseSource.accepted_source_to_module (by decide +kernel : BitwiseSource.accepts source_%s (BitwiseSource.fixture .%s) .wasm .wasmLocals actual_%s = true) left right)\n", tc.name, tc.name, tc.name, tc.name, tc.name, tc.name, tc.name, tc.name, tc.name)

		fmt.Fprintf(&source, "example : actual_%s = moduleBytes .%s := by decide +kernel\n", tc.name, tc.name)
		fmt.Fprintf(&source, "theorem actual_%s_success (left right : BitVec 32) : invokeModule entryName actual_%s left right = .ok (eval .%s left right) := admitted_module_success (by decide +kernel : acceptsModule .wasm .wasmLocals [32,32] 32 .%s entryName actual_%s = true) left right\n", tc.name, tc.name, tc.name, tc.name, tc.name)
	}
	// These cases deliberately vary declaration/parameter identity, contextual
	// identifiers, and export-name LEB length. The generic theorem, not this
	// finite table, is the source-semantics authority.
	for i, names := range [][3]string{
		{"mix", "left0", "Right9"},
		{"kernel", "forall", "exists"},
		{strings.Repeat("LongName", 16), "A1", "b2"},
	} {
		original := fmt.Sprintf("%s: (%s: u32, %s: u32): u32 = %s ^ %s\n", names[0], names[1], names[2], names[1], names[2])
		module, err := New().WithSource("source-bound.oak", original).EmitWasm().Get()
		if err != nil {
			t.Fatal(err)
		}
		if module.TranslationVerified || module.ByteValidation == nil {
			t.Fatal("source binding must not change production verification authority")
		}
		list := func(b []byte) string { return strings.Replace(wasmLeanArray(b), "#[", "[", 1) }
		fmt.Fprintf(&source, "def renamedSource%d : List UInt8 := %s\n", i, list([]byte(original)))
		fmt.Fprintf(&source, "def renamedModule%d : List UInt8 := %s\n", i, list(module.Bytes))
		fmt.Fprintf(&source, "def renamedClaim%d : BitwiseSource.Decl := ⟨%s, %s, %s, .xor⟩\n", i, list([]byte(names[0])), list([]byte(names[1])), list([]byte(names[2])))
		fmt.Fprintf(&source, "theorem renamed%d_source_bound (left right : BitVec 32) : BitwiseSource.Means renamedSource%d renamedClaim%d left right (eval .xor left right) ∧ invokeModule renamedClaim%d.name renamedModule%d left right = .ok (eval .xor left right) := BitwiseSource.accepted_source_to_module (by decide +kernel : BitwiseSource.accepts renamedSource%d renamedClaim%d .wasm .wasmLocals renamedModule%d = true) left right\n", i, i, i, i, i, i, i, i)
	}
	path := filepath.Join(t.TempDir(), "ActualBitwiseModules.lean")
	if err := os.WriteFile(path, []byte(source.String()), 0600); err != nil {
		t.Fatal(err)
	}
	run("env", "lean", path)
}
