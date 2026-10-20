package compiler

import (
	"bytes"
	"context"
	"crypto/sha256"
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

// This exact source is independently pinned in WasmCallComposition.source.
// Equality with it does not establish general source-parser/compiler refinement.
const wasmCallCompositionSource = `difference: (x: u32, y: u32): u32 {
  temp: u32 = x - y
  temp
}
reverse: (x: u32, y: u32): u32 {
  keep: u32 = u32(99)
  result: u32 = difference(y, x)
  result + keep - keep
}
main: (a: u32, b: u32): u32 {
  keep: u32 = a + u32(7)
  result: u32 = reverse(a, b)
  result - keep - keep
}
`

type wasmCompositionCase struct {
	name, source string
	bytes        []byte
	accepted     bool
	valid        bool
	coreOnly     bool
	// A valid byte mutation must observably change the intended result, trap,
	// or fail to provide main. Source-only changes have unchanged engine bytes.
	changed bool
}

func wasmCompositionCases(t *testing.T) []wasmCompositionCase {
	t.Helper()
	comp := New().WithSource("call_composition.oak", wasmCallCompositionSource)
	module, err := comp.EmitWasm().Get()
	if err != nil {
		t.Fatal(err)
	}
	if module.TranslationVerified || module.ByteValidation == nil ||
		module.ByteValidation.SHA256 != fmt.Sprintf("%x", sha256.Sum256(module.Bytes)) {
		t.Fatal("expected unverified translation and independently admitted actual bytes")
	}
	again, err := comp.EmitWasm().Get()
	if err != nil || !bytes.Equal(module.Bytes, again.Bytes) {
		t.Fatal("nondeterministic actual source emission", err)
	}
	cases := []wasmCompositionCase{
		{name: "actual-compiler-module", source: wasmCallCompositionSource, bytes: module.Bytes, accepted: true, valid: true},
		{name: "padded-section-lengths", source: wasmCallCompositionSource, bytes: wasmTestModule(wasmTestSections(module.Bytes), true), accepted: true, valid: true},
		{name: "changed-original-source", source: strings.Replace(wasmCallCompositionSource, "difference(y, x)", "difference(x, y)", 1), bytes: module.Bytes, valid: true},
		{name: "unclaimed-source-spelling", source: wasmCallCompositionSource + "\n", bytes: module.Bytes, valid: true},
	}
	add := func(name string, data []byte, valid bool) {
		cases = append(cases, wasmCompositionCase{name: name, source: wasmCallCompositionSource, bytes: data, valid: valid, changed: valid})
	}
	body := func(name string, index int, old, replacement []byte, valid bool) {
		ss := wasmTestSections(module.Bytes)
		pos := 0
		count := int(wasmTestU32(ss[3].data, &pos))
		payload := encoding.AppendUnsigned(nil, uint64(count))
		for i := 0; i < count; i++ {
			n := int(wasmTestU32(ss[3].data, &pos))
			b := append([]byte(nil), ss[3].data[pos:pos+n]...)
			pos += n
			if i == index {
				if bytes.Count(b, old) != 1 {
					t.Fatalf("%s: expected one byte mutation target in function %d", name, index)
				}
				b = bytes.Replace(b, old, replacement, 1)
			}
			payload = encoding.AppendUnsigned(payload, uint64(len(b)))
			payload = append(payload, b...)
		}
		ss[3].data = payload
		add(name, wasmTestModule(ss, false), valid)
	}
	body("wrong-callee-index", 1, []byte{16, 2}, []byte{16, 0}, true)
	body("out-of-bounds-callee", 1, []byte{16, 2}, []byte{16, 3}, false)
	body("swapped-noncommutative-arguments", 2, []byte{32, 1, 32, 0, 16, 0}, []byte{32, 0, 32, 1, 16, 0}, true)
	body("caller-local-clobber", 1, []byte{106, 33, 2}, []byte{106, 33, 0}, true)
	body("read-fresh-zero-instead-of-argument", 1, []byte{32, 0, 65, 7}, []byte{32, 2, 65, 7}, true)
	body("too-few-locals", 1, []byte{2, 1, 127, 1, 127}, []byte{1, 1, 127}, false)
	body("wrong-local-width", 1, []byte{2, 1, 127, 1, 127}, []byte{2, 1, 126, 1, 127}, false)
	body("early-return-routing", 1, []byte{32, 3, 32, 2, 107, 32, 2, 107}, []byte{32, 3, 15, 32, 2, 107, 32, 2, 107}, true)
	body("wrong-subtraction", 0, []byte{32, 0, 32, 1, 107}, []byte{32, 0, 32, 1, 106}, true)
	for _, item := range []struct {
		name   string
		offset int
	}{{"wrong-parameter-signature", 9}, {"wrong-result-signature", 12}} {
		ss := wasmTestSections(module.Bytes)
		if ss[0].id != 1 || len(ss[0].data) != 19 || ss[0].data[item.offset] != 127 {
			t.Fatal("type-section mutation target changed")
		}
		ss[0].data[item.offset] = 126
		add(item.name, wasmTestModule(ss, false), false)
	}
	for _, item := range []struct {
		name     string
		newIndex byte
	}{{"wrong-export-return-route", 2}, {"out-of-bounds-export", 3}} {
		ss := wasmTestSections(module.Bytes)
		old := []byte{4, 'm', 'a', 'i', 'n', 0, 1}
		if bytes.Count(ss[2].data, old) != 1 {
			t.Fatal("export mutation target changed")
		}
		ss[2].data = bytes.Replace(ss[2].data, old, []byte{4, 'm', 'a', 'i', 'n', 0, item.newIndex}, 1)
		add(item.name, wasmTestModule(ss, false), item.newIndex == 2)
	}
	firstSection := wasmTestSections(module.Bytes)[0]
	typeOnlyEnd := 8 + 1 + len(encoding.AppendUnsigned(nil, uint64(len(firstSection.data)))) + len(firstSection.data)
	for n := 0; n < len(module.Bytes); n++ {
		add(fmt.Sprintf("truncated-%d", n), append([]byte(nil), module.Bytes[:n]...), false)
		// Empty and type-only modules are legal Core, but outside the bounded
		// executable profile. Do not mistake stricter profile admission for
		// an independent engine's full WebAssembly validation judgment.
		cases[len(cases)-1].coreOnly = n == 8 || n == typeOnlyEnd
	}
	add("trailing-byte", append(append([]byte(nil), module.Bytes...), 0), false)
	for _, tc := range cases {
		_, err := check.Validate(tc.bytes)
		if (err == nil) != tc.valid {
			t.Fatalf("%s: Go validator validity=%t, want %t: %v", tc.name, err == nil, tc.valid, err)
		}
	}
	return cases
}

func TestWasmCallCompositionEngine(t *testing.T) {
	engine := wasmtest.Require(t)
	type row struct {
		Name, Module              string
		Valid, CoreValid, Changed bool
	}
	var rows []row
	for _, tc := range wasmCompositionCases(t) {
		rows = append(rows, row{tc.name, base64.StdEncoding.EncodeToString(tc.bytes), tc.valid, tc.valid || tc.coreOnly, tc.changed})
	}
	data, err := json.Marshal(rows)
	if err != nil {
		t.Fatal(err)
	}
	path := filepath.Join(t.TempDir(), "composition.json")
	if err := os.WriteFile(path, data, 0600); err != nil {
		t.Fatal(err)
	}
	// BigInt is an independent mathematical oracle; 32-bit words are presented
	// as both positive unsigned and negative signed host numbers. Calls reuse one
	// instance; the activation theorems separately establish fresh zero locals.
	script := `const path=typeof Deno!=="undefined"?Deno.args[0]:process.argv[1];
const rows=JSON.parse(typeof Deno!=="undefined"?Deno.readTextFileSync(path):require('fs').readFileSync(path,'utf8'));
const values=[0,1,7,99,127,128,0x7fffffff,0x80000000,0xfffffffe,0xffffffff];
const pairs=[];for(const a of values)for(const b of values)pairs.push([a,b]);
let seed=0x42c0ffee;function random(){seed=(Math.imul(seed,1664525)+1013904223)>>>0;return seed}
for(let i=0;i<256;i++)pairs.push([random(),random()]);
for(const r of rows){const bytes=Uint8Array.from(atob(r.Module),c=>c.charCodeAt(0));
if(WebAssembly.validate(bytes)!==r.CoreValid)throw Error(r.Name+': validator disagreement');if(!r.Valid)continue;
const instance=new WebAssembly.Instance(new WebAssembly.Module(bytes),{});
const f=instance.exports.main;let differs=typeof f!=='function';
if(!differs)for(const [x,y]of pairs){for(const signed of [false,true]){
const a=signed?x|0:x,b=signed?y|0:y;
const want=Number(BigInt.asIntN(32,BigInt(y)-BigInt(x)-2n*(BigInt(x)+7n)));
let got;try{got=f(a,b)}catch(e){if(!(e instanceof WebAssembly.RuntimeError))throw e;differs=true;continue;}
if(got!==want){differs=true;if(!r.Changed)throw Error(r.Name+': '+a+','+b+' got '+got+' expected '+want);}
}}
if(differs!==r.Changed)throw Error(r.Name+': semantic mutation was not detected');}`
	ctx, cancel := context.WithTimeout(t.Context(), 60*time.Second)
	defer cancel()
	if out, err := engine.Command(ctx, script, path).CombinedOutput(); err != nil {
		t.Fatalf("composition engine: %v\n%s", err, out)
	}
	t.Logf("checked %d complete byte/source controls; 712 invocations per valid module", len(rows))
}

func TestWasmCallCompositionLean(t *testing.T) {
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
	run := func(args ...string) string {
		t.Helper()
		ctx, cancel := context.WithTimeout(t.Context(), 4*time.Minute)
		defer cancel()
		cmd := exec.CommandContext(ctx, lake, args...)
		cmd.Dir = root
		out, err := cmd.CombinedOutput()
		if err != nil {
			t.Fatalf("lake %v: %v\n%s", args, err, out)
		}
		return string(out)
	}
	run("build", "Oak.WasmCallComposition")
	cases := wasmCompositionCases(t)
	for start := 0; start < len(cases); start += 16 {
		end := min(start+16, len(cases))
		var proof strings.Builder
		proof.WriteString("import Oak.WasmCallComposition\nopen Oak.WasmExecution Oak.WasmCallComposition\nset_option maxRecDepth 32768\nset_option maxHeartbeats 4000000\n")
		fmt.Fprintf(&proof, "def actualOriginal : List UInt8 := %s\ntheorem actual_source : actualOriginal = sourceBytes := by decide +kernel\n#print axioms actual_source\n", wasmCoreLeanList([]byte(wasmCallCompositionSource)))
		audited := []string{"actual_source"}
		for i := start; i < end; i++ {
			tc := cases[i]
			original := "actualOriginal"
			if tc.source != wasmCallCompositionSource {
				original = wasmCoreLeanList([]byte(tc.source))
			}
			fmt.Fprintf(&proof, "\nnamespace Artifact%d\ndef original : List UInt8 := %s\ndef emitted : List UInt8 := %s\n", i, original, wasmCoreLeanList(tc.bytes))
			fmt.Fprintf(&proof, "theorem checked : accepts original emitted = %t := by\n", tc.accepted)
			if tc.source == wasmCallCompositionSource {
				proof.WriteString("  rw [show original = sourceBytes from actual_source]\n  simp only [accepts, beq_self_eq_true, Bool.true_and]\n")
			}
			proof.WriteString("  decide +kernel\n")
			if tc.accepted {
				proof.WriteString(`theorem all_inputs (a b : BitVec 32) (extra : Nat) :
    original = sourceBytes ∧
    Oak.WasmModule.decode emitted = some module ∧
    Oak.WasmModule.invokeExport emitted "main".toUTF8.data.toList (32+extra) [.i32 a,.i32 b] =
      some (.ok ⟨[.i32 (result a b)], #[.i32 a,.i32 b,.i32 (a+7),.i32 (b-a)]⟩) :=
  accepted_invocation checked a b extra
`)
				name := fmt.Sprintf("Artifact%d.all_inputs", i)
				audited = append(audited, name)
				fmt.Fprintf(&proof, "end Artifact%d\n#print axioms %s\n", i, name)
			} else {
				name := fmt.Sprintf("Artifact%d.checked", i)
				audited = append(audited, name)
				fmt.Fprintf(&proof, "end Artifact%d\n#print axioms %s\n", i, name)
			}
		}
		if start == 0 {
			for _, theorem := range []string{"fresh_main", "fresh_reverse", "main_enters_reverse", "reverse_returns", "invoke_more", "invocation", "insufficient_fuel", "accepted_invocation"} {
				name := "Oak.WasmCallComposition." + theorem
				audited = append(audited, name)
				fmt.Fprintf(&proof, "#print axioms %s\n", name)
			}
		}
		path := filepath.Join(t.TempDir(), "ActualCallComposition.lean")
		if err := os.WriteFile(path, []byte(proof.String()), 0600); err != nil {
			t.Fatal(err)
		}
		out := run("env", "lean", path)
		if err := auditWasmCoreAxioms(out, audited); err != nil {
			t.Fatalf("composition axiom audit: %v\n%s", err, out)
		}
		t.Logf("kernel checked and audited artifact controls %d–%d of %d", start+1, end, len(cases))
	}
}
