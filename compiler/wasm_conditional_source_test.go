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

type wasmConditionalDecl struct{ name, first, second string }

func (d wasmConditionalDecl) source() string {
	return fmt.Sprintf("%s: (%s: u32, %s: u32): u32 = (%s < %s) ? (%s - %s) | (%s - %s)\n", d.name, d.first, d.second, d.first, d.second, d.first, d.second, d.second, d.first)
}
func (d wasmConditionalDecl) lean() string {
	return fmt.Sprintf("⟨%s,%s,%s⟩", wasmCoreLeanList([]byte(d.name)), wasmCoreLeanList([]byte(d.first)), wasmCoreLeanList([]byte(d.second)))
}

type wasmConditionalCase struct {
	name, source                       string
	claim                              wasmConditionalDecl
	bytes                              []byte
	accepted, valid, coreOnly, changed bool
	checkParse                         bool
	parsed                             *wasmConditionalDecl
}

func wasmConditionalCases(t *testing.T) []wasmConditionalCase {
	t.Helper()
	declarations := []wasmConditionalDecl{
		{"choose", "x", "y"},
		{"choose", "left0", "right9"}, // Parameter renaming leaves the actual module unchanged.
		{"selectword", "LEFT0", "Right9"},
		{strings.Repeat("F", 64), strings.Repeat("a", 64), strings.Repeat("b", 64)},
	}
	var cases []wasmConditionalCase
	var base []byte
	for i, d := range declarations {
		source := d.source()
		m, err := New().WithSource("conditional.oak", source).EmitWasm().Get()
		if err != nil {
			t.Fatal(err)
		}
		if m.TranslationVerified || m.ByteValidation == nil || m.ByteValidation.SHA256 != fmt.Sprintf("%x", sha256.Sum256(m.Bytes)) {
			t.Fatal("actual emission must retain independent byte admission without translation authority")
		}
		again, err := New().WithSource("conditional.oak", source).EmitWasm().Get()
		if err != nil || !bytes.Equal(m.Bytes, again.Bytes) {
			t.Fatal("independent repeated compilation changed the actual bytes", err)
		}
		if i == 0 {
			base = m.Bytes
		} else if i == 1 && !bytes.Equal(base, m.Bytes) {
			t.Fatal("parameter-only alpha-renaming changed the actual module")
		}
		cases = append(cases,
			wasmConditionalCase{fmt.Sprintf("actual-%d", i), source, d, m.Bytes, true, true, false, false, false, nil},
			wasmConditionalCase{fmt.Sprintf("padded-%d", i), source, d, wasmTestModule(wasmTestSections(m.Bytes), true), true, true, false, false, false, nil})
	}
	d := declarations[0]
	source := d.source()
	addSource := func(name, changed string, claim wasmConditionalDecl) {
		cases = append(cases, wasmConditionalCase{name, changed, claim, base, false, true, false, false, true, nil})
	}
	addSource("renaming-cannot-replay-old-claim", declarations[1].source(), d)
	cases[len(cases)-1].parsed = &declarations[1]
	for _, mutation := range []struct{ name, old, replacement string }{
		{"signed-source-signature", "u32", "i32"},
		{"wrong-source-comparison", " < ", " > "},
		{"wrong-source-true-arm", "? (x - y)", "? (y - x)"},
		{"wrong-source-false-arm", "| (y - x)", "| (x - y)"},
		{"wrong-condition-binding", "= (x < y)", "= (y < x)"},
		{"missing-final-newline", "\n", ""},
		{"CRLF-outside-canonical-grammar", "\n", "\r\n"},
		{"hidden-trailing-comment", "\n", " // changed\n"},
	} {
		addSource(mutation.name, strings.Replace(source, mutation.old, mutation.replacement, 1), d)
	}
	addSource("extra-declaration", source+source, d)
	addSource("source-budget", strings.Repeat(" ", 1025)+source, d)
	for _, rejected := range []struct {
		name string
		d    wasmConditionalDecl
	}{
		{"duplicate-parameters", wasmConditionalDecl{"choose", "x", "x"}},
		{"function-shadows-first", wasmConditionalDecl{"x", "x", "y"}},
		{"function-shadows-second", wasmConditionalDecl{"y", "x", "y"}},
		{"reserved-parameter", wasmConditionalDecl{"choose", "true", "y"}},
		{"reserved-function", wasmConditionalDecl{"while", "x", "y"}},
		{"underscore-outside-identifier-policy", wasmConditionalDecl{"choose", "left_0", "y"}},
		{"unicode-outside-identifier-policy", wasmConditionalDecl{"choose", "π", "y"}},
		{"name-bound", wasmConditionalDecl{strings.Repeat("F", 65), "x", "y"}},
	} {
		addSource(rejected.name, rejected.d.source(), rejected.d)
	}
	addBytes := func(name string, data []byte, valid, changed bool) {
		cases = append(cases, wasmConditionalCase{name, source, d, data, false, valid, false, changed, false, nil})
	}
	mutateBody := func(name string, old, replacement []byte, valid, changed bool) {
		ss := wasmTestSections(base)
		pos := 0
		if wasmTestU32(ss[3].data, &pos) != 1 {
			t.Fatal("expected one code entry")
		}
		n := int(wasmTestU32(ss[3].data, &pos))
		body := ss[3].data[pos : pos+n]
		if bytes.Count(body, old) != 1 {
			t.Fatalf("%s: expected one mutation target in actual function body", name)
		}
		body = bytes.Replace(body, old, replacement, 1)
		ss[3].data = encoding.AppendUnsigned([]byte{1}, uint64(len(body)))
		ss[3].data = append(ss[3].data, body...)
		addBytes(name, wasmTestModule(ss, false), valid, changed)
	}
	mutateBody("signed-comparison-opcode", []byte{73, 4}, []byte{72, 4}, true, true)
	mutateBody("inverted-comparison", []byte{73, 4}, []byte{79, 4}, true, true)
	mutateBody("reversed-true-arm", []byte{32, 0, 32, 1, 107, 33, 2}, []byte{32, 1, 32, 0, 107, 33, 2}, true, true)
	mutateBody("reversed-false-arm", []byte{5, 32, 1, 32, 0, 107, 33, 2}, []byte{5, 32, 0, 32, 1, 107, 33, 2}, true, true)
	mutateBody("phi-clobbers-parameter", []byte{107, 33, 2, 5}, []byte{107, 33, 0, 5}, true, true)
	mutateBody("wrong-phi-read", []byte{11, 32, 2, 11}, []byte{11, 32, 0, 11}, true, true)
	mutateBody("wrong-block-result", []byte{73, 4, 64}, []byte{73, 4, 127}, false, false)
	mutateBody("missing-else", []byte{33, 2, 5, 32}, []byte{33, 2, 32}, true, true)
	mutateBody("out-of-bounds-phi", []byte{11, 32, 2, 11}, []byte{11, 32, 3, 11}, false, false)
	mutateBody("wrong-local-width", []byte{1, 1, 127, 32}, []byte{1, 1, 126, 32}, false, false)
	// Strict metadata binding also rejects an unused extra local, even though
	// its mathematical return values are unchanged.
	mutateBody("extra-unclaimed-local", []byte{1, 1, 127, 32}, []byte{1, 2, 127, 32}, true, false)
	mutateBody("trapping-return-route", []byte{11, 32, 2, 11}, []byte{11, 32, 2, 0, 11}, true, true)
	for _, item := range []struct {
		name string
		i    int
	}{{"wrong-parameter-signature", 3}, {"wrong-return-signature", 6}} {
		ss := wasmTestSections(base)
		if len(ss[0].data) != 7 || ss[0].data[item.i] != 127 {
			t.Fatal("type section mutation target changed")
		}
		ss[0].data[item.i] = 126
		addBytes(item.name, wasmTestModule(ss, false), false, false)
	}
	ss := wasmTestSections(base)
	ss[2].data[len(ss[2].data)-1] = 1
	addBytes("out-of-bounds-export", wasmTestModule(ss, false), false, false)
	badMagic := append([]byte(nil), base...)
	badMagic[0] = 1
	addBytes("bad-magic", badMagic, false, false)
	typeOnlyEnd := 8 + 1 + len(encoding.AppendUnsigned(nil, uint64(len(ss[0].data)))) + len(ss[0].data)
	for n := 0; n < len(base); n++ {
		addBytes(fmt.Sprintf("truncated-%d", n), append([]byte(nil), base[:n]...), false, false)
		cases[len(cases)-1].coreOnly = n == 8 || n == typeOnlyEnd
	}
	addBytes("trailing-byte", append(append([]byte(nil), base...), 0), false, false)
	for _, tc := range cases {
		_, err := check.Validate(tc.bytes)
		if (err == nil) != tc.valid {
			t.Fatalf("%s: bounded validator got %t, expected %t: %v", tc.name, err == nil, tc.valid, err)
		}
	}
	return cases
}

func TestWasmConditionalSourceEngine(t *testing.T) {
	engine := wasmtest.Require(t)
	type row struct {
		Name, Entry, Module       string
		Valid, CoreValid, Changed bool
	}
	var rows []row
	for _, tc := range wasmConditionalCases(t) {
		// Source-only mutations are checked separately from byte execution;
		// their unchanged base artifact still exports choose.
		entry := tc.claim.name
		if !tc.accepted {
			entry = "choose"
		}
		rows = append(rows, row{tc.name, entry, base64.StdEncoding.EncodeToString(tc.bytes), tc.valid, tc.valid || tc.coreOnly, tc.changed})
	}
	data, err := json.Marshal(rows)
	if err != nil {
		t.Fatal(err)
	}
	path := filepath.Join(t.TempDir(), "conditionals.json")
	if err := os.WriteFile(path, data, 0600); err != nil {
		t.Fatal(err)
	}
	script := `const path=typeof Deno!=="undefined"?Deno.args[0]:process.argv[1];
const rows=JSON.parse(typeof Deno!=="undefined"?Deno.readTextFileSync(path):require('fs').readFileSync(path,'utf8'));
const values=[0,1,7,127,128,0x7fffffff,0x80000000,0xfffffffe,0xffffffff];
const pairs=[];for(const a of values)for(const b of values)pairs.push([a,b]);
let seed=0x4277;function random(){seed=(Math.imul(seed,1664525)+1013904223)>>>0;return seed}
for(let i=0;i<128;i++)pairs.push([random(),random()]);
for(const r of rows){const bytes=Uint8Array.from(atob(r.Module),c=>c.charCodeAt(0));
if(WebAssembly.validate(bytes)!==r.CoreValid)throw Error(r.Name+': Core validation mismatch');if(!r.Valid)continue;
const f=new WebAssembly.Instance(new WebAssembly.Module(bytes),{}).exports[r.Entry];let differs=typeof f!=='function';
if(!differs)for(const [a,b]of pairs)for(const signed of [false,true]){
const x=BigInt(a),y=BigInt(b),want=Number(BigInt.asIntN(32,x<y?x-y:y-x));
let got;try{got=f(signed?a|0:a,signed?b|0:b)}catch(e){if(!(e instanceof WebAssembly.RuntimeError))throw e;differs=true;continue}
if(got!==want){differs=true;if(!r.Changed)throw Error(r.Name+': conditional result mismatch')}
}if(differs!==r.Changed)throw Error(r.Name+': mutation witness mismatch');}`
	ctx, cancel := context.WithTimeout(t.Context(), time.Minute)
	defer cancel()
	if out, err := engine.Command(ctx, script, path).CombinedOutput(); err != nil {
		t.Fatalf("conditional engine: %v\n%s", err, out)
	}
	t.Logf("checked %d source/module controls, 418 engine invocations per valid module", len(rows))
}

func TestWasmConditionalSourceLean(t *testing.T) {
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
		cmd.Env = append(os.Environ(), "LEAN_NUM_THREADS=1")
		out, err := cmd.CombinedOutput()
		if err != nil {
			t.Fatalf("lake %v: %v\n%s", args, err, out)
		}
		return string(out)
	}
	run("build", "Oak.WasmConditionalSource")
	cases := wasmConditionalCases(t)
	for start := 0; start < len(cases); {
		end := min(start+4, len(cases))
		// Large original-byte certificates run alone to keep kernel reduction
		// within the same memory limit; this does not alter the checked claim.
		for i := start; i < end; i++ {
			if len(cases[i].source) > 512 {
				end = max(start+1, i)
				break
			}
		}
		var proof strings.Builder
		proof.WriteString("import Oak.WasmConditionalSource\nopen Oak.WasmExecution Oak.WasmConditionalSource\nopen Oak.WasmConditionalExecution (result)\nset_option maxRecDepth 32768\nset_option maxHeartbeats 4000000\n")
		var audited []string
		for i := start; i < end; i++ {
			tc := cases[i]
			fmt.Fprintf(&proof, "namespace Artifact%d\ndef original : List UInt8 := %s\ndef emitted : List UInt8 := %s\ndef claim : Decl := %s\ntheorem checked : accepts original claim emitted = %t := by decide +kernel\n", i, wasmCoreLeanList([]byte(tc.source)), wasmCoreLeanList(tc.bytes), tc.claim.lean(), tc.accepted)
			if tc.checkParse {
				want := "none"
				if tc.parsed != nil {
					want = "some (" + tc.parsed.lean() + " : Decl)"
				}
				fmt.Fprintf(&proof, "theorem parsed : parse original = %s := by decide +kernel\n#print axioms Artifact%d.parsed\n", want, i)
				audited = append(audited, fmt.Sprintf("Artifact%d.parsed", i))
			}
			name := fmt.Sprintf("Artifact%d.checked", i)
			if tc.accepted {
				proof.WriteString(`theorem all_inputs (a b : BitVec 32) (sourceFuel extra : Nat) :
    Grammar original claim ∧
    evaluate claim a b = some (result a b) ∧
    Oak.LoweringRefinement.evalX (toExpr claim) (Oak.BitwiseSourceLowering.inputs a b)
      (fun _ => 0) sourceFuel = some (result a b) ∧
    Oak.WasmModule.decode emitted = some (module claim) ∧
    Oak.WasmModule.invokeExport emitted claim.name (16+extra) [.i32 a,.i32 b] =
      some (.ok ⟨[.i32 (result a b)],#[.i32 a,.i32 b,.i32 (result a b)]⟩) :=
  accepted_source_to_export checked a b sourceFuel extra
`)
				name = fmt.Sprintf("Artifact%d.all_inputs", i)
			}
			audited = append(audited, name)
			fmt.Fprintf(&proof, "end Artifact%d\n#print axioms %s\n", i, name)
		}
		if start == 0 {
			for _, name := range []string{
				"Oak.WasmConditionalSource.parse_sound", "Oak.WasmConditionalSource.parse_exact",
				"Oak.WasmConditionalSource.grammar_evaluation", "Oak.WasmConditionalSource.typed_meaning",
				"Oak.WasmConditionalSource.grammar_to_existing", "Oak.WasmConditionalSource.refuses_source_replay",
				"Oak.WasmConditionalSource.accepted_source_to_export", "Oak.WasmConditionalExecution.invocation",
				"Oak.WasmConditionalExecution.invocation_more", "Oak.WasmConditionalExecution.call_entry",
				"Oak.WasmConditionalExecution.return_to_caller", "Oak.WasmConditionalExecution.call_composition",
			} {
				audited = append(audited, name)
				fmt.Fprintf(&proof, "#print axioms %s\n", name)
			}
		}
		path := filepath.Join(t.TempDir(), "ActualConditional.lean")
		if err := os.WriteFile(path, []byte(proof.String()), 0600); err != nil {
			t.Fatal(err)
		}
		out := run("env", "lean", "-j1", "-M896", path)
		if err := auditWasmCoreAxioms(out, audited); err != nil {
			t.Fatalf("conditional axiom audit: %v\n%s", err, out)
		}
		t.Logf("kernel checked and audited conditional controls %d–%d of %d", start+1, end, len(cases))
		start = end
	}
}
