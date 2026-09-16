package compiler

import (
	"fmt"
	"os"
	"path/filepath"
	"strings"
	"testing"
	"time"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/diagnostic"
	"github.com/SCKelemen/oak/layout"
	"github.com/SCKelemen/oak/parser"
	"github.com/SCKelemen/oak/scanner"
)

// The verdict cache (compiler/verdict_cache.go): a second build of the same
// program takes every verdict from the cache; a change to a callee's body
// re-verifies the callee and its callers and no other body; WithVerifyFresh
// bypasses the cache. The program carries a unique constant so that every
// run of this test starts cold whatever the cache holds.
func TestVerdictCache(t *testing.T) {
	requireArm64Host(t)
	stamp := fmt.Sprintf("%d", time.Now().UnixNano()%1000000007)
	program := func(incBody string) string {
		return "STAMP: u32 = u32(" + stamp + ")\n" +
			"inc: (a: u32) -> u32 = " + incBody + "\n" +
			"twice: (a: u32) -> u32 = inc(a) + inc(a)\n" +
			"other: (a: u32) -> u32 = a * u32(3)\n" +
			"main: (): i32 { assert(twice(u32(1)) > u32(0))\n  assert(other(u32(1)) == u32(3))\n  0 }\n"
	}
	tally := func(source string, fresh bool) (fromCache, verified int, verdicts map[string]string, native map[string]asm.Verdict) {
		t.Helper()
		verdicts = map[string]string{}
		comp := New().WithSource("cache.oak", source).WithNativeBodies()
		if fresh {
			comp = comp.WithVerifyFresh()
		}
		comp = comp.WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
			if d.Source != "native" {
				return
			}
			if n, _ := fmt.Sscanf(d.Message, "native backend: %d of %d verdicts from the verdict cache", &fromCache, &verified); n == 2 {
				return
			}
			if strings.HasPrefix(d.Message, "native backend: asm unit ") {
				rest := strings.TrimPrefix(d.Message, "native backend: asm unit ")
				if colon := strings.IndexByte(rest, ':'); colon > 0 {
					verdicts[rest[:colon]] = rest
				}
			}
		})
		model, err := comp.Check().Get()
		if err != nil {
			t.Fatalf("compile: %v", err)
		}
		return fromCache, verified, verdicts, model.NativeVerdicts
	}
	cold, total, first, firstNative := tally(program("a + u32(1)"), false)
	if cold != 0 || total < 3 {
		t.Fatalf("a cold build must verify every body itself, got %d of %d from the cache", cold, total)
	}
	warm, again, second, secondNative := tally(program("a + u32(1)"), false)
	if warm != total || again != total {
		t.Fatalf("a second build of the same program must take every verdict from the cache, got %d of %d", warm, again)
	}
	for name, verdict := range first {
		if second[name] != verdict {
			t.Errorf("%s: the cached verdict differs:\n  %s\n  %s", name, verdict, second[name])
		}
	}
	for label, verdicts := range map[string]map[string]asm.Verdict{"cold": firstNative, "warm": secondNative} {
		if got := strings.Join(verdicts["twice"].Callees, ","); got != "inc" {
			t.Fatalf("%s twice dependency metadata = %q, want inc", label, got)
		}
	}
	closureInput := make(map[string]asm.Verdict, len(secondNative))
	for name, verdict := range secondNative {
		closureInput[name] = verdict
	}
	inc := closureInput["inc"]
	inc.Kind = asm.VerdictTrusted
	closureInput["inc"] = inc
	if got := provenRestingOnUnproven(closureInput)["twice"]; got != "inc" {
		t.Fatalf("warm cached caller did not retain verified-profile closure: twice via %q", got)
	}
	// A change to inc's body invalidates inc, its caller twice, and main
	// (which reaches inc through twice); other keeps its key.
	changed, changedTotal, _, _ := tally(program("a + u32(2)"), false)
	if changedTotal != total || changed != 1 {
		t.Fatalf("after a callee change exactly the bodies reaching it must be re-verified, got %d of %d from the cache", changed, changedTotal)
	}
	fresh, freshTotal, _, _ := tally(program("a + u32(2)"), true)
	if fresh != 0 || freshTotal != total {
		t.Fatalf("WithVerifyFresh must bypass the cache, got %d of %d", fresh, freshTotal)
	}
}

func TestVerdictCacheRoundTripsDependencies(t *testing.T) {
	dir := t.TempDir()
	key := strings.Repeat("a", 64)
	want := asm.Verdict{
		Kind:    asm.VerdictProven,
		Message: "proof line one\nproof line two",
		Callees: []string{"leaf", "unicodeλ"},
	}
	functions := map[string]*ast.FunctionStatement{
		"leaf":     {},
		"unicodeλ": {},
	}
	storeVerdict(dir, key, want)
	got, ok := cachedVerdict(dir, key, functions)
	if !ok || got.Kind != want.Kind || got.Message != want.Message ||
		strings.Join(got.Callees, "\x00") != strings.Join(want.Callees, "\x00") {
		t.Fatalf("cached verdict = %#v, %v; want %#v, true", got, ok, want)
	}
	got.Callees[0] = "mutated"
	again, ok := cachedVerdict(dir, key, functions)
	if !ok || again.Callees[0] != "leaf" {
		t.Fatalf("cache returned aliased dependency storage: %#v, %v", again, ok)
	}
}

func TestVerdictCacheRejectsMalformedDependencyRecords(t *testing.T) {
	dir := t.TempDir()
	functions := map[string]*ast.FunctionStatement{"leaf": {}}
	cases := []struct {
		name string
		data string
	}{
		{name: "legacy v1", data: "1\nlegacy proof"},
		{name: "wrong version", data: `{"version":1,"kind":1,"message":"proof","callees":[]}`},
		{name: "missing callees", data: `{"version":2,"kind":1,"message":"proof"}`},
		{name: "null callees", data: `{"version":2,"kind":1,"message":"proof","callees":null}`},
		{name: "invalid kind", data: `{"version":2,"kind":9,"message":"proof","callees":[]}`},
		{name: "empty callee", data: `{"version":2,"kind":1,"message":"proof","callees":[""]}`},
		{name: "duplicate callee", data: `{"version":2,"kind":1,"message":"proof","callees":["leaf","leaf"]}`},
		{name: "unknown callee", data: `{"version":2,"kind":1,"message":"proof","callees":["other"]}`},
		{name: "unknown field", data: `{"version":2,"kind":1,"message":"proof","callees":[],"proof":true}`},
		{name: "trailing data", data: `{"version":2,"kind":1,"message":"proof","callees":[]} false`},
		{name: "truncated", data: `{"version":2,"kind":1`},
	}
	for i, test := range cases {
		t.Run(test.name, func(t *testing.T) {
			key := fmt.Sprintf("%064x", i+1)
			if err := os.WriteFile(filepath.Join(dir, key+".verdict"), []byte(test.data), 0o600); err != nil {
				t.Fatal(err)
			}
			if verdict, ok := cachedVerdict(dir, key, functions); ok {
				t.Fatalf("malformed cache record was accepted: %#v", verdict)
			}
		})
	}
	if verdict, ok := cachedVerdict(dir, "../escape", functions); ok {
		t.Fatalf("unsafe cache key was accepted: %#v", verdict)
	}
}

func TestVerdictCacheKeyIncludesMachineOnlyCalleeBodies(t *testing.T) {
	functionMap := func(helperBody string) (map[string]*ast.FunctionStatement, *ast.FunctionStatement) {
		source := "root: (x: u32): u32 = x\nhelper: (x: u32): u32 = " + helperBody + "\n"
		p := parser.New(layout.New(scanner.New(source)))
		program := p.ParseProgram()
		if errs := p.Errors(); len(errs) != 0 {
			t.Fatal(errs)
		}
		functions := map[string]*ast.FunctionStatement{}
		for _, statement := range program.Statements {
			if function, ok := statement.(*ast.FunctionStatement); ok {
				functions[function.Name.Value] = function
			}
		}
		return functions, functions["root"]
	}

	for _, symbol := range []string{"helper", "helper" + asm.VectorEntrySuffix(asm.ArchArm64)} {
		before, rootBefore := functionMap("x + u32(1)")
		after, rootAfter := functionMap("x + u32(2)")
		machine := &asm.Function{
			Name:      "root",
			Arch:      asm.ArchArm64,
			Signature: rootBefore,
			Items: []asm.Item{
				asm.Instruction{Mnemonic: "bl", Operands: []asm.Operand{asm.Symbol{Name: symbol}}},
			},
		}
		beforeKey := verdictCacheKey(machine, rootBefore, before, "")
		machine.Signature = rootAfter
		afterKey := verdictCacheKey(machine, rootAfter, after, "")
		if beforeKey == afterKey {
			t.Fatalf("machine-only callee %q did not contribute its source identity to the cache key", symbol)
		}
	}
}
