package asm

import (
	"fmt"
	"strings"
	"testing"

	"github.com/SCKelemen/oak/ast"
)

func TestFiniteCallApplicationDoesNotImportCalleeLoops(t *testing.T) {
	callee, err := parseSignatureWithBody("sum_to: (n: u32) -> u32 { acc: u32 = u32(0)\n i: u32 = u32(0)\n while i < n { acc = acc + i\n i = i + u32(1) }\n acc }")
	if err != nil {
		t.Fatal(err)
	}
	decl := "caller: (n: u32) -> u32"
	unit, errs := ParseUnit("call_application.oakasm", decl+" = {\n bind w0 = n\n clobber x29, x30\n frame 16\n sub sp, sp, #16\n stp x29, x30, [sp]\n bl sum_to\n ldp x29, x30, [sp]\n add sp, sp, #16\n ret\n}\n")
	if len(errs) != 0 {
		t.Fatal(errs)
	}
	sig, err := parseSignature(decl)
	if err != nil {
		t.Fatal(err)
	}
	fn := unit.Functions[0]
	fn.Callees = map[string]*ast.FunctionStatement{"sum_to": callee}
	if findings := Check(fn, sig, map[string]bool{"sum_to": true}); len(findings) != 0 {
		t.Fatalf("checker: %v", findings)
	}
	result, exec, reason, ok := executeBodyChunk(fn, sig, nil, 0, 0)
	if !ok {
		t.Fatalf("execute call application: %s", reason)
	}
	if result == nil || exec == nil || len(exec.loops) != 0 {
		t.Fatalf("call application imported %d callee loops", len(exec.loops))
	}
	// Concrete execution must expand the same call on both sides, so the
	// witness is the actual sum rather than an arbitrary application value.
	env := map[string]uint64{"n": 4}
	concreteResult, _, reason, ok := executeBodyChunk(fn, sig, env, 0, 0)
	if !ok || theoremHasGeneralApplication(concreteResult, nil) || concreteResult.eval(env) != 6 {
		t.Fatalf("concrete machine call: result=%v, ok=%v, reason=%s", concreteResult, ok, reason)
	}
	spec, err := parseSignatureWithBody(decl + " = sum_to(n)")
	if err != nil {
		t.Fatal(err)
	}
	lo := prepareLowering(fn, sig, env)
	concreteOak, reason, ok := lo.lower(spec.Body, 32)
	if !ok || theoremHasGeneralApplication(concreteOak, nil) || concreteOak.eval(env) != 6 {
		t.Fatalf("concrete Oak call: result=%v, ok=%v, reason=%s", concreteOak, ok, reason)
	}
	verdict := Verify(fn, sig, spec.Body)
	if verdict.Kind != VerdictProven || !strings.Contains(verdict.Message, "sum_to") {
		t.Fatalf("finite looping callee: got %s: %s", verdict.Kind, verdict.Message)
	}
}

func TestFiniteCallLowersToApplication(t *testing.T) {
	callee, err := parseSignatureWithBody("mix: (a: u32, b: u16) -> u32 { out: u32 = a\n i: u32 = u32(0)\n while i < u32(b) { out = out ^ i\n i = i + u32(1) }\n out }")
	if err != nil {
		t.Fatal(err)
	}
	caller, err := parseSignatureWithBody("caller: (x: u32, y: u16) -> u32 = mix(x, y)")
	if err != nil {
		t.Fatal(err)
	}
	lo := newLowering(caller)
	lo.functions = map[string]*ast.FunctionStatement{"mix": callee}
	result, reason, ok := lo.lower(caller.Body, 32)
	if !ok {
		t.Fatalf("lower finite call: %s", reason)
	}
	if result.kind != termApply || result.name != "call:mix:result" || len(result.args) != 2 {
		t.Fatalf("finite call term = %#v", result)
	}
	if result.args[0].kind != termParam || result.args[0].name != "x" || result.args[1].kind != termParam || result.args[1].name != "y" {
		t.Fatalf("finite call arguments = %#v", result.args)
	}
}

func TestSmallStraightLineCallStaysExpanded(t *testing.T) {
	callee, err := parseSignatureWithBody("inc: (a: u32) -> u32 = a + u32(1)")
	if err != nil {
		t.Fatal(err)
	}
	caller, err := parseSignatureWithBody("caller: (x: u32) -> u32 = inc(x)")
	if err != nil {
		t.Fatal(err)
	}
	lo := newLowering(caller)
	lo.functions = map[string]*ast.FunctionStatement{"inc": callee}
	result, reason, ok := lo.lower(caller.Body, 32)
	if !ok {
		t.Fatalf("lower small call: %s", reason)
	}
	if result.kind == termApply {
		t.Fatalf("small straight-line call became an application: %#v", result)
	}
}

func TestWideStraightLineCallUsesApplication(t *testing.T) {
	calleeParams := make([]string, 16)
	callerParams := make([]string, 16)
	arguments := make([]string, 16)
	for i := range calleeParams {
		calleeParams[i] = fmt.Sprintf("p%d: u32", i)
		callerParams[i] = fmt.Sprintf("x%d: u32", i)
		arguments[i] = fmt.Sprintf("x%d", i)
	}
	callee, err := parseSignatureWithBody("wide: (" + strings.Join(calleeParams, ", ") + ") -> u32 = p0")
	if err != nil {
		t.Fatal(err)
	}
	caller, err := parseSignatureWithBody("caller: (" + strings.Join(callerParams, ", ") + ") -> u32 = wide(" + strings.Join(arguments, ", ") + ")")
	if err != nil {
		t.Fatal(err)
	}
	lo := newLowering(caller)
	lo.functions = map[string]*ast.FunctionStatement{"wide": callee}
	result, reason, ok := lo.lower(caller.Body, 32)
	if !ok {
		t.Fatalf("lower wide call: %s", reason)
	}
	if result.kind != termApply || len(result.args) != 16 {
		t.Fatalf("wide straight-line call term = %#v", result)
	}

	// If the machine inlines the body incorrectly, expanding the source
	// application must still expose the genuine counterexample.
	decl := "caller: (" + strings.Join(callerParams, ", ") + ") -> u32"
	unit, errs := ParseUnit("wide_call.oakasm", decl+" = {\n bind w0 = x0\n add w0, w0, #1\n ret\n}\n")
	if len(errs) != 0 {
		t.Fatal(errs)
	}
	fn := unit.Functions[0]
	fn.Callees = map[string]*ast.FunctionStatement{"wide": callee}
	verdict := Verify(fn, caller, caller.Body)
	if verdict.Kind != VerdictMismatch {
		t.Fatalf("incorrectly inlined call = %s: %s; want mismatch", verdict.Kind, verdict.Message)
	}
}

func TestCallApplicationEligibilityFailsClosed(t *testing.T) {
	parse := func(source string) *ast.FunctionStatement {
		t.Helper()
		fn, err := parseSignatureWithBody(source)
		if err != nil {
			t.Fatal(err)
		}
		return fn
	}

	t.Run("borrowed memory", func(t *testing.T) {
		fn := parse("read: (v: []u32) -> u32 = v[0]")
		lo := newLowering(fn)
		if lo.finiteCallApplication(fn, map[string]bool{}) {
			t.Fatal("a borrowed-memory callee was application-eligible")
		}
	})

	t.Run("mutable global", func(t *testing.T) {
		fn := parse("read: (a: u32) -> u32 = g + a")
		lo := newLowering(fn)
		lo.globals = map[string]Global{"g": {Size: 4}}
		if lo.finiteCallApplication(fn, map[string]bool{}) {
			t.Fatal("a mutable-global callee was application-eligible")
		}
	})

	t.Run("declared effect", func(t *testing.T) {
		fn := parse("effectful: (a: u32) -> u32 = a")
		fn.Effects = []*ast.EffectName{{Namespace: "Host", Name: "Write"}}
		lo := newLowering(fn)
		if lo.finiteCallApplication(fn, map[string]bool{}) {
			t.Fatal("an effectful callee was application-eligible")
		}
	})

	t.Run("unknown invocation", func(t *testing.T) {
		fn := parse("unknown: (a: u32) -> u32 = mystery(a)")
		lo := newLowering(fn)
		if lo.finiteCallApplication(fn, map[string]bool{}) {
			t.Fatal("an unknown invocation was application-eligible")
		}
	})

	t.Run("foreign transitive call", func(t *testing.T) {
		foreign := parse("host: (a: u32) -> u32 = a")
		foreign.ExternSymbol = "host"
		outer := parse("outer: (a: u32) -> u32 = host(a)")
		lo := newLowering(outer)
		lo.functions = map[string]*ast.FunctionStatement{"host": foreign}
		if lo.finiteCallApplication(outer, map[string]bool{}) {
			t.Fatal("a callee reaching a foreign call was application-eligible")
		}
	})
}

func TestApplicationLeavesFollowDeclaredOrder(t *testing.T) {
	u8 := &oakType{kind: oakScalar, width: 8}
	u16 := &oakType{kind: oakScalar, width: 16}
	typ := &oakType{kind: oakRecord, fields: []oakField{{name: "second", typ: u16}, {name: "first", typ: u8}}}
	second := paramTerm("second", 16)
	first := paramTerm("first", 8)
	value := &oakValue{typ: typ, fields: map[string]*oakValue{
		"first":  {typ: u8, scalar: first},
		"second": {typ: u16, scalar: second},
	}}
	var got []*term
	bits := 0
	if !appendApplicationLeaves(value, typ, &got, &bits) {
		t.Fatal("finite record did not flatten")
	}
	if len(got) != 2 || got[0] != second || got[1] != first || bits != 24 {
		t.Fatalf("flattened leaves = %#v, bits=%d", got, bits)
	}
}

// A standalone law must see the definition of a bounded callee. Congruence
// alone cannot prove its arithmetic, and an arbitrary application value must
// never stand in for a real counterexample. Native call summaries keep their
// separate profitability policy (TestFiniteCallLowersToApplication).
func TestTheoremExpandsFiniteCallBodies(t *testing.T) {
	for _, tc := range []struct {
		name, callee, claim string
		want                DecisionKind
	}{
		{"true", "step: (x: u32) -> u32 { out: u32 = x\n i: u32 = 0\n while i < u32(2) { out = out + u32(1)\n i = i + u32(1) }\n out }", "law: (x: u32) -> Bool = step(x) == x + u32(2)", DecisionProven},
		{"false", "step: (x: u32) -> u32 { out: u32 = x\n i: u32 = 0\n while i < u32(2) { out = out + u32(1)\n i = i + u32(1) }\n out }", "law: (x: u32) -> Bool = step(x) == x + u32(3)", DecisionRefuted},
		{"trap", "step: (x: u32) -> u32 { assert(x != u32(0))\n out: u32 = x\n i: u32 = 0\n while i < u32(2) { out = out + u32(1)\n i = i + u32(1) }\n out }", "law: (x: u32) -> Bool = step(x) == x + u32(2)", DecisionRefuted},
		{"unbounded", "step: (x: u32) -> u32 { i: u32 = 0\n while i < x { i = i + u32(1) }\n i }", "law: (x: u32) -> Bool = step(x) == x", DecisionUndecided},
	} {
		t.Run(tc.name, func(t *testing.T) {
			callee, err := parseSignatureWithBody(tc.callee)
			if err != nil {
				t.Fatal(err)
			}
			law, err := parseSignatureWithBody(tc.claim)
			if err != nil {
				t.Fatal(err)
			}
			got := DecideTheorem(law, map[string]*ast.FunctionStatement{"step": callee})
			if got.Kind != tc.want {
				t.Fatalf("got %v: %s, want %v", got.Kind, got.Message, tc.want)
			}
		})
	}
}
