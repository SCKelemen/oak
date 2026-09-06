package discipline

import (
	"testing"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/diagnostic"
	"github.com/SCKelemen/oak/parser"
	"github.com/SCKelemen/oak/scanner"
)

func analyze(t *testing.T, input string) *Result {
	t.Helper()
	p := parser.New(scanner.New(input))
	program := p.ParseProgram()
	if errs := p.Errors(); len(errs) > 0 {
		t.Fatalf("parser errors for %q: %v", input, errs)
	}
	return AnalyzeProgram(program)
}

func countCode(result *Result, code diagnostic.Code) int {
	count := 0
	for _, d := range result.Diagnostics() {
		if d.Code == string(code) {
			count++
		}
	}
	return count
}

// The rank certificate must satisfy Oak.Discipline.Ranked: strict decrease on
// stack calls, no increase on tail calls.
func assertRankedCertificate(t *testing.T, program *ast.Program, result *Result) {
	t.Helper()
	functions := make(map[string]*ast.FunctionStatement)
	for _, stmt := range program.Statements {
		if fn, ok := stmt.(*ast.FunctionStatement); ok && fn.Name != nil {
			functions[fn.Name.Value] = fn
		}
	}
	for name, fn := range functions {
		for _, edge := range collectCallEdges(fn, functions) {
			callerRank, callerOK := result.Ranks[name]
			calleeRank, calleeOK := result.Ranks[edge.callee]
			if !callerOK || !calleeOK {
				t.Fatalf("missing rank for edge %s -> %s", name, edge.callee)
			}
			if edge.tail {
				if calleeRank > callerRank {
					t.Fatalf("tail edge %s -> %s increases rank (%d -> %d)", name, edge.callee, callerRank, calleeRank)
				}
			} else if calleeRank >= callerRank {
				t.Fatalf("stack edge %s -> %s does not decrease rank (%d -> %d)", name, edge.callee, callerRank, calleeRank)
			}
		}
	}
}

func TestLinearCallChainIsAcceptedWithValidRanks(t *testing.T) {
	input := "fn c(x: i32) -> i32 { x }\nfn b(x: i32) -> i32 { 1 + c(x) }\nfn a(x: i32) -> i32 { 1 + b(x) }"
	p := parser.New(scanner.New(input))
	program := p.ParseProgram()
	if errs := p.Errors(); len(errs) > 0 {
		t.Fatalf("parser errors: %v", errs)
	}
	result := AnalyzeProgram(program)
	if len(result.Diagnostics()) != 0 {
		t.Fatalf("linear chain must be clean, got %#v", result.Diagnostics())
	}
	assertRankedCertificate(t, program, result)
}

func TestDiamondCallGraphIsAccepted(t *testing.T) {
	input := "fn d(x: i32) -> i32 { x }\nfn b(x: i32) -> i32 { 1 + d(x) }\nfn c(x: i32) -> i32 { 2 + d(x) }\nfn a(x: i32) -> i32 { b(x) + c(x) }"
	result := analyze(t, input)
	if len(result.Diagnostics()) != 0 {
		t.Fatalf("diamond DAG must be clean, got %#v", result.Diagnostics())
	}
}

func TestStackRecursionIsRejected(t *testing.T) {
	// The self call feeds an addition, so it consumes a frame per iteration.
	result := analyze(t, "fn f(n: i32) -> i32 { 1 + f(n) }")
	if got := countCode(result, CodeStackRecursion); got != 1 {
		t.Fatalf("stack recursion produced %d %s diagnostics, want exactly 1: %#v",
			got, CodeStackRecursion, result.Diagnostics())
	}
}

func TestMutualStackRecursionIsRejected(t *testing.T) {
	result := analyze(t, "fn f(n: i32) -> i32 { 1 + g(n) }\nfn g(n: i32) -> i32 { 1 + f(n) }")
	if got := countCode(result, CodeStackRecursion); got != 1 {
		t.Fatalf("mutual stack recursion produced %d %s diagnostics, want exactly 1: %#v",
			got, CodeStackRecursion, result.Diagnostics())
	}
}

func TestSelfTailRecursionLowersToLoopSilently(t *testing.T) {
	result := analyze(t, "fn f(n: i32) -> i32 { f(n) }")
	if len(result.Diagnostics()) != 0 {
		t.Fatalf("loop-lowered self tail recursion must be silent, got %#v", result.Diagnostics())
	}
	if !result.LoopLowered["f"] {
		t.Fatal("self tail recursion in result position must be marked loop-lowered")
	}
}

func TestSelfTailRecursionWithBlockBodyLowers(t *testing.T) {
	result := analyze(t, "fn f(n: i32) -> i32 { x: i32 = 1\nf(x) }")
	if len(result.Diagnostics()) != 0 {
		t.Fatalf("block-body self tail recursion must be silent, got %#v", result.Diagnostics())
	}
	if !result.LoopLowered["f"] {
		t.Fatal("block-body self tail recursion must be marked loop-lowered")
	}
}

// Same-signature mutual tail recursion lowers to a trampoline: silent.
func TestMutualTailRecursionWithMatchingSignaturesLowers(t *testing.T) {
	result := analyze(t, "fn f(n: i32) -> i32 { g(n) }\nfn g(n: i32) -> i32 { f(n) }")
	if len(result.Diagnostics()) != 0 {
		t.Fatalf("trampoline-lowerable cycle must be silent, got %#v", result.Diagnostics())
	}
	if len(result.TrampolineGroups) != 1 {
		t.Fatalf("expected one trampoline group, got %#v", result.TrampolineGroups)
	}
	group := result.TrampolineGroups[0]
	if len(group) != 2 || group[0] != "f" || group[1] != "g" {
		t.Fatalf("trampoline group = %#v, want [f g]", group)
	}
}

// Mismatched signatures cannot share one engine frame: the obligation stays.
func TestMutualTailRecursionWithMismatchedSignaturesRecordsObligation(t *testing.T) {
	result := analyze(t, "fn f(n: i32) -> i32 { g(n) }\nfn g(m: i32) -> i32 { f(m) }")
	if got := countCode(result, CodeTailRecursionObligation); got != 1 {
		t.Fatalf("mismatched-signature tail cycle produced %d %s records, want exactly 1: %#v",
			got, CodeTailRecursionObligation, result.Diagnostics())
	}
	for _, d := range result.Diagnostics() {
		if d.Code == string(CodeTailRecursionObligation) && d.Severity != diagnostic.SeverityWarning {
			t.Fatalf("tail obligation must be a warning, got severity %v", d.Severity)
		}
	}
	if got := countCode(result, CodeStackRecursion); got != 0 {
		t.Fatalf("pure tail cycle must not be a stack-recursion error, got %d", got)
	}
	if len(result.TrampolineGroups) != 0 {
		t.Fatalf("mismatched signatures must not form a trampoline group: %#v", result.TrampolineGroups)
	}
}

// A self call whose arguments also self-call is not loop-lowerable: the inner
// call consumes a frame.
func TestSelfCallInArgumentIsStackRecursion(t *testing.T) {
	result := analyze(t, "fn f(n: i32) -> i32 { f(f(n)) }")
	if got := countCode(result, CodeStackRecursion); got != 1 {
		t.Fatalf("nested self call produced %d %s diagnostics, want exactly 1: %#v",
			got, CodeStackRecursion, result.Diagnostics())
	}
}

func TestBuiltinsAndUnknownCalleesAreNotEdges(t *testing.T) {
	result := analyze(t, "fn f(buf: [16]u8) -> u8 { v: []u8 = buf[0:8]\nexternal(v) }")
	if len(result.Diagnostics()) != 0 {
		t.Fatalf("builtin/unknown callees must not create edges, got %#v", result.Diagnostics())
	}
}

// Terminating recursion: a lowerable-shape match (base case + tail call)
// counts as tail position, so factorial-style functions lower to loops.
func TestFactorialShapedRecursionLowersToLoop(t *testing.T) {
	result := analyze(t, "fn fact(n: i32, acc: i32) -> i32 {\nn ?\n  | 0 -> acc\n  | _ -> fact(n - 1, acc * n)\n}")
	if len(result.Diagnostics()) != 0 {
		t.Fatalf("factorial-shaped recursion must be silent, got %#v", result.Diagnostics())
	}
	if !result.LoopLowered["fact"] {
		t.Fatal("factorial-shaped self tail recursion must be loop-lowered")
	}
}

// A self call inside a non-lowerable arm (binding pattern) fails closed to
// the recorded obligation.
func TestSelfCallInBindingArmIsNotLowered(t *testing.T) {
	result := analyze(t, "fn f(n: i32) -> i32 {\nn ?\n  | 0 -> 0\n  | m -> f(m - 1)\n}")
	if result.LoopLowered["f"] {
		t.Fatal("binding-pattern arm must not be loop-lowered")
	}
	if got := countCode(result, CodeTailRecursionObligation); got != 1 {
		t.Fatalf("non-lowerable tail cycle produced %d %s records, want exactly 1: %#v",
			got, CodeTailRecursionObligation, result.Diagnostics())
	}
}

// Bounded loops (docs/spec/85-discipline.md section 3, Oak.BoundedLoop): the
// canonical counter shape is recognized; everything else records OAK-D0103.
func TestBoundedLoopShapes(t *testing.T) {
	tests := []struct {
		name       string
		input      string
		wantD0103  int
	}{
		{"canonical literal bound", "i: i32 = 0\nwhile i < 10 {\ni = i + 1\n}", 0},
		{"canonical identifier bound", "n: i32 = 8\ni: i32 = 0\nwhile i < n {\ni = i + 2\n}", 0},
		{"inclusive bound", "i: i32 = 0\nwhile i <= 10 {\ni = i + 1\n}", 0},
		{"boolean condition", "i: i32 = 0\nwhile true {\ni = i + 1\n}", 1},
		{"missing advance", "i: i32 = 0\nwhile i < 10 {\nx: i32 = i\n}", 1},
		{"decrementing advance", "i: i32 = 0\nwhile i < 10 {\ni = i - 1\n}", 1},
		{"double assignment to counter", "i: i32 = 0\nwhile i < 10 {\ni = i + 1\ni = i + 1\n}", 1},
		{"bound mutated in body", "n: i32 = 8\ni: i32 = 0\nwhile i < n {\ni = i + 1\nn = n + 1\n}", 1},
	}
	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			result := analyze(t, tt.input)
			if got := countCode(result, CodeUnboundedLoop); got != tt.wantD0103 {
				t.Errorf("input %q: %d %s obligations, want %d: %#v",
					tt.input, got, CodeUnboundedLoop, tt.wantD0103, result.Diagnostics())
			}
		})
	}
}

// ADT variant arms (nil or binding payload) are lowerable tail sites, so
// recursion with an ADT base case lowers to a loop.
func TestVariantArmTailRecursionLowers(t *testing.T) {
	result := analyze(t, "Count: type =\n  | More: i32\n  | Done\n\nwalk: (c: Count, acc: i32): i32 = c ?\n  | .Done -> acc\n  | .More(n) -> walk(.Done, acc + n)\n")
	if len(result.Diagnostics()) != 0 {
		t.Fatalf("variant-arm tail recursion must be silent, got %#v", result.Diagnostics())
	}
	if !result.LoopLowered["walk"] {
		t.Fatal("variant-arm self tail recursion must be loop-lowered")
	}
}
