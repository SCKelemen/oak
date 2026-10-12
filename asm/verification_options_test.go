package asm

import (
	"go/ast"
	"go/parser"
	"go/token"
	"os"
	"reflect"
	"strconv"
	"strings"
	"sync"
	"testing"
)

func TestVerificationOptionsParsingAndIdentity(t *testing.T) {
	zero := VerificationOptions{}
	if zero != NewVerificationOptions("", "", "") || zero.CacheIdentity() != NewVerificationOptions("", "", "").CacheIdentity() {
		t.Fatal("zero options must be exactly the constructed defaults")
	}
	for _, tc := range []struct {
		off  string
		mask uint8
	}{
		{"", 0}, {"bounded", 1}, {"onesided", 2}, {"components", 4}, {"selfprune", 8},
		{"bounded,onesided,components,selfprune", 15}, {"bounded,bounded,,unknown", 1},
		{" bounded,bounded ,ONESIDED", 0}, {",components,,", 4},
	} {
		o := NewVerificationOptions(tc.off, "", "")
		if o.disabled != tc.mask {
			t.Errorf("off %q: got %d want %d", tc.off, o.disabled, tc.mask)
		}
		for _, name := range []string{"bounded", "onesided", "components", "selfprune", "unknown"} {
			if o.verifyOff(name) != (tc.mask&verificationRuleBit(name) != 0) {
				t.Errorf("rule %q in %q", name, tc.off)
			}
		}
	}
	for _, tc := range []struct {
		text  string
		limit int
	}{
		{"", 0}, {"0", 0}, {"base", 0}, {"high", 8 * blastNodeBudget},
		{"-1", 0}, {"garbage", 0}, {" high", 0}, {"999999999999999999999999", 0},
		{strconv.Itoa(blastNodeBudget), 0}, {strconv.Itoa(blastNodeBudget + 1), blastNodeBudget + 1},
	} {
		if got := NewVerificationOptions("", tc.text, "").escalationBudget(); got != tc.limit {
			t.Errorf("budget %q: %d != %d", tc.text, got, tc.limit)
		}
	}
	seen := map[string]bool{}
	for _, raw := range [][3]string{{"", "", ""}, {"bounded", "", ""}, {"unknown", "", ""}, {"", "base", ""}, {"", "", "f"}, {"a,b", "c", ""}, {"a", "b,c", ""}, {"a\x00b", "", ""}} {
		o := NewVerificationOptions(raw[0], raw[1], raw[2])
		if seen[o.CacheIdentity()] {
			t.Fatalf("raw settings collided: %q", raw)
		}
		seen[o.CacheIdentity()] = true
		if o.SelectionActive() != (raw[2] != "") {
			t.Fatalf("selection presence changed: %q", raw)
		}
	}
	for _, tc := range []struct {
		only, name string
		match      bool
	}{
		{"foo", "foo", true}, {"foo", "foobar", false}, {" foo , bar ", "bar", true}, {"foo,,bar", "bar", true}, {"Foo", "foo", false},
	} {
		if got := verifyOnlyNames(tc.only, tc.name); got != tc.match {
			t.Errorf("selection %q/%q: %v", tc.only, tc.name, got)
		}
	}
}

func TestVerificationOptionsExplicitAndLegacyEntry(t *testing.T) {
	decl := "options_add: (left, right: u32) -> u32"
	unit, errs := ParseUnit("options.oakasm", decl+" = {\n bind w0 = left\n bind w1 = right\n add w0, w0, w1\n ret\n}\n")
	if len(errs) != 0 {
		t.Fatal(errs)
	}
	sig, err := parseSignature(decl)
	if err != nil {
		t.Fatal(err)
	}
	spec, err := parseSignatureWithBody(decl + " = left + right")
	if err != nil {
		t.Fatal(err)
	}
	fn := unit.Functions[0]
	t.Setenv("OAK_VERIFY_OFF", "")
	t.Setenv("OAK_VERIFY_BUDGET", "")
	t.Setenv("OAK_VERIFY_ONLY", "")
	want := VerifyWithOptions(fn, sig, spec.Body, VerificationOptions{})
	if want.Kind != VerdictProven {
		t.Fatalf("fixture must prove: %+v", want)
	}
	if got := Verify(fn, sig, spec.Body); !reflect.DeepEqual(got, want) {
		t.Fatalf("legacy default parity: %+v != %+v", got, want)
	}
	t.Setenv("OAK_VERIFY_OFF", "bounded,onesided,components,selfprune")
	t.Setenv("OAK_VERIFY_BUDGET", "high")
	t.Setenv("OAK_VERIFY_ONLY", "another_function")
	if got := VerifyWithOptions(fn, sig, spec.Body, VerificationOptions{}); !reflect.DeepEqual(got, want) {
		t.Fatalf("ambient settings contaminated explicit defaults: %+v", got)
	}
	if got := Verify(fn, sig, spec.Body); got.Kind != VerdictTrusted || got.Message != "skipped under OAK_VERIFY_ONLY" {
		t.Fatalf("legacy wrapper did not recapture selection: %+v", got)
	}
	// Selection must remain a trusted skip, including when lower stages would panic.
	if got := VerifyWithOptions(fn, nil, nil, NewVerificationOptions("", "", "other")); got.Kind != VerdictTrusted {
		t.Fatalf("selection became proof: %+v", got)
	}
}

func TestVerificationOptionsBoundedOwnerIsolation(t *testing.T) {
	for _, off := range []string{"bounded", "", "bounded", ""} {
		session := &verificationSession{options: NewVerificationOptions(off, "", "")}
		for _, remaining := range []int{20, 0, -3} {
			owner := &nodeBudget{session: session, remaining: remaining, calls: 7, loop: true}
			want := 5
			if remaining < want || off != "" {
				want = remaining
			}
			owner.bounded(5, func(child *nodeBudget) (bool, bool) {
				if child.session != session || child.remaining != want || child.calls != 7 || !child.loop || !child.optimistic {
					t.Fatalf("child did not inherit configuration/ledger: %+v", child)
				}
				child.remaining -= 2
				child.calls++
				return false, false
			})
			if owner.remaining != remaining-2 || owner.calls != 8 {
				t.Fatalf("transfer changed: %+v", owner)
			}
		}
	}
	var wg sync.WaitGroup
	for _, off := range []string{"bounded", ""} {
		wg.Add(1)
		go func(off string) {
			defer wg.Done()
			session := &verificationSession{options: NewVerificationOptions(off, "", "")}
			for i := 0; i < 32; i++ {
				owner := &nodeBudget{session: session, remaining: 20}
				owner.bounded(5, func(child *nodeBudget) (bool, bool) {
					want := 5
					if off != "" {
						want = 20
					}
					if child.remaining != want || child.session != session {
						t.Errorf("concurrent session contamination: %q %+v", off, child)
					}
					return true, true
				})
			}
		}(off)
	}
	wg.Wait()
}

// This source gate makes the less frequently exercised nil-budget, header,
// vector, composite and independent trap/effect edges compile-visible. It does
// not replace semantic regression tests or claim a refinement theorem.
func TestVerificationOptionsProductionPropagation(t *testing.T) {
	methods := strings.Fields("verifyChunk verifyChunkJoining verifyExecution verifyExecutionWithApplications decideEqual decideCells decideEffects decideSpans verifyTrapDomain verifyVectorResult verifyLoops verifyLoopsWith headersEqual impliesEqual impliesEqualWithin impliesEqualDepth impliesEqualDepthUncached impliesFiniteConditionalEqual splitDecide splitDecideOn premiseUnderItself impliesEqualOneSidedArms impliesEqualByArms impliesEqualCongruent impliesEqualArms")
	selected := map[string]bool{}
	for _, name := range methods {
		selected[name] = true
	}
	files := []string{"verify.go", "verify_vector.go", "effects.go", "trap_domain.go", "loops.go", "blast.go", "verification_options.go"}
	tracker := map[string]int{}
	owners := 0
	for _, path := range files {
		src, err := os.ReadFile(path)
		if err != nil {
			t.Fatal(err)
		}
		if strings.Contains(string(src), "verifyOffOnce") || strings.Contains(string(src), "verifyOffRules") {
			t.Fatalf("global option state in %s", path)
		}
		file, err := parser.ParseFile(token.NewFileSet(), path, src, 0)
		if err != nil {
			t.Fatal(err)
		}
		for _, decl := range file.Decls {
			fn, ok := decl.(*ast.FuncDecl)
			if !ok {
				continue
			}
			ast.Inspect(fn.Body, func(node ast.Node) bool {
				if call, ok := node.(*ast.CallExpr); ok {
					if id, ok := call.Fun.(*ast.Ident); ok {
						if selected[id.Name] {
							t.Errorf("%s:%s discards session via %s", path, fn.Name.Name, id.Name)
						}
						if id.Name == "trackBDDResourceExhaustion" {
							tracker[fn.Name.Name]++
						}
					}
					if sel, ok := call.Fun.(*ast.SelectorExpr); ok && sel.Sel.Name == "Getenv" && len(call.Args) == 1 {
						if lit, ok := call.Args[0].(*ast.BasicLit); ok && (lit.Value == `"OAK_VERIFY_OFF"` || lit.Value == `"OAK_VERIFY_BUDGET"` || lit.Value == `"OAK_VERIFY_ONLY"`) && fn.Name.Name != "Verify" {
							t.Errorf("selected ambient read below public entry: %s:%s", path, fn.Name.Name)
						}
					}
				}
				if literal, ok := node.(*ast.CompositeLit); ok {
					if typ, ok := literal.Type.(*ast.Ident); ok && typ.Name == "nodeBudget" {
						owners++
						hasSession := false
						for _, elem := range literal.Elts {
							if kv, ok := elem.(*ast.KeyValueExpr); ok {
								if key, ok := kv.Key.(*ast.Ident); ok && key.Name == "session" {
									hasSession = true
								}
							}
						}
						if !hasSession {
							t.Errorf("owner lost session: %s:%s", path, fn.Name.Name)
						}
					}
				}
				return true
			})
		}
	}
	if len(tracker) != 1 || tracker["VerifyWithOptions"] != 1 {
		t.Fatalf("resource tracking must occur exactly once at explicit entry: %v", tracker)
	}
	if owners != 5 {
		t.Fatalf("review changed proof-owner inventory: %d", owners)
	}
}

func TestVerificationOptionsRuleEvaluationOrder(t *testing.T) {
	src, err := os.ReadFile("loops.go")
	if err != nil {
		t.Fatal(err)
	}
	text := string(src)
	// These initializers run before the disabled-rule condition. Moving the
	// condition before them changes work and budget debit even if a rule is off.
	for _, required := range []string{
		`if holds, decided := session.impliesEqualOneSidedArms(premise, a, b, widthOf, budget, depth); decided && !session.optionsValue().verifyOff("onesided") {`,
		`if cb := componentBlaster(names, widths, premise, a, b); cb != nil && !session.optionsValue().verifyOff("components") {`,
		`if limit > budget.remaining || budget.session.optionsValue().verifyOff("bounded") {`,
		`if session.optionsValue().verifyOff("selfprune") || premise.kind == termConst || termSize(premise, map[*term]int{}) < premiseSelfPruneSize {`,
	} {
		if !strings.Contains(text, required) {
			t.Errorf("review rule ordering/debit change: missing %s", required)
		}
	}
}

func TestVerificationOptionsOneSidedDisabledStillAttempts(t *testing.T) {
	// The one-sided helper itself must still run with the switch disabled;
	// acceptance is controlled by its caller after this attempt completes.
	var wantCalls, wantRemaining int
	for i, off := range []string{"", "onesided"} {
		session := &verificationSession{options: NewVerificationOptions(off, "", "")}
		k, x, y := paramTerm("k", 32), paramTerm("x", 32), paramTerm("y", 32)
		c := cmpTerm("lo", paramTerm("p", 32), constTerm(7, 32))
		merged := cmpTerm("lo", k, iteTerm(c, x, y))
		split := iteTerm(c, cmpTerm("lo", k, x), cmpTerm("lo", k, y))
		budget := &nodeBudget{session: session, remaining: loopProofNodeBudget, loop: true}
		if holds, decided := session.impliesEqualOneSidedArms(constTerm(1, 1), merged, split, func(string) int { return 32 }, budget, 0); !decided || !holds {
			t.Fatalf("disabled helper skipped its prior attempt: holds=%v decided=%v", holds, decided)
		}
		if i == 0 {
			wantCalls, wantRemaining = budget.calls, budget.remaining
		} else if budget.calls != wantCalls || budget.remaining != wantRemaining {
			t.Fatalf("disabled attempt ledger changed: calls %d/%d remaining %d/%d", budget.calls, wantCalls, budget.remaining, wantRemaining)
		}
	}
}
