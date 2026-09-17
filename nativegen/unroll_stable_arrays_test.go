package nativegen

import (
	"reflect"
	"strings"
	"testing"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/opt"
)

func stableArrayEligibilityBody(name string, computed, borrowed bool) ast.Expression {
	index := ast.Expression(&ast.IntegerLiteral{Value: 0})
	if computed {
		index = &ast.Identifier{Value: "index"}
	}
	statements := []ast.Statement{
		&ast.VariableDeclaration{Name: &ast.Identifier{Value: name}, Type: &ast.IndexExpression{
			Left: &ast.Identifier{Value: "u32"}, Index: &ast.IntegerLiteral{Value: 2},
		}},
		&ast.ExpressionStatement{Expression: &ast.IndexExpression{Left: &ast.Identifier{Value: name}, Index: index}},
	}
	if borrowed {
		statements = append(statements, &ast.ExpressionStatement{Expression: &ast.PrefixExpression{
			Operator: "&", Right: &ast.Identifier{Value: name},
		}})
	}
	return &ast.BlockExpression{Block: &ast.BlockStatement{Statements: statements}}
}

func TestUnrollStableArrayEligibilityIsConjunction(t *testing.T) {
	for _, test := range []struct {
		name             string
		currentComputed  bool
		currentBorrowed  bool
		originalComputed bool
		originalBorrowed bool
		noReference      bool
		want             bool
	}{
		{name: "both-admit", want: true},
		{name: "no-reference-keeps-current", noReference: true, want: true},
		{name: "original-computed-veto", originalComputed: true},
		{name: "original-borrow-veto", originalBorrowed: true},
		{name: "current-computed-still-refuses", currentComputed: true},
		{name: "current-borrow-still-refuses", currentBorrowed: true},
		{name: "no-reference-current-refusal", currentBorrowed: true, noReference: true},
	} {
		t.Run(test.name, func(t *testing.T) {
			current := &ast.FunctionStatement{Body: stableArrayEligibilityBody("words", test.currentComputed, test.currentBorrowed)}
			original := stableArrayEligibilityBody("words", test.originalComputed, test.originalBorrowed)
			beforeCurrent, beforeOriginal := cloneNode(current.Body), cloneNode(original)
			g := &generator{fn: current, scalarEligibilityReference: original}
			if test.noReference {
				g.scalarEligibilityReference = nil
			}
			if got := g.scalarArrayReplaceable("words", scalars["u32"], 2); got != test.want {
				t.Fatalf("scalar eligibility=%v, want%v", got, test.want)
			}
			if !reflect.DeepEqual(current.Body, beforeCurrent) || !reflect.DeepEqual(original, beforeOriginal) || g.fn != current {
				t.Fatal("eligibility check changed the current function or placement reference")
			}
		})
	}
}

func TestUnrollStableArrayReferenceRequiresOriginalArray(t *testing.T) {
	for _, kind := range []string{"missing", "ambiguous", "wrong-extent", "wrong-element-width", "wrong-element-signedness", "not-array", "unknown-element", "missing-type", "new-trip-name"} {
		t.Run(kind, func(t *testing.T) {
			name := "words"
			current := &ast.FunctionStatement{Body: stableArrayEligibilityBody(name, false, false)}
			original := stableArrayEligibilityBody(name, false, false).(*ast.BlockExpression)
			declaration := original.Block.Statements[0].(*ast.VariableDeclaration)
			switch kind {
			case "missing":
				original.Block.Statements = nil
			case "ambiguous":
				original.Block.Statements = append(original.Block.Statements, cloneNode(declaration).(ast.Statement))
			case "wrong-extent":
				declaration.Type.(*ast.IndexExpression).Index.(*ast.IntegerLiteral).Value = 3
			case "wrong-element-width":
				declaration.Type.(*ast.IndexExpression).Left = &ast.Identifier{Value: "u64"}
			case "wrong-element-signedness":
				declaration.Type.(*ast.IndexExpression).Left = &ast.Identifier{Value: "i32"}
			case "not-array":
				declaration.Type = &ast.Identifier{Value: "u32"}
			case "unknown-element":
				declaration.Type.(*ast.IndexExpression).Left = &ast.Identifier{Value: "UnknownRecord"}
			case "missing-type":
				declaration.Type = nil
			case "new-trip-name":
				name = "words_t0"
				current.Body = stableArrayEligibilityBody(name, false, false)
			}
			if !scalarReplaceable(current, name, 2) {
				t.Fatal("fixture must be admitted by the current predicate")
			}
			g := &generator{fn: current, scalarEligibilityReference: original}
			if g.scalarArrayReplaceable(name, scalars["u32"], 2) {
				t.Fatal("missing or mismatched original array authorized scalar replacement")
			}
		})
	}
}

const stableUnrollArraySource = `f: (seed: u32): [8]u32 {
  v: [8]u32 = [8]u32{seed, seed, seed, seed, seed, seed, seed, seed}
  m: [2]u32 = [2]u32{seed, seed + u32(1)}
  i: u32 = u32(0)
  while i < u32(8) {
    v[i] = v[i] + m[0] * u32(2)
    i = i + u32(1)
  }
  v
}`

func TestUnrollStableArrayStagesKeepImmutableReference(t *testing.T) {
	fn, functions, _, tc := checkedFillFunction(t, stableUnrollArraySource, "f")
	before := cloneNode(fn.Body)
	stages := computeStages(fn, functions, nil, tc, false, false, false, false, false, false, false, false, false, false, true, true)
	constantStages := 0
	for _, stage := range stages {
		unrolled := false
		for _, site := range stage.sites {
			unrolled = unrolled || site.Rewrite == "small constant unrolling"
		}
		if !unrolled {
			if stage.scalarEligibilityReference != nil {
				t.Fatal("pre-unroll fallback acquired a placement veto")
			}
			continue
		}
		constantStages++
		if stage.scalarEligibilityReference == nil || stage.scalarEligibilityReference == fn.Body ||
			stage.scalarEligibilityReference == stage.body || !reflect.DeepEqual(stage.scalarEligibilityReference, before) {
			t.Fatal("unroll stage lacks its independent original-array snapshot")
		}
		current := *fn
		current.Body = stage.body
		g := &generator{fn: &current, scalarEligibilityReference: stage.scalarEligibilityReference}
		if !scalarReplaceable(&current, "v", 8) || g.scalarArrayReplaceable("v", scalars["u32"], 8) {
			t.Fatal("unrolling changed v from computed-index storage to scalar homes")
		}
		if !g.scalarArrayReplaceable("m", scalars["u32"], 2) {
			t.Fatal("the already eligible message array lost scalar replacement")
		}
		if !stage.judged {
			t.Fatal("unrolled stage lost its actual verifier reference")
		}
	}
	if constantStages == 0 || !reflect.DeepEqual(fn.Body, before) {
		t.Fatal("no constant stage, or source syntax mutated")
	}
	// Later source-stage rewrites cannot alias the separate placement tree.
	for _, stage := range stages {
		if stage.scalarEligibilityReference != nil {
			stage.body.(*ast.BlockExpression).Block.Statements[0].(*ast.VariableDeclaration).Name.Value = "changed_output"
			if !reflect.DeepEqual(stage.scalarEligibilityReference, before) || !reflect.DeepEqual(fn.Body, before) {
				t.Fatal("rewritten syntax aliases the eligibility snapshot or source")
			}
			break
		}
	}
}

func TestUnrollStableArraysLowerWithoutChangingVerifierBody(t *testing.T) {
	fn, functions, records, tc := checkedFillFunction(t, stableUnrollArraySource, "f")
	before := cloneNode(fn.Body)
	out, err := CompileFor(Lane{Arch: asm.ArchArm64, NoReductions: true, UnrollSmall: true}, fn, functions, records, nil, nil, tc)
	if err != nil {
		t.Fatal(err)
	}
	if UnrolledSmall(out) == 0 || UnrolledConstant(out) != 0 || out.Body == nil || out.Body == fn.Body || !reflect.DeepEqual(fn.Body, before) {
		t.Fatal("unroll lowering lost its actual rewritten reference or mutated source")
	}
	if objects := FrameObjects(out); len(objects) != 0 {
		t.Fatalf("v must remain in the result area and m in scalar homes, got frame objects %+v", objects)
	}
	resultStore := false
	for _, item := range out.Items {
		if instruction, ok := item.(asm.Instruction); ok && instruction.Mnemonic == "str" {
			if memory, ok := instruction.Operands[1].(asm.Memory); ok && memory.Base.Class == asm.ClassX && memory.Base.Num == 8 {
				resultStore = true
			}
		}
	}
	if !resultStore {
		t.Fatal("result-area stores disappeared")
	}
	if findings := asm.Check(out, fn, nil); len(findings) != 0 {
		t.Fatalf("seam refused: %v", findings)
	}
	if verdict := asm.Verify(out, fn, out.Body); verdict.Kind != asm.VerdictProven {
		t.Fatalf("actual unrolled body was not proven: %s: %s", verdict.Kind, verdict.Message)
	}
}

func TestUnrollStableArraysFixedCopyBudget(t *testing.T) {
	fn, _, _, _ := checkedFillFunction(t, `f: (seed: u32): u32 {
  total: u32 = seed
  large: u32 = u32(0)
  while large < u32(7) {
    `+strings.Repeat("total = total + u32(1)\n", 48)+`
    large = large + u32(1)
  }
  small: u32 = u32(0)
  while small < u32(4) {
    total = total + small
    small = small + u32(1)
  }
  total
}`, "f")
	if maxConstantExpansion != 512 {
		t.Fatalf("small unroll budget changed: %d", maxConstantExpansion)
	}
	before := cloneNode(fn.Body)
	first, changed := unrollSmallConstantLoops(fn, fn.Body)
	second, changedAgain := unrollSmallConstantLoops(fn, fn.Body)
	if !changed || !changedAgain || !reflect.DeepEqual(constantUnrollLoopNames(first), []string{"large"}) {
		t.Fatalf("large loop refusal prevented small-loop expansion:\n%s", first.String())
	}
	if !reflect.DeepEqual(first, second) || !reflect.DeepEqual(fn.Body, before) {
		t.Fatal("selective unroll changed source or depended on prior invocation")
	}
	full, fullChanged := unrollConstantLoops(fn, fn.Body)
	if !fullChanged || len(constantUnrollLoopNames(full)) != 0 || !reflect.DeepEqual(fn.Body, before) {
		t.Fatalf("full unrolling acquired the small strategy's budget:\n%s", full.String())
	}
}

func TestUnrollSmallStageCacheSeparatesStrategies(t *testing.T) {
	for _, smallFirst := range []bool{false, true} {
		name := "full-first"
		if smallFirst {
			name = "small-first"
		}
		t.Run(name, func(t *testing.T) {
			fn, functions, _, tc := checkedFillFunction(t, stableUnrollArraySource, "f")
			before := cloneNode(fn.Body)
			var fullBody, smallBody ast.Expression
			for _, small := range []bool{smallFirst, !smallFirst, smallFirst, !smallFirst} {
				stages := rewriteStages(fn, functions, nil, tc, false, false, false, false, false, false, false, false, false, !small, small, false)
				if len(stages) != 2 {
					t.Fatalf("small=%v: want unrolled and source stages, got %d", small, len(stages))
				}
				stage := stages[0]
				if !stage.judged || len(stage.sites) != 1 || len(constantUnrollLoopNames(stage.body)) != 0 {
					t.Fatalf("small=%v: incomplete unroll stage: %+v", small, stage)
				}
				current := *fn
				current.Body = stage.body
				g := &generator{fn: &current, scalarEligibilityReference: stage.scalarEligibilityReference}
				if small {
					if stage.sites[0].Rewrite != "small constant unrolling" || stage.scalarEligibilityReference == nil || g.scalarArrayReplaceable("v", scalars["u32"], 8) {
						t.Fatal("small strategy reused a full-unroll stage or lost its placement veto")
					}
					if smallBody != nil && smallBody != stage.body {
						t.Fatal("small strategy was not memoized")
					}
					smallBody = stage.body
				} else {
					if stage.sites[0].Rewrite != "constant unrolling" || stage.scalarEligibilityReference != nil || !g.scalarArrayReplaceable("v", scalars["u32"], 8) {
						t.Fatal("full strategy reused a small-unroll stage or acquired its placement veto")
					}
					if fullBody != nil && fullBody != stage.body {
						t.Fatal("full strategy was not memoized")
					}
					fullBody = stage.body
				}
				if stages[1].body != fn.Body || stages[1].scalarEligibilityReference != nil || stages[1].judged {
					t.Fatal("source fallback was contaminated by an unroll strategy")
				}
			}
			if fullBody == smallBody || !reflect.DeepEqual(fn.Body, before) {
				t.Fatal("strategy caches shared a rewritten tree or mutated source")
			}
		})
	}
}

func TestUnrollSmallBudgetIsSharedAcrossTheBody(t *testing.T) {
	loop := func(name string) string {
		return name + `: u32 = u32(0)
  while ` + name + ` < u32(4) {
    ` + strings.Repeat("total = total + u32(1)\n", 12) + name + " = " + name + ` + u32(1)
  }
`
	}
	fn, _, _, _ := checkedFillFunction(t, `f: (seed: u32): u32 {
  total: u32 = seed
  `+loop("first")+loop("second")+`
  last: u32 = u32(0)
  while last < u32(4) {
    total = total + last
    last = last + u32(1)
  }
  total
}`, "f")
	before := cloneNode(fn.Body)
	small, changed := unrollSmallConstantLoops(fn, fn.Body)
	if !changed || !reflect.DeepEqual(constantUnrollLoopNames(small), []string{"second"}) {
		t.Fatalf("small budget was reset per loop, or refusal consumed the remaining budget:\n%s", small.String())
	}
	full, changed := unrollConstantLoops(fn, fn.Body)
	if !changed || len(constantUnrollLoopNames(full)) != 0 || !reflect.DeepEqual(fn.Body, before) {
		t.Fatal("full strategy acquired the small budget, or either strategy mutated source")
	}
}

func TestUnrollSmallRefusalKeepsOriginalPlacement(t *testing.T) {
	fn, functions, _, tc := checkedFillFunction(t, strings.Replace(stableUnrollArraySource, "u32(8) {", "seed {", 1), "f")
	stages := rewriteStages(fn, functions, nil, tc, false, false, false, false, false, false, false, false, false, false, true, false)
	if len(stages) != 1 || stages[0].body != fn.Body || stages[0].scalarEligibilityReference != nil {
		t.Fatal("refused small rewrite changed placement or fallback syntax")
	}
}

func TestUnrollSmallRegistryIsolation(t *testing.T) {
	registry := Registry()
	small, smallOK := registry.Lookup(TransformUnrollSmall)
	full, fullOK := registry.Lookup(TransformUnrollConst)
	if !smallOK || !fullOK {
		t.Fatal("constant unroll strategies missing from registry")
	}
	gated, isGated := small.(opt.Gated)
	neutral, hasShape := small.(opt.Neutral)
	if !isGated || !gated.NeedsVerdict() || !hasShape || neutral.ShapeNeutral() || small.Proof() != opt.LawLicensed || small.Phase() != opt.PhaseLoop {
		t.Fatal("small unroll must remain law-licensed, verifier-gated and shape-changing")
	}
	if gated, ok := full.(opt.Gated); ok && gated.NeedsVerdict() {
		t.Fatal("full unroll strategy unexpectedly acquired a new gate")
	}
	for _, arch := range []string{"", asm.ArchArm64} {
		identity := opt.Identity(Lane{Arch: arch, LoopRewrites: LoopRewriteEligibility{Constant: true}})
		smallCandidate, fullCandidate := small.Apply(identity), full.Apply(identity)
		if smallCandidate == nil || fullCandidate == nil {
			t.Fatalf("a strategy refused its AArch64 identity %q", arch)
		}
		if smallLane, fullLane := smallCandidate.Config.(Lane), fullCandidate.Config.(Lane); !smallLane.UnrollSmall || smallLane.UnrollConstant || !fullLane.UnrollConstant || fullLane.UnrollSmall {
			t.Fatal("strategies toggled each other's flags")
		}
		if full.Apply(smallCandidate) != nil || small.Apply(fullCandidate) != nil || small.Apply(smallCandidate) != nil || full.Apply(fullCandidate) != nil {
			t.Fatal("constant unroll strategies combined or applied twice")
		}
	}
	if small.Apply(opt.Identity(Lane{Arch: asm.ArchRV64})) != nil {
		t.Fatal("small unroll escaped its AArch64 lane")
	}
	if plain := PlainLane(Lane{UnrollConstant: true, UnrollSmall: true}); plain.UnrollConstant || plain.UnrollSmall {
		t.Fatal("plain fallback retained constant unrolling")
	}
	for _, arch := range []string{"", asm.ArchArm64, asm.ArchRV64} {
		out, err := CompileFor(Lane{Arch: arch, UnrollConstant: true, UnrollSmall: true}, nil, nil, nil, nil, nil, nil)
		if out != nil || err == nil {
			t.Fatalf("combined strategies accepted on %q", arch)
		}
		if _, unsupported := err.(Unsupported); unsupported {
			t.Fatal("conflicting strategy configuration became an ordinary unsupported-body fallback")
		}
	}
}

func TestUnrollSmallDoesNotRewriteRV64(t *testing.T) {
	fn, functions, records, tc := checkedFillFunction(t, `f: (seed: u32): u32 {
  total: u32 = seed
  i: u32 = u32(0)
  while i < u32(4) {
    total = total + i
    i = i + u32(1)
  }
  total
}`, "f")
	plain, err := CompileFor(Lane{Arch: asm.ArchRV64, NoReductions: true}, fn, functions, records, nil, nil, tc)
	if err != nil {
		t.Fatal(err)
	}
	small, err := CompileFor(Lane{Arch: asm.ArchRV64, NoReductions: true, UnrollSmall: true}, fn, functions, records, nil, nil, tc)
	if err != nil {
		t.Fatal(err)
	}
	if UnrolledSmall(small) != 0 || !reflect.DeepEqual(plain.Items, small.Items) || !reflect.DeepEqual(plain.Body, small.Body) {
		t.Fatal("AArch64 small strategy affected RV64 lowering")
	}
}
