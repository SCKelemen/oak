package compiler

import (
	"bytes"
	"fmt"
	"reflect"
	"testing"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/layout"
	"github.com/SCKelemen/oak/nativegen"
	"github.com/SCKelemen/oak/object"
	"github.com/SCKelemen/oak/opt"
	"github.com/SCKelemen/oak/parser"
	"github.com/SCKelemen/oak/scanner"
	"github.com/SCKelemen/oak/typechecker"
)

// Keep the whole checked syntax graph, including fields String omits, under
// observation. Exported fields let cloneSyntax copy every map and syntax node.
type nativeRecipeOwnedInputs struct {
	Root          *ast.Program
	Source        *ast.FunctionStatement
	Functions     map[string]*ast.FunctionStatement
	Externs       map[string]*ast.FunctionStatement
	Records       map[string]*ast.RecordLiteral
	ADTs          map[string]*ast.ADTType
	Constants     map[string]asm.Constant
	Symbols       map[string]bool
	Declarations  string
	TCFingerprint string
}

type nativeRecipeOwnershipDriver struct {
	*nativeDriver
	t              *testing.T
	root           *ast.Program
	before         nativeRecipeOwnedInputs
	beforeRecipe   []byte
	beforeTC       string
	legacy         bool
	wrongConstant  bool
	keys           []string
	checks         int
	validations    int
	fallbacks      int
	sourceRewrites int
	optIRBodies    int
}

func (d *nativeRecipeOwnershipDriver) inputs() nativeRecipeOwnedInputs {
	return nativeRecipeOwnedInputs{
		Root: d.root, Source: d.source, Functions: d.functions, Externs: d.externs,
		Records: d.records, ADTs: d.adts, Constants: d.constants, Symbols: d.symbols,
		Declarations: d.declarations, TCFingerprint: d.tcFingerprint,
	}
}

func watchNativeRecipeOwnership(t *testing.T, root *ast.Program, driver *nativeDriver, legacy bool) *nativeRecipeOwnershipDriver {
	t.Helper()
	d := &nativeRecipeOwnershipDriver{nativeDriver: driver, t: t, root: root, legacy: legacy}
	d.before = cloneSyntax(reflect.ValueOf(d.inputs())).Interface().(nativeRecipeOwnedInputs)
	d.beforeRecipe = legacyNativeMaterializationRecipe(driver)
	// Deliberately bypass the production tcFingerprint override here, so a
	// mutation cannot hide behind the already-captured fingerprint string.
	d.beforeTC = driver.tc.NativeLoweringFingerprint()
	return d
}

func (d *nativeRecipeOwnershipDriver) assertUnchanged(stage string) {
	d.t.Helper()
	if !reflect.DeepEqual(d.before, d.inputs()) {
		d.t.Fatalf("%s mutated the checked syntax or shared input maps", stage)
	}
	if got := d.tc.NativeLoweringFingerprint(); got != d.beforeTC {
		d.t.Fatalf("%s mutated checked type/fact authority: %s != %s", stage, got, d.beforeTC)
	}
	live := legacyNativeMaterializationRecipe(d.nativeDriver)
	if !bytes.Equal(live, d.beforeRecipe) {
		d.t.Fatalf("%s changed the original serialized recipe", stage)
	}
	if d.materializationRecipe != nil && !bytes.Equal(d.materializationRecipe, live) {
		d.t.Fatalf("%s left a stale recipe snapshot", stage)
	}
}

func (d *nativeRecipeOwnershipDriver) MaterializationKey(candidate *opt.Candidate) (string, error) {
	d.assertUnchanged("before MaterializationKey")
	lane := candidate.Config.(nativegen.Lane)
	want := legacyNativeMaterializationKey(d.nativeDriver, lane)
	key := want
	if !d.legacy {
		var err error
		key, err = d.nativeDriver.MaterializationKey(candidate)
		if err != nil || key != want {
			d.t.Fatalf("candidate %s differs from the live original key: %q != %q (%v)", candidate.Name(), key, want, err)
		}
	}
	d.keys = append(d.keys, candidate.Name()+":"+key)
	d.assertUnchanged("after MaterializationKey")
	return key, nil
}

func (d *nativeRecipeOwnershipDriver) Materialize(candidate *opt.Candidate) error {
	d.assertUnchanged("before Materialize")
	defer d.assertUnchanged("after Materialize")
	err := d.nativeDriver.Materialize(candidate)
	if err == nil {
		body := candidate.Body.(*asm.Function)
		if d.wrongConstant {
			// Keep the machine body's legal register/frame footprint, but
			// make it disagree with the checked source through the real
			// artifact materialization/admission/verification pipeline.
			changed := false
			for index, item := range body.Items {
				instruction, ok := item.(asm.Instruction)
				if !ok || instruction.Mnemonic != "movz" || len(instruction.Operands) != 2 {
					continue
				}
				immediate, ok := instruction.Operands[1].(asm.Immediate)
				if ok && immediate.Value == 7 {
					immediate.Value = 8
					instruction.Operands[1] = immediate
					body.Items[index] = instruction
					changed = true
				}
			}
			if !changed {
				d.t.Fatal("wrong-body control did not find the returned constant")
			}
		}
		d.sourceRewrites += nativegen.StrengthReduced(body)
		if nativegen.OptIRLowered(body) > 0 {
			d.optIRBodies++
		}
	}
	return err
}

func (d *nativeRecipeOwnershipDriver) Key(candidate *opt.Candidate) string {
	d.assertUnchanged("before Key")
	defer d.assertUnchanged("after Key")
	return d.nativeDriver.Key(candidate)
}

func (d *nativeRecipeOwnershipDriver) Measure(candidate *opt.Candidate) opt.Metrics {
	d.assertUnchanged("before Measure")
	defer d.assertUnchanged("after Measure")
	return d.nativeDriver.Measure(candidate)
}

func (d *nativeRecipeOwnershipDriver) Check(candidate *opt.Candidate) []string {
	d.assertUnchanged("before Check")
	defer d.assertUnchanged("after Check")
	d.checks++
	return d.nativeDriver.Check(candidate)
}

func (d *nativeRecipeOwnershipDriver) Validate(candidate *opt.Candidate) opt.Verdict {
	d.assertUnchanged("before Validate")
	defer d.assertUnchanged("after Validate")
	d.validations++
	return d.nativeDriver.Validate(candidate)
}

func (d *nativeRecipeOwnershipDriver) ValidationFallback(candidate *opt.Candidate, verdict opt.Verdict) *opt.Candidate {
	d.assertUnchanged("before ValidationFallback")
	defer d.assertUnchanged("after ValidationFallback")
	d.fallbacks++
	return d.nativeDriver.ValidationFallback(candidate, verdict)
}

func nativeRecipeCheckedFixture(t *testing.T, text, arch string) (*ast.Program, *nativeDriver, nativegen.Lane) {
	t.Helper()
	p := parser.New(layout.New(scanner.New(text)))
	root := p.ParseProgram()
	if errors := p.Errors(); len(errors) != 0 {
		t.Fatalf("fixture parse: %v", errors)
	}
	tc := typechecker.NewWithPlatformSizes(object.NewEnvironment(), 64, 64)
	tc.CheckProgram(root)
	if errors := tc.Errors(); len(errors) != 0 {
		t.Fatalf("fixture check: %v", errors)
	}
	functions := map[string]*ast.FunctionStatement{}
	symbols := map[string]bool{}
	for _, statement := range root.Statements {
		if function, ok := statement.(*ast.FunctionStatement); ok {
			functions[function.Name.Value] = function
			symbols[function.Name.Value] = true
		}
	}
	if functions["calc"] == nil {
		t.Fatal("fixture has no calc function")
	}
	constants := constantGlobals(root, tc)
	globals, aggregates, _ := addressableGlobals(root, tc, constants, nil)
	tables, _ := nativeGlobalArrays(root)
	verified, cached := 0, 0
	driver := &nativeDriver{
		source: functions["calc"], functions: functions, tc: tc,
		tcFingerprint: tc.NativeLoweringFingerprint(), constants: constants,
		symbols: symbols, declarations: programDeclarations(root),
		verdicts: map[*asm.Function]asm.Verdict{}, verified: &verified, fromCache: &cached,
	}
	lane := nativegen.Lane{Arch: arch, Globals: globals, Aggregates: aggregates, Tables: tables}
	lane.UnrollFillsEligible = nativegen.CanUnrollFills(driver.source, tc, constants)
	lane.LoopRewrites = nativegen.AnalyzeLoopRewriteEligibility(driver.source, functions, tc)
	return root, driver, lane
}

func nativeRecipeSearchRegistry(names ...string) *opt.Registry {
	var selected []opt.Transform
	for _, transform := range nativegen.Registry().Transforms() {
		for _, name := range names {
			if transform.Name() == name {
				selected = append(selected, transform)
			}
		}
	}
	return opt.NewRegistry(selected...)
}

type nativeRecipeSearchResult struct {
	Keys                                          []string
	Assembly, Candidate, Remarks, Error           string
	Verdict                                       opt.Verdict
	Considered, Materialized, Validations, Checks int
	Fallbacks, SourceRewrites, OptIRBodies        int
}

func runNativeRecipeOwnershipSearch(t *testing.T, text, arch, kind string, scoped bool) nativeRecipeSearchResult {
	t.Helper()
	root, driver, lane := nativeRecipeCheckedFixture(t, text, arch)
	registry := nativeRecipeSearchRegistry(nativegen.TransformStrength, nativegen.TransformCleanup)
	if kind == "optir" {
		planner := newOptIRCallEffectPlanner(root, driver.tc, checkedOptIRGlobals(root, driver.tc))
		applyNativeOptIRCandidate(&lane, nativeOptIRCandidate(driver.source, planner, driver.tc, lane.Globals))
		if lane.OptIR == nil || lane.OptIRMemory == nil || lane.OptIRChanges == 0 {
			t.Fatal("fixture did not produce a checked global-memory OptIR candidate")
		}
		registry = nativeRecipeSearchRegistry(nativegen.TransformOptIR, nativegen.TransformCleanup)
	} else if kind == "refused" {
		delete(driver.symbols, "callee") // An actual seam refusal for the identity's call.
		registry = nativeRecipeSearchRegistry()
	} else if kind == "unsupported" {
		lane.Arch = "unsupported-recipe-test"
		registry = nativeRecipeSearchRegistry()
	} else if kind == "mismatch" {
		registry = nativeRecipeSearchRegistry()
	}
	facts := nativegen.FunctionFacts(driver.source, driver.tc)
	observer := watchNativeRecipeOwnership(t, root, driver, !scoped)
	observer.wrongConstant = kind == "mismatch"
	report := &opt.Report{}
	search := &opt.Search{Registry: registry, Costs: opt.CostsFor(arch), Report: report, Beam: 2, Validations: 2, RefineRounds: 2}
	run := func() (*opt.Selection, error) {
		return search.Run("calc", opt.Identity(nativegen.PlainLane(lane)), facts, observer)
	}
	var selection *opt.Selection
	var err error
	if scoped {
		selection, err = driver.withMaterializationRecipe(run)
	} else {
		selection, err = run()
	}
	if driver.materializationRecipe != nil {
		t.Fatal("actual search exit retained the recipe snapshot")
	}
	observer.assertUnchanged("after search")
	result := nativeRecipeSearchResult{
		Keys: observer.keys, Checks: observer.checks, Validations: observer.validations,
		Fallbacks: observer.fallbacks, SourceRewrites: observer.sourceRewrites,
		OptIRBodies: observer.optIRBodies, Remarks: report.String(),
	}
	if err != nil {
		result.Error = err.Error()
		if kind != "unsupported" {
			t.Fatalf("actual %s search failed: %v", kind, err)
		}
		return result
	}
	if kind == "unsupported" || selection == nil {
		t.Fatalf("unexpected search result: selection=%v, error=%v", selection, err)
	}
	result.Considered, result.Materialized = selection.Considered, selection.Materialized
	result.Candidate, result.Verdict = selection.Candidate.Name(), selection.Verdict
	result.Assembly = nativegen.Describe(selection.Candidate.Body.(*asm.Function))
	if observer.validations != len(selection.Validations) || *driver.verified != observer.validations || *driver.fromCache != 0 {
		t.Fatal("search validations diverged from fresh native-driver validation calls")
	}
	if kind == "refused" {
		if selection.Verdict.Outcome != opt.Refused || observer.validations != 0 {
			t.Fatalf("identity did not take the seam-refusal exit: %+v", selection.Verdict)
		}
	} else if kind == "mismatch" {
		if selection.Verdict.Outcome != opt.Mismatch || observer.checks != 1 || observer.validations != 1 {
			t.Fatalf("wrong-body identity escaped real admission/validation: %+v, checks=%d, validations=%d", selection.Verdict, observer.checks, observer.validations)
		}
	} else if selection.Verdict.Outcome != opt.Proven || observer.checks == 0 || observer.validations == 0 {
		t.Fatalf("fixture did not perform admitted, proven native search: %+v", selection.Verdict)
	}
	return result
}

func TestNativeMaterializationRecipeActualSearchPreservesOwnership(t *testing.T) {
	t.Setenv("OAK_VERIFY_CACHE", "0")
	t.Setenv("OAK_VERIFY_ONLY", "")
	t.Setenv("OAK_VERIFY_BUDGET", "")
	for _, fixture := range []struct{ name, source string }{
		{"rewrite", "calc: (x: u32): u32 { x * u32(8) }"},
		{"optir", `
state: u32 = u32(0)
calc: (first: u32, last: u32): u32 {
  state = first
  state = last
  last
}
`},
	} {
		for _, arch := range []string{asm.ArchArm64, asm.ArchRV64} {
			t.Run(fixture.name+"/"+arch, func(t *testing.T) {
				live := runNativeRecipeOwnershipSearch(t, fixture.source, arch, fixture.name, false)
				scoped := runNativeRecipeOwnershipSearch(t, fixture.source, arch, fixture.name, true)
				if !reflect.DeepEqual(live, scoped) {
					t.Fatalf("snapshot changed actual search behavior\nlive: %+v\nscoped: %+v", live, scoped)
				}
				if len(scoped.Keys) < 2 || scoped.Materialized < 2 {
					t.Fatal("fixture did not exercise multiple actual candidates")
				}
				if fixture.name == "rewrite" && scoped.SourceRewrites == 0 {
					t.Fatal("fixture did not perform a source rewrite")
				}
				if fixture.name == "optir" && scoped.OptIRBodies == 0 {
					t.Fatal("fixture did not materialize the checked OptIR candidate")
				}
			})
		}
	}
}

func TestNativeMaterializationRecipeActualIdentityExits(t *testing.T) {
	for _, fixture := range []struct{ name, source string }{
		{"unsupported", "calc: (): u32 { u32(7) }"},
		{"refused", "callee: (x: u32): u32 { x + u32(1) }\ncalc: (x: u32): u32 { callee(x) }"},
	} {
		t.Run(fixture.name, func(t *testing.T) {
			live := runNativeRecipeOwnershipSearch(t, fixture.source, asm.ArchArm64, fixture.name, false)
			scoped := runNativeRecipeOwnershipSearch(t, fixture.source, asm.ArchArm64, fixture.name, true)
			if !reflect.DeepEqual(live, scoped) {
				t.Fatalf("snapshot changed identity exit\nlive: %+v\nscoped: %+v", live, scoped)
			}
		})
	}
}

func TestNativeMaterializationRecipeActualSearchRejectsWrongBody(t *testing.T) {
	t.Setenv("OAK_VERIFY_CACHE", "0")
	t.Setenv("OAK_VERIFY_ONLY", "")
	t.Setenv("OAK_VERIFY_BUDGET", "")
	const source = "calc: (): u32 { u32(7) }"
	live := runNativeRecipeOwnershipSearch(t, source, asm.ArchArm64, "mismatch", false)
	scoped := runNativeRecipeOwnershipSearch(t, source, asm.ArchArm64, "mismatch", true)
	if !reflect.DeepEqual(live, scoped) {
		t.Fatalf("snapshot changed wrong-body rejection\nlive: %+v\nscoped: %+v", live, scoped)
	}
	if len(scoped.Keys) != 1 || scoped.Considered != 1 || scoped.Materialized != 1 {
		t.Fatalf("wrong-body control bypassed the identity's keyed artifact: %+v", scoped)
	}
}

func TestNativeMaterializationRecipeFallbackPreservesOwnership(t *testing.T) {
	root, driver, lane := nativeRecipeCheckedFixture(t, "calc: (x: u32): u32 { x * u32(8) }", asm.ArchArm64)
	observer := watchNativeRecipeOwnership(t, root, driver, false)
	_, err := driver.withMaterializationRecipe(func() (*opt.Selection, error) {
		// Drive the production fallback's positive branch explicitly: these
		// tiny proven fixtures do not naturally request a validation fallback.
		// This checks proposal ownership without inventing a verifier result.
		lane.UnrollFills, lane.RotateLoops = true, true
		candidate := opt.Identity(lane).With(nativegen.TransformUnrollFills, lane).With(nativegen.TransformRotate, lane)
		before := cloneSyntax(reflect.ValueOf(candidate)).Interface().(*opt.Candidate)
		next := observer.ValidationFallback(candidate, opt.Verdict{Outcome: opt.Trusted})
		if next == nil || !reflect.DeepEqual(candidate, before) || next.Config.(nativegen.Lane).RotateLoops {
			return nil, fmt.Errorf("fallback failed to preserve its input and remove rotation")
		}
		if _, err := observer.MaterializationKey(next); err != nil {
			return nil, err
		}
		return nil, nil
	})
	if err != nil || driver.materializationRecipe != nil || observer.fallbacks != 1 {
		t.Fatalf("fallback scope: error=%v, requests=%d, retained=%v", err, observer.fallbacks, driver.materializationRecipe != nil)
	}
	observer.assertUnchanged("after fallback scope")
}
