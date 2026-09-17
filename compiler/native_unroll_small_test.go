package compiler

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/nativegen"
	"github.com/SCKelemen/oak/opt"
	"github.com/SCKelemen/oak/target"
)

// Exercise the separate small-loop candidate on the checked standard-library
// compressor without running the complete native search. The driver still
// performs ordinary lowering, seam admission, and fresh semantic validation.
func TestNativeBlake3SmallUnrollCandidateProven(t *testing.T) {
	t.Setenv("OAK_VERIFY_CACHE", "0")
	t.Setenv("OAK_VERIFY_BUDGET", "")
	packageRoot := nativeBlake3Module(t, [][]byte{nil})
	comp := New().WithPackageDir(packageRoot).
		WithTarget(target.Target{OS: target.OSDarwin, Arch: target.ArchArm64}).
		WithNativeAsm()
	comp.options.InlineHelpers = true
	comp.options.NativeBodies = false
	model, err := comp.SemanticModel().Get()
	if err != nil {
		t.Fatal(err)
	}

	root, tc := model.Tree.Root, model.TypeChecker
	functions := map[string]*ast.FunctionStatement{}
	externs := map[string]*ast.FunctionStatement{}
	records := map[string]*ast.RecordLiteral{}
	adts := map[string]*ast.ADTType{}
	templates := map[string]*ast.ADTType{}
	symbols := map[string]bool{}
	for _, statement := range root.Statements {
		if adt, ok := statement.(*ast.ADTType); ok && adt.Name != nil {
			if len(adt.TypeParams) > 0 {
				templates[adt.Name.Value] = adt
			} else if record, ok := recordShape(adt); ok {
				records[adt.Name.Value] = record
			} else {
				adts[adt.Name.Value] = adt
			}
			continue
		}
		function, ok := statement.(*ast.FunctionStatement)
		if !ok || function.Name == nil {
			continue
		}
		symbols[function.Name.Value] = true
		if function.ExternSymbol != "" {
			externs[function.Name.Value] = function
		} else if function.Receiver == nil && len(function.TypeParams) == 0 {
			functions[function.Name.Value] = function
			if nativegen.VectorContract(function) {
				symbols[nativegen.NativeSymbolFor(asm.ArchArm64, function)] = true
			}
		}
	}
	specializeInstantiations(tc, templates, records, adts)
	source := functions[nativeBlake3CompressName]
	if source == nil {
		t.Fatal("real BLAKE3 compression function was not loaded")
	}
	constants := constantGlobals(root, tc)
	globals, aggregates, _ := addressableGlobals(root, tc, constants, records)
	tables, _ := nativeGlobalArrays(root)
	verified, fromCache := 0, 0
	driver := &nativeDriver{
		source: source, functions: functions, externs: externs, records: records, adts: adts,
		constants: constants, tc: tc, symbols: symbols, declarations: programDeclarations(root),
		cacheDir: "", verdicts: map[*asm.Function]asm.Verdict{}, verified: &verified, fromCache: &fromCache,
	}
	lane := nativegen.Lane{
		Arch: asm.ArchArm64, PackedStackArgs: true, NoReductions: true,
		UnrollSmall: true, Reallocate: true, HoistInvariants: true, Cleanup: true,
		Globals: globals, Aggregates: aggregates, Tables: tables,
	}
	candidate := &opt.Candidate{Config: lane, Applied: []string{
		nativegen.TransformUnrollSmall, nativegen.TransformReallocate,
		nativegen.TransformHoist, nativegen.TransformCleanup,
	}}
	if err := driver.Materialize(candidate); err != nil {
		t.Fatalf("small-unroll candidate materialization failed: %v", err)
	}
	body := candidate.Body.(*asm.Function)
	if nativegen.UnrolledSmall(body) == 0 || nativegen.UnrolledConstant(body) != 0 || body.Body == nil {
		t.Fatalf("candidate did not retain its distinct rewritten body: small=%d full=%d body=%v",
			nativegen.UnrolledSmall(body), nativegen.UnrolledConstant(body), body.Body != nil)
	}
	stackMemory, rotateAt := 0, -1
	for i, item := range body.Items {
		instruction, ok := item.(asm.Instruction)
		if !ok {
			continue
		}
		if instruction.Mnemonic == "ror" && rotateAt < 0 {
			rotateAt = i
		}
		if strings.HasPrefix(instruction.Mnemonic, "ld") || strings.HasPrefix(instruction.Mnemonic, "st") {
			for _, operand := range instruction.Operands {
				if memory, ok := operand.(asm.Memory); ok && memory.Base.Class == asm.ClassSP {
					stackMemory++
				}
			}
		}
	}
	if body.Frame != 160 || stackMemory != 10 || rotateAt < 0 {
		t.Fatalf("small unroll lost the intended placement: frame=%d stack memory=%d rotate=%d",
			body.Frame, stackMemory, rotateAt)
	}
	if findings := driver.Check(candidate); len(findings) != 0 {
		t.Fatalf("small-unroll seam refused: %v", findings)
	}
	result := driver.Validate(candidate)
	verdict := driver.verdicts[body]
	if result.Outcome != opt.Proven || verdict.Kind != asm.VerdictProven ||
		!strings.Contains(verdict.Message, "all 8 result chunks") || verified != 1 || fromCache != 0 {
		t.Fatalf("small unroll must freshly prove all chunks: outcome=%s verdict=%s (%s), verified=%d cached=%d",
			result.Outcome, verdict.Kind, verdict.Message, verified, fromCache)
	}
	metrics := driver.Measure(candidate)
	if len(metrics.LoopBodies) != 1 || metrics.LoopBodies[0].ExactTrips != 7 {
		t.Fatalf("small candidate must retain its exact seven-round loop: %+v", metrics.LoopBodies)
	}
	// Price the same placement without small unrolling, including the real
	// bottom-tested tail. A mere upper bound used to charge that tail four
	// trips instead of its exact eight and favor the slower rolled form.
	rolledLane := lane
	rolledLane.UnrollSmall = false
	rolledLane.ElideProven = true
	rolledLane.RotateLoops = true
	rolled := opt.Identity(rolledLane)
	if err := driver.Materialize(rolled); err != nil {
		t.Fatal(err)
	}
	if findings := driver.Check(rolled); len(findings) != 0 {
		t.Fatalf("rolled comparator seam refused: %v", findings)
	}
	if proof := driver.Validate(rolled); proof.Outcome != opt.Proven {
		t.Fatalf("rolled comparator did not prove: %s", proof.Message)
	}
	rolledMetrics := driver.Measure(rolled)
	if len(rolledMetrics.LoopBodies) != 2 || rolledMetrics.LoopBodies[0].ExactTrips != 7 || rolledMetrics.LoopBodies[1].ExactTrips != 8 {
		t.Fatalf("rolled comparator lacks exact main/tail counts: %+v", rolledMetrics.LoopBodies)
	}
	if smallCost, rolledCost := opt.AArch64Costs.Estimate(metrics), opt.AArch64Costs.Estimate(rolledMetrics); smallCost >= rolledCost {
		t.Fatalf("exact trip costing still favors rolled comparator: small=%v rolled=%v", smallCost, rolledCost)
	}
	// The corrected costs also expose the existing fully unrolled winner.
	// Exercise its normal admission and proof directly, independently of the
	// slower end-to-end test which pins production search selection.
	fullLane := nativegen.PlainLane(lane)
	fullLane.UnrollConstant, fullLane.Reallocate = true, true
	fullLane.Schedule, fullLane.Cleanup = true, true
	full := &opt.Candidate{Config: fullLane, Applied: []string{
		nativegen.TransformUnrollConst, nativegen.TransformSchedule,
		nativegen.TransformReallocate, nativegen.TransformCleanup,
	}}
	if err := driver.Materialize(full); err != nil {
		t.Fatal(err)
	}
	if findings := driver.Check(full); len(findings) != 0 {
		t.Fatalf("fully unrolled seam refused: %v", findings)
	}
	fullBody := full.Body.(*asm.Function)
	if proof := driver.Validate(full); proof.Outcome != opt.Proven || driver.verdicts[fullBody].Kind != asm.VerdictProven ||
		!strings.Contains(driver.verdicts[fullBody].Message, "all 8 result chunks") {
		t.Fatalf("fully unrolled candidate did not prove all chunks: %s (%s)", proof.Message, driver.verdicts[fullBody].Message)
	}
	requireNativeBlake3StrongProfile(t, fullBody)
	if nativegen.UnrolledConstant(fullBody) == 0 {
		t.Fatal("direct fully unrolled candidate lost its rewrite")
	}
	if fullCost, rolledCost := opt.AArch64Costs.Estimate(driver.Measure(full)), opt.AArch64Costs.Estimate(rolledMetrics); fullCost >= rolledCost {
		t.Fatalf("exact trip costing did not favor full unrolling: full=%v rolled=%v", fullCost, rolledCost)
	}

	// Preserve the candidate's legal footprint but alter its computation. The
	// verifier must refute the changed rotate rather than recognize the source
	// function or the optimization label.
	changed := *body
	changed.Items = append([]asm.Item(nil), body.Items...)
	instruction := changed.Items[rotateAt].(asm.Instruction)
	instruction.Operands = append([]asm.Operand(nil), instruction.Operands...)
	count, ok := instruction.Operands[2].(asm.Immediate)
	if !ok {
		t.Fatal("expected fixed rotate count")
	}
	count.Value = (count.Value + 1) % 32
	instruction.Operands[2] = count
	changed.Items[rotateAt] = instruction
	if got := asm.Verify(&changed, source, verifiedBody(body, source)); got.Kind != asm.VerdictMismatch {
		t.Fatalf("changed rotate must be refuted, got %s: %s", got.Kind, got.Message)
	}
}
