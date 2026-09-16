package asm

import (
	"context"
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"
	"time"
)

// TestNativeCNFReplayApplyMatchesLean fixes the production replay decision
// before asking Lean to evaluate the same numeric snapshot. Corrupt memo
// snapshots below exercise replay refusal only: without validateCNFAllocation,
// they do not claim that a successful lookup would denote a sound CNF gate.
func TestNativeCNFReplayApplyMatchesLean(t *testing.T) {
	type replayCase struct {
		name            string
		builder         *cnfBuilder
		maxInt          int
		op, x, y        int
		wantRoot        int
		wantAccepted    bool
		wantProjectable bool
	}

	base := newCNFBuilder()
	left := base.variable(0)
	right := base.variable(1)
	for _, operation := range []int{opAnd, opOr, opXor} {
		for polarity := 0; polarity < 4; polarity++ {
			base.apply(operation, left^(polarity&1), right^((polarity>>1)&1))
		}
	}
	const replayMaxInt = 100
	cases := []replayCase{
		// Every switch arm is pinned for every operation. Reversed inputs also
		// pin that sorting happens before fold selection.
		{name: "and identical", builder: base, maxInt: replayMaxInt, op: opAnd, x: 4, y: 4, wantRoot: 4, wantAccepted: true, wantProjectable: true},
		{name: "and complements reversed", builder: base, maxInt: replayMaxInt, op: opAnd, x: 5, y: 4, wantRoot: 0, wantAccepted: true, wantProjectable: true},
		{name: "and false reversed", builder: base, maxInt: replayMaxInt, op: opAnd, x: 4, y: 0, wantRoot: 0, wantAccepted: true, wantProjectable: true},
		{name: "and true reversed", builder: base, maxInt: replayMaxInt, op: opAnd, x: 4, y: 1, wantRoot: 4, wantAccepted: true, wantProjectable: true},
		{name: "or identical", builder: base, maxInt: replayMaxInt, op: opOr, x: 5, y: 5, wantRoot: 5, wantAccepted: true, wantProjectable: true},
		{name: "or complements", builder: base, maxInt: replayMaxInt, op: opOr, x: 4, y: 5, wantRoot: 1, wantAccepted: true, wantProjectable: true},
		{name: "or false reversed", builder: base, maxInt: replayMaxInt, op: opOr, x: 5, y: 0, wantRoot: 5, wantAccepted: true, wantProjectable: true},
		{name: "or true reversed", builder: base, maxInt: replayMaxInt, op: opOr, x: 4, y: 1, wantRoot: 1, wantAccepted: true, wantProjectable: true},
		{name: "xor identical", builder: base, maxInt: replayMaxInt, op: opXor, x: 5, y: 5, wantRoot: 0, wantAccepted: true, wantProjectable: true},
		{name: "xor complements reversed", builder: base, maxInt: replayMaxInt, op: opXor, x: 5, y: 4, wantRoot: 1, wantAccepted: true, wantProjectable: true},
		{name: "xor false reversed", builder: base, maxInt: replayMaxInt, op: opXor, x: 4, y: 0, wantRoot: 4, wantAccepted: true, wantProjectable: true},
		{name: "xor true reversed", builder: base, maxInt: replayMaxInt, op: opXor, x: 4, y: 1, wantRoot: 5, wantAccepted: true, wantProjectable: true},
		// Folded edges intentionally do not consult allocation or maxInt. These
		// pins preserve that admission order without claiming input provenance.
		{name: "identical unallocated edge folds", builder: base, maxInt: replayMaxInt, op: opAnd, x: 200, y: 200, wantRoot: 200, wantAccepted: true, wantProjectable: true},
		{name: "unallocated complements fold", builder: base, maxInt: replayMaxInt, op: opOr, x: 201, y: 200, wantRoot: 1, wantAccepted: true, wantProjectable: true},

		// The fixture allocates four polarity combinations for each operation.
		// These roots are fixed independently of the replay lookup.
		{name: "and memo positive", builder: base, maxInt: replayMaxInt, op: opAnd, x: 2, y: 4, wantRoot: 6, wantAccepted: true, wantProjectable: true},
		{name: "and memo left negative reversed", builder: base, maxInt: replayMaxInt, op: opAnd, x: 4, y: 3, wantRoot: 8, wantAccepted: true, wantProjectable: true},
		{name: "and memo right negative", builder: base, maxInt: replayMaxInt, op: opAnd, x: 2, y: 5, wantRoot: 10, wantAccepted: true, wantProjectable: true},
		{name: "and memo both negative reversed", builder: base, maxInt: replayMaxInt, op: opAnd, x: 5, y: 3, wantRoot: 12, wantAccepted: true, wantProjectable: true},
		{name: "or memo positive reversed", builder: base, maxInt: replayMaxInt, op: opOr, x: 4, y: 2, wantRoot: 14, wantAccepted: true, wantProjectable: true},
		{name: "or memo left negative", builder: base, maxInt: replayMaxInt, op: opOr, x: 3, y: 4, wantRoot: 16, wantAccepted: true, wantProjectable: true},
		{name: "or memo right negative reversed", builder: base, maxInt: replayMaxInt, op: opOr, x: 5, y: 2, wantRoot: 18, wantAccepted: true, wantProjectable: true},
		{name: "or memo both negative", builder: base, maxInt: replayMaxInt, op: opOr, x: 3, y: 5, wantRoot: 20, wantAccepted: true, wantProjectable: true},
		{name: "xor memo positive", builder: base, maxInt: replayMaxInt, op: opXor, x: 2, y: 4, wantRoot: 22, wantAccepted: true, wantProjectable: true},
		{name: "xor memo left negative reversed", builder: base, maxInt: replayMaxInt, op: opXor, x: 4, y: 3, wantRoot: 24, wantAccepted: true, wantProjectable: true},
		{name: "xor memo right negative", builder: base, maxInt: replayMaxInt, op: opXor, x: 2, y: 5, wantRoot: 26, wantAccepted: true, wantProjectable: true},
		{name: "xor memo both negative reversed", builder: base, maxInt: replayMaxInt, op: opXor, x: 5, y: 3, wantRoot: 28, wantAccepted: true, wantProjectable: true},
	}

	andKey := cnfKey{op: opAnd, x: 2, y: 4, z: -1}
	missing := cloneCNFTraceBuilder(base)
	delete(missing.memo, andKey)
	cases = append(cases, replayCase{name: "missing memo", builder: missing, maxInt: replayMaxInt, op: opAnd, x: 2, y: 4, wantProjectable: true})
	zeroGate := cloneCNFTraceBuilder(base)
	zeroGate.memo[andKey] = 0
	cases = append(cases, replayCase{name: "zero memo gate", builder: zeroGate, maxInt: replayMaxInt, op: opAnd, x: 2, y: 4, wantProjectable: true})
	outOfRangeGate := cloneCNFTraceBuilder(base)
	outOfRangeGate.memo[andKey] = outOfRangeGate.variables + 1
	cases = append(cases, replayCase{name: "memo gate outside variables", builder: outOfRangeGate, maxInt: replayMaxInt, op: opAnd, x: 2, y: 4, wantProjectable: true})
	cases = append(cases,
		replayCase{name: "max int guard refuses", builder: base, maxInt: 5, op: opAnd, x: 2, y: 4, wantProjectable: true},
		replayCase{name: "max int guard boundary", builder: base, maxInt: 6, op: opAnd, x: 2, y: 4, wantRoot: 6, wantAccepted: true, wantProjectable: true},
		replayCase{name: "ite tag rejected before fold", builder: base, maxInt: replayMaxInt, op: cnfIte, x: 4, y: 4, wantProjectable: true},
		replayCase{name: "unknown operation", builder: base, maxInt: replayMaxInt, op: 99, x: 2, y: 4, wantProjectable: true},
		replayCase{name: "negative operation projection refused", builder: base, maxInt: replayMaxInt, op: -1, x: 2, y: 4},
		replayCase{name: "negative left edge projection refused", builder: base, maxInt: replayMaxInt, op: opAnd, x: -2, y: 4},
		replayCase{name: "negative right edge projection refused", builder: base, maxInt: replayMaxInt, op: opOr, x: 2, y: -4},
		replayCase{name: "negative max int projection refused", builder: base, maxInt: -1, op: opXor, x: 2, y: 4},
	)

	leanExamples := make([]string, 0, len(cases))
	t.Run("decisions", func(t *testing.T) {
		for index, test := range cases {
			t.Run(test.name, func(t *testing.T) {
				replay := &nativeCNFReplay{
					bl:       &blaster{cnf: test.builder},
					gateKeys: map[cnfKey]bool{},
					maxInt:   test.maxInt,
				}
				root, err := replay.apply(test.op, test.x, test.y)
				accepted := err == nil
				if accepted != test.wantAccepted {
					t.Fatalf("accepted = %t, want %t: root=%d error=%v", accepted, test.wantAccepted, root, err)
				}
				if accepted && root != test.wantRoot {
					t.Fatalf("root = %d, want %d", root, test.wantRoot)
				}

				example, projectionErr := renderNativeCNFReplayApplyExample(index, test.builder,
					test.maxInt, test.op, test.x, test.y, test.wantRoot, test.wantAccepted)
				projectable := projectionErr == nil
				if projectable != test.wantProjectable {
					t.Fatalf("projectable = %t, want %t: %v", projectable, test.wantProjectable, projectionErr)
				}
				if projectable {
					leanExamples = append(leanExamples, example)
				}
			})
		}
	})
	if t.Failed() {
		return
	}

	t.Run("kernel", func(t *testing.T) {
		lake, err := exec.LookPath("lake")
		if err != nil {
			requireOracle(t, "lake not on PATH; the formal workflow runs this kernel oracle")
		}
		if len(leanExamples) == 0 {
			t.Fatal("no production replay decisions were available for the kernel pin")
		}
		leanSource := "import Oak.CNFReplayApply\n\nnamespace Oak.CNFReplayApply\n\n" +
			strings.Join(leanExamples, "\n\n") + "\n\nend Oak.CNFReplayApply\n"
		leanPath := filepath.Join(t.TempDir(), "NativeCNFReplayApplyProductionPins.lean")
		file, err := os.OpenFile(leanPath, os.O_WRONLY|os.O_CREATE|os.O_EXCL, 0o600)
		if err != nil {
			t.Fatal(err)
		}
		if _, err := file.WriteString(leanSource); err != nil {
			file.Close()
			t.Fatal(err)
		}
		if err := file.Close(); err != nil {
			t.Fatal(err)
		}

		ctx, cancel := context.WithTimeout(context.Background(), 90*time.Second)
		defer cancel()
		command := exec.CommandContext(ctx, lake, "env", "lean", leanPath)
		command.Dir = filepath.Join("..", "spec", "lean")
		if output, err := command.CombinedOutput(); err != nil {
			t.Fatalf("kernel-checking native CNF replay pins: %v (context: %v)\n%s\n--- source ---\n%s",
				err, ctx.Err(), output, leanSource)
		}
	})
}

func renderNativeCNFReplayApplyExample(index int, builder *cnfBuilder,
	maxInt, operation, x, y, root int, accepted bool) (string, error) {
	if maxInt < 0 || operation < 0 || x < 0 || y < 0 || root < 0 {
		return "", fmt.Errorf("replay decision is outside the Nat projection")
	}
	snapshot, err := renderCNFAllocationSnapshot(builder)
	if err != nil {
		return "", err
	}
	expected := "none"
	if accepted {
		expected = fmt.Sprintf("some %d", root)
	}
	return fmt.Sprintf("def snapshot%d : CNFDenseAllocation.Snapshot := %s\n"+
		"example : replayApply snapshot%d.variables %d snapshot%d.memo %d %d %d = %s := by decide",
		index, snapshot, index, maxInt, index, operation, x, y, expected), nil
}

// TestNativeCNFReplayTermMatchesLean is deliberately a nonempty, one-bit
// correspondence pin. It does not project general Go terms, width adaptation,
// empty result lists, or whole-word result semantics. In particular, Lean's
// differenceTerm [] identity is outside nativeCNFReplay.disequality admission.
// The full allocation is valid here; later composition uses that fact to
// justify the input-stability and memo-soundness premises.
func TestNativeCNFReplayTermMatchesLean(t *testing.T) {
	const replayMaxInt = 100
	widths := map[string]int{"a": 1, "b": 1, "c": 1}
	bl := newCNFBlaster([]string{"a", "b", "c"}, widths)
	a := paramTerm("a", 1)
	b := paramTerm("b", 1)
	c := paramTerm("c", 1)
	falseTerm := constTerm(0, 1)
	trueTerm := constTerm(1, 1)
	andAB := nativeReplayOneBitBinary("and", a, b)

	// Blasting the first gate before c makes input DIMACS indices 1, 2 and
	// 4, with gate output 3 between them. The formal term must use those
	// actual input outputs, not source positions or a dense-input guess.
	if roots := bl.blast(andAB); len(roots) != 1 || roots[0] != 6 {
		t.Fatalf("producer a&b roots = %v, want [6]", roots)
	}
	if roots := bl.blast(c); len(roots) != 1 || roots[0] != 8 {
		t.Fatalf("producer c roots = %v, want [8]", roots)
	}
	if bl.cnf.inputs[0] != 1 || bl.cnf.inputs[1] != 2 || bl.cnf.inputs[2] != 4 {
		t.Fatalf("interleaved inputs = %v, want source outputs 0:1, 1:2, 2:4", bl.cnf.inputs)
	}

	andIdentity := nativeReplayOneBitBinary("and", andAB, trueTerm)
	orIdentity := nativeReplayOneBitBinary("or", falseTerm, c)
	xorComplement := nativeReplayOneBitBinary("xor", andAB, trueTerm)
	shared := nativeReplayOneBitBinary("or", andAB, andAB)
	orBC := nativeReplayOneBitBinary("or", b, c)
	distributeLeft := nativeReplayOneBitBinary("and", a, orBC)
	andAC := nativeReplayOneBitBinary("and", a, c)
	distributeRight := nativeReplayOneBitBinary("or", andAB, andAC)

	type termCase struct {
		name     string
		term     *term
		wantRoot int
	}
	cases := []termCase{
		{name: "false constant", term: falseTerm, wantRoot: 0},
		{name: "true constant", term: trueTerm, wantRoot: 1},
		{name: "parameter a", term: a, wantRoot: 2},
		{name: "and gate", term: andAB, wantRoot: 6},
		{name: "interleaved parameter c", term: c, wantRoot: 8},
		{name: "and true identity", term: andIdentity, wantRoot: 6},
		{name: "or false identity", term: orIdentity, wantRoot: 8},
		{name: "xor true complement", term: xorComplement, wantRoot: 7},
		{name: "repeated shared subterm", term: shared, wantRoot: 6},
		{name: "distributivity left", term: distributeLeft, wantRoot: 12},
		{name: "distributivity right", term: distributeRight, wantRoot: 16},
	}
	for _, test := range cases {
		if roots := bl.blast(test.term); len(roots) != 1 || roots[0] != test.wantRoot {
			t.Fatalf("producer %s roots = %v, want [%d]", test.name, roots, test.wantRoot)
		}
	}
	producerDifference := bddFalse
	producerDifference = bl.apply(opOr, producerDifference,
		bl.apply(opXor, bl.memo[distributeLeft][0], bl.memo[distributeRight][0]))
	if producerDifference != 18 {
		t.Fatalf("producer distributivity difference = %d, want 18", producerDifference)
	}
	if _, err := validateCNFAllocation(bl.cnf); err != nil {
		t.Fatalf("one-bit term fixture does not satisfy the production allocation boundary: %v", err)
	}

	replay, err := newNativeCNFReplay(bl)
	if err != nil {
		t.Fatal(err)
	}
	replay.maxInt = replayMaxInt
	leanTerms := make([]string, 0, len(cases))
	t.Run("decisions", func(t *testing.T) {
		for index, test := range cases {
			t.Run(test.name, func(t *testing.T) {
				roots, err := replay.term(test.term)
				if err != nil {
					t.Fatal(err)
				}
				if len(roots) != 1 || roots[0] != test.wantRoot {
					t.Fatalf("replayed roots = %v, want [%d]", roots, test.wantRoot)
				}
				rendered, err := renderNativeCNFReplayOneBitTerm(bl, test.term)
				if err != nil {
					t.Fatal(err)
				}
				leanTerms = append(leanTerms, fmt.Sprintf(
					"def term%d : Term := %s\nexample : replayTerm termSnapshot %d term%d = some %d := by decide",
					index, rendered, replayMaxInt, index, test.wantRoot))
			})
		}
		leftRoots, err := replay.term(distributeLeft)
		if err != nil {
			t.Fatal(err)
		}
		rightRoots, err := replay.term(distributeRight)
		if err != nil {
			t.Fatal(err)
		}
		difference, err := replay.disequality(leftRoots, rightRoots)
		if err != nil {
			t.Fatal(err)
		}
		if difference != 18 {
			t.Fatalf("replayed distributivity difference = %d, want 18", difference)
		}
		if err := replay.finish(); err != nil {
			t.Fatalf("one-bit corpus did not cover the completed producer: %v", err)
		}

		if _, err := renderNativeCNFReplayOneBitTerm(bl, paramTerm("a", 2)); err == nil {
			t.Fatal("two-bit parameter entered the one-bit formal projection")
		}
		if _, err := renderNativeCNFReplayOneBitTerm(bl,
			nativeReplayOneBitBinary("add", a, b)); err == nil {
			t.Fatal("unsupported operation entered the one-bit formal projection")
		}
		if _, err := renderNativeCNFReplayOneBitTerm(bl, paramTerm("missing", 1)); err == nil {
			t.Fatal("unallocated parameter entered the one-bit formal projection")
		}
	})
	if t.Failed() {
		return
	}

	t.Run("kernel", func(t *testing.T) {
		lake, err := exec.LookPath("lake")
		if err != nil {
			requireOracle(t, "lake not on PATH; the formal workflow runs this kernel oracle")
		}
		snapshot, err := renderCNFAllocationSnapshot(bl.cnf)
		if err != nil {
			t.Fatal(err)
		}
		leftIndex, rightIndex := len(cases)-2, len(cases)-1
		leanExamples := fmt.Sprintf(
			"def termSnapshot : CNFDenseAllocation.Snapshot := %s\n"+
				"example : (CNFDenseAllocation.check termSnapshot).isSome = true := by decide\n\n%s\n\n"+
				"example : replayTerm termSnapshot %d (differenceTerm [(term%d, term%d)]) = some 18 := by decide",
			snapshot, strings.Join(leanTerms, "\n\n"), replayMaxInt, leftIndex, rightIndex)
		leanSource := "import Oak.CNFReplayTerm\n\nnamespace Oak.CNFReplayTerm\n\n" +
			leanExamples + "\n\nend Oak.CNFReplayTerm\n"
		leanPath := filepath.Join(t.TempDir(), "NativeCNFReplayTermProductionPins.lean")
		file, err := os.OpenFile(leanPath, os.O_WRONLY|os.O_CREATE|os.O_EXCL, 0o600)
		if err != nil {
			t.Fatal(err)
		}
		if _, err := file.WriteString(leanSource); err != nil {
			file.Close()
			t.Fatal(err)
		}
		if err := file.Close(); err != nil {
			t.Fatal(err)
		}

		ctx, cancel := context.WithTimeout(context.Background(), 90*time.Second)
		defer cancel()
		command := exec.CommandContext(ctx, lake, "env", "lean", leanPath)
		command.Dir = filepath.Join("..", "spec", "lean")
		if output, err := command.CombinedOutput(); err != nil {
			t.Fatalf("kernel-checking native CNF term replay pins: %v (context: %v)\n%s\n--- source ---\n%s",
				err, ctx.Err(), output, leanSource)
		}
	})
}

func nativeReplayOneBitBinary(operation string, left, right *term) *term {
	return &term{kind: termBinary, width: 1, op: operation, left: left, right: right}
}

// Keep the original one-bit corpus under its original result-width guard;
// the shared projector also covers whole words and operand width adaptation.
func renderNativeCNFReplayOneBitTerm(bl *blaster, root *term) (string, error) {
	if root == nil || root.width != 1 {
		return "", fmt.Errorf("result is outside the one-bit projection")
	}
	bits, err := renderNativeCNFReplayWord(bl, root)
	if err != nil {
		return "", err
	}
	return bits[0], nil
}
