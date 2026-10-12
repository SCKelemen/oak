package asm

import (
	"context"
	"errors"
	"io"
	"strings"
	"sync"
	"testing"
)

func checkedTypedCNFTestFixture(t *testing.T, shared bool) (typedCNFAudit, *blaster, [][]int) {
	t.Helper()
	x, y := typedCNFParam("x", 4, 4), typedCNFParam("x", 4, 4)
	if shared {
		y = x
	}
	p, l, r := typedCNFConst(1, 1), typedCNFBinary("add", 4, x, y), typedCNFParam("z", 4, 4)
	bl, claim, emitted := typedCNFProduce(p, l, r, []string{"x", "z"}, map[string]int{"x": 4, "z": 4})
	a, err := checkTypedCNFImplication(t.Context(), bl, p, l, r, claim, emitted, typedCNFDiagnosticLimits)
	if err != nil {
		t.Fatal(err)
	}
	return a, bl, emitted
}

// Value-only identity diagnostic; no term, slice, map or mutable alias escapes.
func (a typedCNFAudit) testIdentity() (shared, wrapper bool, err error) {
	if _, ok := a.stats(); !ok {
		return false, false, errInvalidTypedCNFAudit
	}
	r := a.checked.roots
	return r[1].left == r[1].right, r[3].cond == r[0] && r[3].left.left == r[1] && r[3].left.right == r[2], nil
}

func TestCheckedTypedCNFOwnership(t *testing.T) {
	for _, shared := range []bool{false, true} {
		a, bl, emitted := checkedTypedCNFTestFixture(t, shared)
		gotShared, wrapper, err := a.testIdentity()
		if err != nil || gotShared != shared || !wrapper {
			t.Fatalf("owned identity: %t %t %v", gotShared, wrapper, err)
		}
		want := typedCNFDIMACS(checkedTypedCNFLabel, bl.cnf.variables, emitted)
		before := a.testStats(t)
		// Producer rows can alias one another; neither is the owned checked row.
		bl.cnf.clauses[0][0] *= -1
		emitted[len(emitted)-1][0] *= -1
		bl.cnf.variables = 1
		bl.params[0] = "mutated"
		for node, bits := range bl.memo {
			node.op = "changed"
			bits[0] ^= 1
		}
		copyAudit := a
		detached := a.testStats(t)
		detached.Visits = -1
		var output strings.Builder
		if err := copyAudit.writeDIMACS(t.Context(), checkedTypedCNFLabel, &output, len(want)); err != nil || output.String() != want {
			t.Fatalf("owned bytes changed: %v", err)
		}
		if a.testStats(t) != before {
			t.Fatal("projection or detached stats mutated audit")
		}
		if err := a.checkValues(map[string]uint64{"x": 3, "z": 6}, typedCNFMemory); err != nil {
			t.Fatal(err)
		}
	}
}

type checkedTypedCNFWriter struct {
	write func([]byte) (int, error)
}

func (w checkedTypedCNFWriter) Write(p []byte) (int, error) { return w.write(p) }

func TestCheckedTypedCNFSerialization(t *testing.T) {
	a, bl, emitted := checkedTypedCNFTestFixture(t, false)
	want := typedCNFDIMACS(checkedTypedCNFLabel, bl.cnf.variables, emitted)
	if checkedTypedCNFLabel != typedFixtureLabel || len(checkedTypedCNFLabel) != 69 {
		t.Fatal("fixed label changed")
	}
	for _, cap := range []int{len(want), len(want) - 1, 0, -1} {
		var out strings.Builder
		err := a.writeDIMACS(t.Context(), checkedTypedCNFLabel, &out, cap)
		if cap == len(want) {
			if err != nil || out.String() != want {
				t.Fatalf("exact bytes: %v", err)
			}
		} else if !errors.Is(err, errTypedCNFResource) || out.Len() > max(cap, 0) {
			t.Fatalf("output ceiling: %v", err)
		}
	}
	for _, label := range []string{"", "other", checkedTypedCNFLabel + "\np cnf 1 1", checkedTypedCNFLabel[:68] + "\r", strings.Repeat("x", 1024)} {
		var out strings.Builder
		if err := a.writeDIMACS(t.Context(), label, &out, len(want)); err == nil || out.Len() != 0 {
			t.Fatal("invalid label wrote bytes")
		}
	}
	if err := a.writeDIMACS(nil, checkedTypedCNFLabel, io.Discard, len(want)); err == nil {
		t.Fatal("nil context accepted")
	}
	if err := a.writeDIMACS(t.Context(), checkedTypedCNFLabel, nil, len(want)); err == nil {
		t.Fatal("nil writer accepted")
	}
	boom := errors.New("writer failure")
	for _, fault := range []struct {
		writer io.Writer
		want   error
	}{
		{checkedTypedCNFWriter{func(p []byte) (int, error) { return 0, boom }}, boom},
		{checkedTypedCNFWriter{func(p []byte) (int, error) { return len(p) - 1, nil }}, io.ErrShortWrite},
	} {
		if err := a.writeDIMACS(t.Context(), checkedTypedCNFLabel, fault.writer, len(want)); !errors.Is(err, fault.want) {
			t.Fatalf("writer error: %v", err)
		}
	}
	for _, cancelAt := range []int{0, 1, len(want)} {
		ctx, cancel := context.WithCancel(t.Context())
		written := 0
		if cancelAt == 0 {
			cancel()
		}
		writer := checkedTypedCNFWriter{func(p []byte) (int, error) {
			written += len(p)
			if written >= cancelAt {
				cancel()
			}
			return len(p), nil
		}}
		err := a.writeDIMACS(ctx, checkedTypedCNFLabel, writer, len(want))
		cancel()
		if !errors.Is(err, context.Canceled) || (cancelAt == 0 && written != 0) {
			t.Fatalf("serialization cancellation: %v", err)
		}
	}
}

func TestCheckedTypedCNFZeroAndPartial(t *testing.T) {
	// These deliberately incomplete literals are permitted only as negative controls.
	for _, a := range []typedCNFAudit{{}, {checked: &checkedTypedCNFSnapshot{}}} {
		if stats, ok := a.stats(); ok || stats != (typedCNFAuditStats{}) {
			t.Fatal("incomplete audit returned checked statistics")
		}
		if err := a.writeDIMACS(t.Context(), checkedTypedCNFLabel, io.Discard, 1); !errors.Is(err, errInvalidTypedCNFAudit) {
			t.Fatal("incomplete audit serialized")
		}
		if err := a.checkValues(nil, typedCNFMemory); !errors.Is(err, errInvalidTypedCNFAudit) {
			t.Fatal("incomplete audit evaluated")
		}
	}
}

func TestCheckedTypedCNFConcurrentProjections(t *testing.T) {
	a, bl, emitted := checkedTypedCNFTestFixture(t, true)
	want := typedCNFDIMACS(checkedTypedCNFLabel, bl.cnf.variables, emitted)
	before := a.testStats(t)
	var wg sync.WaitGroup
	for i := 0; i < 4; i++ {
		wg.Add(1)
		go func() {
			defer wg.Done()
			var out strings.Builder
			if err := a.writeDIMACS(t.Context(), checkedTypedCNFLabel, &out, len(want)); err != nil || out.String() != want {
				t.Errorf("concurrent projection: %v", err)
			}
			if err := a.checkValues(map[string]uint64{"x": 7, "z": 14}, typedCNFMemory); err != nil {
				t.Error(err)
			}
		}()
	}
	wg.Wait()
	if a.testStats(t) != before {
		t.Fatal("concurrent projection changed counters")
	}
}

func TestCheckedTypedCNFIndependentStreams(t *testing.T) {
	for _, changeBuilder := range []bool{false, true} {
		x, z := typedCNFParam("x", 4, 4), typedCNFParam("z", 4, 4)
		p := typedCNFConst(1, 1)
		l := typedCNFBinary("add", 4, x, typedCNFConst(4, 1))
		bl, claim, emitted := typedCNFProduce(p, l, z, []string{"x", "z"}, map[string]int{"x": 4, "z": 4})
		// Separate the producer-side arrays before corrupting exactly one stream.
		for i := range emitted {
			emitted[i] = append([]int(nil), emitted[i]...)
		}
		if changeBuilder {
			bl.cnf.clauses[0][0] *= -1
		} else {
			emitted[0][0] *= -1
		}
		a, err := checkTypedCNFImplication(t.Context(), bl, p, l, z, claim, emitted, typedCNFDiagnosticLimits)
		if err == nil || !strings.Contains(err.Error(), "ordered clause trace") || a != (typedCNFAudit{}) {
			t.Fatalf("independent stream refusal: %v", err)
		}
		// Earlier memo validation must still win over this later clause mismatch.
		g := bl.cnf.gates[0]
		key, _ := cnfGateMemoKey(0, g)
		bl.cnf.memo[key]++
		a, err = checkTypedCNFImplication(t.Context(), bl, p, l, z, claim, emitted, typedCNFDiagnosticLimits)
		if err == nil || !strings.Contains(err.Error(), "gate memo") || a != (typedCNFAudit{}) {
			t.Fatalf("phase order changed: %v", err)
		}
	}
}
