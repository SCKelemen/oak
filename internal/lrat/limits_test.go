package lrat

import (
	"context"
	"crypto/sha256"
	"errors"
	"fmt"
	"os"
	"reflect"
	"strconv"
	"strings"
	"sync"
	"testing"
	"time"
)

func errorText(err error) string {
	if err == nil {
		return ""
	}
	return err.Error()
}

func compareOriginal(t *testing.T, formula, proof string) {
	t.Helper()
	old, oldErr := originalCheck(formula, proof)
	for _, mode := range []int{0, 1, 2} {
		var got Result
		var err error
		switch mode {
		case 0:
			got, err = Check(formula, proof)
		case 1:
			got, err = CheckWithLimits(context.Background(), formula, proof, Limits{})
		case 2:
			got, err = CheckWithLimits(context.Background(), formula, proof, Limits{MaxWork: 1 << 24, MaxStorage: 1 << 24, MaxCount: 1 << 24, MaxFormulaBytes: 8 << 20, MaxCertificateBytes: 8 << 20})
		}
		if got.Additions != old.Additions || got.Deletions != old.Deletions || errorText(err) != errorText(oldErr) {
			t.Fatalf("mode=%d formula=%q proof=%q old=%+v/%v new=%+v/%v", mode, formula, proof, old, oldErr, got, err)
		}
	}
	oldN, oldC, oldE := originalParseDIMACS(formula)
	n, c, e := ParseDIMACS(formula)
	if n != oldN || errorText(e) != errorText(oldE) || len(c) != len(oldC) {
		t.Fatalf("parser disagrees: %d/%v vs %d/%v", n, e, oldN, oldE)
	}
	for i := range c {
		if !reflect.DeepEqual([]int(c[i]), []int(oldC[i])) {
			t.Fatal("parser clauses disagree")
		}
	}
}

func TestLimitedOriginalDifferential(t *testing.T) {
	maxInt := int(^uint(0) >> 1)
	pairs := [][2]string{
		{testFormula, testProof}, {"", ""}, {"p cnf 0 1\n0\n", ""},
		{"p cnf 0 1\n0\n", "garbage"}, {"p cnf 0 1\n0\n", "1 d 1 0"},
		{"p cnf 1 1\n0", "2 1 -1 0 -99 400 0"},
		{"p cnf 1 2\n1 0\n-1 0", "999 d 0\n3 0 1 2 0"},
		{"p cnf 1 2\n1 0\n-1 0", "2 d 1 1 0"},
		{"p cnf 2 3\n1 2 1 0\n-1 0\n-2 0", "4 0 2 3 1 0"},
		{"p\u2003cnf\u00851\u00a02\n1\v0\n-1\f0", "3 0 1 2 0"},
		{"p cnf 1 1\n\xff 0", ""}, {"c ignored\xff\np cnf 0 1\n0", "c ignored\xff"},
		{fmt.Sprintf("p cnf %d 1\n0", maxInt), ""},
		{fmt.Sprintf("p cnf %d 2\n%d 0\n-%d 0", maxInt, maxInt, maxInt), fmt.Sprintf("%d 0 1 2 0", maxInt)},
		{"p cnf 1 2\n1 0\n-1 0", "3\u20030 1 2 0"},
		{"p cnf 1 2\n1 0\n-1 0", "3 0 1 2 0\n\n4 0 -1 0"},
		{"p cnf 1 1\n1\n0", "2 -1 1 0 -1 0\n2 d 1 0"},
	}
	tokens := []string{"0", "+0", "-0", "+1", "-1", "00", "+", "--1", "1x", "\xff", "１２", strconv.Itoa(maxInt), strconv.Itoa(-maxInt - 1), strconv.Itoa(maxInt) + "0", strings.Repeat("0", 2048) + "1", strings.Repeat("0", 2048) + "x"}
	for _, token := range tokens {
		pairs = append(pairs, [2]string{"p cnf 1 1\n" + token + " 0", ""}, [2]string{"p cnf 0 1\n0", token + " 0 1 0"}, [2]string{"p cnf 0 1\n0", "2 d " + token + " 0"})
	}
	for _, p := range pairs {
		compareOriginal(t, p[0], p[1])
	}
	// All one-byte deletions and bounded substitutions cover parser precedence,
	// incomplete lines and logical refusals, without resource-adversarial oracles.
	for _, base := range [][2]string{{testFormula, testProof}, {"p cnf 0 1\n0", "2 0 1 0\n2 d 1 0"}} {
		for side := 0; side < 2; side++ {
			for i := range base[side] {
				for _, replacement := range []string{"", "0", "-", "\xff", "\n", "\t", "\u2003"} {
					p := base
					p[side] = p[side][:i] + replacement + p[side][i+1:]
					compareOriginal(t, p[0], p[1])
				}
			}
		}
	}
	// Generated proofs use generic contradictory units with varying domains,
	// duplicate literals, initial clauses, legal sparse IDs and deletion counts.
	for variables := 1; variables <= 12; variables++ {
		for variable := 1; variable <= variables; variable++ {
			f := fmt.Sprintf("p cnf %d 2\n%d %d 0\n-%d 0", variables, variable, variable, variable)
			for _, id := range []int{3, 17, 99999} {
				compareOriginal(t, f, fmt.Sprintf("%d 0 1 2 0\n%d d 1 2 0", id, id))
			}
		}
	}
}

func TestLimitedWordsOriginalDifferential(t *testing.T) {
	words := []uint32{Magic, 2, 4, 12, 19, 6, 9, 0, 2, 1, 3, 2, 0, 3, 2, 1, 2, 2, 0, 2, 0, 5, 1, 3, 2, 1, 2, 1, 5, 2, 1, 2, 0, 6, 0, 3, 5, 3, 4}
	compare := func(w []uint32) {
		t.Helper()
		old, e := originalCheckWords(w)
		got, err := CheckWords(w)
		if old.Additions != got.Additions || old.Deletions != got.Deletions || errorText(e) != errorText(err) {
			t.Fatalf("words %v: %v/%v vs %v/%v", w, old, e, got, err)
		}
	}
	compare(words)
	for i := range words {
		compare(words[:i])
		for _, value := range []uint32{0, 1, 2, 7, ^uint32(0)} {
			w := append([]uint32(nil), words...)
			w[i] = value
			compare(w)
		}
	}
}

func TestLimitedExactBudgetsAndCounts(t *testing.T) {
	m := &meter{ctx: context.Background()}
	want, err := check(testFormula, testProof, m)
	if err != nil {
		t.Fatal(err)
	}
	limits := Limits{MaxWork: m.work, MaxStorage: m.storage, MaxCount: m.count, MaxFormulaBytes: uint64(len(testFormula)), MaxCertificateBytes: uint64(len(testProof))}
	got, err := CheckWithLimits(context.Background(), testFormula, testProof, limits)
	if err != nil || got != want {
		t.Fatalf("exact: %v %v", got, err)
	}
	cases := []struct {
		resource string
		limits   Limits
	}{{"work", limits}, {"storage", limits}, {"count", limits}, {"text", limits}, {"text", limits}}
	cases[0].limits.MaxWork--
	cases[1].limits.MaxStorage--
	cases[2].limits.MaxCount--
	cases[3].limits.MaxFormulaBytes--
	cases[4].limits.MaxCertificateBytes--
	for _, c := range cases {
		_, err = CheckWithLimits(context.Background(), testFormula, testProof, c.limits)
		var stop *LimitError
		if !errors.As(err, &stop) || !errors.Is(err, ErrLimit) || stop.Resource != c.resource {
			t.Fatalf("%s: %v", c.resource, err)
		}
	}
	t.Logf("small exact charges work=%d storage_slots=%d count=%d", m.work, m.storage, m.count)
	// No call-owned stop or assignment survives into a later check.
	got, err = CheckWithLimits(context.Background(), testFormula, testProof, limits)
	if got != want || err != nil {
		t.Fatal(got, err)
	}
}

func TestLimitedCancellationEveryCheckpoint(t *testing.T) {
	fixtures := [][2]string{
		{"c ignored\n" + testFormula, " \t\nc skip me\n" + testProof},
		{"p cnf 999999999 2\n999999999 0\n-999999999 0", "9999999 0 1 2 0\n9999999 d 1 2 0"},
		{"p cnf 0 1\n0", "\xff🐈bad"},
		{"p cnf 0 1\n0", "2 d -1 0"},
		{"p cnf 1 1\n0", "2 1 -1 0 -99 0"},
	}
	phases := map[string]bool{}
	for _, f := range fixtures {
		visits := 0
		m := &meter{ctx: context.Background(), checkpoint: func(p string) { visits++; phases[p] = true }}
		check(f[0], f[1], m)
		for target := 1; target <= visits; target++ {
			ctx, cancel := context.WithCancel(context.Background())
			seen := 0
			m := &meter{ctx: ctx, checkpoint: func(string) {
				seen++
				if seen == target {
					cancel()
				}
			}}
			_, err := check(f[0], f[1], m)
			cancel()
			if !errors.Is(err, context.Canceled) || seen != target {
				t.Fatalf("checkpoint %d/%d: seen=%d err=%v", target, visits, seen, err)
			}
		}
	}
	for _, phase := range []string{"entry", "success", "formula-scan", "formula-token", "formula-whitespace", "integer", "formula-copy-literal", "proof-comment", "proof-whitespace", "proof-token", "proof-hints", "proof-literal", "rup-literal", "rup-assumption", "domain-entry", "database-entry", "quote", "diagnostic", "allocation-finished", "copy-finished"} {
		if !phases[phase] {
			t.Errorf("unreached required cancellation phase %s", phase)
		}
	}
	ctx, cancel := context.WithDeadline(context.Background(), time.Unix(1, 0))
	defer cancel()
	if _, err := CheckWithLimits(ctx, testFormula, testProof, Limits{}); !errors.Is(err, context.DeadlineExceeded) {
		t.Fatal(err)
	}
	if _, err := CheckWithLimits(nil, testFormula, testProof, Limits{}); err == nil {
		t.Fatal("nil context accepted")
	}
}

func TestLimitedGrowthResetOverflow(t *testing.T) {
	// Every denied allocation retains the old slice, including reused capacity.
	m := &meter{ctx: context.Background(), limits: Limits{MaxStorage: 3}}
	old := []int{1, 2}
	got, ok := grow(old, 3, 1, m, "test-growth")
	if ok || !errors.Is(m.err, ErrLimit) || !reflect.DeepEqual(got, old) {
		t.Fatal(got, ok, m.err)
	}
	m = &meter{ctx: context.Background(), work: ^uint64(0)}
	if m.visit("overflow", 1) || !errors.Is(m.err, ErrLimit) {
		t.Fatal("work overflow")
	}
	m = &meter{ctx: context.Background(), storage: ^uint64(0)}
	if m.reserve("overflow", 1) || !errors.Is(m.err, ErrLimit) {
		t.Fatal("storage overflow")
	}
	m = &meter{ctx: context.Background(), count: ^uint64(0)}
	if m.item("overflow") || !errors.Is(m.err, ErrLimit) {
		t.Fatal("count overflow")
	}
	a := assignment{stamps: []uint32{3, 4, 5, 6}, gen: ^uint32(0), m: &meter{ctx: context.Background()}}
	a.next()
	if a.gen != 1 || !reflect.DeepEqual(a.stamps, []uint32{0, 0, 0, 0}) {
		t.Fatal(a)
	}
	for target := 1; target <= 4; target++ {
		ctx, cancel := context.WithCancel(context.Background())
		visits := 0
		m := &meter{ctx: ctx, checkpoint: func(p string) {
			if p == "assignment-reset" {
				visits++
				if visits == target {
					cancel()
				}
			}
		}}
		a := assignment{stamps: []uint32{3, 4, 5, 6}, gen: ^uint32(0), m: m}
		a.next()
		cancel()
		if !errors.Is(m.err, context.Canceled) || visits != target {
			t.Fatal(m.err, visits)
		}
	}
	for _, declared := range []uint64{0, 1, denseVariableLimit, denseVariableLimit + 1, uint64(^uint(0) >> 1)} {
		// Check selection without allocating a full dense boundary in every test.
		if useDenseLiteralDomain(declared, 0) != originaluseDenseLiteralDomain(declared, 0) {
			t.Fatal("domain selection changed")
		}
	}
}

func TestLimitedAmplificationAndChurn(t *testing.T) {
	// RUP re-scans a long falsified clause on every independent addition.
	f := "p cnf 1 1\n" + strings.Repeat("1 ", 128) + "0"
	proof := strings.Builder{}
	for id := 2; id < 20; id++ {
		fmt.Fprintf(&proof, "%d 1 0 1 0\n", id)
	}
	m := &meter{ctx: context.Background()}
	_, err := check(f, proof.String(), m)
	if err == nil || errorText(err) != "the certificate never derives the empty clause" {
		t.Fatal(err)
	}
	visits := 0
	limited := &meter{ctx: context.Background(), limits: Limits{MaxWork: m.work / 2}, checkpoint: func(p string) {
		if p == "rup-literal" {
			visits++
		}
	}}
	_, err = check(f, proof.String(), limited)
	if !errors.Is(err, ErrLimit) || visits < 128 {
		t.Fatal(visits, err)
	}
	// Empty clauses consume database metadata even after deletion.
	proof.Reset()
	for id := 2; id < 40; id++ {
		fmt.Fprintf(&proof, "%d 0 1 0\n%d d %d 0\n", id, id, id)
	}
	m = &meter{ctx: context.Background()}
	_, err = check("p cnf 0 1\n0", proof.String(), m)
	if err != nil {
		t.Fatal(err)
	}
	_, err = CheckWithLimits(context.Background(), "p cnf 0 1\n0", proof.String(), Limits{MaxStorage: m.storage - 1})
	if !errors.Is(err, ErrLimit) {
		t.Fatal(err)
	}
}

func TestLimitedConcurrentCalls(t *testing.T) {
	var wg sync.WaitGroup
	for i := 0; i < 12; i++ {
		wg.Add(1)
		go func() {
			defer wg.Done()
			for j := 0; j < 20; j++ {
				r, e := CheckWithLimits(context.Background(), testFormula, testProof, Limits{MaxWork: 1 << 20, MaxStorage: 1 << 20})
				if e != nil || r != (Result{2, 2}) {
					t.Error(r, e)
				}
				ctx, cancel := context.WithCancel(context.Background())
				cancel()
				if _, e := CheckWithLimits(ctx, testFormula, testProof, Limits{}); !errors.Is(e, context.Canceled) {
					t.Error(e)
				}
			}
		}()
	}
	wg.Wait()
}

func TestLimitedRetainedCertificate(t *testing.T) {
	read := func(path, want string) string {
		t.Helper()
		b, e := os.ReadFile(path)
		if e != nil {
			t.Fatal(e)
		}
		if len(b) > 8<<20 || fmt.Sprintf("%x", sha256.Sum256(b)) != want {
			t.Fatal("retained identity mismatch", path)
		}
		return string(b)
	}
	formula := read("testdata/retained.cnf", "ca659ecd4ed22d4e5d461edb10999857acfb6a008572baee77d0bd35cacb962a")
	proof := read("testdata/retained.lrat", "a04613d4720c24082730adedec8d3242d8dbaf1b0d9b2aeff7e6b87375197c90")
	limits := Limits{MaxWork: 16777216, MaxStorage: 16777216, MaxCount: 16777216, MaxFormulaBytes: 8 << 20, MaxCertificateBytes: 8 << 20}
	m := &meter{ctx: context.Background(), limits: limits}
	r, e := check(formula, proof, m)
	if e != nil || r != (Result{1561, 561}) {
		t.Fatalf("saved certificate: result=%+v err=%v work=%d storage=%d count=%d", r, e, m.work, m.storage, m.count)
	}
	original, e := originalCheck(formula, proof)
	if e != nil || original.Additions != r.Additions || original.Deletions != r.Deletions {
		t.Fatal(original, e)
	}
	t.Logf("retained exact charges work=%d storage_slots=%d count=%d additions=%d deletions=%d", m.work, m.storage, m.count, r.Additions, r.Deletions)
}

func TestLimitedIntegerAndQuotedCompatibility(t *testing.T) {
	tokens := []string{"", "+", "-", "0", "-0", "+00000001", strconv.Itoa(int(^uint(0) >> 1)), strconv.Itoa(-int(^uint(0)>>1) - 1), strings.Repeat("0", 4096), strings.Repeat("0", 4096) + "1", strings.Repeat("0", 4096) + "x", "\xff\x00\n\t\"\\", "猫\u2028\u0085\ufffd", "1_0"}
	for _, s := range tokens {
		m := &meter{ctx: context.Background()}
		n, ok := atoi(s, m)
		want, e := strconv.Atoi(s)
		if ok != (e == nil) || (ok && n != want) {
			t.Fatalf("atoi %q: %d/%v vs %d/%v", s, n, ok, want, e)
		}
		q := quoted(s, m)
		if q != strconv.Quote(s) || m.err != nil {
			t.Fatalf("quote %q: %q vs %q (%v)", s, q, strconv.Quote(s), m.err)
		}
	}
}

func TestLimitedPartialCountsAndLateCancellation(t *testing.T) {
	for _, tc := range []struct {
		phase      string
		occurrence int
		want       Result
	}{
		{"addition-commit", 2, Result{1, 2}}, {"proof-deletion", 2, Result{1, 1}}, {"success", 1, Result{2, 2}},
	} {
		ctx, cancel := context.WithCancel(context.Background())
		count := 0
		m := &meter{ctx: ctx, checkpoint: func(p string) {
			if p == tc.phase {
				count++
				if count == tc.occurrence {
					cancel()
				}
			}
		}}
		got, err := check(testFormula, testProof, m)
		cancel()
		if got != tc.want || !errors.Is(err, context.Canceled) {
			t.Fatalf("%s: %v/%v want %v/canceled", tc.phase, got, err, tc.want)
		}
	}
	// Initial-empty acceptance also has a final publication checkpoint.
	ctx, cancel := context.WithCancel(context.Background())
	m := &meter{ctx: ctx, checkpoint: func(p string) {
		if p == "success" {
			cancel()
		}
	}}
	if _, err := check("p cnf 0 1\n0", "", m); !errors.Is(err, context.Canceled) {
		t.Fatal(err)
	}
	cancel()
}
