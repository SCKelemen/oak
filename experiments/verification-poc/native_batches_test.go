package main

import (
	"fmt"
	"regexp"
	"strings"
	"testing"
)

var nativeCaseDeclaration = regexp.MustCompile(`(?m)^([A-Za-z_][A-Za-z0-9_]*_case_[0-9]+): \(\): Bool \{`)

// Generated cases own their state. Keep their bodies and assertions unchanged,
// but avoid quadratic source-position work on a single enormous translation unit.
func batchOakCorpus(source string, size int) ([]string, error) {
	if size <= 0 {
		return nil, fmt.Errorf("invalid native batch size")
	}
	matches := nativeCaseDeclaration.FindAllStringSubmatchIndex(source, -1)
	if len(matches) == 0 {
		return []string{source}, nil
	}
	const mainHeader = "main: (): i32 {\n"
	mainAt := strings.LastIndex(source, mainHeader)
	if mainAt < 0 || mainAt < matches[len(matches)-1][0] {
		return nil, fmt.Errorf("generated corpus main missing")
	}
	var expected strings.Builder
	expected.WriteString(mainHeader)
	names := make([]string, len(matches))
	seen := map[string]bool{}
	for i, m := range matches {
		names[i] = source[m[2]:m[3]]
		if seen[names[i]] {
			return nil, fmt.Errorf("duplicate generated case")
		}
		seen[names[i]] = true
		fmt.Fprintf(&expected, "assert(%s())\n", names[i])
	}
	expected.WriteString("42\n}\n")
	if strings.TrimSpace(source[mainAt:]) != strings.TrimSpace(expected.String()) {
		return nil, fmt.Errorf("generated main must assert every case exactly once, in order")
	}
	if len(matches) <= size {
		return []string{source}, nil
	}
	batches := []string{}
	shared := source[:matches[0][0]]
	for first := 0; first < len(matches); first += size {
		last := first + size
		if last > len(matches) {
			last = len(matches)
		}
		end := mainAt
		if last < len(matches) {
			end = matches[last][0]
		}
		var out strings.Builder
		out.WriteString(shared)
		out.WriteString(source[matches[first][0]:end])
		out.WriteString(mainHeader)
		for i := first; i < last; i++ {
			fmt.Fprintf(&out, "assert(%s())\n", names[i])
		}
		out.WriteString("42\n}\n")
		batches = append(batches, out.String())
	}
	return batches, nil
}
func runOakStream(t *testing.T, source string) {
	t.Helper()
	batches, err := batchOakCorpus(source, 64)
	if err != nil {
		t.Fatal(err)
	}
	if len(batches) == 1 {
		runOakStreamUnit(t, batches[0])
		return
	}
	for i, batch := range batches {
		if !t.Run(fmt.Sprintf("batch-%03d", i), func(t *testing.T) { runOakStreamUnit(t, batch) }) {
			t.FailNow()
		}
	}
}
func nativeBatchFixture(count int) string {
	var out, main strings.Builder
	out.WriteString("shared: (): Bool { true }\n")
	main.WriteString("main: (): i32 {\n")
	for i := 0; i < count; i++ {
		fmt.Fprintf(&out, "batch_case_%d: (): Bool {\n// payload %d\nshared()\n}\n", i, i)
		fmt.Fprintf(&main, "assert(batch_case_%d())\n", i)
	}
	main.WriteString("42\n}\n")
	out.WriteString(main.String())
	return out.String()
}
func TestNativeCorpusBatchCoverage(t *testing.T) {
	source := nativeBatchFixture(130)
	batches, err := batchOakCorpus(source, 64)
	if err != nil {
		t.Fatal(err)
	}
	if len(batches) != 3 {
		t.Fatalf("got %d batches", len(batches))
	}
	for _, batch := range batches {
		if strings.Count(batch, "shared: (): Bool") != 1 {
			t.Fatal("shared definitions changed")
		}
		if len(nativeCaseDeclaration.FindAllStringIndex(batch, -1)) > 64 {
			t.Fatal("oversized batch")
		}
	}
	combined := strings.Join(batches, "\n")
	for i := 0; i < 130; i++ {
		body := fmt.Sprintf("batch_case_%d: (): Bool {\n// payload %d\nshared()\n}\n", i, i)
		assertion := fmt.Sprintf("assert(batch_case_%d())", i)
		if strings.Count(combined, body) != 1 || strings.Count(combined, assertion) != 1 {
			t.Fatalf("case %d omitted, duplicated or modified", i)
		}
	}
	small := nativeBatchFixture(1)
	one, err := batchOakCorpus(small, 64)
	if err != nil || len(one) != 1 || one[0] != small {
		t.Fatal("single unit changed")
	}
}
func TestNativeCorpusBatchRejectsLostAssertions(t *testing.T) {
	good := nativeBatchFixture(130)
	for _, bad := range []string{
		strings.Replace(good, "assert(batch_case_0())\n", "", 1),
		strings.Replace(good, "assert(batch_case_0())", "assert(batch_case_1())", 1),
		strings.Replace(good, "42\n}", "assert(shared())\n42\n}", 1),
		strings.Replace(good, "batch_case_1: ()", "batch_case_0: ()", 1),
	} {
		if _, err := batchOakCorpus(bad, 64); err == nil {
			t.Fatal("unsafe corpus split accepted")
		}
	}
	if _, err := batchOakCorpus(good, 0); err == nil {
		t.Fatal("zero batch size accepted")
	}
}
