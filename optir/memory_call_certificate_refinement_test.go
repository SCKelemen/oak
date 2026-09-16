package optir

import (
	"fmt"
	"os"
	"path/filepath"
	"strconv"
	"strings"
	"testing"
)

// The three present call-effect kinds and the structural core of the small
// postorder trace checker are modeled in Oak.OptIRCallSummaryCertificate.
// Lean proves the join laws and model checker's soundness; these bounded pins
// require selected decisions made by the production Go procedures to occur as
// kernel-checked examples. They are not a universal Go-to-Lean refinement.
func TestCheckedMemoryCallProofTraceMatchesLeanRefinement(t *testing.T) {
	contents, err := os.ReadFile(filepath.Join("..", "spec", "lean", "Oak", "OptIRCallSummaryCertificate.lean"))
	if err != nil {
		t.Fatal(err)
	}
	lean := string(contents)
	kinds := []MemoryAccessKind{MemoryRead, MemoryWrite, MemoryReadWrite}
	var missing []string
	require := func(name, line string) {
		if !strings.Contains(lean, line) {
			missing = append(missing, name+":\n  "+line)
		}
	}
	for _, left := range kinds {
		for _, right := range kinds {
			got := joinCheckedMemoryCallEffectKinds(left, right)
			line := fmt.Sprintf("example : Effect.join (some %s) (some %s) = some %s := by decide",
				renderCheckedMemoryCallProofKind(t, left), renderCheckedMemoryCallProofKind(t, right),
				renderCheckedMemoryCallProofKind(t, got))
			require("join "+string(left)+" with "+string(right), line)
		}
	}

	readX := proofAccess("global:x", MemoryRead, "u32")
	writeX := proofAccess("global:x", MemoryWrite, "u32")
	readWriteX := proofAccess("global:x", MemoryReadWrite, "u32")
	writeY := proofAccess("global:y", MemoryWrite, "u64")
	leaf := checkedMemoryCallProofStep{name: "leaf", direct: []CheckedMemoryCallAccess{readX}, summary: []CheckedMemoryCallAccess{readX}}
	root := checkedMemoryCallProofStep{name: "root", children: []checkedMemoryCallProofChild{{callee: "leaf", accesses: []CheckedMemoryCallAccess{readX}}}, summary: []CheckedMemoryCallAccess{readX}}
	left := checkedMemoryCallProofStep{name: "left", direct: []CheckedMemoryCallAccess{writeY}, children: []checkedMemoryCallProofChild{{callee: "leaf", accesses: []CheckedMemoryCallAccess{readX}}}, summary: []CheckedMemoryCallAccess{readX, writeY}}
	right := checkedMemoryCallProofStep{name: "right", direct: []CheckedMemoryCallAccess{writeX}, summary: []CheckedMemoryCallAccess{writeX}}
	diamondRoot := checkedMemoryCallProofStep{
		name: "root",
		children: []checkedMemoryCallProofChild{
			{callee: "left", accesses: []CheckedMemoryCallAccess{readX, writeY}},
			{callee: "right", accesses: []CheckedMemoryCallAccess{writeX}},
		},
		summary: []CheckedMemoryCallAccess{readWriteX, writeY},
	}
	tests := []struct {
		name  string
		root  string
		trace []checkedMemoryCallProofStep
	}{
		{name: "NoModRef leaf", root: "root", trace: []checkedMemoryCallProofStep{{name: "root"}}},
		{name: "leaf", root: "leaf", trace: []checkedMemoryCallProofStep{leaf}},
		{name: "chain", root: "root", trace: []checkedMemoryCallProofStep{leaf, root}},
		{name: "diamond", root: "root", trace: []checkedMemoryCallProofStep{leaf, left, right, diamondRoot}},
		{name: "parent before child", root: "leaf", trace: []checkedMemoryCallProofStep{root, leaf}},
		{name: "duplicate", root: "leaf", trace: []checkedMemoryCallProofStep{leaf, leaf}},
		{name: "wrong root", root: "other", trace: []checkedMemoryCallProofStep{leaf}},
		{name: "disconnected", root: "root", trace: []checkedMemoryCallProofStep{leaf, {name: "root"}}},
		{name: "forged child", root: "root", trace: []checkedMemoryCallProofStep{leaf, {
			name: "root", children: []checkedMemoryCallProofChild{{callee: "leaf", accesses: []CheckedMemoryCallAccess{writeX}}}, summary: []CheckedMemoryCallAccess{writeX},
		}}},
		{name: "conflicting types", root: "root", trace: []checkedMemoryCallProofStep{{
			name: "root", direct: []CheckedMemoryCallAccess{readX, proofAccess("global:x", MemoryWrite, "u64")}, summary: []CheckedMemoryCallAccess{readWriteX},
		}}},
	}
	for _, test := range tests {
		_, err := verifyCheckedMemoryCallProofTrace(test.root, test.trace)
		line := fmt.Sprintf("example : check %s %s = %v := by decide",
			renderCheckedMemoryCallProofTrace(t, test.trace), strconv.Quote(test.root), err == nil)
		require(test.name, line)
	}
	if len(missing) != 0 {
		t.Fatalf("%d call-summary decision(s) not stated in OptIRCallSummaryCertificate.lean:\n%s", len(missing), strings.Join(missing, "\n"))
	}
}

func proofAccess(region string, kind MemoryAccessKind, typ Type) CheckedMemoryCallAccess {
	return CheckedMemoryCallAccess{Region: RegionID(region), Kind: kind, ValueType: typ}
}

func renderCheckedMemoryCallProofKind(t *testing.T, kind MemoryAccessKind) string {
	t.Helper()
	switch kind {
	case MemoryRead:
		return ".read"
	case MemoryWrite:
		return ".write"
	case MemoryReadWrite:
		return ".readWrite"
	default:
		t.Fatalf("call-summary refinement has unsupported access kind %q", kind)
		return ""
	}
}

func renderCheckedMemoryCallProofAccesses(t *testing.T, accesses []CheckedMemoryCallAccess) string {
	t.Helper()
	parts := make([]string, 0, len(accesses))
	for _, access := range accesses {
		parts = append(parts, fmt.Sprintf("⟨%s, %s, %s⟩", strconv.Quote(string(access.Region)),
			renderCheckedMemoryCallProofKind(t, access.Kind), strconv.Quote(string(access.ValueType))))
	}
	return "[" + strings.Join(parts, ", ") + "]"
}

func renderCheckedMemoryCallProofTrace(t *testing.T, trace []checkedMemoryCallProofStep) string {
	t.Helper()
	steps := make([]string, 0, len(trace))
	for _, step := range trace {
		children := make([]string, 0, len(step.children))
		for _, child := range step.children {
			children = append(children, fmt.Sprintf("⟨%s, %s⟩", strconv.Quote(child.callee),
				renderCheckedMemoryCallProofAccesses(t, child.accesses)))
		}
		steps = append(steps, fmt.Sprintf("⟨%s, %s, [%s], %s⟩", strconv.Quote(step.name),
			renderCheckedMemoryCallProofAccesses(t, step.direct), strings.Join(children, ", "),
			renderCheckedMemoryCallProofAccesses(t, step.summary)))
	}
	return "[" + strings.Join(steps, ", ") + "]"
}
