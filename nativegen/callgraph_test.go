package nativegen

import (
	"reflect"
	"testing"

	"github.com/SCKelemen/oak/asm"
)

const callGraphSource = `
leaf: (x: u32): u32 = x + u32(1)
mid: (x: u32): u32 = leaf(x) * u32(2)
pub top: (x: u32): u32 = mid(x) + leaf(x)
alone: (x: u32): u32 = x
even: (n: u32): u32 = n == u32(0) ? u32(1) | odd(n - u32(1))
odd: (n: u32): u32 = n == u32(0) ? u32(0) | even(n - u32(1))
main: (): u32 = top(u32(3)) + even(u32(4))
`

func TestCallGraphEdgesReachabilityAndOrder(t *testing.T) {
	_, functions, _, _ := checkedFillFunction(t, callGraphSource, "top")
	g := BuildCallGraph(functions)
	if got := g.Callees("top"); !reflect.DeepEqual(got, []string{"leaf", "mid"}) {
		t.Fatalf("top's callees: %v", got)
	}
	if got := g.Callers("leaf"); !reflect.DeepEqual(got, []string{"mid", "top"}) {
		t.Fatalf("leaf's callers: %v", got)
	}
	// top is exported and main is main: both root edges; alone is off the root.
	if got := g.Unreachable(); !reflect.DeepEqual(got, []string{"alone"}) {
		t.Fatalf("unreachable: %v", got)
	}
	// Callees before callers; the mutual recursion one component.
	order := g.Components()
	position := map[string]int{}
	for i, component := range order {
		for _, name := range component {
			position[name] = i
		}
	}
	if !(position["leaf"] < position["mid"] && position["mid"] < position["top"] && position["top"] < position["main"]) {
		t.Fatalf("callees must come before callers: %v", order)
	}
	if position["even"] != position["odd"] {
		t.Fatalf("even and odd must share a component: %v", order)
	}
	recursive := g.Recursive()
	if !recursive["even"] || !recursive["odd"] || recursive["leaf"] || recursive["main"] {
		t.Fatalf("recursion: %v", recursive)
	}
}

func TestVerdictRootsFollowCallReasons(t *testing.T) {
	verdicts := map[string]asm.Verdict{
		"words":  {Kind: asm.VerdictTrusted, Message: "asm unit h__words: not verified (a frame load at a data-dependent index)"},
		"cv":     {Kind: asm.VerdictTrusted, Message: "asm unit h__cv: not verified (a call to h__words: the record argument block lies in the frame's unknown region)"},
		"update": {Kind: asm.VerdictTrusted, Message: "asm unit h__update: not verified (a call to h__cv whose body contains a frame load (in a loop body))"},
		"final":  {Kind: asm.VerdictTrusted, Message: "asm unit h__final: not verified (a call to h__words: the record argument block lies in the frame's unknown region)"},
		"init":   {Kind: asm.VerdictProven, Message: "asm unit h__init: proven"},
		"other":  {Kind: asm.VerdictTrusted, Message: "asm unit h__other: not verified (more paths than the budget)"},
	}
	symbols := map[string]string{"h__words": "words", "h__cv": "cv", "h__update": "update", "h__final": "final", "h__init": "init", "h__other": "other"}
	roots := VerdictRoots(verdicts, symbols)
	if len(roots) != 1 || roots[0].Name != "words" || !reflect.DeepEqual(roots[0].Blocked, []string{"cv", "final", "update"}) {
		t.Fatalf("roots: %+v", roots)
	}
}
