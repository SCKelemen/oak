package compiler

import (
	"context"
	"os"
	"strings"
	"testing"
	"time"
)

// The TLC refinement fallback (docs/spec/112-protocols.md section 4a): a
// hand-written module in set-and-function style is outside the normal
// form, so the projection is written as a module of its own and a
// refinement module states Projection!Spec as a property; TLC decides.

// A Slots module written with a set of parked slots rather than the
// projection's element guards. It admits exactly the projection's
// behaviors.
const slotsSetsModule = `---- MODULE SlotsSets ----
EXTENDS Naturals, FiniteSets
CONSTANTS Who
VARIABLES state, parked, woken, last
vars == <<state, parked, woken, last>>
Parked == {k \in 0..1 : parked[k]}
Init == state = "Running" /\ parked = [k \in 0..1 |-> FALSE] /\ woken = [k \in 0..1 |-> 0] /\ last = 9
Park(who) == state = "Running" /\ who \in 0..1 /\ who \notin Parked /\ parked' = [parked EXCEPT ![who] = TRUE] /\ UNCHANGED <<state, woken, last>>
Wake(who) == state = "Running" /\ who \in Parked /\ woken[who] < 2 /\ parked' = [parked EXCEPT ![who] = FALSE] /\ woken' = [woken EXCEPT ![who] = woken[who] + 1] /\ last' = who /\ UNCHANGED state
Halt == state = "Running" /\ Parked = 0..1 /\ state' = "Halted" /\ UNCHANGED <<parked, woken, last>>
Next == (\E who \in Who : Park(who)) \/ (\E who \in Who : Wake(who)) \/ Halt
Spec == Init /\ [][Next]_vars
====
`

func TestTLARefinementModules(t *testing.T) {
	tree, err := New().WithSource("p.oak", slotsProtocolSource).Parse().Get()
	if err != nil {
		t.Fatal(err)
	}
	decl := Protocols(tree)[0]
	report, err := ProtocolConformance(decl, slotsSetsModule, RecordDeclarations(tree.Root))
	if err != nil {
		t.Fatal(err)
	}
	if report.Conforms || len(report.Unsupported) == 0 {
		t.Fatalf("a set-and-function module is outside the normal form:\n%s", FormatTLAConformance(report))
	}
	ref, err := ProtocolRefinement(decl, slotsSetsModule, RecordDeclarations(tree.Root), nil, "")
	if err != nil {
		t.Fatal(err)
	}
	for _, want := range []string{
		"---- MODULE SlotsProjection ----",
		"CONSTANTS Who",
	} {
		if !strings.Contains(ref.Projection, want) {
			t.Fatalf("projection lacks %q:\n%s", want, ref.Projection)
		}
	}
	for _, want := range []string{
		"---- MODULE SlotsSetsRefinement ----",
		"EXTENDS SlotsSets",
		"Projection == INSTANCE SlotsProjection WITH state <- state, parked <- parked, woken <- woken, last <- last",
		"RefinementSpec == Projection!Spec",
	} {
		if !strings.Contains(ref.Refinement, want) {
			t.Fatalf("refinement lacks %q:\n%s", want, ref.Refinement)
		}
	}
	if strings.Contains(ref.Refinement, "CONSTANTS") {
		t.Fatalf("Who is the module's own constant; the refinement declares nothing:\n%s", ref.Refinement)
	}
	// The module declares the projection's payload constant by name, so it
	// takes the projection's default domain.
	if ref.Config != "SPECIFICATION Spec\nPROPERTY RefinementSpec\nCONSTANTS\n    Who = {0, 1, 2, 3}\n" {
		t.Fatalf("config:\n%s", ref.Config)
	}
	// A renamed state variable maps through -map; a missing one is an error.
	renamed := strings.Replace(strings.Replace(slotsSetsModule, "VARIABLES state,", "VARIABLES st,", 1), "state", "st", -1)
	renamed = strings.Replace(renamed, "VARIABLES st,", "VARIABLES st,", 1)
	if _, err := ProtocolRefinement(decl, renamed, RecordDeclarations(tree.Root), nil, ""); err == nil || !strings.Contains(err.Error(), "declares no variable state") {
		t.Fatalf("an unmapped variable must be named: %v", err)
	}
	mapped, err := ProtocolRefinement(decl, renamed, RecordDeclarations(tree.Root), map[string]string{"state": "st"}, "")
	if err != nil {
		t.Fatal(err)
	}
	if !strings.Contains(mapped.Refinement, "WITH state <- st,") {
		t.Fatalf("the mapping must reach the INSTANCE:\n%s", mapped.Refinement)
	}
	// A module with constants of its own needs their values.
	own := strings.Replace(slotsSetsModule, "CONSTANTS Who", "CONSTANTS Who, Limit", 1)
	if _, err := ProtocolRefinement(decl, own, RecordDeclarations(tree.Root), nil, ""); err == nil || !strings.Contains(err.Error(), "Limit") {
		t.Fatalf("the module's own constants need -against-cfg: %v", err)
	}
	withCfg, err := ProtocolRefinement(decl, own, RecordDeclarations(tree.Root), nil, "SPECIFICATION Spec\nCONSTANTS\n    Who = {0, 1}\n    Limit = 2\n")
	if err != nil {
		t.Fatal(err)
	}
	if !strings.Contains(withCfg.Config, "    Limit = 2\n") || !strings.Contains(withCfg.Config, "    Who = {0, 1}\n") || strings.Count(withCfg.Config, "Who =") != 1 {
		t.Fatalf("the module's configuration carries its constants once:\n%s", withCfg.Config)
	}
}

// With TLC available (OAK_TLA2TOOLS_JAR and a Java runtime), the
// set-and-function module refines the projection, and a module that halts
// one parked slot early is caught at the Halt step.
func TestTLARefinementRunsTLC(t *testing.T) {
	if _, _, reason := LocateTLC(); reason != "" {
		t.Skip(reason)
	}
	tree, err := New().WithSource("p.oak", slotsProtocolSource).Parse().Get()
	if err != nil {
		t.Fatal(err)
	}
	decl := Protocols(tree)[0]
	ctx, cancel := context.WithTimeout(context.Background(), 4*time.Minute)
	defer cancel()
	ref, err := CheckRefinement(ctx, decl, slotsSetsModule, RecordDeclarations(tree.Root), nil, "", t.TempDir())
	if err != nil {
		t.Fatal(err)
	}
	if !ref.Ran || !ref.Refines {
		t.Fatalf("the set module refines the projection: ran=%v refines=%v reason=%q\n%s", ref.Ran, ref.Refines, ref.Reason, ref.Output)
	}
	early := strings.Replace(strings.Replace(slotsSetsModule, "Parked = 0..1", "Cardinality(Parked) >= 1", 1), "MODULE SlotsSets ", "MODULE SlotsEarly ", 1)
	bad, err := CheckRefinement(ctx, decl, early, RecordDeclarations(tree.Root), nil, "", t.TempDir())
	if err != nil {
		t.Fatal(err)
	}
	if !bad.Ran || bad.Refines || !strings.Contains(bad.Output, "Halt") {
		t.Fatalf("halting early is a behavior the projection does not admit: ran=%v refines=%v\n%s", bad.Ran, bad.Refines, bad.Output)
	}
	if _, err := os.Stat(bad.Dir + "/SlotsEarlyRefinement.cfg"); err != nil {
		t.Fatalf("the modules are written where the report says: %v", err)
	}
}
