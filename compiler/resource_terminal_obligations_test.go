package compiler

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/typechecker"
)

// Terminal-state obligations (docs/spec/50-borrowing.md section 9
// "Terminal-state obligations", authority roadmap milestone 6): a protocol
// may declare terminal states; an owned resource of such a protocol — a
// fresh result, a local root, a consumed parameter — must reach one on
// every path before its last name leaves scope, unless its custody passes
// on by return, consumption, or a surviving alias.
func obligationDeclarations(terminal ...string) []typechecker.ResourceProtocolDeclaration {
	mode := func(index int, m typechecker.ResourceParameterMode) typechecker.ResourceParameterDeclaration {
		return typechecker.ResourceParameterDeclaration{Index: index, Mode: m}
	}
	borrowed, consumed := typechecker.ResourceParameterBorrowed, typechecker.ResourceParameterConsumed
	return []typechecker.ResourceProtocolDeclaration{{
		Name:          "HandleLifecycle",
		ResourceTypes: []string{"Handle"},
		States:        []string{"Open", "Closed", "Aborted"},
		Initial:       "Open",
		Terminal:      terminal,
		Transitions: []typechecker.ResourceTransitionDeclaration{
			{Name: "open", Callable: "open", From: "Open", To: "Open", ReturnsFresh: true},
			{Name: "inspect", Callable: "inspect", From: "Open", To: "Open", Parameters: []typechecker.ResourceParameterDeclaration{mode(0, borrowed)}},
			{Name: "close", Callable: "close", From: "Open", To: "Closed", Parameters: []typechecker.ResourceParameterDeclaration{mode(0, consumed)}},
			{Name: "abort", Callable: "abort", From: "Open", To: "Aborted", Parameters: []typechecker.ResourceParameterDeclaration{mode(0, consumed)}},
			// renew consumes and hands back fresh authority: a transfer.
			{Name: "renew", Callable: "renew", From: "Open", To: "Open", Parameters: []typechecker.ResourceParameterDeclaration{mode(0, consumed)}, ReturnsFresh: true},
		},
	}}
}

const obligationBase = `
Option[T]: type = Some: T | None
Handle: type = struct { id: u32 }
Holder: type = struct { h: Handle }
open: (id: u32): Handle = Handle { id: id }
inspect: (h: Handle): () = {}
close: (h: Handle): () = {}
abort: (h: Handle): () = {}
renew: (h: Handle): Handle {
  next: Handle = Handle { id: h.id }
  close(h)
  next
}
`

func checkObligations(t *testing.T, name, body string, extra ...typechecker.ResourceTransitionDeclaration) error {
	t.Helper()
	declarations := obligationDeclarations("Closed", "Aborted")
	declarations[0].Transitions = append(declarations[0].Transitions, extra...)
	_, err := New().
		WithSource(name+".oak", obligationBase+body).
		WithResourceProtocols(declarations).
		Check().
		Get()
	return err
}

func TestObligationUnclosedFreshHandle(t *testing.T) {
	err := checkObligations(t, "unclosed", `
f: (): u32 {
  h: Handle = open(u32(1))
  inspect(h)
  0
}
`)
	expectCode(t, "unclosed", err, typechecker.CodeResourceUnclosed)
	for _, want := range []string{"Closed, Aborted", `"abort", "close"`} {
		if !strings.Contains(err.Error(), want) {
			t.Fatalf("diagnostic should mention %q: %v", want, err)
		}
	}
	// Either terminal transition discharges the obligation.
	for name, closer := range map[string]string{"close": "close(h)", "abort": "abort(h)"} {
		t.Run(name, func(t *testing.T) {
			if err := checkObligations(t, "closed", `
f: (): u32 {
  h: Handle = open(u32(1))
  inspect(h)
  `+closer+`
  0
}
`); err != nil {
				t.Fatalf("a closed handle satisfies its obligation: %v", err)
			}
		})
	}
}

func TestObligationCheckedOnEveryPath(t *testing.T) {
	err := checkObligations(t, "one-path", `
f: (flag: Bool): u32 {
  h: Handle = open(u32(1))
  flag ? { close(h) } | { inspect(h) }
  0
}
`)
	expectCode(t, "one-path", err, typechecker.CodeResourceUnclosed)
	if !strings.Contains(err.Error(), "some paths only") {
		t.Fatalf("diagnostic should say the close is partial: %v", err)
	}
	if err := checkObligations(t, "both-paths", `
f: (flag: Bool): u32 {
  h: Handle = open(u32(1))
  flag ? { close(h) } | { abort(h) }
  0
}
`); err != nil {
		t.Fatalf("closing on every path satisfies the obligation: %v", err)
	}
	// An inner scope's fresh handle is checked when that scope ends.
	expectCode(t, "inner-scope", checkObligations(t, "inner-scope", `
f: (flag: Bool): u32 {
  flag ? {
    h: Handle = open(u32(1))
    inspect(h)
  } | { }
  0
}
`), typechecker.CodeResourceUnclosed)
}

func TestObligationTransferByReturn(t *testing.T) {
	// Returning the handle — bare, through a variant, or inside a record —
	// passes custody to the caller.
	for name, body := range map[string]string{
		"bare":    "f: (): Handle {\n  h: Handle = open(u32(1))\n  inspect(h)\n  h\n}",
		"variant": "f: (): Option[Handle] {\n  h: Handle = open(u32(1))\n  .Some(h)\n}",
		"record":  "f: (): Holder {\n  h: Handle = open(u32(1))\n  box: Holder = Holder { h: h }\n  box\n}",
		"call":    "f: (): Handle = open(u32(1))",
	} {
		t.Run(name, func(t *testing.T) {
			if err := checkObligations(t, "return", "\n"+body+"\n"); err != nil {
				t.Fatalf("a returned handle transfers its custody: %v", err)
			}
		})
	}
}

func TestObligationTransferByConsumptionAndAlias(t *testing.T) {
	// Handing the handle to a consuming operation, or to a surviving outer
	// name, moves the obligation with the custody; no double cleanup exists
	// because the consumed name cannot be closed again.
	if err := checkObligations(t, "renew", `
f: (): u32 {
  h: Handle = open(u32(1))
  next: Handle = renew(h)
  close(next)
  0
}
`); err != nil {
		t.Fatalf("consumption transfers custody: %v", err)
	}
	// A single-arm match keeps one path, so the outer name's provenance
	// survives the join: custody moves from the inner fresh handle to the
	// outer binding, which then owes the close.
	if err := checkObligations(t, "outer-alias", `
Tag: type = | Only
f: (t: Tag): u32 {
  keep: Handle = open(u32(0))
  close(keep)
  t ? | .Only => {
    h: Handle = open(u32(1))
    keep = h
  }
  close(keep)
  0
}
`); err != nil {
		t.Fatalf("an outer alias keeps custody alive: %v", err)
	}
	expectCode(t, "outer-alias-unclosed", checkObligations(t, "outer-alias-unclosed", `
Tag: type = | Only
f: (t: Tag): u32 {
  keep: Handle = open(u32(0))
  close(keep)
  t ? | .Only => {
    h: Handle = open(u32(1))
    keep = h
  }
  0
}
`), typechecker.CodeResourceUnclosed)
	expectCode(t, "double", checkObligations(t, "double", `
f: (): u32 {
  h: Handle = open(u32(1))
  next: Handle = renew(h)
  close(h)
  close(next)
  0
}
`), typechecker.CodeResourceUsedAfterConsume)
}

func TestObligationMovedFieldNotReclosed(t *testing.T) {
	// A record field holding a fresh handle owes the terminal state; once
	// the field is moved out the record owes nothing for it.
	expectCode(t, "field-unclosed", checkObligations(t, "field-unclosed", `
f: (): u32 {
  box: Holder = Holder { h: open(u32(1)) }
  box.h.id
}
`), typechecker.CodeResourceUnclosed)
	if err := checkObligations(t, "field-moved", `
f: (): u32 {
  box: Holder = Holder { h: open(u32(1)) }
  close(box.h)
  0
}
`); err != nil {
		t.Fatalf("closing through the path discharges the field's obligation: %v", err)
	}
}

func TestObligationParameters(t *testing.T) {
	// sink consumes without itself being a closer (its transition stays
	// in Open), so the body owes the terminal state.
	consumed := typechecker.ResourceTransitionDeclaration{Name: "sink", Callable: "sink", From: "Open", To: "Open",
		Parameters: []typechecker.ResourceParameterDeclaration{{Index: 0, Mode: typechecker.ResourceParameterConsumed}}}
	borrowed := typechecker.ResourceTransitionDeclaration{Name: "sink", Callable: "sink", From: "Open", To: "Open",
		Parameters: []typechecker.ResourceParameterDeclaration{{Index: 0, Mode: typechecker.ResourceParameterBorrowed}}}
	// A consumed parameter took custody: the callee owes the terminal state.
	expectCode(t, "consumed-unclosed", checkObligations(t, "consumed-unclosed", `
sink: (h: Handle): u32 {
  inspect(h)
  0
}
`, consumed), typechecker.CodeResourceUnclosed)
	if err := checkObligations(t, "consumed-closed", `
sink: (h: Handle): u32 {
  close(h)
  0
}
`, consumed); err != nil {
		t.Fatalf("a consumed parameter closed in the body satisfies its obligation: %v", err)
	}
	// A closer's own consumed parameter owes nothing more: the transition is
	// the terminal step.
	closer := consumed
	closer.To = "Closed"
	if err := checkObligations(t, "closer", `
sink: (h: Handle): u32 {
  inspect(h)
  0
}
`, closer); err != nil {
		t.Fatalf("a closer's consumed parameter is discharged by the transition itself: %v", err)
	}
	// A borrowed parameter owes nothing: the caller keeps custody.
	if err := checkObligations(t, "borrowed", `
sink: (h: Handle): u32 {
  inspect(h)
  0
}
`, borrowed); err != nil {
		t.Fatalf("a borrowed parameter carries no obligation: %v", err)
	}
}

func TestObligationRebindingLosesCustody(t *testing.T) {
	expectCode(t, "rebind", checkObligations(t, "rebind", `
f: (): u32 {
  h: Handle = open(u32(1))
  h = open(u32(2))
  close(h)
  0
}
`), typechecker.CodeResourceUnclosed)
}

func TestObligationOnlyWhenDeclared(t *testing.T) {
	// Without terminal states the protocol lets values drop in any state.
	_, err := New().
		WithSource("droppable.oak", obligationBase+`
f: (): u32 {
  h: Handle = open(u32(1))
  inspect(h)
  0
}
`).
		WithResourceProtocols(obligationDeclarations()).
		Check().
		Get()
	if err != nil {
		t.Fatalf("a protocol without terminal states imposes no obligation: %v", err)
	}
	// Terminal states must exist.
	_, err = New().WithSource("bad.oak", obligationBase).WithResourceProtocols(obligationDeclarations("Gone")).Check().Get()
	if err == nil {
		t.Fatal("an unknown terminal state must be rejected")
	}
}

func TestObligationSemIRRoundTrip(t *testing.T) {
	result, err := New().WithSource("terminal.oak", obligationBase).ResourceSemIR(obligationDeclarations("Closed", "Aborted")).Get()
	if err != nil {
		t.Fatalf("resource SemIR stage failed: %v", err)
	}
	if len(result.Module.Protocols) != 1 {
		t.Fatalf("expected one protocol, got %d", len(result.Module.Protocols))
	}
	states := result.Module.Protocols[0].TerminalStates()
	if len(states) != 2 || states[0] != "Closed" || states[1] != "Aborted" {
		t.Fatalf("terminal states should round-trip as a guarantee, got %v", states)
	}
	model, err := typechecker.ResourceModelFromSemIR(result.Module)
	if err != nil {
		t.Fatalf("model from SemIR: %v", err)
	}
	obligation, ok := model.Obligations["Handle"]
	if !ok || len(obligation.Closers) != 2 || obligation.Closers[0] != "abort" || obligation.Closers[1] != "close" {
		t.Fatalf("Handle should owe Closed/Aborted via abort and close, got %#v (present=%v)", obligation, ok)
	}
}
