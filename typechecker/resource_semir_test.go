package typechecker

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/semir"
)

func resourceSemanticModule() semir.Module {
	return semir.Module{
		Definitions: []semir.Definition{
			{
				Name:     "Handle",
				Type:     semir.Type{Kind: semir.TypeRecord},
				Protocol: "HandleLifecycle",
				Authority: semir.Authority{
					Ownership: semir.OwnershipOwned,
					Resource:  semir.ResourceAuthorityLive,
				},
			},
			{
				Name:     "PlainState",
				Type:     semir.Type{Kind: semir.TypeRecord},
				Protocol: "PlainLifecycle",
				Authority: semir.Authority{
					Ownership: semir.OwnershipOwned,
				},
			},
		},
		Protocols: []semir.Protocol{
			{
				Name:    "HandleLifecycle",
				Initial: "Open",
				States:  []semir.State{{Name: "Open"}, {Name: "Closed"}},
				Transitions: []semir.Transition{
					{
						Name:    "close",
						From:    "Open",
						To:      "Closed",
						Effects: []semir.Effect{semir.ResourceConsumeArgument(0)},
					},
					{
						Name: "renew",
						From: "Open",
						To:   "Open",
						Effects: []semir.Effect{
							semir.ResourceConsumeArgument(0),
							semir.ResourceReturnFresh(),
						},
					},
				},
			},
			{
				Name:    "PlainLifecycle",
				Initial: "Idle",
				States:  []semir.State{{Name: "Idle"}},
				Transitions: []semir.Transition{
					{
						Name:    "tick",
						From:    "Idle",
						To:      "Idle",
						Effects: []semir.Effect{{Namespace: "time", Name: "observe"}},
					},
				},
			},
		},
	}
}

func TestResourceModelFromSemIRDerivesTypesAndOperations(t *testing.T) {
	model, err := ResourceModelFromSemIR(resourceSemanticModule())
	if err != nil {
		t.Fatalf("resource model derivation failed: %v", err)
	}
	if !model.ResourceTypes["Handle"] {
		t.Fatal("resource-bearing semantic definition should become a resource type")
	}
	if model.ResourceTypes["PlainState"] {
		t.Fatal("protocol membership alone must not invent resource authority")
	}
	closeOp, ok := model.Operations["close"]
	if !ok || len(closeOp.Consumes) != 1 || closeOp.Consumes[0] != 0 || closeOp.ReturnsFresh {
		t.Fatalf("unexpected close resource operation: %#v", closeOp)
	}
	renewOp, ok := model.Operations["renew"]
	if !ok || len(renewOp.Consumes) != 1 || renewOp.Consumes[0] != 0 || !renewOp.ReturnsFresh {
		t.Fatalf("unexpected renew resource operation: %#v", renewOp)
	}
	if _, ok := model.Operations["tick"]; ok {
		t.Fatal("non-resource protocol effects must not become resource operations")
	}
}

func TestCheckProgramWithSemIRAutomaticallyRejectsUseAfterConsume(t *testing.T) {
	input := `
Handle: type = struct { id: u32 }
close: (h: Handle): () = {}
f: (h: Handle): u32 {
  close(h)
  h.id
}`
	tc := setupTypeChecker(input)
	program := parseProgram(input)
	if err := tc.CheckProgramWithSemIR(program, resourceSemanticModule()); err != nil {
		t.Fatalf("semantic resource checking failed: %v", err)
	}

	got := resourceDiagnostics(tc)
	if len(got) != 1 || !strings.Contains(got[0], "cannot be used after") {
		t.Fatalf("expected automatic OAK-B0111, got %v (all errors: %v)", got, tc.Errors())
	}
}

func TestCheckProgramWithSemIRDerivesFreshReturnAuthority(t *testing.T) {
	input := `
Handle: type = struct { id: u32 }
renew: (h: Handle): Handle = h
f: (h: Handle): u32 {
  next: Handle = renew(h)
  next.id
}`
	tc := setupTypeChecker(input)
	program := parseProgram(input)
	if err := tc.CheckProgramWithSemIR(program, resourceSemanticModule()); err != nil {
		t.Fatalf("semantic resource checking failed: %v", err)
	}
	if got := resourceDiagnostics(tc); len(got) != 0 {
		t.Fatalf("fresh returned authority should be usable: %v", got)
	}
}

func TestResourceModelFromSemIRRejectsConflictingCallableSemantics(t *testing.T) {
	module := semir.Module{
		Protocols: []semir.Protocol{
			{
				Name:    "Left",
				Initial: "S",
				States:  []semir.State{{Name: "S"}},
				Transitions: []semir.Transition{{
					Name:    "close",
					From:    "S",
					To:      "S",
					Effects: []semir.Effect{semir.ResourceConsumeArgument(0)},
				}},
			},
			{
				Name:    "Right",
				Initial: "S",
				States:  []semir.State{{Name: "S"}},
				Transitions: []semir.Transition{{
					Name:    "close",
					From:    "S",
					To:      "S",
					Effects: []semir.Effect{semir.ResourceConsumeArgument(1)},
				}},
			},
		},
	}

	_, err := ResourceModelFromSemIR(module)
	if err == nil || !strings.Contains(err.Error(), "conflicting semantics") {
		t.Fatalf("expected conflicting callable semantics rejection, got %v", err)
	}
}

func TestResourceModelFromSemIRRejectsMalformedResourceEffect(t *testing.T) {
	module := resourceSemanticModule()
	module.Protocols[0].Transitions[0].Effects = []semir.Effect{{
		Namespace:  semir.ResourceEffectNamespace,
		Name:       semir.ResourceEffectConsume,
		Parameters: []string{"arg:bad"},
	}}

	_, err := ResourceModelFromSemIR(module)
	if err == nil || !strings.Contains(err.Error(), "invalid argument index") {
		t.Fatalf("expected malformed semantic resource effect rejection, got %v", err)
	}
}
