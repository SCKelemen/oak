package semir

import (
	"strings"
	"testing"
)

func TestIrqDefinitionsExerciseFiveAxes(t *testing.T) {
	module := Module{
		Definitions: []Definition{
			{
				Name: "IrqId",
				Type: Type{
					Kind: TypeScalar,
					Parameters: []TypeParameter{
						{Name: "N", Phantom: true},
					},
				},
				Representation: Representation{
					Kind:      RepresentationMachineInt,
					Bits:      16,
					Size:      2,
					Alignment: 2,
				},
				Propositions: []Proposition{
					{
						Name:   "in_range",
						Status: ProofSpecified,
						Expr:   Apply(OpLt, Ref("value"), Ref("N")),
					},
				},
			},
			{
				Name: "Irq",
				Type: Type{
					Kind: TypeRecord,
					Fields: []Field{
						{Name: "enabled", Type: "bool"},
						{Name: "priority", Type: "u8"},
						{Name: "latched_pending", Type: "bool"},
						{Name: "level_asserted", Type: "bool"},
						{Name: "active", Type: "bool"},
					},
				},
				Representation: Representation{
					Kind:      RepresentationRecord,
					Alignment: 1,
				},
				Authority: Authority{
					Ownership: OwnershipOwned,
					RequiredEffects: []Effect{
						{Namespace: "irq", Name: "mutate_local"},
					},
					ForbiddenEffects: []Effect{
						{Namespace: "memory", Name: "allocate"},
						{Namespace: "thread", Name: "block"},
					},
				},
				Protocol: "VirtualIrq",
			},
		},
		Protocols: []Protocol{
			{
				Name:    "VirtualIrq",
				Initial: "Idle",
				States: []State{
					{Name: "Idle"},
					{Name: "Pending"},
					{Name: "Active"},
				},
				Transitions: []Transition{
					{Name: "inject", From: "Idle", To: "Pending"},
					{Name: "acknowledge", From: "Pending", To: "Active"},
					{Name: "eoi", From: "Active", To: "Idle"},
				},
				Guarantees: []TemporalProperty{
					{
						Name: "active_was_pending",
						Formula: Temporal(
							TemporalAlways,
							Temporal(TemporalImplies, Atom("active"), Atom("was_pending")),
						),
					},
				},
			},
		},
	}

	if err := module.Validate(); err != nil {
		t.Fatalf("valid semantic module rejected: %v", err)
	}
}

func TestAuthorityRejectsRequiredForbiddenConflict(t *testing.T) {
	authority := Authority{
		RequiredEffects:  []Effect{{Namespace: "memory", Name: "allocate"}},
		ForbiddenEffects: []Effect{{Namespace: "memory", Name: "allocate"}},
	}

	err := authority.Validate()
	if err == nil || !strings.Contains(err.Error(), "both required and forbidden") {
		t.Fatalf("expected required/forbidden conflict, got %v", err)
	}
}

func TestProtocolRejectsUnknownTransitionState(t *testing.T) {
	protocol := Protocol{
		Name:    "Broken",
		Initial: "Idle",
		States:  []State{{Name: "Idle"}},
		Transitions: []Transition{
			{Name: "wake", From: "Idle", To: "Running"},
		},
	}

	err := protocol.Validate()
	if err == nil || !strings.Contains(err.Error(), "unknown target state") {
		t.Fatalf("expected unknown-state error, got %v", err)
	}
}

func TestExpressionValidationRejectsWrongArity(t *testing.T) {
	err := Apply(OpLt, Ref("value")).Validate()
	if err == nil || !strings.Contains(err.Error(), "expects 2 arguments") {
		t.Fatalf("expected arity error, got %v", err)
	}
}

func TestDefinitionRejectsNonPowerOfTwoAlignment(t *testing.T) {
	definition := Definition{
		Name: "BadLayout",
		Type: Type{Kind: TypeRecord},
		Representation: Representation{
			Kind:      RepresentationRecord,
			Alignment: 3,
		},
	}

	err := definition.Validate()
	if err == nil || !strings.Contains(err.Error(), "not a power of two") {
		t.Fatalf("expected alignment error, got %v", err)
	}
}
