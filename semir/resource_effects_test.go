package semir

import (
	"strings"
	"testing"
)

func TestResourceTransitionSemanticsDecodesStructuredEffects(t *testing.T) {
	transition := Transition{
		Name: "renew",
		Effects: []Effect{
			ResourceConsumeArgument(2),
			{Namespace: "memory", Name: "write"},
			ResourceConsumeReceiver(),
			ResourceConsumeArgument(0),
			ResourceReturnFresh(),
		},
	}

	semantics, present, err := transition.ResourceSemantics()
	if err != nil {
		t.Fatalf("resource semantics rejected: %v", err)
	}
	if !present {
		t.Fatal("expected resource semantics to be present")
	}
	if len(semantics.Consumes) != 2 || semantics.Consumes[0] != 0 || semantics.Consumes[1] != 2 {
		t.Fatalf("expected sorted consumed arguments [0 2], got %v", semantics.Consumes)
	}
	if !semantics.ConsumesReceiver {
		t.Fatal("expected receiver-consumption semantic fact")
	}
	if !semantics.ReturnsFresh {
		t.Fatal("expected fresh-return semantic fact")
	}
}

func TestResourceTransitionSemanticsIgnoresUnrelatedEffects(t *testing.T) {
	transition := Transition{Effects: []Effect{{Namespace: "memory", Name: "allocate"}}}
	semantics, present, err := transition.ResourceSemantics()
	if err != nil {
		t.Fatalf("unrelated effect rejected: %v", err)
	}
	if present || len(semantics.Consumes) != 0 || semantics.ConsumesReceiver || semantics.ReturnsFresh {
		t.Fatalf("unrelated effects must not invent resource semantics: %#v", semantics)
	}
}

func TestResourceTransitionSemanticsRejectsMalformedConsume(t *testing.T) {
	transition := Transition{
		Name: "close",
		Effects: []Effect{{
			Namespace:  ResourceEffectNamespace,
			Name:       ResourceEffectConsume,
			Parameters: []string{"arg:not-a-number"},
		}},
	}

	_, present, err := transition.ResourceSemantics()
	if !present || err == nil || !strings.Contains(err.Error(), "invalid argument index") {
		t.Fatalf("expected malformed consume rejection, got present=%v err=%v", present, err)
	}
}

func TestResourceTransitionSemanticsRejectsDuplicateReceiverConsume(t *testing.T) {
	transition := Transition{
		Name: "close",
		Effects: []Effect{
			ResourceConsumeReceiver(),
			ResourceConsumeReceiver(),
		},
	}

	_, present, err := transition.ResourceSemantics()
	if !present || err == nil || !strings.Contains(err.Error(), "duplicates receiver") {
		t.Fatalf("expected duplicate receiver consume rejection, got present=%v err=%v", present, err)
	}
}

func TestValidateResourceSemanticsRequiresResolvedCallable(t *testing.T) {
	module := Module{
		Protocols: []Protocol{{
			Name:    "HandleLifecycle",
			Initial: "Open",
			States:  []State{{Name: "Open"}, {Name: "Closed"}},
			Transitions: []Transition{{
				Name:    "CloseTransition",
				From:    "Open",
				To:      "Closed",
				Effects: []Effect{ResourceConsumeArgument(0)},
			}},
		}},
	}

	err := module.ValidateResourceSemantics()
	if err == nil || !strings.Contains(err.Error(), "no resolved callable") {
		t.Fatalf("expected resource transition callable requirement, got %v", err)
	}
}

func TestValidateResourceSemanticsRejectsReceiverConsumeOnFreeCallable(t *testing.T) {
	module := Module{
		Definitions: []Definition{{
			Name:      "Handle",
			Authority: Authority{Resource: ResourceAuthorityLive},
		}},
		Protocols: []Protocol{{
			Name:    "HandleLifecycle",
			Initial: "Open",
			States:  []State{{Name: "Open"}},
			Transitions: []Transition{{
				Name:     "CloseTransition",
				Callable: "close",
				From:     "Open",
				To:       "Open",
				Effects:  []Effect{ResourceConsumeReceiver()},
			}},
		}},
	}

	err := module.ValidateResourceSemantics()
	if err == nil || !strings.Contains(err.Error(), "no receiver identity") {
		t.Fatalf("expected free-callable receiver rejection, got %v", err)
	}
}

func TestValidateResourceSemanticsRequiresResourceBearingReceiverDefinition(t *testing.T) {
	module := Module{
		Definitions: []Definition{{Name: "Handle"}},
		Protocols: []Protocol{{
			Name:    "HandleLifecycle",
			Initial: "Open",
			States:  []State{{Name: "Open"}},
			Transitions: []Transition{{
				Name:     "CloseTransition",
				Callable: "Handle::close",
				From:     "Open",
				To:       "Open",
				Effects:  []Effect{ResourceConsumeReceiver()},
			}},
		}},
	}

	err := module.ValidateResourceSemantics()
	if err == nil || !strings.Contains(err.Error(), "without a resource-bearing definition") {
		t.Fatalf("expected non-resource receiver definition rejection, got %v", err)
	}
}

func TestValidateResourceSemanticsQualifiesProtocolAndTransition(t *testing.T) {
	module := Module{
		Protocols: []Protocol{{
			Name:    "HandleLifecycle",
			Initial: "Open",
			States:  []State{{Name: "Open"}, {Name: "Closed"}},
			Transitions: []Transition{{
				Name:     "CloseTransition",
				Callable: "close",
				From:     "Open",
				To:       "Closed",
				Effects: []Effect{{
					Namespace: ResourceEffectNamespace,
					Name:      "typo",
				}},
			}},
		}},
	}

	err := module.ValidateResourceSemantics()
	if err == nil || !strings.Contains(err.Error(), `protocol "HandleLifecycle" transition "CloseTransition"`) {
		t.Fatalf("expected qualified resource semantic error, got %v", err)
	}
}
