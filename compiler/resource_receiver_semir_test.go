package compiler

import (
	"testing"

	"github.com/SCKelemen/oak/typechecker"
)

func TestEmitResourceSemIRPreservesReceiverConsumption(t *testing.T) {
	resources := typechecker.ResolvedResourceProgram{
		Types: []typechecker.ResolvedResourceType{{
			Name:     "Handle",
			Protocol: "HandleLifecycle",
		}},
		Protocols: []typechecker.ResolvedResourceProtocol{{
			Name:    "HandleLifecycle",
			States:  []string{"Open", "Closed"},
			Initial: "Open",
			Transitions: []typechecker.ResolvedResourceTransition{{
				Name:             "close-method-transition",
				Callable:         "Handle::close",
				From:             "Open",
				To:               "Closed",
				ConsumesReceiver: true,
			}},
		}},
	}

	module, err := emitResourceSemIR(resources)
	if err != nil {
		t.Fatalf("resource SemIR emission failed: %v", err)
	}
	if len(module.Protocols) != 1 || len(module.Protocols[0].Transitions) != 1 {
		t.Fatalf("unexpected emitted resource protocols: %#v", module.Protocols)
	}
	transition := module.Protocols[0].Transitions[0]
	semantics, present, err := transition.ResourceSemantics()
	if err != nil || !present {
		t.Fatalf("receiver resource effects did not decode: present=%v err=%v", present, err)
	}
	if !semantics.ConsumesReceiver || len(semantics.Consumes) != 0 || semantics.ReturnsFresh {
		t.Fatalf("unexpected emitted receiver semantics: %#v", semantics)
	}
}

func TestEmitResourceSemIRKeepsReceiverAndArgumentsDistinct(t *testing.T) {
	resources := typechecker.ResolvedResourceProgram{
		Types: []typechecker.ResolvedResourceType{{
			Name:     "Handle",
			Protocol: "HandleLifecycle",
		}},
		Protocols: []typechecker.ResolvedResourceProtocol{{
			Name:    "HandleLifecycle",
			States:  []string{"Open"},
			Initial: "Open",
			Transitions: []typechecker.ResolvedResourceTransition{{
				Name:             "transfer-transition",
				Callable:         "Handle::transfer",
				From:             "Open",
				To:               "Open",
				Consumes:         []int{0},
				ConsumesReceiver: true,
			}},
		}},
	}

	module, err := emitResourceSemIR(resources)
	if err != nil {
		t.Fatalf("resource SemIR emission failed: %v", err)
	}
	semantics, present, err := module.Protocols[0].Transitions[0].ResourceSemantics()
	if err != nil || !present {
		t.Fatalf("mixed receiver/argument resource effects did not decode: present=%v err=%v", present, err)
	}
	if !semantics.ConsumesReceiver || len(semantics.Consumes) != 1 || semantics.Consumes[0] != 0 {
		t.Fatalf("receiver was conflated with explicit argument zero: %#v", semantics)
	}
}
