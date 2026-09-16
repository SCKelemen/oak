package semir

import (
	"strings"
	"testing"
)

func sealedSemanticModule() Module {
	return Module{
		Definitions: []Definition{{
			Name:     "Handle",
			Type:     Type{Kind: TypeOpaque},
			Protocol: "HandleLifecycle",
			Authority: Authority{
				Resource: ResourceAuthorityLive,
			},
		}},
		Protocols: []Protocol{{
			Name:                     "HandleLifecycle",
			States:                   []State{{Name: "Fresh"}, {Name: "Published"}},
			Initial:                  "Fresh",
			SealedInitialConstructor: "mint",
			TypestateArity:           1,
			Transitions: []Transition{{
				Name: "mint-transition", Callable: "mint", From: "Fresh", To: "Fresh",
				Effects: []Effect{ResourceReturnFresh()},
			}},
		}},
	}
}

func TestValidateResourceSemanticsAcceptsSealedInitialConstructor(t *testing.T) {
	if err := sealedSemanticModule().ValidateResourceSemantics(); err != nil {
		t.Fatalf("valid sealed constructor rejected: %v", err)
	}
}

func TestValidateResourceSemanticsRejectsMalformedSealedInitialConstructor(t *testing.T) {
	for _, test := range []struct {
		name string
		edit func(*Module)
		want string
	}{
		{
			name: "zero typestate arity",
			edit: func(module *Module) { module.Protocols[0].TypestateArity = 0 },
			want: "not typestate-indexed",
		},
		{
			name: "missing transition",
			edit: func(module *Module) { module.Protocols[0].SealedInitialConstructor = "missing" },
			want: "alternate fresh or trusted mint route",
		},
		{
			name: "wrong edge",
			edit: func(module *Module) { module.Protocols[0].Transitions[0].To = "Published" },
			want: "must be an Fresh -> Fresh transition",
		},
		{
			name: "not fresh",
			edit: func(module *Module) { module.Protocols[0].Transitions[0].Effects = nil },
			want: "must return fresh authority",
		},
		{
			name: "trusted constructor",
			edit: func(module *Module) {
				module.Protocols[0].Transitions[0].Effects = append(module.Protocols[0].Transitions[0].Effects, ResourceReturnTrusted())
			},
			want: "cannot use trusted result identity",
		},
		{
			name: "alternate fresh",
			edit: func(module *Module) {
				module.Protocols[0].Transitions = append(module.Protocols[0].Transitions, Transition{
					Name: "forge", Callable: "forge", From: "Fresh", To: "Fresh", Effects: []Effect{ResourceReturnFresh()},
				})
			},
			want: "alternate fresh or trusted mint route",
		},
		{
			name: "alternate trusted alias",
			edit: func(module *Module) {
				module.Protocols[0].Transitions = append(module.Protocols[0].Transitions, Transition{
					Name: "forge", Callable: "forge", From: "Fresh", To: "Fresh",
					Effects: []Effect{ResourceReturnAlias(0), ResourceReturnTrusted()},
				})
			},
			want: "alternate fresh or trusted mint route",
		},
		{
			name: "multiple governed resources",
			edit: func(module *Module) {
				other := module.Definitions[0]
				other.Name = "Other"
				module.Definitions = append(module.Definitions, other)
			},
			want: "governs 2 resource definitions",
		},
	} {
		t.Run(test.name, func(t *testing.T) {
			module := sealedSemanticModule()
			test.edit(&module)
			err := module.ValidateResourceSemantics()
			if err == nil || !strings.Contains(err.Error(), test.want) {
				t.Fatalf("error = %v, want text %q", err, test.want)
			}
		})
	}
}

func TestValidateResourceSemanticsRejectsConstructorSharedBySealedProtocols(t *testing.T) {
	module := sealedSemanticModule()
	otherDefinition := module.Definitions[0]
	otherDefinition.Name = "Other"
	otherDefinition.Protocol = "OtherLifecycle"
	module.Definitions = append(module.Definitions, otherDefinition)
	otherProtocol := module.Protocols[0]
	otherProtocol.Name = "OtherLifecycle"
	module.Protocols = append(module.Protocols, otherProtocol)

	err := module.ValidateResourceSemantics()
	if err == nil || !strings.Contains(err.Error(), "designated by both protocols") {
		t.Fatalf("error = %v, want shared constructor rejection", err)
	}
}
