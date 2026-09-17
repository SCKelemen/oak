package typechecker

import (
	"strings"
	"testing"
)

const sealedResolutionProgram = `
Fresh: type = struct { fresh_: u8 }
Published: type = struct { published_: u8 }
Archived: type = struct { archived_: u8 }
Handle[S]: type = struct { id: u32 }
Other[S]: type = struct { id: u32 }
Envelope: type = struct { handles: [1]Handle[Fresh] }
Box[T]: type = Full: T | Empty
PublishOutcome: type = Done: Handle[Published] | Refused: Handle[Fresh]
MultiOutcome: type = Done: Handle[Published] | ArchivedDone: Handle[Archived] | Refused: Handle[Fresh]
MixedOutcome: type = Done: Handle[Published] | OtherDone: Other[Fresh]

mint: (): Handle[Fresh] = Handle { id: u32(0) }
mint_published: (): Handle[Published] = Handle { id: u32(0) }
mint_other: (): Other[Fresh] = Other { id: u32(0) }
renew_envelope: (e: Envelope): Envelope = e
renew_box: (b: Box[Box[Handle[Fresh]]]): Box[Box[Handle[Fresh]]] = b
publish: (h: Handle[Fresh]): Handle[Published] = Handle { id: h.id }
publish_from_published: (h: Handle[Published]): Handle[Published] = Handle { id: h.id }
publish_other_argument: (h: Other[Fresh]): Handle[Published] = Handle { id: h.id }
publish_wrong_target: (h: Handle[Fresh]): Handle[Fresh] = Handle { id: h.id }
publish_return_other: (h: Handle[Fresh]): Other[Published] = Other { id: h.id }
guarded_publish: (h: Handle[Fresh]): PublishOutcome = .Refused(h)
multi_publish: (h: Handle[Fresh]): MultiOutcome = .Refused(h)
mixed_publish: (h: Handle[Fresh]): MixedOutcome = .Done(Handle { id: h.id })
`

func sealedHandleDeclarations() []ResourceProtocolDeclaration {
	return []ResourceProtocolDeclaration{{
		Name:                     "HandleLifecycle",
		ResourceTypes:            []string{"Handle"},
		States:                   []string{"Fresh", "Published"},
		Initial:                  "Fresh",
		TypestateArity:           1,
		SealedInitialConstructor: "mint",
		Transitions: []ResourceTransitionDeclaration{{
			Name:         "mint-transition",
			Callable:     "mint",
			From:         "Fresh",
			To:           "Fresh",
			ReturnsFresh: true,
		}},
	}}
}

func TestResolveResourceDeclarationsCarriesSealedInitialConstructor(t *testing.T) {
	tc := checkedResourceProgram(t, sealedResolutionProgram)
	resolved, err := tc.ResolveResourceDeclarations(sealedHandleDeclarations())
	if err != nil {
		t.Fatalf("sealed resource resolution failed: %v", err)
	}
	if len(resolved.Protocols) != 1 || resolved.Protocols[0].SealedInitialConstructor != "mint" {
		t.Fatalf("sealed constructor designation was not retained: %#v", resolved.Protocols)
	}
}

func TestResolveResourceDeclarationsRejectsMalformedSealedConstructor(t *testing.T) {
	tc := checkedResourceProgram(t, sealedResolutionProgram)
	for _, test := range []struct {
		name string
		edit func(*ResourceProtocolDeclaration)
		want string
	}{
		{
			name: "zero typestate arity",
			edit: func(protocol *ResourceProtocolDeclaration) { protocol.TypestateArity = 0 },
			want: "not typestate-indexed",
		},
		{
			name: "multiple resource templates",
			edit: func(protocol *ResourceProtocolDeclaration) {
				protocol.ResourceTypes = append(protocol.ResourceTypes, "Other")
			},
			want: "governs 2 resource types",
		},
		{
			name: "missing transition",
			edit: func(protocol *ResourceProtocolDeclaration) { protocol.SealedInitialConstructor = "missing" },
			want: "alternate fresh or trusted mint route",
		},
		{
			name: "wrong edge",
			edit: func(protocol *ResourceProtocolDeclaration) { protocol.Transitions[0].To = "Published" },
			want: "must be an Fresh -> Fresh transition",
		},
		{
			name: "not fresh",
			edit: func(protocol *ResourceProtocolDeclaration) { protocol.Transitions[0].ReturnsFresh = false },
			want: "must return fresh authority",
		},
		{
			name: "trusted constructor",
			edit: func(protocol *ResourceProtocolDeclaration) { protocol.Transitions[0].Trusted = true },
			want: "cannot use trusted result identity",
		},
		{
			name: "wrong state return",
			edit: func(protocol *ResourceProtocolDeclaration) {
				protocol.SealedInitialConstructor = "mint_published"
				protocol.Transitions[0].Callable = "mint_published"
			},
			want: "must return Handle[Fresh] directly",
		},
		{
			name: "wrong template return",
			edit: func(protocol *ResourceProtocolDeclaration) {
				protocol.SealedInitialConstructor = "mint_other"
				protocol.Transitions[0].Callable = "mint_other"
			},
			want: "must return Handle[Fresh] directly",
		},
	} {
		t.Run(test.name, func(t *testing.T) {
			declarations := sealedHandleDeclarations()
			test.edit(&declarations[0])
			_, err := tc.ResolveResourceDeclarations(declarations)
			if err == nil || !strings.Contains(err.Error(), test.want) {
				t.Fatalf("error = %v, want text %q", err, test.want)
			}
		})
	}
}

func TestResolveResourceDeclarationsRejectsCrossProtocolSealedMintRoutes(t *testing.T) {
	tc := checkedResourceProgram(t, sealedResolutionProgram)
	for _, test := range []struct {
		name         string
		resourceType string
		transition   ResourceTransitionDeclaration
	}{
		{
			name:         "fresh nested fixed-array aggregate",
			resourceType: "Envelope",
			transition: ResourceTransitionDeclaration{
				Name: "renew-envelope", Callable: "renew_envelope", From: "Live", To: "Live", ReturnsFresh: true,
			},
		},
		{
			name:         "trusted alias nested fixed-array aggregate",
			resourceType: "Envelope",
			transition: ResourceTransitionDeclaration{
				Name: "renew-envelope", Callable: "renew_envelope", From: "Live", To: "Live",
				Parameters:   []ResourceParameterDeclaration{{Index: 0, Mode: ResourceParameterBorrowed}},
				ReturnsAlias: true, AliasesArgument: 0, Trusted: true,
			},
		},
		{
			name:         "fresh nested same generic ADT",
			resourceType: "Box",
			transition: ResourceTransitionDeclaration{
				Name: "renew-box", Callable: "renew_box", From: "Live", To: "Live", ReturnsFresh: true,
			},
		},
	} {
		t.Run(test.name, func(t *testing.T) {
			declarations := sealedHandleDeclarations()
			declarations = append(declarations, ResourceProtocolDeclaration{
				Name:          "EnvelopeLifecycle",
				ResourceTypes: []string{test.resourceType},
				States:        []string{"Live"},
				Initial:       "Live",
				Transitions:   []ResourceTransitionDeclaration{test.transition},
			})
			_, err := tc.ResolveResourceDeclarations(declarations)
			if err == nil || !strings.Contains(err.Error(), "alternate fresh or trusted mint route") {
				t.Fatalf("error = %v, want alternate sealed mint rejection", err)
			}
		})
	}
}

func sealedAliasTransition(name, callable, target string) ResourceTransitionDeclaration {
	return ResourceTransitionDeclaration{
		Name: name, Callable: callable, From: "Fresh", To: target,
		Parameters:      []ResourceParameterDeclaration{{Index: 0, Mode: ResourceParameterConsumed}},
		ReturnsAlias:    true,
		AliasesArgument: 0,
	}
}

func unsealedOtherDeclarations() ResourceProtocolDeclaration {
	return ResourceProtocolDeclaration{
		Name:           "OtherLifecycle",
		ResourceTypes:  []string{"Other"},
		States:         []string{"Fresh", "Published"},
		Initial:        "Fresh",
		TypestateArity: 1,
	}
}

func TestResolveResourceDeclarationsValidatesSealedAliasSignatures(t *testing.T) {
	tc := checkedResourceProgram(t, sealedResolutionProgram)
	for _, test := range []struct {
		name        string
		transitions []ResourceTransitionDeclaration
	}{
		{
			name:        "direct target",
			transitions: []ResourceTransitionDeclaration{sealedAliasTransition("publish", "publish", "Published")},
		},
		{
			name:        "guarded target and refused source",
			transitions: []ResourceTransitionDeclaration{sealedAliasTransition("guarded-publish", "guarded_publish", "Published")},
		},
		{
			name: "multiple targets and refused source",
			transitions: []ResourceTransitionDeclaration{
				sealedAliasTransition("multi-publish", "multi_publish", "Published"),
				sealedAliasTransition("multi-archive", "multi_publish", "Archived"),
			},
		},
	} {
		t.Run(test.name, func(t *testing.T) {
			declarations := sealedHandleDeclarations()
			declarations[0].States = append(declarations[0].States, "Archived")
			declarations[0].Transitions = append(declarations[0].Transitions, test.transitions...)
			if _, err := tc.ResolveResourceDeclarations(declarations); err != nil {
				t.Fatalf("valid sealed alias signature rejected: %v", err)
			}
		})
	}
}

func TestResolveResourceDeclarationsRejectsInvalidSealedAliasSignatures(t *testing.T) {
	tc := checkedResourceProgram(t, sealedResolutionProgram)
	for _, test := range []struct {
		name       string
		transition ResourceTransitionDeclaration
		other      *ResourceProtocolDeclaration
		want       string
	}{
		{
			name:       "source state mismatch",
			transition: sealedAliasTransition("publish", "publish_from_published", "Published"),
			want:       "must be exactly Handle[Fresh]",
		},
		{
			name:       "source template mismatch",
			transition: sealedAliasTransition("publish", "publish_other_argument", "Published"),
			other:      ptrResourceProtocol(unsealedOtherDeclarations()),
			want:       "must be exactly Handle[Fresh]",
		},
		{
			name: "aliased source is not consumed",
			transition: func() ResourceTransitionDeclaration {
				transition := sealedAliasTransition("publish", "publish", "Published")
				transition.Parameters[0].Mode = ResourceParameterBorrowed
				return transition
			}(),
			want: "must consume its aliased argument",
		},
		{
			name:       "target state missing",
			transition: sealedAliasTransition("publish", "publish_wrong_target", "Published"),
			want:       "does not contain Handle[Published]",
		},
		{
			name:       "target template mismatch",
			transition: sealedAliasTransition("publish", "publish_return_other", "Published"),
			other:      ptrResourceProtocol(unsealedOtherDeclarations()),
			want:       "does not contain Handle[Published]",
		},
		{
			name:       "undeclared result state",
			transition: sealedAliasTransition("publish", "multi_publish", "Published"),
			want:       "undeclared Handle state \"Archived\"",
		},
		{
			name:       "alternate sealed result template",
			transition: sealedAliasTransition("publish", "mixed_publish", "Published"),
			other: ptrResourceProtocol(ResourceProtocolDeclaration{
				Name: "OtherLifecycle", ResourceTypes: []string{"Other"}, States: []string{"Fresh", "Published"}, Initial: "Fresh",
				TypestateArity: 1, SealedInitialConstructor: "mint_other",
				Transitions: []ResourceTransitionDeclaration{{
					Name: "mint-other", Callable: "mint_other", From: "Fresh", To: "Fresh", ReturnsFresh: true,
				}},
			}),
			want: "alternate sealed template \"Other\"",
		},
	} {
		t.Run(test.name, func(t *testing.T) {
			declarations := sealedHandleDeclarations()
			declarations[0].States = append(declarations[0].States, "Archived")
			declarations[0].Transitions = append(declarations[0].Transitions, test.transition)
			if test.other != nil {
				declarations = append(declarations, *test.other)
			}
			_, err := tc.ResolveResourceDeclarations(declarations)
			if err == nil || !strings.Contains(err.Error(), test.want) {
				t.Fatalf("error = %v, want text %q", err, test.want)
			}
		})
	}
}

func ptrResourceProtocol(protocol ResourceProtocolDeclaration) *ResourceProtocolDeclaration {
	return &protocol
}
