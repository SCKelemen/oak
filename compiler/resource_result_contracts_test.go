package compiler

import (
	"errors"
	"strings"
	"testing"

	"github.com/SCKelemen/oak/semir"
	"github.com/SCKelemen/oak/typechecker"
)

// Checked result contracts (docs/spec/50-borrowing.md section 9 "Result
// identity", authority roadmap milestone 4 stage (a)): a resource-returning
// operation declares what its result is — fresh authority or an alias of
// one argument — and both sides are held to it. The callee's body must
// produce the declared identity (OAK-B0117); the caller treats an alias
// result as the argument's own authority under a new name.
func resultContractDeclarations() []typechecker.ResourceProtocolDeclaration {
	mode := func(index int, m typechecker.ResourceParameterMode) typechecker.ResourceParameterDeclaration {
		return typechecker.ResourceParameterDeclaration{Index: index, Mode: m}
	}
	return []typechecker.ResourceProtocolDeclaration{{
		Name:          "HandleLifecycle",
		ResourceTypes: []string{"Handle"},
		States:        []string{"Open", "Closed"},
		Initial:       "Open",
		Transitions: []typechecker.ResourceTransitionDeclaration{
			{Name: "open", Callable: "open", From: "Open", To: "Open", ReturnsFresh: true},
			{Name: "inspect", Callable: "inspect", From: "Open", To: "Open", Parameters: []typechecker.ResourceParameterDeclaration{mode(0, typechecker.ResourceParameterBorrowed)}},
			{Name: "close", Callable: "close", From: "Open", To: "Closed", Parameters: []typechecker.ResourceParameterDeclaration{mode(0, typechecker.ResourceParameterConsumed)}},
			{Name: "update_pair", Callable: "update_pair", From: "Open", To: "Open", Parameters: []typechecker.ResourceParameterDeclaration{
				mode(0, typechecker.ResourceParameterBorrowedMut), mode(1, typechecker.ResourceParameterBorrowed)}},
			// same returns its consumed argument as the same authority.
			{Name: "same", Callable: "same", From: "Open", To: "Open", ReturnsAlias: true, AliasesArgument: 0,
				Parameters: []typechecker.ResourceParameterDeclaration{mode(0, typechecker.ResourceParameterConsumed)}},
			// pick returns an alias of its second, borrowed argument.
			{Name: "pick", Callable: "pick", From: "Open", To: "Open", ReturnsAlias: true, AliasesArgument: 1,
				Parameters: []typechecker.ResourceParameterDeclaration{mode(0, typechecker.ResourceParameterBorrowed), mode(1, typechecker.ResourceParameterBorrowed)}},
			// renew claims fresh authority.
			{Name: "renew", Callable: "renew", From: "Open", To: "Open", ReturnsFresh: true,
				Parameters: []typechecker.ResourceParameterDeclaration{mode(0, typechecker.ResourceParameterBorrowed)}},
		},
	}}
}

const resultContractBase = `
Handle: type = struct { id: u32 }
open: (id: u32): Handle = Handle { id: id }
inspect: (h: Handle): () = {}
close: (h: Handle): () = {}
update_pair: (left: Handle, right: Handle): () = {}
`

func checkResultContracts(t *testing.T, name, body string) error {
	t.Helper()
	_, err := New().
		WithSource(name+".oak", resultContractBase+body).
		WithResourceProtocols(resultContractDeclarations()).
		Check().
		Get()
	return err
}

func resultContractCodes(err error) []string {
	var diagnosticErr *DiagnosticError
	if !errors.As(err, &diagnosticErr) {
		return nil
	}
	var codes []string
	for _, d := range diagnosticErr.Diagnostics {
		if d != nil {
			codes = append(codes, d.Code)
		}
	}
	return codes
}

func expectResultContractCode(t *testing.T, err error, code, wantText string) {
	t.Helper()
	if err == nil {
		t.Fatalf("expected %s, got no error", code)
	}
	codes := resultContractCodes(err)
	found := false
	for _, c := range codes {
		if c == code {
			found = true
		}
	}
	if !found {
		t.Fatalf("expected %s, got %v: %v", code, codes, err)
	}
	if wantText != "" && !strings.Contains(err.Error(), wantText) {
		t.Fatalf("diagnostic should mention %q: %v", wantText, err)
	}
}

// Honest bodies pass: an alias body returns the declared parameter, directly
// or through a local alias or a nested alias-returning call; a fresh body
// builds a new value.
func TestResultContractHonestBodies(t *testing.T) {
	body := `
same: (h: Handle): Handle = h
pick: (a: Handle, b: Handle): Handle {
  chosen: Handle = b
  chosen
}
renew: (h: Handle): Handle = Handle { id: h.id }
f: (h: Handle): u32 {
  g: Handle = same(h)
  g.id
}
`
	if err := checkResultContracts(t, "honest", body); err != nil {
		t.Fatalf("honest result contracts must be accepted: %v", err)
	}
}

// A fresh-return body may not hand back a parameter or its alias: renaming
// does not manufacture freshness.
func TestResultContractFreshBodyReturningParameterRejected(t *testing.T) {
	body := `
same: (h: Handle): Handle = h
pick: (a: Handle, b: Handle): Handle = b
renew: (h: Handle): Handle {
  again: Handle = h
  again
}
`
	err := checkResultContracts(t, "freshlie", body)
	expectResultContractCode(t, err, typechecker.CodeResourceResultContract, "declared to return fresh authority")
}

// An alias body must return the declared parameter's authority on every
// path; a different parameter or a fresh value is rejected.
func TestResultContractAliasBodyReturningOtherRejected(t *testing.T) {
	for name, pick := range map[string]string{
		"other parameter": "pick: (a: Handle, b: Handle): Handle = a",
		"fresh value":     "pick: (a: Handle, b: Handle): Handle = open(b.id)",
		"one branch":      "pick: (a: Handle, b: Handle): Handle {\n  first: Bool = a.id == u32(0)\n  first ? { a } | { b }\n}",
	} {
		t.Run(name, func(t *testing.T) {
			body := "\nsame: (h: Handle): Handle = h\nrenew: (h: Handle): Handle = Handle { id: h.id }\n" + pick + "\n"
			err := checkResultContracts(t, "aliaslie", body)
			expectResultContractCode(t, err, typechecker.CodeResourceResultContract, "declared to return an alias of \"b\"")
		})
	}
}

// At the call site an alias result is the argument's authority: exclusive
// use of the result against the argument conflicts, and consuming the
// result consumes the argument.
func TestResultContractAliasResultSharesAuthorityAtCallSite(t *testing.T) {
	honest := `
same: (h: Handle): Handle = h
pick: (a: Handle, b: Handle): Handle = b
renew: (h: Handle): Handle = Handle { id: h.id }
`
	t.Run("exclusive use conflicts", func(t *testing.T) {
		body := honest + `
f: (x: Handle, y: Handle): u32 {
  z: Handle = pick(x, y)
  update_pair(z, y)
  x.id
}
`
		err := checkResultContracts(t, "aliasconflict", body)
		expectResultContractCode(t, err, typechecker.CodeResourceCallAliasConflict, "")
	})
	t.Run("consuming the result consumes the argument", func(t *testing.T) {
		body := honest + `
f: (x: Handle, y: Handle): u32 {
  z: Handle = pick(x, y)
  close(z)
  y.id
}
`
		err := checkResultContracts(t, "aliasconsume", body)
		expectResultContractCode(t, err, typechecker.CodeResourceUsedAfterConsume, "")
	})
	t.Run("nested alias result as argument", func(t *testing.T) {
		body := honest + `
f: (x: Handle, y: Handle): u32 {
  update_pair(pick(x, y), y)
  x.id
}
`
		err := checkResultContracts(t, "aliasnested", body)
		expectResultContractCode(t, err, typechecker.CodeResourceCallAliasConflict, "")
	})
	t.Run("alias of a consumed argument is the only surviving name", func(t *testing.T) {
		body := honest + `
f: (h: Handle): u32 {
  g: Handle = same(h)
  inspect(g)
  h.id
}
`
		err := checkResultContracts(t, "aliastransfer", body)
		expectResultContractCode(t, err, typechecker.CodeResourceUsedAfterConsume, "")
	})
	t.Run("distinct arguments stay distinct", func(t *testing.T) {
		body := honest + `
f: (x: Handle, y: Handle): u32 {
  z: Handle = pick(x, y)
  update_pair(z, x)
  x.id
}
`
		if err := checkResultContracts(t, "aliasdistinct", body); err != nil {
			t.Fatalf("an alias of y is distinct from x: %v", err)
		}
	})
}

// A borrowed parameter may be returned when the contract declares the
// result an alias of it: the caller keeps custody and gains a second name.
// Without the declaration the same return is retention (OAK-B0114).
func TestResultContractAliasExemptsRetention(t *testing.T) {
	declarations := resultContractDeclarations()
	declarations[0].Transitions = append(declarations[0].Transitions,
		typechecker.ResourceTransitionDeclaration{Name: "peek", Callable: "peek", From: "Open", To: "Open", ReturnsAlias: true, AliasesArgument: 0,
			Parameters: []typechecker.ResourceParameterDeclaration{{Index: 0, Mode: typechecker.ResourceParameterBorrowed}}},
		typechecker.ResourceTransitionDeclaration{Name: "keep", Callable: "keep", From: "Open", To: "Open",
			Parameters: []typechecker.ResourceParameterDeclaration{{Index: 0, Mode: typechecker.ResourceParameterBorrowed}}},
	)
	source := resultContractBase + `
same: (h: Handle): Handle = h
pick: (a: Handle, b: Handle): Handle = b
renew: (h: Handle): Handle = Handle { id: h.id }
peek: (h: Handle): Handle = h
keep: (h: Handle): Handle = h
`
	_, err := New().WithSource("retention.oak", source).WithResourceProtocols(declarations).Check().Get()
	codes := resultContractCodes(err)
	if len(codes) != 1 || codes[0] != typechecker.CodeResourceParameterForwarded {
		t.Fatalf("keep retains a borrowed parameter and peek does not; got %v: %v", codes, err)
	}
	// keep is declared on line 12 of the assembled source; peek on line 11.
	if !strings.Contains(err.Error(), "]: 12:") {
		t.Fatalf("diagnostic should point at keep's return: %v", err)
	}
}

// Declarations are validated: a result cannot be both fresh and an alias,
// the aliased argument must exist and be resource-typed, and the return
// type must be a resource.
func TestResultContractDeclarationValidation(t *testing.T) {
	source := resultContractBase + `
same: (h: Handle): Handle = h
pick: (a: Handle, b: Handle): Handle = b
renew: (h: Handle): Handle = Handle { id: h.id }
count: (h: Handle): u32 = h.id
`
	for name, mutate := range map[string]func(*typechecker.ResourceTransitionDeclaration){
		"fresh and alias":       func(d *typechecker.ResourceTransitionDeclaration) { d.ReturnsFresh = true },
		"argument out of range": func(d *typechecker.ResourceTransitionDeclaration) { d.AliasesArgument = 3 },
		"non-resource return":   func(d *typechecker.ResourceTransitionDeclaration) { d.Callable = "count"; d.Name = "count" },
	} {
		t.Run(name, func(t *testing.T) {
			declarations := resultContractDeclarations()
			for i := range declarations[0].Transitions {
				if declarations[0].Transitions[i].Name == "same" {
					mutate(&declarations[0].Transitions[i])
				}
			}
			_, err := New().WithSource("declare.oak", source).WithResourceProtocols(declarations).Check().Get()
			if err == nil {
				t.Fatal("invalid result declaration must be rejected")
			}
		})
	}
}

// The alias fact round-trips through SemIR as resource.return-alias arg:N.
func TestResultContractSemIRRoundTrip(t *testing.T) {
	source := resultContractBase + `
same: (h: Handle): Handle = h
pick: (a: Handle, b: Handle): Handle = b
renew: (h: Handle): Handle = Handle { id: h.id }
`
	result, err := New().WithSource("alias.oak", source).ResourceSemIR(resultContractDeclarations()).Get()
	if err != nil {
		t.Fatalf("resource SemIR stage failed: %v", err)
	}
	var found bool
	for _, protocol := range result.Module.Protocols {
		for _, transition := range protocol.Transitions {
			if transition.Callable != "pick" {
				continue
			}
			semantics, present, err := transition.ResourceSemantics()
			if err != nil || !present {
				t.Fatalf("pick semantics: present=%v err=%v", present, err)
			}
			if !semantics.ReturnsAlias || semantics.AliasesArgument != 1 || semantics.ReturnsFresh {
				t.Fatalf("pick should alias argument 1, got %#v", semantics)
			}
			for _, effect := range transition.Effects {
				if effect.Name == semir.ResourceEffectReturnAlias && len(effect.Parameters) == 1 && effect.Parameters[0] == "arg:1" {
					found = true
				}
			}
		}
	}
	if !found {
		t.Fatalf("pick transition lacks resource.return-alias arg:1 in emitted SemIR: %#v", result.Module.Protocols)
	}
}
