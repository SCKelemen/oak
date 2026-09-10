package compiler

// Protocol declarations (docs/spec/112-protocols.md). `Name: protocol = {
// initial S; t: A -> B; ... }` is one fact — a finite control-state machine —
// projected into ordinary Oak the same way derived declarations are
// (compiler/synth.go): the state and step sum types, the initial-state,
// legality and transition functions checked by every gate, the resource
// protocol facts for `via`-bound transitions, and (compiler/protocol_tla.go)
// a TLA+ module whose actions are the transitions. One declaration, every
// view; the compiler never reconstructs a machine from code.

import (
	"fmt"
	"sort"
	"strings"
	"unicode"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/diagnostic"
	"github.com/SCKelemen/oak/modules"
	"github.com/SCKelemen/oak/typechecker"
)

const (
	// CodeProtocolShape reports a protocol declaration that does not describe
	// a machine: no initial state, an unknown state, a repeated transition, a
	// payload that changes between lines of one step, or a `via` without a
	// resource.
	CodeProtocolShape = "OAK-M0301"
)

// protocolStep is one step name: its payload (shared by every line naming
// it) and its (from, to) pairs in declaration order.
type protocolStep struct {
	name    string
	payload *ast.FunctionParameter
	from    []string
	to      []string
	node    *ast.ProtocolTransition
}

// protocolMachine is the checked shape of one declaration.
type protocolMachine struct {
	decl    *ast.ProtocolDeclaration
	name    string
	states  []string
	initial string
	steps   []*protocolStep
}

// variantName spells a transition name as its step variant: inject -> Inject.
// Transitions are named like functions; variants are named like types, and a
// lowercase `.inject` in argument position would read as a field accessor.
func variantName(transition string) string {
	if transition == "" {
		return transition
	}
	return strings.ToUpper(transition[:1]) + transition[1:]
}

// snakeCase spells CamelCase as snake_case for the generated functions:
// VirtualIrq -> virtual_irq.
func snakeCase(name string) string {
	var out strings.Builder
	for i, r := range name {
		if unicode.IsUpper(r) {
			if i > 0 {
				out.WriteByte('_')
			}
			out.WriteRune(unicode.ToLower(r))
		} else {
			out.WriteRune(r)
		}
	}
	return out.String()
}

// analyzeProtocol checks one declaration and returns its machine.
func analyzeProtocol(decl *ast.ProtocolDeclaration, report func(code string, node ast.Node, format string, args ...interface{})) (*protocolMachine, bool) {
	ok := true
	m := &protocolMachine{decl: decl, name: decl.Name.Value}
	seen := map[string]bool{}
	addState := func(id *ast.Identifier) {
		if !seen[id.Value] {
			seen[id.Value] = true
			m.states = append(m.states, id.Value)
			if r := []rune(id.Value); len(r) > 0 && !unicode.IsUpper(r[0]) {
				report(CodeProtocolShape, id, "state %s: states are spelled like variants, with an initial capital", id.Value)
				ok = false
			}
		}
	}
	if decl.Initial == nil {
		report(CodeProtocolShape, decl.Name, "protocol %s declares no initial state (`initial S`)", decl.Name.Value)
		ok = false
	} else {
		m.initial = decl.Initial.Value
		addState(decl.Initial)
	}
	if len(decl.Transitions) == 0 {
		report(CodeProtocolShape, decl.Name, "protocol %s declares no transitions", decl.Name.Value)
		ok = false
	}
	steps := map[string]*protocolStep{}
	pairs := map[string]bool{}
	for _, t := range decl.Transitions {
		addState(t.From)
		addState(t.To)
		if t.Param != nil {
			typeName, isIdent := t.Param.Type.(*ast.Identifier)
			if !isIdent {
				report(CodeProtocolShape, t.Param.Name, "transition %s: a payload is one of u8, u16, u32, Bool", t.Name.Value)
				ok = false
			} else if _, scalar := commandScalars[typeName.Value]; !scalar {
				report(CodeProtocolShape, t.Param.Type, "transition %s: payload type %s is not one of u8, u16, u32, Bool", t.Name.Value, typeName.Value)
				ok = false
			}
		}
		if t.Callable != nil && len(decl.Resources) == 0 {
			report(CodeProtocolShape, t.Callable, "transition %s names a callable, but protocol %s governs no resource type (`resource T`)", t.Name.Value, decl.Name.Value)
			ok = false
		}
		key := t.Name.Value + "\x00" + t.From.Value
		if pairs[key] {
			report(CodeProtocolShape, t.Name, "transition %s from %s is declared twice", t.Name.Value, t.From.Value)
			ok = false
			continue
		}
		pairs[key] = true
		step, exists := steps[t.Name.Value]
		if !exists {
			step = &protocolStep{name: t.Name.Value, payload: t.Param, node: t}
			steps[t.Name.Value] = step
			m.steps = append(m.steps, step)
		} else if !sameOptionalParam(step.payload, t.Param) {
			report(CodeProtocolShape, t.Name, "transition %s carries a different payload than its earlier line", t.Name.Value)
			ok = false
		}
		step.from = append(step.from, t.From.Value)
		step.to = append(step.to, t.To.Value)
	}
	if ok && decl.Initial != nil {
		reachable := false
		for _, t := range decl.Transitions {
			if t.From.Value == m.initial {
				reachable = true
			}
		}
		if !reachable {
			report(CodeProtocolShape, decl.Initial, "protocol %s: no transition leaves the initial state %s", decl.Name.Value, m.initial)
			ok = false
		}
	}
	return m, ok
}

func sameOptionalParam(a, b *ast.FunctionParameter) bool {
	if (a == nil) != (b == nil) {
		return false
	}
	if a == nil {
		return true
	}
	ta, okA := a.Type.(*ast.Identifier)
	tb, okB := b.Type.(*ast.Identifier)
	return okA && okB && ta.Value == tb.Value && a.Name.Value == b.Name.Value
}

// lowerProtocols replaces every protocol declaration with its projections and
// returns the resource protocol facts of `via`-bound transitions.
func lowerProtocols(tree *SyntaxTree) ([]typechecker.ResourceProtocolDeclaration, error) {
	program := tree.Root
	var diags []*diagnostic.Diagnostic
	report := func(code string, node ast.Node, format string, args ...interface{}) {
		diags = append(diags, diagnostic.NewDiagnosticFromNodeWithCode(node, "compiler", code, modules.DemangleText(fmt.Sprintf(format, args...))))
	}
	var resources []typechecker.ResourceProtocolDeclaration
	var out []ast.Statement
	found := false
	declared := map[string]bool{}
	for _, stmt := range program.Statements {
		if name := declarationName(stmt); name != "" {
			declared[name] = true
		}
	}
	for _, stmt := range program.Statements {
		decl, isProtocol := stmt.(*ast.ProtocolDeclaration)
		if !isProtocol {
			out = append(out, stmt)
			continue
		}
		found = true
		machine, ok := analyzeProtocol(decl, report)
		if !ok {
			continue
		}
		projected := machine.project()
		for _, generated := range projected {
			if name := declarationName(generated); declared[name] {
				report(CodeProtocolShape, decl.Name, "protocol %s projects %s, which the program already declares", decl.Name.Value, name)
				ok = false
			}
		}
		if !ok {
			continue
		}
		out = append(out, projected...)
		if facts, has := machine.resourceFacts(); has {
			resources = append(resources, facts)
		}
	}
	if len(diags) != 0 {
		return nil, &DiagnosticError{Phase: "protocol", Diagnostics: diags}
	}
	if found {
		program.Statements = out
	}
	return resources, nil
}

// resourceFacts projects `via`-bound transitions into the typestate facts
// the resource checker enforces (typechecker/resource_resolution.go).
func (m *protocolMachine) resourceFacts() (typechecker.ResourceProtocolDeclaration, bool) {
	if len(m.decl.Resources) == 0 {
		return typechecker.ResourceProtocolDeclaration{}, false
	}
	facts := typechecker.ResourceProtocolDeclaration{Name: m.name, States: append([]string(nil), m.states...), Initial: m.initial}
	for _, r := range m.decl.Resources {
		facts.ResourceTypes = append(facts.ResourceTypes, r.Value)
	}
	for _, t := range m.decl.Transitions {
		if t.Callable == nil {
			continue
		}
		facts.Transitions = append(facts.Transitions, typechecker.ResourceTransitionDeclaration{
			Name: t.Name.Value + "@" + t.From.Value, Callable: t.Callable.Value, From: t.From.Value, To: t.To.Value,
		})
	}
	return facts, len(facts.Transitions) > 0
}

// project builds the Oak declarations: NameState, NameStep, name_initial,
// name_legal, name_next.
func (m *protocolMachine) project() []ast.Statement {
	ctx := m.decl.Name.Token.SemanticContext
	s := newSynth(helperContext(ctx, m.name))
	stateType := m.name + "State"
	stepType := m.name + "Step"
	prefix := snakeCase(m.name)
	exported := m.decl.Exported

	adt := func(name string, variants []*ast.ADTVariant) *ast.ADTType {
		return &ast.ADTType{Token: s.tok(0, "type"), EndToken: s.tok(0, ""), Name: s.id(name), Variants: variants, Exported: exported}
	}
	var stateVariants []*ast.ADTVariant
	for _, st := range m.states {
		stateVariants = append(stateVariants, &ast.ADTVariant{Token: s.tok(0, st), Name: s.id(st)})
	}
	var stepVariants []*ast.ADTVariant
	for _, step := range m.steps {
		v := &ast.ADTVariant{Token: s.tok(0, step.name), Name: s.id(variantName(step.name))}
		if step.payload != nil {
			v.Payload = s.id(step.payload.Type.(*ast.Identifier).Value)
		}
		stepVariants = append(stepVariants, v)
	}

	// name_legal: step ? | .T => (state ? | .From => true | _ => false) ...
	// name_next:  step ? | .T => (state ? | .From => .To | _ => state) ...
	stateParam := func() *ast.FunctionParameter { return s.param("state", s.id(stateType)) }
	stepParam := func() *ast.FunctionParameter { return s.param("step", s.id(stepType)) }
	binding := func(step *protocolStep) string {
		if step.payload == nil {
			return ""
		}
		return "_"
	}
	covers := func(step *protocolStep) bool { return len(step.from) == len(m.states) }

	var legalArms, nextArms []*ast.MatchArm
	for _, step := range m.steps {
		var legalInner, nextInner []*ast.MatchArm
		for i, from := range step.from {
			legalInner = append(legalInner, s.arm(from, "", s.boolean(true)))
			nextInner = append(nextInner, s.arm(from, "", s.variant(step.to[i], nil)))
		}
		if !covers(step) {
			legalInner = append(legalInner, s.wildcardArm(s.boolean(false)))
			nextInner = append(nextInner, s.wildcardArm(s.id("state")))
		}
		legalArms = append(legalArms, s.arm(variantName(step.name), binding(step), s.match(s.id("state"), legalInner...)))
		nextArms = append(nextArms, s.arm(variantName(step.name), binding(step), s.match(s.id("state"), nextInner...)))
	}
	initial := s.fnExpr(prefix+"_initial", nil, s.id(stateType), s.variant(m.initial, nil))
	legal := s.fnExpr(prefix+"_legal", []*ast.FunctionParameter{stateParam(), stepParam()}, s.id("Bool"), s.match(s.id("step"), legalArms...))
	next := s.fn(prefix+"_next", []*ast.FunctionParameter{stateParam(), stepParam()}, s.id(stateType),
		s.expr(s.call("assert", s.call(prefix+"_legal", s.id("state"), s.id("step")))),
		s.expr(s.match(s.id("step"), nextArms...)))
	for _, fn := range []*ast.FunctionStatement{initial, legal, next} {
		fn.Exported = exported
	}
	return []ast.Statement{adt(stateType, stateVariants), adt(stepType, stepVariants), initial, legal, next}
}

// Protocols returns the protocol declarations of a parsed tree, in order.
func Protocols(tree *SyntaxTree) []*ast.ProtocolDeclaration {
	var decls []*ast.ProtocolDeclaration
	for _, stmt := range tree.Root.Statements {
		if decl, ok := stmt.(*ast.ProtocolDeclaration); ok {
			decls = append(decls, decl)
		}
	}
	return decls
}

// sortedKeys is a small helper for deterministic emission.
func sortedKeys(m map[string]bool) []string {
	keys := make([]string, 0, len(m))
	for k := range m {
		keys = append(keys, k)
	}
	sort.Strings(keys)
	return keys
}
