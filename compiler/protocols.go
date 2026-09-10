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
	"reflect"
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
	lines   []*ast.ProtocolTransition
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
	if (decl.Data == nil) != (decl.Init == nil) {
		report(CodeProtocolShape, decl.Name, "protocol %s declares `data` and `init` together or not at all", decl.Name.Value)
		ok = false
	}
	if decl.Data != nil && decl.Init != nil {
		fields := map[string]bool{}
		for _, f := range decl.Data.FieldOrder {
			fields[f.Name] = true
		}
		for _, f := range decl.Init.FieldOrder {
			if !fields[f.Name] {
				report(CodeProtocolShape, decl.Init, "protocol %s: init names %s, which data does not declare", decl.Name.Value, f.Name)
				ok = false
			}
		}
		for _, f := range decl.Data.FieldOrder {
			if _, set := decl.Init.Fields[f.Name]; !set {
				report(CodeProtocolShape, decl.Init, "protocol %s: init does not set %s", decl.Name.Value, f.Name)
				ok = false
			}
		}
	}
	steps := map[string]*protocolStep{}
	pairs := map[string]bool{}
	guarded := map[string]bool{}
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
		if decl.Data == nil && mentionsIdentifier(t.Guard, "data") || decl.Data == nil && t.Effects != nil && mentionsIdentifier(t.Effects, "data") {
			report(CodeProtocolShape, t.Name, "transition %s refers to data, but protocol %s declares none", t.Name.Value, decl.Name.Value)
			ok = false
		}
		key := t.Name.Value + "\x00" + t.From.Value
		if pairs[key] && (!guarded[key] || t.Guard == nil) {
			report(CodeProtocolShape, t.Name, "transition %s from %s is declared twice; several lines from one state must each carry a `when` guard", t.Name.Value, t.From.Value)
			ok = false
			continue
		}
		pairs[key] = true
		guarded[key] = t.Guard != nil
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
		step.lines = append(step.lines, t)
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
// name_legal, name_next — and, with data, NameData, name_initial_data, a
// legality predicate that reads the data record and a transition function
// that mutates it through a span.
func (m *protocolMachine) project() []ast.Statement {
	ctx := m.decl.Name.Token.SemanticContext
	s := newSynth(helperContext(ctx, m.name))
	stateType := m.name + "State"
	stepType := m.name + "Step"
	dataType := m.name + "Data"
	prefix := snakeCase(m.name)
	exported := m.decl.Exported
	withData := m.decl.Data != nil

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
	out := []ast.Statement{adt(stateType, stateVariants), adt(stepType, stepVariants)}

	stateParam := func() *ast.FunctionParameter { return s.param("state", s.id(stateType)) }
	stepParam := func() *ast.FunctionParameter { return s.param("step", s.id(stepType)) }
	// The payload binding is the declared parameter name when any line of
	// the step mentions it, else the discard binding.
	binding := func(step *protocolStep) string {
		if step.payload == nil {
			return ""
		}
		for _, line := range step.lines {
			if mentionsIdentifier(line.Guard, step.payload.Name.Value) || line.Effects != nil && mentionsIdentifier(line.Effects, step.payload.Name.Value) {
				return step.payload.Name.Value
			}
		}
		return "_"
	}
	isState := func(from string) ast.Expression {
		return s.match(s.id("state"), s.arm(from, "", s.boolean(true)), s.wildcardArm(s.boolean(false)))
	}

	initial := s.fnExpr(prefix+"_initial", nil, s.id(stateType), s.variant(m.initial, nil))
	initial.Exported = exported
	out = append(out, initial)

	if !withData {
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
		legal := s.fnExpr(prefix+"_legal", []*ast.FunctionParameter{stateParam(), stepParam()}, s.id("Bool"), s.match(s.id("step"), legalArms...))
		next := s.fn(prefix+"_next", []*ast.FunctionParameter{stateParam(), stepParam()}, s.id(stateType),
			s.expr(s.call("assert", s.call(prefix+"_legal", s.id("state"), s.id("step")))),
			s.expr(s.match(s.id("step"), nextArms...)))
		legal.Exported, next.Exported = exported, exported
		return append(out, legal, next)
	}

	// NameData and its initial value.
	dataShape := cloneSyntax(reflect.ValueOf(m.decl.Data)).Interface().(*ast.RecordLiteral)
	out = append(out, adt(dataType, []*ast.ADTVariant{{Token: s.tok(0, dataType), Name: s.id(dataType), Literal: dataShape}}))
	initValues := cloneSyntax(reflect.ValueOf(m.decl.Init)).Interface().(*ast.RecordLiteral)
	initValues.TypeName = s.id(dataType)
	initialData := s.fnExpr(prefix+"_initial_data", nil, s.id(dataType), initValues)
	initialData.Exported = exported
	out = append(out, initialData)

	// name_legal(state, data, step): per step, OR over its lines of
	// (state is From) && guard; the guard reads the data record by value.
	dataValue := func() *ast.FunctionParameter { return s.param("data", s.id(dataType)) }
	// A match expression cannot be an operand in the backend, so every
	// "state is From" test is hoisted into a Bool binding first; names are
	// unique across the whole function (one declaration per name).
	var legalArms []*ast.MatchArm
	for si, step := range m.steps {
		var body []ast.Statement
		var terms []ast.Expression
		for k, line := range step.lines {
			fromName := fmt.Sprintf("from_%d_%d", si, k)
			body = append(body, s.decl(fromName, s.id("Bool"), isState(line.From.Value)))
			var term ast.Expression = s.id(fromName)
			if line.Guard != nil {
				term = s.and(term, cloneExpression(line.Guard))
			}
			terms = append(terms, term)
		}
		body = append(body, s.expr(s.or(terms...)))
		legalArms = append(legalArms, s.arm(variantName(step.name), binding(step), s.block(body...)))
	}
	legal := s.fnExpr(prefix+"_legal", []*ast.FunctionParameter{stateParam(), dataValue(), stepParam()}, s.id("Bool"), s.match(s.id("step"), legalArms...))
	legal.Exported = exported
	out = append(out, legal)

	// name_next(state, data: [*]NameData, step): the first line whose state
	// and guard hold applies its effects and names the target. Effects run
	// on a local copy of the record (`data.x` rewritten to `record.x`) that
	// is written back through the span once: a plain local admits every
	// field and element assignment, while an element store through a span
	// into a record field does not lower yet (oak #80).
	const local = "record"
	var nextArms []*ast.MatchArm
	for si, step := range m.steps {
		var body []ast.Statement
		for k, line := range step.lines {
			fromName := fmt.Sprintf("from_%d_%d", si, k)
			body = append(body, s.decl(fromName, s.id("Bool"), isState(line.From.Value)))
			condition := s.and(s.not(s.id("done")), s.id(fromName))
			if line.Guard != nil {
				condition = s.and(condition, renameIdentifier(cloneExpression(line.Guard), "data", local).(ast.Expression))
			}
			var effects []ast.Statement
			if line.Effects != nil {
				rewritten := renameIdentifier(cloneSyntax(reflect.ValueOf(line.Effects)).Interface().(*ast.BlockStatement), "data", local).(*ast.BlockStatement)
				effects = append(effects, rewritten.Statements...)
			}
			effects = append(effects, s.assign("result", s.variant(line.To.Value, nil)), s.assign("done", s.boolean(true)))
			body = append(body, s.expr(s.cond(condition, s.block(effects...), nil)))
		}
		nextArms = append(nextArms, s.arm(variantName(step.name), binding(step), s.block(body...)))
	}
	next := s.fn(prefix+"_next", []*ast.FunctionParameter{stateParam(), s.param("data", s.span(s.id(dataType))), stepParam()}, s.id(stateType),
		s.expr(s.call("assert", s.call(prefix+"_legal", s.id("state"), s.index(s.id("data"), s.intLit(0)), s.id("step")))),
		s.decl(local, s.id(dataType), s.index(s.id("data"), s.intLit(0))),
		s.decl("result", s.id(stateType), s.id("state")),
		s.decl("done", s.id("Bool"), s.boolean(false)),
		s.expr(s.match(s.id("step"), nextArms...)),
		s.store(s.index(s.id("data"), s.intLit(0)), s.id(local)),
		s.expr(s.id("result")))
	next.Exported = exported
	return append(out, next)
}

// cloneExpression deep-copies an expression so a guard can appear in more
// than one projection.
func cloneExpression(e ast.Expression) ast.Expression {
	return cloneSyntax(reflect.ValueOf(e)).Interface().(ast.Expression)
}

// mentionsIdentifier reports whether a syntax subtree names `name`.
func mentionsIdentifier(node ast.Node, name string) bool {
	if node == nil {
		return false
	}
	found := false
	var walk func(v reflect.Value)
	walk = func(v reflect.Value) {
		if found {
			return
		}
		switch v.Kind() {
		case reflect.Interface, reflect.Pointer:
			if v.IsNil() {
				return
			}
			if id, ok := v.Interface().(*ast.Identifier); ok {
				if id.Value == name {
					found = true
				}
				return
			}
			walk(v.Elem())
		case reflect.Struct:
			for i := 0; i < v.NumField(); i++ {
				if v.Type().Field(i).IsExported() {
					walk(v.Field(i))
				}
			}
		case reflect.Slice:
			for i := 0; i < v.Len(); i++ {
				walk(v.Index(i))
			}
		case reflect.Map:
			iter := v.MapRange()
			for iter.Next() {
				walk(iter.Value())
			}
		}
	}
	walk(reflect.ValueOf(node))
	return found
}

// renameIdentifier rewrites every identifier `from` in a (freshly cloned)
// subtree to `to`; the transition function's effects address the local copy
// of the record this way.
func renameIdentifier(node ast.Node, from, to string) ast.Node {
	var walk func(v reflect.Value)
	walk = func(v reflect.Value) {
		switch v.Kind() {
		case reflect.Interface, reflect.Pointer:
			if v.IsNil() {
				return
			}
			if id, ok := v.Interface().(*ast.Identifier); ok {
				if id.Value == from {
					id.Value = to
					id.Token.Literal = to
				}
				return
			}
			walk(v.Elem())
		case reflect.Struct:
			for i := 0; i < v.NumField(); i++ {
				if v.Type().Field(i).IsExported() {
					walk(v.Field(i))
				}
			}
		case reflect.Slice:
			for i := 0; i < v.Len(); i++ {
				walk(v.Index(i))
			}
		case reflect.Map:
			iter := v.MapRange()
			for iter.Next() {
				walk(iter.Value())
			}
		}
	}
	walk(reflect.ValueOf(node))
	return node
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
