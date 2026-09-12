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
	"github.com/SCKelemen/oak/layout"
	"github.com/SCKelemen/oak/parser"
	"github.com/SCKelemen/oak/scanner"
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

// livenessState reads a liveness term that names a state: an identifier
// with an initial capital (states are spelled like variants).
func livenessState(expr ast.Expression) (string, bool) {
	ident, isIdent := expr.(*ast.Identifier)
	if !isIdent {
		return "", false
	}
	r := []rune(ident.Value)
	if len(r) == 0 || !unicode.IsUpper(r[0]) {
		return "", false
	}
	return ident.Value, true
}

// protocolMachine is the checked shape of one declaration.
type protocolMachine struct {
	decl    *ast.ProtocolDeclaration
	name    string
	states  []string
	initial string
	steps   []*protocolStep
	// typestate names the governed resource types that are record
	// templates with one type parameter: their handles carry the protocol
	// state in the type (docs/spec/112-protocols.md section 5a).
	typestate map[string]bool
	// quantifiers are the count/all/any/none forms the guards and effects
	// use over array data fields (docs/spec/112-protocols.md section 1),
	// each projected as one bounded helper function.
	quantifiers []quantifierUse
	// records are the program's plain record declarations, for the element
	// type of an array-of-records data field.
	records map[string]*ast.RecordLiteral
}

// quantifierUse is one count/all/any/none form over a data field: the
// field, its length, and for an array of records the Bool field read.
type quantifierUse struct {
	form   string
	field  string
	sub    string
	length int64
}

func (q quantifierUse) helperName(prefix string) string {
	name := prefix + "_" + q.form + "_" + q.field
	if q.sub != "" {
		name += "_" + q.sub
	}
	return name
}

var quantifierForms = map[string]bool{"count": true, "all": true, "any": true, "none": true}

// RecordDeclarations collects a program's plain (non-generic) record
// declarations by name: the element types array-of-records protocol data
// may use.
func RecordDeclarations(program *ast.Program) map[string]*ast.RecordLiteral {
	records := map[string]*ast.RecordLiteral{}
	if program == nil {
		return records
	}
	for _, stmt := range program.Statements {
		adt, isADT := stmt.(*ast.ADTType)
		if !isADT || adt.Name == nil || len(adt.TypeParams) != 0 || len(adt.Variants) != 1 {
			continue
		}
		if literal, isRecord := adt.Variants[0].Literal.(*ast.RecordLiteral); isRecord {
			records[adt.Name.Value] = literal
		}
	}
	return records
}

// rewriteExpressions replaces every expression below node (and node's own
// expression fields) with f's result, descending into the replacement.
func rewriteExpressions(node ast.Node, f func(ast.Expression) ast.Expression) {
	if node == nil {
		return
	}
	rewriteValue(reflect.ValueOf(node), f)
}

var expressionType = reflect.TypeOf((*ast.Expression)(nil)).Elem()

func rewriteValue(v reflect.Value, f func(ast.Expression) ast.Expression) {
	switch v.Kind() {
	case reflect.Ptr:
		if !v.IsNil() {
			rewriteValue(v.Elem(), f)
		}
	case reflect.Interface:
		if v.IsNil() {
			return
		}
		if v.Type() == expressionType && v.CanSet() {
			replaced := f(v.Interface().(ast.Expression))
			if replaced != nil {
				v.Set(reflect.ValueOf(replaced))
			}
		}
		rewriteValue(v.Elem(), f)
	case reflect.Struct:
		for i := 0; i < v.NumField(); i++ {
			if v.Field(i).CanSet() {
				rewriteValue(v.Field(i), f)
			}
		}
	case reflect.Slice:
		for i := 0; i < v.Len(); i++ {
			rewriteValue(v.Index(i), f)
		}
	case reflect.Map:
		iter := v.MapRange()
		for iter.Next() {
			value := iter.Value()
			if value.Kind() == reflect.Interface && value.Type() == expressionType && !value.IsNil() {
				replaced := f(value.Interface().(ast.Expression))
				if replaced != nil {
					v.SetMapIndex(iter.Key(), reflect.ValueOf(replaced))
					rewriteValue(reflect.ValueOf(replaced), f)
					continue
				}
			}
			rewriteValue(value, f)
		}
	}
}

// quantifierCall recognizes count/all/any/none over `data.field` or
// `data.field, sub`; the shape is validated by analyzeProtocol.
func quantifierCall(e ast.Expression) (form, field, sub string, ok bool) {
	call, isCall := e.(*ast.InvocationExpression)
	if !isCall || call == nil {
		return "", "", "", false
	}
	fn, isIdent := call.Function.(*ast.Identifier)
	if !isIdent || fn == nil || !quantifierForms[fn.Value] || len(call.Arguments) == 0 || len(call.Arguments) > 2 {
		return "", "", "", false
	}
	target, isIndex := call.Arguments[0].(*ast.IndexExpression)
	if !isIndex {
		return fn.Value, "", "", true
	}
	name, isField := dataField(target)
	if !isField {
		return fn.Value, "", "", true
	}
	if len(call.Arguments) == 2 {
		subIdent, isSub := call.Arguments[1].(*ast.Identifier)
		if !isSub || subIdent == nil {
			return fn.Value, name, "", true
		}
		return fn.Value, name, subIdent.Value, true
	}
	return fn.Value, name, "", true
}

// checkQuantifiers validates the quantifier forms in a guard or effect
// block and records each distinct use. A one-argument form needs an
// [N]Bool field; a two-argument form needs an [N]R field with R a declared
// record whose named field is Bool.
func (m *protocolMachine) checkQuantifiers(node ast.Node, where string, report func(code string, node ast.Node, format string, args ...interface{})) bool {
	ok := true
	fieldTypes := map[string]ast.Expression{}
	if m.decl.Data != nil {
		for _, f := range m.decl.Data.FieldOrder {
			fieldTypes[f.Name] = f.Value
		}
	}
	seen := map[string]bool{}
	for _, q := range m.quantifiers {
		seen[q.helperName("")] = true
	}
	rewriteExpressions(node, func(e ast.Expression) ast.Expression {
		call, isCall := e.(*ast.InvocationExpression)
		if !isCall {
			return nil
		}
		fn, isIdent := call.Function.(*ast.Identifier)
		if !isIdent || fn == nil || !quantifierForms[fn.Value] {
			return nil
		}
		form, field, sub, _ := quantifierCall(e)
		if field == "" {
			report(CodeProtocolShape, e, "%s: %s takes data.field (an [N]Bool field) or data.field, sub (an [N]R field and a Bool field of R)", where, form)
			ok = false
			return nil
		}
		typ, declared := fieldTypes[field]
		if !declared {
			report(CodeProtocolShape, e, "%s: %s over data.%s, which data does not declare", where, form, field)
			ok = false
			return nil
		}
		length, element, isArray := arrayShape(typ)
		if !isArray {
			report(CodeProtocolShape, e, "%s: %s over data.%s, which is not a fixed array", where, form, field)
			ok = false
			return nil
		}
		if sub == "" {
			if element != "Bool" {
				report(CodeProtocolShape, e, "%s: %s over data.%s needs an [N]Bool field; name the Bool field of its %s elements as a second argument", where, form, field, element)
				ok = false
				return nil
			}
		} else {
			record, isRecord := m.records[element]
			if !isRecord {
				report(CodeProtocolShape, e, "%s: %s over data.%s, %s: %s is not a declared record", where, form, field, sub, element)
				ok = false
				return nil
			}
			subType, hasSub := record.Fields[sub]
			subIdent, isIdent := subType.(*ast.Identifier)
			if !hasSub || !isIdent || subIdent.Value != "Bool" {
				report(CodeProtocolShape, e, "%s: %s over data.%s, %s: %s has no Bool field %s", where, form, field, sub, element, sub)
				ok = false
				return nil
			}
		}
		use := quantifierUse{form: form, field: field, sub: sub, length: length}
		if !seen[use.helperName("")] {
			seen[use.helperName("")] = true
			m.quantifiers = append(m.quantifiers, use)
		}
		return nil
	})
	return ok
}

// rewriteQuantifiers replaces quantifier forms in a cloned guard or effect
// block with calls to the projected helpers, which take the data record.
func (m *protocolMachine) rewriteQuantifiers(node ast.Node, prefix string, s *synth) {
	rewriteExpressions(node, func(e ast.Expression) ast.Expression {
		form, field, sub, isQuantifier := quantifierCall(e)
		if !isQuantifier || field == "" {
			return nil
		}
		use := quantifierUse{form: form, field: field, sub: sub}
		return s.call(use.helperName(prefix), s.id("data"))
	})
}

// quantifierHelpers projects one bounded helper per quantifier use, as
// parsed Oak: `name_count_acks: (data: NameData): u32` folds the array.
func (m *protocolMachine) quantifierHelpers(prefix, dataType string) []ast.Statement {
	var out []ast.Statement
	for _, q := range m.quantifiers {
		element := fmt.Sprintf("data.%s[i]", q.field)
		if q.sub != "" {
			element += "." + q.sub
		}
		var src string
		switch q.form {
		case "count":
			src = fmt.Sprintf("%s: (data: %s): u32 {\n  n: u32 = u32(0)\n  i: u32 = u32(0)\n  while i < u32(%d) {\n    %s ? { n = n + u32(1) } | { }\n    i = i + u32(1)\n  }\n  n\n}\n", q.helperName(prefix), dataType, q.length, element)
		case "all":
			src = fmt.Sprintf("%s: (data: %s): Bool {\n  ok: Bool = true\n  i: u32 = u32(0)\n  while i < u32(%d) {\n    ok = ok && %s\n    i = i + u32(1)\n  }\n  ok\n}\n", q.helperName(prefix), dataType, q.length, element)
		case "any":
			src = fmt.Sprintf("%s: (data: %s): Bool {\n  found: Bool = false\n  i: u32 = u32(0)\n  while i < u32(%d) {\n    found = found || %s\n    i = i + u32(1)\n  }\n  found\n}\n", q.helperName(prefix), dataType, q.length, element)
		case "none":
			src = fmt.Sprintf("%s: (data: %s): Bool {\n  ok: Bool = true\n  i: u32 = u32(0)\n  while i < u32(%d) {\n    ok = ok && !%s\n    i = i + u32(1)\n  }\n  ok\n}\n", q.helperName(prefix), dataType, q.length, element)
		}
		if m.decl.Exported {
			src = "pub " + src
		}
		p := parser.New(layout.New(scanner.New(src)))
		program := p.ParseProgram()
		if len(p.Errors()) != 0 || program == nil || len(program.Statements) != 1 {
			continue
		}
		out = append(out, program.Statements[0])
	}
	return out
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
// ProtocolPrefix is the snake_case prefix of a protocol's projected
// functions: `Turnstile` -> `turnstile` (docs/spec/112-protocols.md §2).
func ProtocolPrefix(name string) string { return snakeCase(name) }

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
	return analyzeProtocolWith(decl, nil, report)
}

// analyzeProtocolWith is analyzeProtocol with the program's record
// declarations, which array-of-records data and two-argument quantifier
// forms need.
func analyzeProtocolWith(decl *ast.ProtocolDeclaration, records map[string]*ast.RecordLiteral, report func(code string, node ast.Node, format string, args ...interface{})) (*protocolMachine, bool) {
	ok := true
	m := &protocolMachine{decl: decl, name: decl.Name.Value, records: records}
	if m.records == nil {
		m.records = map[string]*ast.RecordLiteral{}
	}
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
			// The control state is the module's `state` variable and the
			// projection's `state` parameter; a field of that name would
			// shadow both.
			if f.Name == "state" || f.Name == "step" || f.Name == "data" {
				report(CodeProtocolShape, decl.Data, "protocol %s: data field %s is reserved by the projection (the control state, the step, the record)", decl.Name.Value, f.Name)
				ok = false
			}
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
	defer func() {
		// Fairness names declared steps; liveness names reached states or
		// Bool data expressions in the guard subset (checked after the
		// transitions, which declare both).
		for _, f := range decl.Fairness {
			if _, known := steps[f.Step.Value]; !known {
				report(CodeProtocolShape, f.Step, "fairness names step %s, which protocol %s does not declare", f.Step.Value, decl.Name.Value)
				ok = false
			}
		}
		for _, l := range decl.Liveness {
			for _, side := range []ast.Expression{l.From, l.Target} {
				if side == nil {
					continue
				}
				if state, isState := livenessState(side); isState {
					if !seen[state] {
						report(CodeProtocolShape, side, "eventually names state %s, which protocol %s does not reach", state, decl.Name.Value)
						ok = false
					}
					continue
				}
				if decl.Data == nil {
					report(CodeProtocolShape, side, "eventually refers to data, but protocol %s declares none", decl.Name.Value)
					ok = false
					continue
				}
				if !m.checkQuantifiers(&ast.ExpressionStatement{Expression: side}, "eventually", report) {
					ok = false
				}
			}
		}
	}()
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
		if t.Guard != nil && !m.checkQuantifiers(&ast.ExpressionStatement{Expression: t.Guard}, fmt.Sprintf("transition %s: guard", t.Name.Value), report) {
			ok = false
		}
		if t.Effects != nil && !m.checkQuantifiers(t.Effects, fmt.Sprintf("transition %s: effects", t.Name.Value), report) {
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
	functions := map[string]*ast.FunctionStatement{}
	templates := map[string]int{}
	for _, stmt := range program.Statements {
		if name := declarationName(stmt); name != "" {
			declared[name] = true
		}
		if fn, isFunction := stmt.(*ast.FunctionStatement); isFunction && fn.Name != nil {
			if fn.Receiver == nil {
				functions[fn.Name.Value] = fn
			} else if receiver, isIdent := fn.Receiver.Type.(*ast.Identifier); isIdent {
				// Methods are known to the checker as Type::method; a via
				// clause spells them Type.method.
				functions[receiver.Value+"::"+fn.Name.Value] = fn
			}
		}
		if adt, isADT := stmt.(*ast.ADTType); isADT && adt.Name != nil && len(adt.TypeParams) > 0 && len(adt.Variants) == 1 {
			if _, isRecord := adt.Variants[0].Literal.(*ast.RecordLiteral); isRecord {
				templates[adt.Name.Value] = len(adt.TypeParams)
			}
		}
	}
	for _, stmt := range program.Statements {
		decl, isProtocol := stmt.(*ast.ProtocolDeclaration)
		if !isProtocol {
			out = append(out, stmt)
			continue
		}
		found = true
		machine, ok := analyzeProtocolWith(decl, RecordDeclarations(program), report)
		if !ok {
			continue
		}
		machine.typestate = map[string]bool{}
		for _, r := range decl.Resources {
			if r != nil && templates[r.Value] == 1 {
				machine.typestate[r.Value] = true
			}
		}
		projected := machine.project()
		if len(machine.typestate) > 0 {
			projected = append(projected, machine.stateMarkers()...)
		}
		if decl.Data != nil {
			projected = append(projected, machine.quantifierHelpers(snakeCase(machine.name), machine.name+"Data")...)
		}
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
		if facts, has := machine.resourceFacts(functions, report); has {
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
// the resource checker enforces (typechecker/resource_resolution.go). The
// parameter modes, callable contracts, and result identity written on the
// via clause resolve against the callable's declaration in the elaborated
// program — parameter names to zero-based indices, `receiver` to the
// receiver slot, `Type.method` to the checker's `Type::method` identity —
// so the same declaration reads identically whether the callable lives in
// this package or an imported one (internal names are already substituted
// by the module loader). Every name is resolved here and every failure is
// a protocol shape error: nothing reaches the checker half-resolved.
func (m *protocolMachine) resourceFacts(functions map[string]*ast.FunctionStatement, report func(code string, node ast.Node, format string, args ...interface{})) (typechecker.ResourceProtocolDeclaration, bool) {
	if len(m.decl.Resources) == 0 {
		return typechecker.ResourceProtocolDeclaration{}, false
	}
	facts := typechecker.ResourceProtocolDeclaration{Name: m.name, States: append([]string(nil), m.states...), Initial: m.initial}
	for _, r := range m.decl.Resources {
		facts.ResourceTypes = append(facts.ResourceTypes, r.Value)
	}
	ok := true
	for _, t := range m.decl.Transitions {
		if t.Callable == nil {
			continue
		}
		callable := t.Callable.Value
		if t.CallableType != nil {
			callable = t.CallableType.Value + "::" + t.Callable.Value
		}
		spelled := strings.ReplaceAll(callable, "::", ".")
		transition := typechecker.ResourceTransitionDeclaration{
			Name: t.Name.Value + "@" + t.From.Value, Callable: callable, From: t.From.Value, To: t.To.Value, Trusted: t.Trusted,
		}
		// Typestate-indexed resources (112-protocols.md section 5a): a
		// transition that consumes a Handle[From] and returns a Handle[To]
		// hands back the same resource in its next state — an alias of the
		// consumed argument by construction. A result clause written on the
		// same line must agree with that.
		typestateAlias := -1
		if len(m.typestate) > 0 {
			if fn := functions[callable]; fn != nil {
				if !m.checkTypestateSignature(t, fn, report) {
					ok = false
					continue
				}
				if index := m.typestateAliasIndex(t, fn); index >= 0 {
					transition.ReturnsAlias, transition.AliasesArgument = true, index
					typestateAlias = index
				}
			}
		}
		if len(t.Modes) == 0 && t.Result == nil && !t.Trusted {
			facts.Transitions = append(facts.Transitions, transition)
			continue
		}
		fn := functions[callable]
		if fn == nil {
			if t.CallableType != nil {
				report(CodeProtocolShape, t.Callable, "transition %s: via %s names a method, but %s declares no method %s in this program", t.Name.Value, spelled, t.CallableType.Value, t.Callable.Value)
			} else {
				report(CodeProtocolShape, t.Callable, "transition %s: via %s names parameter modes or a result identity, but %s is not a function declared in this program", t.Name.Value, spelled, spelled)
			}
			ok = false
			continue
		}
		// parameterIndex resolves a parameter name of the callable; -1 when
		// the name is not one of its parameters.
		parameterIndex := func(name string) int {
			for i, parameter := range fn.Parameters {
				if parameter != nil && parameter.Name != nil && parameter.Name.Value == name {
					return i
				}
			}
			return -1
		}
		modeOf := func(word string) typechecker.ResourceParameterMode {
			switch word {
			case "borrowed mut":
				return typechecker.ResourceParameterBorrowedMut
			case "consumed":
				return typechecker.ResourceParameterConsumed
			}
			return typechecker.ResourceParameterBorrowed
		}
		seen := map[string]bool{}
		for _, entry := range t.Modes {
			if seen[entry.Name.Value] {
				report(CodeProtocolShape, entry.Name, "transition %s: via %s marks %s twice", t.Name.Value, spelled, entry.Name.Value)
				ok = false
				continue
			}
			seen[entry.Name.Value] = true
			if entry.Name.Value == "receiver" {
				if entry.Contract != nil {
					report(CodeProtocolShape, entry.Name, "transition %s: via %s gives the receiver a callable contract; a receiver carries a mode", t.Name.Value, spelled)
					ok = false
					continue
				}
				if fn.Receiver == nil {
					report(CodeProtocolShape, entry.Name, "transition %s: via %s marks a receiver mode, but %s has no receiver", t.Name.Value, spelled, spelled)
					ok = false
					continue
				}
				transition.Receiver = modeOf(entry.Mode)
				continue
			}
			index := parameterIndex(entry.Name.Value)
			if index < 0 {
				report(CodeProtocolShape, entry.Name, "transition %s: via %s marks %s, which is not a parameter of %s", t.Name.Value, spelled, entry.Name.Value, spelled)
				ok = false
				continue
			}
			if entry.Contract == nil {
				transition.Parameters = append(transition.Parameters, typechecker.ResourceParameterDeclaration{Index: index, Mode: modeOf(entry.Mode)})
				continue
			}
			// A callable contract is positional over the function type of
			// the parameter it constrains: one word per parameter of that
			// type, `_` leaving the position unmarked.
			functionType, isFunction := fn.Parameters[index].Type.(*ast.FunctionTypeExpression)
			if !isFunction {
				report(CodeProtocolShape, entry.Name, "transition %s: via %s gives %s a callable contract, but %s is not a function-typed parameter", t.Name.Value, spelled, entry.Name.Value, entry.Name.Value)
				ok = false
				continue
			}
			if len(entry.Contract.Modes) != len(functionType.Parameters) {
				report(CodeProtocolShape, entry.Name, "transition %s: via %s: the contract on %s lists %d modes, but its function type has %d parameters (write `_` for an unmarked parameter)", t.Name.Value, spelled, entry.Name.Value, len(entry.Contract.Modes), len(functionType.Parameters))
				ok = false
				continue
			}
			contract := &typechecker.ResourceCallableContract{ReturnsFresh: entry.Contract.ReturnsFresh}
			for position, word := range entry.Contract.Modes {
				if word == "_" {
					continue
				}
				contract.Parameters = append(contract.Parameters, typechecker.ResourceParameterDeclaration{Index: position, Mode: modeOf(word)})
			}
			if len(contract.Parameters) == 0 && !contract.ReturnsFresh {
				report(CodeProtocolShape, entry.Name, "transition %s: via %s: the contract on %s marks nothing; drop it or mark a parameter or `: fresh`", t.Name.Value, spelled, entry.Name.Value)
				ok = false
				continue
			}
			transition.Parameters = append(transition.Parameters, typechecker.ResourceParameterDeclaration{Index: index, Callable: contract})
		}
		if t.Result != nil {
			resultIndices := make([]int, 0, len(t.Result.Names))
			resultOK := true
			seenOrigin := map[string]bool{}
			for _, name := range t.Result.Names {
				if name.Value == "receiver" {
					report(CodeProtocolShape, name, "transition %s: via %s: a result identity names explicit parameters; identities over the receiver are not admitted yet", t.Name.Value, spelled)
					resultOK = false
					continue
				}
				if seenOrigin[name.Value] {
					report(CodeProtocolShape, name, "transition %s: via %s names %s twice in its result identity", t.Name.Value, spelled, name.Value)
					resultOK = false
					continue
				}
				seenOrigin[name.Value] = true
				index := parameterIndex(name.Value)
				if index < 0 {
					report(CodeProtocolShape, name, "transition %s: via %s: result identity names %s, which is not a parameter of %s", t.Name.Value, spelled, name.Value, spelled)
					resultOK = false
					continue
				}
				resultIndices = append(resultIndices, index)
			}
			if resultOK && typestateAlias >= 0 && !(t.Result.Kind == "alias" && len(resultIndices) == 1 && resultIndices[0] == typestateAlias) {
				report(CodeProtocolShape, t.Result.Names[0], "transition %s: via %s: a typestate transition already returns an alias of its consumed handle; the result clause must be `: alias %s` or be omitted", t.Name.Value, spelled, fn.Parameters[typestateAlias].Name.Value)
				resultOK = false
			}
			if !resultOK {
				ok = false
			} else {
				switch t.Result.Kind {
				case "fresh":
					transition.ReturnsFresh = true
				case "alias":
					transition.ReturnsAlias, transition.AliasesArgument = true, resultIndices[0]
				case "borrow":
					transition.ReturnsBorrow, transition.BorrowsArguments = true, resultIndices
				case "borrow mut":
					transition.ReturnsBorrow, transition.BorrowsArguments, transition.BorrowMutable = true, resultIndices, true
				}
			}
		} else if t.Trusted {
			report(CodeProtocolShape, t.Callable, "transition %s: via unsafe %s trusts a result identity, but the line declares none (`: fresh`, `: alias h`, `: borrow h`)", t.Name.Value, spelled)
			ok = false
		}
		facts.Transitions = append(facts.Transitions, transition)
	}
	return facts, ok && len(facts.Transitions) > 0
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
		guarded := func(step *protocolStep) bool {
			for _, line := range step.lines {
				if line.Guard != nil {
					return true
				}
			}
			return false
		}
		var legalArms, nextArms []*ast.MatchArm
		for si, step := range m.steps {
			if guarded(step) {
				// Lines with payload guards: the first line whose source
				// state and guard hold, in declaration order — the same
				// sequential shape the data-carrying projection uses.
				var legalBody, nextBody []ast.Statement
				var terms []ast.Expression
				for k, line := range step.lines {
					fromName := fmt.Sprintf("from_%d_%d", si, k)
					legalBody = append(legalBody, s.decl(fromName, s.id("Bool"), isState(line.From.Value)))
					nextBody = append(nextBody, s.decl(fromName, s.id("Bool"), isState(line.From.Value)))
					var term ast.Expression = s.id(fromName)
					condition := s.and(s.not(s.id("done")), s.id(fromName))
					if line.Guard != nil {
						term = s.and(term, cloneExpression(line.Guard))
						condition = s.and(condition, cloneExpression(line.Guard))
					}
					terms = append(terms, term)
					nextBody = append(nextBody, s.expr(s.cond(condition, s.block(s.assign("result", s.variant(line.To.Value, nil)), s.assign("done", s.boolean(true))), nil)))
				}
				legalBody = append(legalBody, s.expr(s.or(terms...)))
				legalArms = append(legalArms, s.arm(variantName(step.name), binding(step), s.block(legalBody...)))
				nextBody = append(nextBody, s.expr(s.id("result")))
				nextArms = append(nextArms, s.arm(variantName(step.name), binding(step), s.block(nextBody...)))
				continue
			}
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
		anyGuarded := false
		for _, step := range m.steps {
			anyGuarded = anyGuarded || guarded(step)
		}
		var next *ast.FunctionStatement
		if anyGuarded {
			next = s.fn(prefix+"_next", []*ast.FunctionParameter{stateParam(), stepParam()}, s.id(stateType),
				s.expr(s.call("assert", s.call(prefix+"_legal", s.id("state"), s.id("step")))),
				s.decl("result", s.id(stateType), s.id("state")),
				s.decl("done", s.id("Bool"), s.boolean(false)),
				s.expr(s.match(s.id("step"), nextArms...)))
		} else {
			next = s.fn(prefix+"_next", []*ast.FunctionParameter{stateParam(), stepParam()}, s.id(stateType),
				s.expr(s.call("assert", s.call(prefix+"_legal", s.id("state"), s.id("step")))),
				s.expr(s.match(s.id("step"), nextArms...)))
		}
		legal.Exported, next.Exported = exported, exported
		out = append(out, legal, next)
		// The compiler-known lowering (docs/spec/112-protocols.md section
		// 2a): a transition table, or a shift DFA when the machine is small
		// enough, computed here from the declaration; the Oak bodies above
		// stay the meaning. A byte-driven machine also gets `name_run`.
		if lowering := m.lowering(); lowering != nil {
			legal.Lowering = loweringKind(lowering, "legal")
			next.Lowering = loweringKind(lowering, "next")
			if lowering.Shift {
				stateADT := out[0].(*ast.ADTType)
				for i := range m.states {
					stateADT.TagValues = append(stateADT.TagValues, 6*i)
				}
			}
			if lowering.ByteSymbol {
				step := m.steps[0]
				run := s.fn(prefix+"_run", []*ast.FunctionParameter{stateParam(), s.param("bytes", s.view(s.id("u8")))}, s.id(stateType),
					s.decl("current", s.id(stateType), s.id("state")),
					s.decl("i", s.id("u32"), s.u32(0)),
					s.loop(s.lt(s.id("i"), s.call("len", s.id("bytes"))),
						s.assign("current", s.call(prefix+"_next", s.id("current"), s.variant(variantName(step.name), s.index(s.id("bytes"), s.id("i"))))),
						s.assign("i", s.add(s.id("i"), s.u32(1)))),
					s.expr(s.id("current")))
				run.Exported = exported
				run.Lowering = loweringKind(lowering, "run")
				out = append(out, run)
			}
		}
		return out
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
				guard := cloneExpression(line.Guard)
				holder := &ast.ExpressionStatement{Expression: guard}
				m.rewriteQuantifiers(holder, prefix, s)
				term = s.and(term, holder.Expression)
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
				guard := &ast.ExpressionStatement{Expression: cloneExpression(line.Guard)}
				m.rewriteQuantifiers(guard, prefix, s)
				condition = s.and(condition, renameIdentifier(guard.Expression, "data", local).(ast.Expression))
			}
			var effects []ast.Statement
			if line.Effects != nil {
				cloned := cloneSyntax(reflect.ValueOf(line.Effects)).Interface().(*ast.BlockStatement)
				m.rewriteQuantifiers(cloned, prefix, s)
				rewritten := renameIdentifier(cloned, "data", local).(*ast.BlockStatement)
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

// stateMarkers declares one marker type per state of a typestate-indexed
// protocol (docs/spec/112-protocols.md section 5a): `Offloaded: type =
// struct { offloaded_: u8 }`. Markers are distinct nominal islands, so
// `Segment[Offloaded]` and `Segment[Published]` are distinct types; they
// are never instantiated as values, so they cost nothing at run time.
func (m *protocolMachine) stateMarkers() []ast.Statement {
	var out []ast.Statement
	for _, state := range m.states {
		src := fmt.Sprintf("%s: type = struct { %s_: u8 }\n", state, snakeCase(state))
		p := parser.New(layout.New(scanner.New(src)))
		program := p.ParseProgram()
		if len(p.Errors()) != 0 || program == nil || len(program.Statements) != 1 {
			continue
		}
		out = append(out, program.Statements[0])
	}
	return out
}

// typestateIndex reads Segment[X] from a type expression: the template and
// the state it names. A bare template or an unrelated type is not indexed.
func typestateIndex(typ ast.Expression) (template, state string, ok bool) {
	index, isIndex := typ.(*ast.IndexExpression)
	if !isIndex || index == nil {
		return "", "", false
	}
	left, leftIsIdent := index.Left.(*ast.Identifier)
	right, rightIsIdent := index.Index.(*ast.Identifier)
	if !leftIsIdent || !rightIsIdent || left == nil || right == nil {
		return "", "", false
	}
	return left.Value, right.Value, true
}

// checkTypestateSignature holds a via callable to its line: every parameter
// of a typestate-indexed resource type must name the line's source state,
// a return of that type must name its target state, a bare template or a
// type-variable index is rejected (docs/spec/112-protocols.md section 5a).
func (m *protocolMachine) checkTypestateSignature(t *ast.ProtocolTransition, fn *ast.FunctionStatement, report func(code string, node ast.Node, format string, args ...interface{})) bool {
	ok := true
	typeVars := map[string]bool{}
	for _, tp := range fn.TypeParams {
		if tp != nil && tp.Name != nil {
			typeVars[tp.Name.Value] = true
		}
	}
	check := func(typ ast.Expression, want, role string) {
		if typ == nil {
			return
		}
		if ident, isIdent := typ.(*ast.Identifier); isIdent && ident != nil && m.typestate[ident.Value] {
			report(CodeProtocolShape, typ, "transition %s: via %s %s %s without its state; a typestate-indexed handle is spelled %s[%s]", t.Name.Value, fn.Name.Value, role, ident.Value, ident.Value, want)
			ok = false
			return
		}
		template, state, indexed := typestateIndex(typ)
		if !indexed || !m.typestate[template] {
			return
		}
		if typeVars[state] {
			report(CodeProtocolShape, typ, "transition %s: via %s %s %s[%s] with a type variable; a transition names the concrete state %s", t.Name.Value, fn.Name.Value, role, template, state, want)
			ok = false
			return
		}
		if state != want {
			report(CodeProtocolShape, typ, "transition %s: %s -> %s via %s %s %s[%s], but the line requires %s[%s]", t.Name.Value, t.From.Value, t.To.Value, fn.Name.Value, role, template, state, template, want)
			ok = false
		}
	}
	for _, parameter := range fn.Parameters {
		if parameter != nil {
			check(parameter.Type, t.From.Value, "takes")
		}
	}
	if fn.Receiver != nil {
		check(fn.Receiver.Type, t.From.Value, "takes receiver")
	}
	check(fn.ReturnType, t.To.Value, "returns")
	return ok
}

// typestateAliasIndex finds the parameter a typestate transition rebuilds:
// the one consumed parameter of the indexed type when the callable returns
// that type in the target state. -1 when the callable is not that shape.
func (m *protocolMachine) typestateAliasIndex(t *ast.ProtocolTransition, fn *ast.FunctionStatement) int {
	returned, _, indexedReturn := typestateIndex(fn.ReturnType)
	if !indexedReturn || !m.typestate[returned] {
		return -1
	}
	consumed := map[string]bool{}
	for _, entry := range t.Modes {
		if entry.Mode == "consumed" && entry.Name != nil {
			consumed[entry.Name.Value] = true
		}
	}
	index := -1
	for i, parameter := range fn.Parameters {
		if parameter == nil || parameter.Name == nil {
			continue
		}
		if template, _, indexed := typestateIndex(parameter.Type); indexed && template == returned && consumed[parameter.Name.Value] {
			if index >= 0 {
				return -1
			}
			index = i
		}
	}
	return index
}

// lowering computes the transition table of a machine without a data
// record (docs/spec/112-protocols.md section 2a). Symbols are the step tags
// when no step carries a payload, or the 256 values of the single step's
// u8 payload, with every guard evaluated for every value. It returns nil —
// the branch-tree projection stands — when the machine has another shape,
// when a guard is outside the evaluator's vocabulary, or when the table
// would not fit a u8 (more than 254 states or 64 KiB of entries).
func (m *protocolMachine) lowering() *ast.ProtocolLowering {
	if m.decl.Data != nil || len(m.states) == 0 || len(m.states) > 254 {
		return nil
	}
	stateIndex := map[string]int{}
	for i, st := range m.states {
		stateIndex[st] = i
	}
	sink := len(m.states)
	// A payload that no guard reads does not affect transitions: the step
	// is one symbol. Only a payload some guard mentions makes the payload
	// values the symbols.
	payloads := 0
	for _, step := range m.steps {
		if step.payload == nil {
			continue
		}
		for _, line := range step.lines {
			if mentionsIdentifier(line.Guard, step.payload.Name.Value) {
				payloads++
				break
			}
		}
	}
	lowering := &ast.ProtocolLowering{Protocol: m.name, States: len(m.states)}
	// firstLine resolves (state, step, payload value) to the target of the
	// first line whose source and guard hold; ok is false when a guard is
	// outside the compile-time vocabulary.
	firstLine := func(state string, step *protocolStep, payload uint64) (target int, legal bool, ok bool) {
		for _, line := range step.lines {
			if line.From.Value != state {
				continue
			}
			if line.Guard != nil {
				holds, evaluable := evalPayloadGuard(line.Guard, step.payload.Name.Value, payload)
				if !evaluable {
					return 0, false, false
				}
				if !holds {
					continue
				}
			}
			return stateIndex[line.To.Value], true, true
		}
		return sink, false, true
	}
	switch {
	case payloads == 0:
		lowering.Symbols = len(m.steps)
		if len(m.states)*len(m.steps) > 65536 {
			return nil
		}
		for _, state := range m.states {
			for _, step := range m.steps {
				target, _, ok := firstLine(state, step, 0)
				if !ok {
					return nil
				}
				lowering.Table = append(lowering.Table, target)
			}
		}
	case payloads == 1 && len(m.steps) == 1:
		step := m.steps[0]
		payloadType, isIdent := step.payload.Type.(*ast.Identifier)
		if !isIdent || payloadType.Value != "u8" {
			return nil
		}
		lowering.Symbols, lowering.ByteSymbol, lowering.StepName = 256, true, variantName(step.name)
		if len(m.states)*256 > 65536 {
			return nil
		}
		for _, state := range m.states {
			for value := 0; value < 256; value++ {
				target, _, ok := firstLine(state, step, uint64(value))
				if !ok {
					return nil
				}
				lowering.Table = append(lowering.Table, target)
			}
		}
	default:
		return nil
	}
	// The sink row: every symbol keeps the sink (Oak.Protocol.runSink_sink).
	for t := 0; t < lowering.Symbols; t++ {
		lowering.Table = append(lowering.Table, sink)
	}
	lowering.Shift = len(m.states)+1 <= 10
	return lowering
}

// kind copies the lowering for one projected function.
func loweringKind(l *ast.ProtocolLowering, kind string) *ast.ProtocolLowering {
	copied := *l
	copied.Kind = kind
	return &copied
}

// evalPayloadGuard evaluates a guard over a scalar payload at compile time:
// the payload name, integer and Boolean literals, width conversions
// (`u8(128)`), `+ - * / %`, comparisons, and `&& || !` — the guard
// vocabulary of docs/spec/112-protocols.md section 1 without data fields.
// Arithmetic is unsigned modulo 2^64 with the result masked to the payload
// width, matching the total machine arithmetic of 20-types.md; division by
// zero is not evaluable (it would trap at run time). Anything else is
// reported not evaluable and the lowering falls back to the branch tree.
func evalPayloadGuard(guard ast.Expression, payload string, value uint64) (bool, bool) {
	const width = uint64(0xFF)
	var num func(e ast.Expression) (uint64, bool)
	var boolean func(e ast.Expression) (bool, bool)
	num = func(e ast.Expression) (uint64, bool) {
		switch x := e.(type) {
		case *ast.Identifier:
			if x.Value == payload {
				return value & width, true
			}
			return 0, false
		case *ast.IntegerLiteral:
			return uint64(x.Value), true
		case *ast.InvocationExpression:
			name, isIdent := x.Function.(*ast.Identifier)
			if !isIdent || len(x.Arguments) != 1 {
				return 0, false
			}
			switch name.Value {
			case "u8", "u16", "u32", "u64", "i8", "i16", "i32", "i64":
				v, ok := num(x.Arguments[0])
				if !ok {
					return 0, false
				}
				switch name.Value {
				case "u8", "i8":
					return v & 0xFF, true
				case "u16", "i16":
					return v & 0xFFFF, true
				case "u32", "i32":
					return v & 0xFFFFFFFF, true
				}
				return v, true
			}
			return 0, false
		case *ast.InfixExpression:
			l, okL := num(x.Left)
			r, okR := num(x.Right)
			if !okL || !okR {
				return 0, false
			}
			switch x.Operator {
			case "+":
				return (l + r) & width, true
			case "-":
				return (l - r) & width, true
			case "*":
				return (l * r) & width, true
			case "/":
				if r == 0 {
					return 0, false
				}
				return l / r, true
			case "%":
				if r == 0 {
					return 0, false
				}
				return l % r, true
			}
			return 0, false
		}
		return 0, false
	}
	boolean = func(e ast.Expression) (bool, bool) {
		switch x := e.(type) {
		case *ast.Boolean:
			return x.Value, true
		case *ast.PrefixExpression:
			if x.Operator != "!" {
				return false, false
			}
			v, ok := boolean(x.Right)
			return !v, ok
		case *ast.InfixExpression:
			switch x.Operator {
			case "&&", "||":
				l, okL := boolean(x.Left)
				r, okR := boolean(x.Right)
				if !okL || !okR {
					return false, false
				}
				if x.Operator == "&&" {
					return l && r, true
				}
				return l || r, true
			case "==", "!=", "<", "<=", ">", ">=":
				l, okL := num(x.Left)
				r, okR := num(x.Right)
				if !okL || !okR {
					return false, false
				}
				switch x.Operator {
				case "==":
					return l == r, true
				case "!=":
					return l != r, true
				case "<":
					return l < r, true
				case "<=":
					return l <= r, true
				case ">":
					return l > r, true
				}
				return l >= r, true
			}
		}
		return false, false
	}
	return boolean(guard)
}
