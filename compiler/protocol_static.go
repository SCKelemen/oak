package compiler

import (
	"fmt"
	"reflect"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/layout"
	"github.com/SCKelemen/oak/parser"
	"github.com/SCKelemen/oak/scanner"
	"github.com/SCKelemen/oak/typechecker"
)

// staticProjection is the machine in the handle's type
// (docs/spec/112-protocols.md section 2b): for a protocol without a
// `resource` clause, a handle record template `Name[S]` over one marker type
// per state (`NameIdle`), `name_handle()` as the only construction at the
// initial state, and one transition function per declared line that
// consumes the handle at its source state and returns it at its target —
// as a `NameStepOutcome` (`Moved` or `Refused`) when the line has a guard,
// the refused handle coming back. The transitions are registered as a resource protocol over
// `Name`, so the typestate checker (section 5a) enforces consumption and
// construction: an illegal step is a type error, and the state is never
// stored — a handle is the data record, or one byte the backend never
// reads. The dynamic projection (section 2) is untouched; both are built
// from the same lines.
func (m *protocolMachine) staticProjection() ([]ast.Statement, typechecker.ResourceProtocolDeclaration) {
	ctx := m.decl.Name.Token.SemanticContext
	s := newSynth(helperContext(ctx, m.name+"Static"))
	prefix := snakeCase(m.name)
	dataType := m.name + "Data"
	withData := m.decl.Data != nil
	exported := m.decl.Exported
	marker := func(state string) string { return m.name + state }
	handleAt := func(state string) ast.Expression { return s.app(m.name, s.id(marker(state))) }

	var out []ast.Statement
	for _, state := range m.states {
		src := fmt.Sprintf("%s: type = struct { %s_: u8 }\n", marker(state), snakeCase(state))
		p := parser.New(layout.New(scanner.New(src)))
		program := p.ParseProgram()
		if len(p.Errors()) != 0 || program == nil || len(program.Statements) != 1 {
			continue
		}
		if adt, isADT := program.Statements[0].(*ast.ADTType); isADT {
			adt.Exported = exported
		}
		out = append(out, program.Statements[0])
	}
	var handle *ast.ADTType
	if withData {
		handle = s.recordType(m.name, []string{"S"}, s.set("data", s.id(dataType)))
	} else {
		handle = s.recordType(m.name, []string{"S"}, s.set("at_", s.id("u8")))
	}
	handle.Exported = exported
	out = append(out, handle)

	fresh := func(data ast.Expression) ast.Expression {
		if withData {
			return s.record(m.name, s.set("data", data))
		}
		return s.record(m.name, s.set("at_", s.u8(0)))
	}
	start := s.fnExpr(prefix+"_handle", nil, handleAt(m.initial), fresh(s.call(prefix+"_initial_data")))
	start.Exported = exported
	out = append(out, start)

	// The checker matches a handle's type index against the protocol's
	// state names, so the facts speak in marker names.
	facts := typechecker.ResourceProtocolDeclaration{
		Name:          m.name,
		ResourceTypes: []string{m.name},
		Initial:       marker(m.initial),
	}
	for _, state := range m.states {
		facts.States = append(facts.States, marker(state))
	}
	// The construction at the initial state returns fresh authority: the
	// handle it hands out is tracked from there.
	facts.Transitions = append(facts.Transitions, typechecker.ResourceTransitionDeclaration{
		Name: "handle@" + m.initial, Callable: prefix + "_handle", From: marker(m.initial), To: marker(m.initial), ReturnsFresh: true,
	})
	const local = "record"
	for _, step := range m.steps {
		for _, line := range step.lines {
			name := prefix + "_" + snakeCase(step.name)
			if len(step.lines) > 1 {
				name += "_from_" + snakeCase(line.From.Value)
			}
			params := []*ast.FunctionParameter{s.param("handle", handleAt(line.From.Value))}
			if step.payload != nil {
				params = append(params, s.param(step.payload.Name.Value, cloneExpression(step.payload.Type)))
			}
			// The line's effects run on a copy of the record, as in
			// name_next; the guard reads the same copy.
			var body []ast.Statement
			var next ast.Expression
			if withData {
				body = append(body, s.decl(local, s.id(dataType), s.field(s.id("handle"), "data")))
				if line.Effects != nil {
					cloned := cloneSyntax(reflect.ValueOf(line.Effects)).Interface().(*ast.BlockStatement)
					m.rewriteQuantifiers(cloned, prefix, s)
					effects := renameIdentifier(cloned, "data", local).(*ast.BlockStatement)
					body = append(body, effects.Statements...)
				}
				next = fresh(s.id(local))
			} else {
				next = fresh(nil)
			}
			var fn *ast.FunctionStatement
			if line.Guard == nil {
				fn = s.fn(name, params, handleAt(line.To.Value), append(body, s.expr(next))...)
			} else {
				guard := &ast.ExpressionStatement{Expression: cloneExpression(line.Guard)}
				m.rewriteQuantifiers(guard, prefix, s)
				condition := renameIdentifier(guard.Expression, "data", local).(ast.Expression)
				// A guarded line's outcome is its own sum type, so the
				// projection depends on no prelude: Moved carries the handle
				// at the target state, Refused hands the consumed handle back.
				outcomeName := m.name + variantName(step.name)
				if len(step.lines) > 1 {
					outcomeName += "From" + line.From.Value
				}
				outcomeName += "Outcome"
				outcome := &ast.ADTType{Token: s.tok(0, "type"), EndToken: s.tok(0, ""), Name: s.id(outcomeName), Exported: exported, Variants: []*ast.ADTVariant{
					{Token: s.tok(0, "Moved"), Name: s.id("Moved"), Payload: handleAt(line.To.Value)},
					{Token: s.tok(0, "Refused"), Name: s.id("Refused"), Payload: handleAt(line.From.Value)},
				}}
				out = append(out, outcome)
				var accepted []ast.Statement
				if withData {
					accepted = body[1:]
				}
				accepted = append(accepted, s.expr(s.variant("Moved", next)))
				var head []ast.Statement
				if withData {
					head = body[:1]
				}
				fn = s.fn(name, params, s.id(outcomeName), append(head, s.expr(s.cond(condition, s.block(accepted...), s.block(s.expr(s.variant("Refused", s.id("handle")))))))...)
			}
			fn.Exported = exported
			out = append(out, fn)
			// The result — the handle, or the outcome sum carrying it in
			// either variant — is the consumed handle under a new name.
			facts.Transitions = append(facts.Transitions, typechecker.ResourceTransitionDeclaration{
				Name: step.name + "@" + line.From.Value, Callable: name, From: marker(line.From.Value), To: marker(line.To.Value),
				Parameters:   []typechecker.ResourceParameterDeclaration{{Index: 0, Mode: typechecker.ResourceParameterConsumed}},
				ReturnsAlias: true, AliasesArgument: 0,
			})
		}
	}
	return out, facts
}
