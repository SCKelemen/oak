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
// as a `NameStepOutcome` sum, one variant per target state and `Refused`
// with the handle handed back, when the group of lines from that state has
// a guard. The transitions are registered as a resource protocol over
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
		Name:                     m.name,
		ResourceTypes:            []string{m.name},
		Initial:                  marker(m.initial),
		TypestateArity:           1,
		SealedInitialConstructor: prefix + "_handle",
	}
	for _, state := range m.states {
		facts.States = append(facts.States, marker(state))
	}
	// The construction at the initial state returns fresh authority: the
	// handle it hands out is tracked from there.
	facts.Transitions = append(facts.Transitions, typechecker.ResourceTransitionDeclaration{
		Name: "handle@" + m.initial, Callable: prefix + "_handle", From: marker(m.initial), To: marker(m.initial), ReturnsFresh: true,
	})
	const local = "oak_record"
	for _, step := range m.steps {
		// The lines of a step are grouped by source state: one function per
		// group, trying the group's lines in declaration order as name_next
		// does. A group of one unguarded line returns the handle at its
		// target; any other group returns an outcome sum with one variant
		// per target state reached before the first unguarded line, and
		// Refused when no line is unguarded.
		var sources []string
		groups := map[string][]*ast.ProtocolTransition{}
		for _, line := range step.lines {
			from := line.From.Value
			if _, seen := groups[from]; !seen {
				sources = append(sources, from)
			}
			groups[from] = append(groups[from], line)
		}
		for _, from := range sources {
			lines := groups[from]
			name := prefix + "_" + snakeCase(step.name)
			if len(sources) > 1 {
				name += "_from_" + snakeCase(from)
			}
			params := []*ast.FunctionParameter{s.param("handle", handleAt(from))}
			if step.payload != nil {
				params = append(params, s.param(step.payload.Name.Value, cloneExpression(step.payload.Type)))
			}
			// The lines that can apply: up to and including the first
			// unguarded one.
			var applicable []*ast.ProtocolTransition
			catchAll := false
			for _, line := range lines {
				applicable = append(applicable, line)
				if m.lineGuard(s, line) == nil {
					catchAll = true
					break
				}
			}
			var targets []string
			seenTarget := map[string]bool{}
			for _, line := range applicable {
				if !seenTarget[line.To.Value] {
					seenTarget[line.To.Value] = true
					targets = append(targets, line.To.Value)
				}
			}
			// The effects of a line run on a copy of the record, as in
			// name_next; a guard reads the same copy.
			moved := func(line *ast.ProtocolTransition) []ast.Statement {
				var body []ast.Statement
				if withData && line.Effects != nil {
					cloned := cloneSyntax(reflect.ValueOf(line.Effects)).Interface().(*ast.BlockStatement)
					m.rewriteQuantifiers(cloned, prefix, s)
					effects := renameIdentifier(cloned, "data", local).(*ast.BlockStatement)
					body = append(body, effects.Statements...)
				}
				return body
			}
			var head []ast.Statement
			if withData {
				head = append(head, s.decl(local, s.id(dataType), s.field(s.id("handle"), "data")))
			}
			next := func() ast.Expression {
				if withData {
					return fresh(s.id(local))
				}
				return fresh(nil)
			}
			var fn *ast.FunctionStatement
			if len(applicable) == 1 && catchAll {
				body := append(head, moved(applicable[0])...)
				fn = s.fn(name, params, handleAt(applicable[0].To.Value), append(body, s.expr(next()))...)
			} else {
				outcomeName := m.name + variantName(step.name)
				if len(sources) > 1 {
					outcomeName += "From" + from
				}
				outcomeName += "Outcome"
				outcome := &ast.ADTType{Token: s.tok(0, "type"), EndToken: s.tok(0, ""), Name: s.id(outcomeName), Exported: exported}
				// Variants are spelled To<State>: a bare state name would
				// collide with NameState's variants, which the interpreter and
				// the checker resolve by variant name.
				for _, target := range targets {
					outcome.Variants = append(outcome.Variants, &ast.ADTVariant{Token: s.tok(0, "To"+target), Name: s.id("To" + target), Payload: handleAt(target)})
				}
				if !catchAll {
					outcome.Variants = append(outcome.Variants, &ast.ADTVariant{Token: s.tok(0, "Refused"), Name: s.id("Refused"), Payload: handleAt(from)})
				}
				out = append(out, outcome)
				// Nested conditionals in line order; the refusal is the last
				// alternative.
				var result ast.Expression = s.variant("Refused", s.id("handle"))
				for i := len(applicable) - 1; i >= 0; i-- {
					line := applicable[i]
					arm := s.block(append(moved(line), s.expr(s.variant("To"+line.To.Value, next())))...)
					effective := m.lineGuard(s, line)
					if effective == nil {
						result = arm
						continue
					}
					guard := &ast.ExpressionStatement{Expression: effective}
					m.rewriteQuantifiers(guard, prefix, s)
					condition := renameIdentifier(guard.Expression, "data", local).(ast.Expression)
					var otherwise ast.Expression = result
					if block, isBlock := otherwise.(*ast.BlockExpression); isBlock {
						result = s.cond(condition, arm, block)
					} else {
						result = s.cond(condition, arm, s.block(s.expr(otherwise)))
					}
				}
				fn = s.fn(name, params, s.id(outcomeName), append(head, s.expr(result))...)
			}
			fn.Exported = exported
			out = append(out, fn)
			// One fact per target state: the same callable, the same
			// semantics, so the checker's target set is the union.
			for _, target := range targets {
				facts.Transitions = append(facts.Transitions, typechecker.ResourceTransitionDeclaration{
					Name: step.name + "@" + from + ">" + target, Callable: name, From: marker(from), To: marker(target),
					Parameters:   []typechecker.ResourceParameterDeclaration{{Index: 0, Mode: typechecker.ResourceParameterConsumed}},
					ReturnsAlias: true, AliasesArgument: 0,
				})
			}
		}
	}
	return out, facts
}
