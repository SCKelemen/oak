package typechecker

import (
	"fmt"
	"sort"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/diagnostic"
	"github.com/SCKelemen/oak/resourceflow"
)

// CodeResourceUsedAfterConsume is shared semantically with the borrow checker.
// It lives here too because typechecker must not import borrowchecker (the
// borrow checker already depends on typechecker).
const CodeResourceUsedAfterConsume = "OAK-B0111"

// ResourceOperation is internal semantic metadata for a callable. It freezes
// no source syntax: frontends/protocol lowering can mark which arguments lose
// old authority, and whether the result denotes fresh authority.
type ResourceOperation struct {
	Consumes    []int
	ReturnsFresh bool
}

// ResourceModel is the syntax-independent bridge from resolved types/callables
// to resource-flow analysis. ResourceTypes contains nominal source type names;
// Operations contains semantic consuming operations by resolved callable name.
type ResourceModel struct {
	ResourceTypes map[string]bool
	Operations    map[string]ResourceOperation
}

func NewResourceModel() ResourceModel {
	return ResourceModel{
		ResourceTypes: make(map[string]bool),
		Operations:    make(map[string]ResourceOperation),
	}
}

func (m *ResourceModel) MarkResourceType(name string) {
	if m.ResourceTypes == nil {
		m.ResourceTypes = make(map[string]bool)
	}
	m.ResourceTypes[name] = true
}

func (m *ResourceModel) MarkOperation(name string, operation ResourceOperation) {
	if m.Operations == nil {
		m.Operations = make(map[string]ResourceOperation)
	}
	copyOperation := operation
	copyOperation.Consumes = append([]int(nil), operation.Consumes...)
	m.Operations[name] = copyOperation
}

// CheckProgramWithResources is the integrated typed-program entrypoint for the
// internal resource protocol model. Existing CheckProgram remains unchanged
// until Oak freezes how source declarations opt into resource semantics.
func (tc *TypeChecker) CheckProgramWithResources(program *ast.Program, model ResourceModel) {
	tc.CheckProgram(program)
	tc.CheckResourceFlow(program, model)
}

// CheckResourceFlow runs path-sensitive authority analysis over an already
// typed AST. Each function has independent authority; no resource state leaks
// between function bodies.
func (tc *TypeChecker) CheckResourceFlow(program *ast.Program, model ResourceModel) {
	if tc == nil || program == nil {
		return
	}
	for _, statement := range program.Statements {
		fn, ok := statement.(*ast.FunctionStatement)
		if !ok || fn == nil || fn.ExternSymbol != "" {
			continue
		}
		analysis := &typedResourceAnalysis{
			tc:       tc,
			model:    model,
			flow:     resourceflow.New(),
			reported: make(map[string]bool),
		}
		if fn.Receiver != nil && fn.Receiver.Name != nil && model.isResourceType(fn.Receiver.Type) {
			analysis.flow.Register(fn.Receiver.Name.Value, fn.Receiver.Name)
		}
		for _, parameter := range fn.Parameters {
			if parameter != nil && parameter.Name != nil && model.isResourceType(parameter.Type) {
				analysis.flow.Register(parameter.Name.Value, parameter.Name)
			}
		}
		analysis.expression(fn.Body)
	}
}

type typedResourceAnalysis struct {
	tc       *TypeChecker
	model    ResourceModel
	flow     *resourceflow.Flow
	reported map[string]bool
}

func (m ResourceModel) isResourceType(expr ast.Expression) bool {
	if expr == nil {
		return false
	}
	switch t := expr.(type) {
	case *ast.Identifier:
		return m.ResourceTypes[t.Value]
	case *ast.IndexExpression:
		// Generic nominal applications retain the nominal base in Left.
		if ident, ok := t.Left.(*ast.Identifier); ok {
			return m.ResourceTypes[ident.Value]
		}
	}
	return m.ResourceTypes[expr.String()]
}

func (m ResourceModel) operation(expr ast.Expression) (ResourceOperation, bool) {
	ident, ok := expr.(*ast.Identifier)
	if !ok || ident == nil {
		return ResourceOperation{}, false
	}
	op, exists := m.Operations[ident.Value]
	return op, exists
}

func (a *typedResourceAnalysis) statement(stmt ast.Statement) {
	if stmt == nil {
		return
	}
	switch s := stmt.(type) {
	case *ast.VariableDeclaration:
		a.variable(s)
	case *ast.AssignmentStatement:
		a.expression(s.Value)
	case *ast.IndexAssignmentStatement:
		if s.Target != nil {
			a.expression(s.Target.Left)
			if !s.Target.Dot {
				a.expression(s.Target.Index)
			}
		}
		a.expression(s.Value)
	case *ast.ExpressionStatement:
		a.expression(s.Expression)
	case *ast.BlockStatement:
		a.block(s)
	case *ast.IfStatement:
		a.ifStatement(s)
	case *ast.WhileStatement:
		a.whileStatement(s)
	}
}

func (a *typedResourceAnalysis) block(block *ast.BlockStatement) {
	if block == nil {
		return
	}
	for _, stmt := range block.Statements {
		a.statement(stmt)
	}
}

func (a *typedResourceAnalysis) variable(stmt *ast.VariableDeclaration) {
	if stmt == nil || stmt.Name == nil {
		return
	}
	if stmt.Value != nil {
		a.expression(stmt.Value)
	}
	isResource := a.model.isResourceType(stmt.Type)
	if !isResource {
		if call, ok := stmt.Value.(*ast.InvocationExpression); ok {
			if op, exists := a.model.operation(call.Function); exists && op.ReturnsFresh {
				isResource = true
			}
		}
	}
	if !isResource {
		return
	}
	if source, ok := stmt.Value.(*ast.Identifier); ok && a.flow.Registered(source.Value) {
		if a.flow.CanUse(source.Value) {
			a.flow.Alias(stmt.Name.Value, source.Value, stmt.Name)
		}
		return
	}
	// A resource-returning transition/constructor creates a new authority
	// class. This is never revival of the consumed input binding.
	a.flow.Register(stmt.Name.Value, stmt.Name)
}

func (a *typedResourceAnalysis) ifStatement(stmt *ast.IfStatement) {
	if stmt == nil {
		return
	}
	a.expression(stmt.Condition)
	incoming := a.flow.Clone()

	a.flow = incoming.Clone()
	a.block(stmt.Consequence)
	consequence := a.flow.Clone()

	a.flow = incoming.Clone()
	switch alternative := stmt.Alternative.(type) {
	case nil:
	case *ast.IfStatement:
		a.ifStatement(alternative)
	case *ast.BlockStatement:
		a.block(alternative)
	}
	alternative := a.flow.Clone()
	a.flow = resourceflow.Join(consequence, alternative)
}

func (a *typedResourceAnalysis) whileStatement(stmt *ast.WhileStatement) {
	if stmt == nil {
		return
	}
	// A loop may execute zero times, so its incoming state participates in
	// the loop-head fixed point. The lattice has height three; probing a
	// second iteration is enough to expose re-use/double-consume from a
	// first-iteration consumption and reaches the conservative fixed point.
	incoming := a.flow.Clone()

	a.flow = incoming.Clone()
	a.expression(stmt.Condition)
	a.block(stmt.Body)
	oneIteration := a.flow.Clone()

	invariant := resourceflow.Join(incoming, oneIteration)
	a.flow = invariant.Clone()
	a.expression(stmt.Condition)
	a.block(stmt.Body)
	twoIterations := a.flow.Clone()

	a.flow = resourceflow.Join(incoming, oneIteration, twoIterations)
}

func (a *typedResourceAnalysis) expression(expr ast.Expression) {
	if expr == nil {
		return
	}
	switch e := expr.(type) {
	case *ast.Identifier:
		a.use(e.Value, e)
	case *ast.PrefixExpression:
		a.expression(e.Right)
	case *ast.InfixExpression:
		a.expression(e.Left)
		if e.Operator == "&&" || e.Operator == "||" {
			incoming := a.flow.Clone()
			a.flow = incoming.Clone()
			a.expression(e.Right)
			rightEvaluated := a.flow.Clone()
			a.flow = resourceflow.Join(incoming, rightEvaluated)
			return
		}
		a.expression(e.Right)
	case *ast.InvocationExpression:
		a.invocation(e)
	case *ast.IndexExpression:
		a.expression(e.Left)
		if !e.Dot {
			a.expression(e.Index)
		}
	case *ast.SliceExpression:
		a.expression(e.Seq)
		a.expression(e.Low)
		a.expression(e.High)
	case *ast.BlockExpression:
		a.block(e.Block)
	case *ast.RecordLiteral:
		if len(e.FieldOrder) > 0 {
			for _, field := range e.FieldOrder {
				a.expression(field.Value)
			}
		} else {
			names := make([]string, 0, len(e.Fields))
			for name := range e.Fields {
				names = append(names, name)
			}
			sort.Strings(names)
			for _, name := range names {
				a.expression(e.Fields[name])
			}
		}
	case *ast.ArrayLiteral:
		for _, element := range e.Elements {
			a.expression(element)
		}
	case *ast.MatchExpression:
		a.match(e)
	case *ast.VariantExpression:
		a.expression(e.Payload)
	case *ast.FunctionLiteral:
		// Capturing resource closures are rejected by the existing closure
		// discipline. Analyze the body independently so local resource uses
		// are still checked without lending outer authority to the closure.
		outer := a.flow
		a.flow = resourceflow.New()
		a.block(e.Body)
		a.flow = outer
	}
}

func (a *typedResourceAnalysis) invocation(expr *ast.InvocationExpression) {
	if expr == nil {
		return
	}
	// The callee identifier is not a resource value. Non-identifier callees
	// may themselves evaluate expressions, so preserve their effects.
	if _, simple := expr.Function.(*ast.Identifier); !simple {
		a.expression(expr.Function)
	}
	for _, argument := range expr.Arguments {
		a.expression(argument)
	}

	op, consuming := a.model.operation(expr.Function)
	if !consuming {
		return
	}
	for _, index := range op.Consumes {
		if index < 0 || index >= len(expr.Arguments) {
			continue
		}
		ident, ok := expr.Arguments[index].(*ast.Identifier)
		if !ok || ident == nil || !a.flow.Registered(ident.Value) {
			continue
		}
		// Argument evaluation already performed the ordinary Use check. If it
		// failed, do not emit a second diagnostic for the consuming action.
		if a.flow.CanUse(ident.Value) {
			a.flow.Consume(ident.Value, expr)
		}
	}
}

func (a *typedResourceAnalysis) match(expr *ast.MatchExpression) {
	if expr == nil {
		return
	}
	a.expression(expr.Scrutinee)
	incoming := a.flow.Clone()
	branches := make([]*resourceflow.Flow, 0, len(expr.Arms))
	for _, arm := range expr.Arms {
		if arm == nil {
			continue
		}
		a.flow = incoming.Clone()
		a.expression(arm.Body)
		branches = append(branches, a.flow.Clone())
	}
	if len(branches) == 0 {
		a.flow = incoming
		return
	}
	a.flow = resourceflow.Join(branches...)
}

func (a *typedResourceAnalysis) use(name string, node ast.Node) {
	if a == nil || a.flow == nil || name == "" || !a.flow.Registered(name) || a.flow.CanUse(name) {
		return
	}
	range_ := diagnostic.NodeToRange(node)
	key := fmt.Sprintf("%s@%d:%d", name, range_.Start.Line, range_.Start.Character)
	if a.reported[key] {
		return
	}
	a.reported[key] = true

	authority, _ := a.flow.AuthorityOf(name)
	title := fmt.Sprintf("resource %q cannot be used after its authority was consumed", name)
	if authority == resourceflow.AuthorityMaybeConsumed {
		title = fmt.Sprintf("resource %q cannot be used because its authority may have been consumed", name)
	}
	d := a.tc.addTypeDiagnostic(node, CodeResourceUsedAfterConsume, title)
	consumptions := a.flow.Consumptions(name)
	for _, consumed := range consumptions {
		if consumed.Site != nil {
			d.AddSecondary(diagnostic.NodeToRange(consumed.Site),
				fmt.Sprintf("resource authority was consumed on an incoming path through %q", consumed.Name))
		}
		for _, edge := range a.flow.AliasPath(consumed.Name, name) {
			message := fmt.Sprintf("resource alias %q derives authority from %q", edge.Child, edge.Parent)
			if edge.Origin != nil {
				d.AddSecondary(diagnostic.NodeToRange(edge.Origin), message)
			} else {
				d.AddNote(message)
			}
		}
	}
	if authority == resourceflow.AuthorityMaybeConsumed {
		d.AddNote("authority is unavailable after this control-flow join because at least one reachable path consumed it")
	}
	d.AddHelp("use the fresh resource value returned by the consuming operation, if the protocol returns one")
}
