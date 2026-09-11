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
// no source syntax: frontends/protocol lowering can describe call-local
// authority modes, permanent consumption, and fresh result authority.
type ResourceOperation struct {
	Parameters   []ResourceParameterDeclaration
	Consumes     []int
	ReturnsFresh bool
}

// ResourceModel is the syntax-independent bridge from resolved types/callables
// to resource-flow analysis. ResourceTypes contains nominal source type names;
// Operations contains semantic resource operations by resolved callable name.
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
	normalized, err := normalizeResourceOperation(operation)
	if err != nil {
		// Keep malformed input for the checking entry point to diagnose. Never
		// silently replace a conflicting contract with an empty operation.
		operation.Parameters = append([]ResourceParameterDeclaration(nil), operation.Parameters...)
		operation.Consumes = append([]int(nil), operation.Consumes...)
		m.Operations[name] = operation
		return
	}
	m.Operations[name] = normalized
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
	// Normalize here too: callers can populate Operations without MarkOperation.
	normalized := NewResourceModel()
	normalized.ResourceTypes = model.ResourceTypes
	names := make([]string, 0, len(model.Operations))
	for name := range model.Operations {
		names = append(names, name)
	}
	sort.Strings(names)
	for _, name := range names {
		op, err := normalizeResourceOperation(model.Operations[name])
		if err != nil {
			tc.addResourceDiagnosticWithCode(nil, CodeResourceCallAliasConflict,
				fmt.Sprintf("invalid resource contract for %q: %v", name, err))
			return
		}
		normalized.Operations[name] = op
	}
	model = normalized
	for _, statement := range program.Statements {
		fn, ok := statement.(*ast.FunctionStatement)
		if !ok || fn == nil || fn.ExternSymbol != "" {
			continue
		}
		analysis := &typedResourceAnalysis{
			tc:                tc,
			model:             model,
			flow:              resourceflow.New(),
			reported:          make(map[string]bool),
			unknownResources:  make(map[string]bool),
			entryModes:        make(map[string]entryAuthority),
			callableContracts: make(map[string]string),
			unknownCallables:  make(map[string]bool),
		}
		analysis.pushScope()
		if fn.Receiver != nil && fn.Receiver.Name != nil {
			analysis.bind(fn.Receiver.Name.Value)
			if model.isResourceType(fn.Receiver.Type) {
				analysis.flow.Register(fn.Receiver.Name.Value, fn.Receiver.Name)
			}
		}
		// The function's own contract fixes what its body may do with each
		// resource parameter (callee-entry authority, docs/spec/50-borrowing.md
		// section 9): a borrowed parameter enters with shared authority, a
		// borrowed-mut one with mutable authority, a consumed one with full
		// authority. Unmarked parameters keep their ordinary meaning.
		own, hasContract := analysis.contractOperation(functionIdentity(fn))
		for index, parameter := range fn.Parameters {
			if parameter == nil || parameter.Name == nil {
				continue
			}
			analysis.bind(parameter.Name.Value)
			if _, isCallable := parameter.Type.(*ast.FunctionTypeExpression); isCallable {
				// A function-typed parameter arrives without a contract.
				analysis.unknownCallables[parameter.Name.Value] = true
			}
			if model.isResourceType(parameter.Type) {
				analysis.flow.Register(parameter.Name.Value, parameter.Name)
				if hasContract {
					if mode := own.parameterMode(index); mode != ResourceParameterUnspecified {
						analysis.entryModes[parameter.Name.Value] = entryAuthority{mode: mode, declaration: parameter.Name}
					}
				}
			}
		}
		analysis.expression(fn.Body)
		analysis.checkRetainedReturn(fn)
	}
}

// bindCallable records what a function-valued binding may be called as: a
// global function's identity when initialized from that function (its
// contract travels with the value), unknown when the initializer is a
// closure, a parameter, another unknown callable, or a call result.
func (a *typedResourceAnalysis) bindCallable(stmt *ast.VariableDeclaration) {
	_, declaredCallable := stmt.Type.(*ast.FunctionTypeExpression)
	if source, ok := stmt.Value.(*ast.Identifier); ok && source != nil {
		if a.isLocalBinding(source.Value) {
			if global, carried := a.callableContracts[source.Value]; carried {
				a.callableContracts[stmt.Name.Value] = global
				return
			}
			if a.unknownCallables[source.Value] {
				a.unknownCallables[stmt.Name.Value] = true
			}
			return
		}
		if a.tc != nil && a.tc.globalEnv != nil {
			if typ, exists := a.tc.globalEnv.GetType(source.Value); exists {
				if _, isFunction := typ.(*FunctionType); isFunction {
					a.callableContracts[stmt.Name.Value] = source.Value
					return
				}
			}
		}
	}
	if _, isClosure := stmt.Value.(*ast.FunctionLiteral); isClosure || declaredCallable {
		a.unknownCallables[stmt.Name.Value] = true
	}
}

// tailIdentifiers collects the identifiers an expression may evaluate to
// as a function's result: the expression itself, the last statement of a
// block, and every arm of a match. Calls and literals contribute nothing
// (their results are checked where they are built).
func tailIdentifiers(expr ast.Expression) []*ast.Identifier {
	switch e := expr.(type) {
	case *ast.Identifier:
		return []*ast.Identifier{e}
	case *ast.BlockExpression:
		if e.Block == nil || len(e.Block.Statements) == 0 {
			return nil
		}
		if last, ok := e.Block.Statements[len(e.Block.Statements)-1].(*ast.ExpressionStatement); ok {
			return tailIdentifiers(last.Expression)
		}
	case *ast.MatchExpression:
		var out []*ast.Identifier
		for _, arm := range e.Arms {
			if arm != nil {
				out = append(out, tailIdentifiers(arm.Body)...)
			}
		}
		return out
	}
	return nil
}

// checkRetainedReturn rejects a body that returns a borrowed or
// borrowed-mut parameter (or an alias of one) as its result: the caller
// keeps custody of a borrowed resource, so handing it back would mint a
// second authority over the same resource (OAK-B0114, retention).
func (a *typedResourceAnalysis) checkRetainedReturn(fn *ast.FunctionStatement) {
	if len(a.entryModes) == 0 || fn == nil || fn.Body == nil {
		return
	}
	for _, ident := range tailIdentifiers(fn.Body) {
		a.checkRetention(ident, "returned as this function's result")
	}
}

// checkRetention reports a borrowed or borrowed-mut parameter (or alias)
// being retained — returned, or stored in an aggregate — beyond the call
// that lent it.
func (a *typedResourceAnalysis) checkRetention(ident *ast.Identifier, how string) {
	if ident == nil || !a.flow.Registered(ident.Value) {
		return
	}
	parameter, entry, governed := a.entryAuthorityOf(ident.Value)
	if !governed || entry.mode == ResourceParameterConsumed {
		return
	}
	title := fmt.Sprintf("parameter %q enters with %s authority and cannot be %s: a borrowed resource stays in the caller's custody", parameter, entry.mode, how)
	d := a.tc.addResourceDiagnosticWithCode(ident, CodeResourceParameterForwarded, title)
	if entry.declaration != nil {
		d.AddSecondary(diagnostic.NodeToRange(entry.declaration), fmt.Sprintf("%q is declared %s by this function's resource contract", parameter, entry.mode))
	}
	if parameter != ident.Value {
		for _, edge := range a.flow.AliasPath(parameter, ident.Value) {
			message := fmt.Sprintf("resource alias %q derives authority from %q", edge.Child, edge.Parent)
			if edge.Origin != nil {
				d.AddSecondary(diagnostic.NodeToRange(edge.Origin), message)
			} else {
				d.AddNote(message)
			}
		}
	}
	d.AddNote("only a consumed parameter may be returned or stored: consumption transfers custody, borrowing never does (docs/spec/50-borrowing.md section 9)")
	d.AddHelp("declare the parameter consumed in this function's contract, or return a fresh resource from a consuming operation")
}

type typedResourceAnalysis struct {
	tc               *TypeChecker
	model            ResourceModel
	flow             *resourceflow.Flow
	reported         map[string]bool
	unknownResources map[string]bool
	scopes           []map[string]struct{}
	freshCalls       map[*ast.InvocationExpression]bool
	// entryModes records, per resource parameter of the function under
	// analysis, the authority its own contract grants on entry.
	entryModes map[string]entryAuthority
	// callableContracts maps a local function-value binding to the global
	// function it was initialized from, whose contract calls through the
	// binding carry; unknownCallables marks function-typed bindings whose
	// contract cannot be known (parameters, closures, reassigned values).
	callableContracts map[string]string
	unknownCallables  map[string]bool
}

// entryAuthority is a resource parameter's contract mode together with the
// declaration that diagnostics point back to.
type entryAuthority struct {
	mode        ResourceParameterMode
	declaration ast.Node
}

// functionIdentity names a function the way callableIdentity names its
// calls: the bare name for a top-level function, Receiver::name for a
// method.
func functionIdentity(fn *ast.FunctionStatement) string {
	if fn == nil || fn.Name == nil {
		return ""
	}
	if fn.Receiver != nil {
		if receiver, ok := fn.Receiver.Type.(*ast.Identifier); ok && receiver != nil {
			return receiver.Value + "::" + fn.Name.Value
		}
	}
	return fn.Name.Value
}

// parameterMode is the normalized mode of one parameter of an operation:
// the declared mode, or consumed for an index listed in Consumes.
func (op ResourceOperation) parameterMode(index int) ResourceParameterMode {
	for _, declaration := range op.Parameters {
		if declaration.Index == index && declaration.Mode != ResourceParameterUnspecified {
			return declaration.Mode
		}
	}
	for _, consumed := range op.Consumes {
		if consumed == index {
			return ResourceParameterConsumed
		}
	}
	return ResourceParameterUnspecified
}

// authorityRank orders the modes by what they permit: shared < mutable <
// full. Forwarding is legal only when the callee asks for no more than the
// caller-side parameter entered with.
func authorityRank(mode ResourceParameterMode) int {
	switch mode {
	case ResourceParameterBorrowed:
		return 1
	case ResourceParameterBorrowedMut:
		return 2
	case ResourceParameterConsumed:
		return 3
	}
	return 0
}

// entryAuthorityOf finds the contract mode governing an argument: the
// argument's own parameter, or the mode-marked parameter it aliases.
func (a *typedResourceAnalysis) entryAuthorityOf(name string) (string, entryAuthority, bool) {
	if authority, direct := a.entryModes[name]; direct {
		return name, authority, true
	}
	names := make([]string, 0, len(a.entryModes))
	for parameter := range a.entryModes {
		names = append(names, parameter)
	}
	sort.Strings(names)
	for _, parameter := range names {
		if a.flow.Aliases(name, parameter) {
			return parameter, a.entryModes[parameter], true
		}
	}
	return "", entryAuthority{}, false
}

// checkParameterForwarding rejects a call that forwards one of the
// function's own resource parameters beyond its entry authority
// (OAK-B0114): a borrowed parameter to a borrowed-mut or consuming
// position, a borrowed-mut parameter to a consuming position. It reports
// every offending argument and returns false when any was found, so the
// call neither consumes nor establishes fresh authority.
func (a *typedResourceAnalysis) checkParameterForwarding(expr *ast.InvocationExpression, op ResourceOperation) bool {
	if len(a.entryModes) == 0 {
		return true
	}
	ok := true
	for index, argument := range expr.Arguments {
		ident, isIdent := argument.(*ast.Identifier)
		if !isIdent || ident == nil || !a.flow.Registered(ident.Value) {
			continue
		}
		required := op.parameterMode(index)
		if required == ResourceParameterUnspecified {
			continue
		}
		parameter, entry, governed := a.entryAuthorityOf(ident.Value)
		if !governed || authorityRank(required) <= authorityRank(entry.mode) {
			continue
		}
		ok = false
		callee, _ := a.callableIdentity(expr)
		title := fmt.Sprintf("parameter %q enters with %s authority and cannot be passed to the %s parameter of %s", parameter, entry.mode, required, callee)
		d := a.tc.addResourceDiagnosticWithCode(argument, CodeResourceParameterForwarded, title)
		if entry.declaration != nil {
			d.AddSecondary(diagnostic.NodeToRange(entry.declaration), fmt.Sprintf("%q is declared %s by this function's resource contract", parameter, entry.mode))
		}
		if parameter != ident.Value {
			for _, edge := range a.flow.AliasPath(parameter, ident.Value) {
				message := fmt.Sprintf("resource alias %q derives authority from %q", edge.Child, edge.Parent)
				if edge.Origin != nil {
					d.AddSecondary(diagnostic.NodeToRange(edge.Origin), message)
				} else {
					d.AddNote(message)
				}
			}
		}
		switch entry.mode {
		case ResourceParameterBorrowed:
			d.AddNote("a borrowed parameter permits shared use only: it can neither be mutated through a borrowed-mut contract nor consumed (docs/spec/50-borrowing.md section 9)")
		case ResourceParameterBorrowedMut:
			d.AddNote("a borrowed-mut parameter permits mutation for the duration of the call but never permanent custody: it cannot be consumed (docs/spec/50-borrowing.md section 9)")
		}
		d.AddHelp("declare the parameter with the stronger mode in this function's contract, or have the caller perform the operation")
	}
	return ok
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

func (m ResourceModel) operationByName(name string) (ResourceOperation, bool) {
	if name == "" {
		return ResourceOperation{}, false
	}
	op, exists := m.Operations[name]
	return op, exists
}

// contractOperation resolves a callable identity to its contract, falling
// back from a specialization's mangled name to the template it was
// instantiated from: a contract declared for a generic function holds for
// every specialization (docs/spec/50-borrowing.md section 9).
func (a *typedResourceAnalysis) contractOperation(identity string) (ResourceOperation, bool) {
	if op, exists := a.model.operationByName(identity); exists {
		return op, true
	}
	if a.tc != nil {
		if template, specialized := a.tc.instantiationTemplates[identity]; specialized {
			return a.model.operationByName(template)
		}
	}
	return ResourceOperation{}, false
}

func (a *typedResourceAnalysis) pushScope() {
	if a == nil {
		return
	}
	a.scopes = append(a.scopes, make(map[string]struct{}))
}

func (a *typedResourceAnalysis) popScope() {
	if a == nil || len(a.scopes) == 0 {
		return
	}
	a.scopes = a.scopes[:len(a.scopes)-1]
}

func (a *typedResourceAnalysis) bind(name string) {
	if a == nil || name == "" {
		return
	}
	if len(a.scopes) == 0 {
		a.pushScope()
	}
	a.scopes[len(a.scopes)-1][name] = struct{}{}
}

func (a *typedResourceAnalysis) isLocalBinding(name string) bool {
	if a == nil || name == "" {
		return false
	}
	for i := len(a.scopes) - 1; i >= 0; i-- {
		if _, exists := a.scopes[i][name]; exists {
			return true
		}
	}
	return false
}

func cloneResourceProvenance(source map[string]bool) map[string]bool {
	cloned := make(map[string]bool, len(source))
	for name, unknown := range source {
		if unknown {
			cloned[name] = true
		}
	}
	return cloned
}

// callableIdentity resolves a checked invocation to the semantic callable key
// used by ResourceModel. Direct calls must still denote a global function after
// lexical shadowing; method calls use the checked receiver type and the same
// Receiver::method key as the type environment. No resource rule is inferred
// from source spelling alone.
func (a *typedResourceAnalysis) callableIdentity(expr *ast.InvocationExpression) (string, bool) {
	if a == nil || a.tc == nil || a.tc.globalEnv == nil || expr == nil {
		return "", false
	}
	switch function := expr.Function.(type) {
	case *ast.Identifier:
		if function == nil || function.Value == "" {
			return "", false
		}
		if a.isLocalBinding(function.Value) {
			// A local function value carries the contract of the global it
			// was initialized from, and nothing else.
			if global, carried := a.callableContracts[function.Value]; carried {
				return global, true
			}
			return "", false
		}
		typ, exists := a.tc.globalEnv.GetType(function.Value)
		if !exists || typ == nil {
			return "", false
		}
		if _, ok := typ.(*FunctionType); !ok {
			return "", false
		}
		return function.Value, true

	case *ast.IndexExpression:
		if function == nil || !function.Dot {
			return "", false
		}
		method, ok := function.Index.(*ast.Identifier)
		if !ok || method == nil || method.Value == "" {
			return "", false
		}
		receiverType := a.tc.env.CheckedExpressionType(function.Left)
		receiverName := nominalTypeName(receiverType)
		if receiverName == "" {
			return "", false
		}
		key := receiverName + "::" + method.Value
		typ, exists := a.tc.globalEnv.GetType(key)
		if !exists || typ == nil {
			return "", false
		}
		if _, ok := typ.(*FunctionType); !ok {
			return "", false
		}
		return key, true
	}
	return "", false
}

func (a *typedResourceAnalysis) operation(expr *ast.InvocationExpression) (ResourceOperation, bool) {
	identity, ok := a.callableIdentity(expr)
	if !ok {
		return ResourceOperation{}, false
	}
	return a.contractOperation(identity)
}

// checkUnknownCallable fails closed when a resource is passed through a
// callable whose contract is unknown (OAK-B0115): a function-typed
// parameter, a closure, or a reassigned function value. An unknown
// contract is not an empty effect set.
func (a *typedResourceAnalysis) checkUnknownCallable(expr *ast.InvocationExpression) bool {
	callee, isIdent := expr.Function.(*ast.Identifier)
	if !isIdent || callee == nil || !a.unknownCallables[callee.Value] {
		return true
	}
	for _, argument := range expr.Arguments {
		if !a.isResourceValue(argument) {
			continue
		}
		d := a.tc.addResourceDiagnosticWithCode(argument, CodeResourceUnknownCallable,
			fmt.Sprintf("resource passed through %q, a callable whose resource contract is unknown", callee.Value))
		d.AddNote("a function-typed parameter, a closure, or a reassigned function value has no checked contract; an unknown contract is not an empty one (docs/spec/50-borrowing.md section 9)")
		d.AddHelp("call the operation by its global name, or bind the function value directly from the global function so its contract is carried")
		return false
	}
	return true
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
		if s.Name != nil {
			if _, carried := a.callableContracts[s.Name.Value]; carried || a.unknownCallables[s.Name.Value] {
				// A reassigned function value has no single contract.
				delete(a.callableContracts, s.Name.Value)
				a.unknownCallables[s.Name.Value] = true
			}
		}
		if a.isResourceValue(s.Value) || (s.Name != nil && (a.flow.Registered(s.Name.Value) || a.unknownResources[s.Name.Value])) {
			a.tc.addResourceDiagnosticWithCode(s, CodeResourceCallAliasConflict,
				"resource reassignment requires tracked destination provenance")
		}
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
	incomingProvenance := cloneResourceProvenance(a.unknownResources)
	a.pushScope()
	defer func() {
		a.popScope()
		a.unknownResources = incomingProvenance
	}()
	for _, stmt := range block.Statements {
		a.statement(stmt)
	}
}

func (a *typedResourceAnalysis) variable(stmt *ast.VariableDeclaration) {
	if stmt == nil || stmt.Name == nil {
		return
	}
	// The declaration becomes visible only after its initializer has been
	// evaluated, so a local with the same name as a global callable does not
	// retroactively shadow that callable inside its own initializer.
	defer a.bind(stmt.Name.Value)
	if stmt.Value != nil {
		a.expression(stmt.Value)
	}
	a.bindCallable(stmt)

	fresh := false
	if call, ok := stmt.Value.(*ast.InvocationExpression); ok {
		if a.freshCalls[call] {
			fresh = true
		}
	}
	isResource := a.model.isResourceType(stmt.Type) || fresh
	if !isResource {
		return
	}

	if source, ok := stmt.Value.(*ast.Identifier); ok {
		if a.flow.Registered(source.Value) {
			if a.flow.CanUse(source.Value) {
				a.flow.Alias(stmt.Name.Value, source.Value, stmt.Name)
			}
			return
		}
		if a.unknownResources[source.Value] {
			a.unknownResources[stmt.Name.Value] = true
			return
		}
	}

	if fresh {
		// Only an explicit semantic fresh-return fact introduces a new authority
		// class for an initialized local resource. This is never revival of an
		// input resource consumed by the operation.
		a.flow.Register(stmt.Name.Value, stmt.Name)
		return
	}

	if stmt.Value != nil && a.isResourceValue(stmt.Value) {
		// A projection or other resource-valued expression without a tracked
		// authority source is not fresh merely because it receives a new name.
		// Preserve unknown provenance so a later exclusive/consuming call fails
		// closed instead of synthesizing a distinct authority class.
		a.unknownResources[stmt.Name.Value] = true
		return
	}

	// An uninitialized resource binding is an independent local authority root.
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
				if ident, isIdent := field.Value.(*ast.Identifier); isIdent {
					a.checkRetention(ident, "stored in a record")
				}
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
			if ident, isIdent := element.(*ast.Identifier); isIdent {
				a.checkRetention(ident, "stored in an array")
			}
		}
	case *ast.MatchExpression:
		a.match(e)
	case *ast.VariantExpression:
		a.expression(e.Payload)
	case *ast.FunctionLiteral:
		// Capturing resource closures are rejected by the existing closure
		// discipline. Analyze the body independently so local resource uses
		// are still checked without lending outer authority to the closure.
		outerFlow := a.flow
		outerScopes := a.scopes
		outerUnknown := a.unknownResources
		a.flow = resourceflow.New()
		a.scopes = nil
		a.unknownResources = make(map[string]bool)
		a.pushScope()
		for _, argument := range e.Arguments {
			if argument != nil {
				a.bind(argument.Value)
			}
		}
		a.block(e.Body)
		a.flow = outerFlow
		a.scopes = outerScopes
		a.unknownResources = outerUnknown
	}
}

func (a *typedResourceAnalysis) invocation(expr *ast.InvocationExpression) {
	if expr == nil {
		return
	}
	if a.freshCalls == nil {
		a.freshCalls = make(map[*ast.InvocationExpression]bool)
	}
	delete(a.freshCalls, expr)
	diagnosticsBefore := len(a.tc.Diagnostics())
	// The callee identifier is not a resource value. Non-identifier callees
	// may themselves evaluate expressions, so preserve their effects.
	if _, simple := expr.Function.(*ast.Identifier); !simple {
		a.expression(expr.Function)
	}
	for _, argument := range expr.Arguments {
		a.expression(argument)
	}
	if !a.checkUnknownCallable(expr) {
		return
	}

	op, present := a.operation(expr)
	if !present {
		return
	}
	// Call-local resource modes are checked after ordinary argument uses and
	// before permanent consumption. Invalid calls therefore do not mutate
	// authority state and cannot create cascading use-after-consume errors.
	if len(a.tc.Diagnostics()) != diagnosticsBefore || !a.checkCallResourceExclusivity(expr, op) {
		return
	}
	if !a.checkParameterForwarding(expr, op) {
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
	a.freshCalls[expr] = op.ReturnsFresh
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
	d := a.tc.addResourceDiagnostic(node, title)
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
