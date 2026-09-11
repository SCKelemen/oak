package typechecker

import (
	"fmt"
	"sort"
	"strings"

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
	// ReturnsAlias marks a result aliasing the argument at AliasesArgument
	// (docs/spec/50-borrowing.md section 9, result identity).
	ReturnsAlias    bool
	AliasesArgument int
	// ReturnsBorrow marks a result that is a shared borrow dependent on the
	// arguments at BorrowsArguments (docs/spec/50-borrowing.md section 9,
	// borrowed results); sorted, without duplicates.
	ReturnsBorrow    bool
	BorrowsArguments []int
	// BorrowMutable makes the borrowed result a mutable reborrow whose
	// owners are suspended while it lives.
	BorrowMutable bool
	// Terminal marks an operation whose transition enters a terminal state
	// of its protocol: it is a closer, so its own consumed parameters owe no
	// further terminal state inside its body.
	Terminal bool
	// Targets are the states the operation's transitions enter, sorted:
	// the states a typestate-indexed handle may be constructed in inside
	// its body (docs/spec/112-protocols.md section 5a).
	Targets []string
	// Receiver is the authority mode of a method's receiver, its own slot
	// beside the explicit parameters (docs/spec/50-borrowing.md section 9).
	Receiver ResourceParameterMode
	// Trusted marks the result identity as an assumption recorded from a
	// `via unsafe` line: the body is not validated against it (OAK-B0117
	// is not raised for this callable), callers reason from it unchanged.
	Trusted bool
}

// ResourceModel is the syntax-independent bridge from resolved types/callables
// to resource-flow analysis. ResourceTypes contains nominal source type names;
// Operations contains semantic resource operations by resolved callable name.
type ResourceModel struct {
	ResourceTypes map[string]bool
	Operations    map[string]ResourceOperation
	// Obligations maps a resource type to its terminal-state obligation,
	// when its protocol declares one (docs/spec/50-borrowing.md section 9).
	Obligations map[string]ResourceObligation
	// Initials maps a resource type to its protocol's initial state, the one
	// state a typestate-indexed handle may be constructed in anywhere.
	Initials map[string]string
}

// ResourceObligation is a protocol's terminal-state obligation: an owned
// resource must reach one of Terminal before its last name leaves scope;
// Closers are the callables whose transition enters a terminal state.
type ResourceObligation struct {
	Terminal []string
	Closers  []string
}

func NewResourceModel() ResourceModel {
	return ResourceModel{
		ResourceTypes: make(map[string]bool),
		Operations:    make(map[string]ResourceOperation),
		Obligations:   make(map[string]ResourceObligation),
		Initials:      make(map[string]string),
	}
}

// MarkInitial records a resource type's initial protocol state.
func (m *ResourceModel) MarkInitial(typeName, state string) {
	if m.Initials == nil {
		m.Initials = make(map[string]string)
	}
	m.Initials[typeName] = state
}

// MarkObligation records a terminal-state obligation for a resource type.
func (m *ResourceModel) MarkObligation(typeName string, obligation ResourceObligation) {
	if m.Obligations == nil {
		m.Obligations = make(map[string]ResourceObligation)
	}
	m.Obligations[typeName] = obligation
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
	normalized.ResourceTypes = tc.expandResourceTemplates(model.ResourceTypes)
	normalized.Obligations = make(map[string]ResourceObligation, len(model.Obligations))
	normalized.Initials = make(map[string]string, len(model.Initials))
	for name := range normalized.ResourceTypes {
		// Instantiations inherit their template's obligation and initial state.
		base := name
		if inst, isInstance := tc.recordInstantiationArgs[name]; isInstance && model.ResourceTypes[inst.Template] {
			base = inst.Template
		}
		if obligation, has := model.Obligations[base]; has {
			normalized.Obligations[name] = obligation
		}
		if initial, has := model.Initials[base]; has {
			normalized.Initials[name] = initial
		}
	}
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
			tc:                 tc,
			model:              model,
			flow:               resourceflow.New(),
			reported:           make(map[string]bool),
			unknownResources:   make(map[string]bool),
			entryModes:         make(map[string]entryAuthority),
			callableContracts:  make(map[string]string),
			unknownCallables:   make(map[string]bool),
			parameterContracts: make(map[string]*ResourceCallableContract),
			aliasCalls:         make(map[*ast.InvocationExpression]string),
			parameters:         make(map[string]bool),
			dependents:         make(map[string]map[string]bool),
			dependentScope:     make(map[string]int),
			dependentDecl:      make(map[string]ast.Node),
			borrowCalls:        make(map[*ast.InvocationExpression]map[string]bool),
			expired:            make(map[string]map[string]bool),
			expiredScope:       make(map[string]int),
			expiredDecl:        make(map[string]ast.Node),
			mutableDependents:  make(map[string]bool),
			mutableCalls:       make(map[*ast.InvocationExpression]bool),
			unprovenRoots:      make(map[string]bool),
			owned:              make(map[string]string),
			ownedOrigin:        make(map[string]ast.Node),
			transferred:        make(map[string]bool),
			pathTypes:          make(map[string]string),
		}
		for _, ident := range tailIdentifiers(fn.Body) {
			analysis.transferred[ident.Value] = true
		}
		analysis.pushScope()
		// The function's own contract fixes what its body may do with each
		// resource parameter (callee-entry authority, docs/spec/50-borrowing.md
		// section 9): a borrowed parameter enters with shared authority, a
		// borrowed-mut one with mutable authority, a consumed one with full
		// authority. Unmarked parameters keep their ordinary meaning. A
		// method's receiver is governed by the contract's receiver slot.
		own, hasContract := analysis.contractOperation(functionIdentity(fn))
		analysis.own, analysis.hasOwn = own, hasContract
		if fn.Receiver != nil && fn.Receiver.Name != nil {
			analysis.bind(fn.Receiver.Name.Value)
			if model.isResourceType(fn.Receiver.Type) {
				analysis.flow.Register(fn.Receiver.Name.Value, fn.Receiver.Name)
				if hasContract && own.Receiver != ResourceParameterUnspecified {
					analysis.entryModes[fn.Receiver.Name.Value] = entryAuthority{mode: own.Receiver, declaration: fn.Receiver.Name}
				}
			}
		}
		for index, parameter := range fn.Parameters {
			if parameter == nil || parameter.Name == nil {
				continue
			}
			analysis.bind(parameter.Name.Value)
			if _, isCallable := parameter.Type.(*ast.FunctionTypeExpression); isCallable {
				// A function-typed parameter arrives without a contract unless
				// this function's own contract declares one for it.
				if contract := own.callableContract(index); hasContract && contract != nil {
					analysis.parameterContracts[parameter.Name.Value] = contract
				} else {
					analysis.unknownCallables[parameter.Name.Value] = true
				}
			}
			if model.isResourceType(parameter.Type) {
				analysis.flow.Register(parameter.Name.Value, parameter.Name)
				analysis.parameters[parameter.Name.Value] = true
				if hasContract {
					if mode := own.parameterMode(index); mode != ResourceParameterUnspecified {
						analysis.entryModes[parameter.Name.Value] = entryAuthority{mode: mode, declaration: parameter.Name}
						if mode == ResourceParameterConsumed && !own.Terminal {
							// Consumption transferred custody here: the callee owes
							// the terminal state, unless it is the closer itself.
							analysis.markOwned(parameter.Name.Value, model.typeNameOf(parameter.Type), parameter.Name)
						}
					}
				}
			} else if len(fn.TypeParams) == 0 {
				// An aggregate parameter (a record or ADT holding resources)
				// enters with its resource paths: under a contracted mode each
				// path carries the parameter's entry authority as a tracked
				// class, with sibling paths never assumed distinct; without a
				// mode the paths have unknown provenance and fail closed.
				// Generic templates are analyzed through their specializations.
				paramType := tc.parseTypeExpression(parameter.Type)
				mode := ResourceParameterUnspecified
				if hasContract {
					mode = own.parameterMode(index)
				}
				pathTypes := tc.resourcePathTypesOf(parameter.Name.Value, paramType, model.ResourceTypes)
				for path, typeName := range pathTypes {
					analysis.pathTypes[path] = typeName
				}
				for _, path := range analysis.resourcePaths(parameter.Name.Value, paramType) {
					if mode == ResourceParameterUnspecified {
						analysis.unknownResources[path] = true
						continue
					}
					analysis.flow.Register(path, parameter.Name)
					analysis.parameters[path] = true
					analysis.entryModes[path] = entryAuthority{mode: mode, declaration: parameter.Name}
					analysis.unprovenRoots[parameter.Name.Value] = true
					if mode == ResourceParameterConsumed && !own.Terminal {
						analysis.markOwned(path, pathTypes[path], parameter.Name)
					}
				}
			}
		}
		analysis.expression(fn.Body)
		// The function's own scope ends here: consumed parameters it took
		// custody of must have reached a terminal state or been returned.
		analysis.checkScopeExit(0)
		// The body's scopes have ended; the result checks judge names bound
		// inside them by the dependencies they had.
		analysis.mergeDependents(analysis.expired, analysis.expiredScope, analysis.expiredDecl)
		// A trusted result identity (`via unsafe`) is the explicit boundary
		// where the body is not held to its claim; every other check —
		// entry authority, retention, exclusivity — still applies.
		if hasContract && !own.Trusted {
			analysis.checkResultContract(fn, own)
		}
		analysis.checkRetainedReturn(fn, own, hasContract)
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

// methodReceiver is the receiver expression of a method call
// (recv.method(args)), or nil for a plain call.
func methodReceiver(expr *ast.InvocationExpression) ast.Expression {
	if access, isAccess := expr.Function.(*ast.IndexExpression); isAccess && access.Dot {
		return access.Left
	}
	return nil
}

// reassign gives a resource binding a new provenance (docs/spec/
// 50-borrowing.md section 9): from a live registered name it becomes that
// name's alias, so later exclusive use of the two conflicts; from a
// fresh-return call it becomes a new authority, reviving nothing; from any
// other resource-valued expression its provenance becomes unknown and later
// exclusive or consuming use fails closed. The binding's entry authority, if
// it was a parameter, no longer applies to the new value. A binding that
// was never a tracked resource is untouched.
func (a *typedResourceAnalysis) reassign(s *ast.AssignmentStatement) {
	if s == nil || s.Name == nil {
		return
	}
	name := s.Name.Value
	tracked := a.flow.Registered(name) || a.unknownResources[name]
	if !tracked && !a.isResourceValue(s.Value) {
		// A whole-record reassignment b = c rebinds every tracked field
		// path of b to c's corresponding path.
		recordType := a.tc.env.CheckedExpressionType(s.Value)
		if len(a.resourcePaths(name, recordType)) > 0 {
			for _, path := range a.dependentPathsUnder(name) {
				// Rebinding the record releases what its fields depended on;
				// bindPath below decides what they depend on now.
				if len(a.ownerDependents(path)) == 0 {
					a.clearDependent(path)
				}
			}
			source, isIdent := s.Value.(*ast.Identifier)
			switch s.Value.(type) {
			case *ast.RecordLiteral, *ast.VariantExpression, *ast.InvocationExpression:
				for _, path := range a.resourcePaths(name, recordType) {
					if owners := a.ownerDependents(path); len(owners) > 0 {
						a.reportDependent(s.Name, fmt.Sprintf("%q cannot be rebound while %q borrows from it", path, owners[0]), owners[0], a.dependents[owners[0]])
						return
					}
				}
				a.bindRecordValue(name, recordType, s.Value, s.Name)
				return
			}
			for _, path := range a.resourcePaths(name, recordType) {
				if !a.flow.Registered(path) && !a.unknownResources[path] {
					continue
				}
				if isIdent && source != nil {
					a.bindPath(path, &ast.IndexExpression{Token: s.Name.Token, Left: source, Index: &ast.Identifier{Token: s.Name.Token, Value: path[len(name)+1:]}, Dot: true}, s.Name)
				} else {
					a.flow.Forget(path)
					a.unknownResources[path] = true
				}
			}
		}
		return
	}
	delete(a.entryModes, name)
	delete(a.unknownResources, name)
	if dependents := a.ownerDependents(name); len(dependents) > 0 {
		// Rebinding an owner would release the storage a live borrowed
		// result depends on.
		a.reportDependent(s.Name, fmt.Sprintf("%q cannot be rebound while %q borrows from it", name, dependents[0]), dependents[0], a.dependents[dependents[0]])
		a.flow.Forget(name)
		a.unknownResources[name] = true
		return
	}
	// Rebinding a borrowed result releases its own dependency; the new
	// right-hand side decides what it depends on now.
	a.clearDependent(name)
	targetScope := a.scopeOf(name)
	// Rebinding the only live name of an owned resource loses its custody.
	if typeName, isOwned := a.owned[name]; isOwned && a.flow.Registered(name) {
		if authority, _ := a.flow.AuthorityOf(name); authority != resourceflow.AuthorityConsumed && len(a.flow.ClassMates(name)) == 0 {
			a.reportUnclosed(name, typeName, authority)
		}
	}
	a.releaseOwned(name)
	if source, ok := s.Value.(*ast.Identifier); ok && source != nil && a.flow.Registered(source.Value) {
		if a.flow.CanUse(source.Value) {
			if dependent, owners, isDependent := a.dependentOf(source.Value); isDependent {
				if a.dependentScope[dependent] > targetScope {
					a.reportDependent(s.Name, fmt.Sprintf("%q cannot be rebound to %q: the borrowed result would outlive its scope", name, source.Value), dependent, owners)
					a.flow.Forget(name)
					a.unknownResources[name] = true
					return
				}
				a.flow.Rebind(name, source.Value, s.Name)
				a.setDependent(name, owners, targetScope, s.Name, a.mutableDependents[dependent])
				return
			}
			a.flow.Rebind(name, source.Value, s.Name)
			a.inheritOwnership(name, source.Value, s.Name)
		} else {
			// Ordinary evaluation reported the use-after-consume; the
			// destination now has no usable provenance.
			a.flow.Forget(name)
			a.unknownResources[name] = true
		}
		return
	}
	if call, ok := s.Value.(*ast.InvocationExpression); ok && a.freshCalls[call] {
		a.flow.RebindFresh(name, s.Name)
		if typ, known := a.tc.env.GetType(name); known {
			a.markOwned(name, nominalTypeName(typ), s.Name)
		}
		return
	}
	if typeName, constructed := a.isTypestateConstruction(s.Value); constructed {
		a.flow.RebindFresh(name, s.Name)
		a.markOwned(name, typeName, s.Name)
		return
	}
	if call, ok := s.Value.(*ast.InvocationExpression); ok {
		if source, aliased := a.aliasCalls[call]; aliased && source != "" && a.flow.CanUse(source) {
			a.flow.Rebind(name, source, s.Name)
			return
		}
		if owners, isBorrow := a.borrowCalls[call]; isBorrow && len(owners) > 0 {
			// The result must not outlive any owner it depends on: an owner
			// bound in a scope inside the target's would be gone first.
			for _, owner := range sortedOwners(owners) {
				if a.scopeOf(owner) > targetScope {
					a.reportDependent(s.Name, fmt.Sprintf("%q cannot be rebound to a borrowed result of %q, which is bound in an inner scope: the result would outlive its owner", name, owner), "", owners)
					a.flow.Forget(name)
					a.unknownResources[name] = true
					return
				}
			}
			a.flow.RebindFresh(name, s.Name)
			a.setDependent(name, owners, targetScope, s.Name, a.mutableCalls[call])
			return
		}
	}
	a.flow.Forget(name)
	a.unknownResources[name] = true
}

// resourceName is the flow name of a resource-valued expression: an
// identifier's own name, or the dotted path of a record projection
// (b.inner, b.pair.left) whose root is an identifier
// (docs/spec/50-borrowing.md section 9, projections). Anything else has no
// name and therefore no tracked provenance.
func resourceName(expr ast.Expression) (string, bool) {
	switch e := expr.(type) {
	case *ast.Identifier:
		if e == nil || e.Value == "" {
			return "", false
		}
		return e.Value, true
	case *ast.IndexExpression:
		if e == nil || !e.Dot {
			return "", false
		}
		field, isField := e.Index.(*ast.Identifier)
		if !isField || field == nil {
			return "", false
		}
		base, ok := resourceName(e.Left)
		if !ok {
			return "", false
		}
		return base + "." + field.Value, true
	}
	return "", false
}

// resourcePaths lists the resource-typed field paths below a record value
// of the given type, recursing into nested named records: for
// Box { inner: Handle, pair: Pair { left: Handle } } and root "b",
// b.inner and b.pair.left.
func (a *typedResourceAnalysis) resourcePaths(root string, typ Type) []string {
	return a.tc.resourcePathsOf(root, typ, a.model.ResourceTypes)
}

// aggregatePaths lists the resource paths below a named aggregate-valued
// expression (an identifier or a record projection), or nothing for
// anything else.
func (a *typedResourceAnalysis) aggregatePaths(expr ast.Expression) []string {
	name, ok := resourceName(expr)
	if !ok || a.tc == nil || a.tc.env == nil {
		return nil
	}
	return a.resourcePaths(name, a.tc.env.CheckedExpressionType(expr))
}

// sameUnprovenRoot reports whether two distinct paths lie under one
// aggregate parameter whose paths were never proven distinct.
func (a *typedResourceAnalysis) sameUnprovenRoot(left, right string) bool {
	if left == right {
		return false
	}
	leftRoot, _, leftIsPath := strings.Cut(left, ".")
	rightRoot, _, rightIsPath := strings.Cut(right, ".")
	return leftIsPath && rightIsPath && leftRoot == rightRoot && a.unprovenRoots[leftRoot]
}

// bindRecordFields gives a freshly declared record binding's resource
// fields their provenance from the record literal that built it: a field
// initialized from a live named resource aliases it (consuming through
// b.inner consumes h), a field initialized from a fresh-return call is a new
// authority, and any other resource-valued initializer leaves the field
// with unknown provenance. Records not built from a literal here — a
// parameter, a call result — keep untracked fields, so exclusive or
// consuming use of them fails closed: distinct fields are never assumed
// distinct resources without provenance saying so.
func (a *typedResourceAnalysis) bindRecordFields(stmt *ast.VariableDeclaration) {
	if stmt == nil || stmt.Name == nil {
		return
	}
	var aggregateType Type
	if stmt.Type != nil {
		aggregateType = a.tc.parseTypeExpression(stmt.Type)
	} else if a.tc.env != nil {
		aggregateType = a.tc.env.CheckedDeclarationType(stmt)
	}
	if len(a.resourcePaths(stmt.Name.Value, aggregateType)) == 0 {
		return
	}
	a.bindRecordValue(stmt.Name.Value, aggregateType, stmt.Value, stmt.Name)
}

// bindRecordValue gives the resource paths below root, a record of the
// given type, the provenance of value: a literal binds field by field
// (recursing into record-typed fields), a named record aliases every path
// to the source's corresponding path, and anything else leaves every path
// with unknown provenance.
func (a *typedResourceAnalysis) bindRecordValue(root string, aggregateType Type, value ast.Expression, origin ast.Node) {
	paths := a.resourcePaths(root, aggregateType)
	if len(paths) == 0 {
		return
	}
	for path, typeName := range a.tc.resourcePathTypesOf(root, aggregateType, a.model.ResourceTypes) {
		a.pathTypes[path] = typeName
	}
	clear := func() {
		for _, path := range paths {
			a.flow.Forget(path)
			delete(a.unknownResources, path)
		}
	}
	unknownAll := func() {
		clear()
		for _, path := range paths {
			a.unknownResources[path] = true
		}
	}
	switch v := value.(type) {
	case *ast.RecordLiteral:
		record, isRecord := aggregateType.(*RecordType)
		if !isRecord || record == nil {
			unknownAll()
			return
		}
		for _, field := range v.FieldOrder {
			fieldType, declared := record.Fields[field.Name]
			if !declared {
				continue
			}
			path := root + "." + field.Name
			if a.model.ResourceTypes[nominalTypeName(fieldType)] {
				a.bindPath(path, field.Value, origin)
				continue
			}
			a.bindRecordValue(path, fieldType, field.Value, origin)
		}
	case *ast.VariantExpression:
		// Construction: the chosen variant's payload path takes the
		// payload's provenance; the other variants' paths are absent.
		clear()
		if v.Variant == nil || v.Payload == nil {
			return
		}
		payloadType := a.tc.payloadTypeOfVariant(aggregateType, v.Variant.Value)
		path := root + ".$" + v.Variant.Value
		if payloadType == nil {
			return
		}
		if a.model.ResourceTypes[nominalTypeName(payloadType)] {
			a.bindPath(path, v.Payload, origin)
			return
		}
		a.bindRecordValue(path, payloadType, v.Payload, origin)
	case *ast.InvocationExpression:
		// A contracted call's result fact applies to every resource path of
		// an aggregate result: fresh registers each as a new class, alias
		// makes each an alias of the argument, borrow makes each a dependent.
		clear()
		if a.freshCalls[v] {
			pathTypes := a.tc.resourcePathTypesOf(root, aggregateType, a.model.ResourceTypes)
			for _, path := range paths {
				a.flow.Register(path, origin)
				a.markOwned(path, pathTypes[path], origin)
			}
			return
		}
		if source, aliased := a.aliasCalls[v]; aliased {
			for _, path := range paths {
				if source != "" && a.flow.CanUse(source) {
					a.flow.Alias(path, source, origin)
				} else {
					a.unknownResources[path] = true
				}
			}
			return
		}
		if owners, borrowed := a.borrowCalls[v]; borrowed {
			for _, path := range paths {
				if len(owners) > 0 && a.adoptDependency(path, owners, a.mutableCalls[v], origin, value) {
					a.flow.Register(path, origin)
				} else {
					a.unknownResources[path] = true
				}
			}
			return
		}
		for _, path := range paths {
			a.unknownResources[path] = true
		}
	default:
		if source, ok := resourceName(value); ok {
			for _, path := range paths {
				sourcePath := source + path[len(root):]
				a.flow.Forget(path)
				delete(a.unknownResources, path)
				if a.flow.Registered(sourcePath) && a.flow.CanUse(sourcePath) {
					if dependent, owners, isDependent := a.dependentOf(sourcePath); isDependent {
						// A copied record carries each borrowed field's
						// dependency, under the copy's own lifetime.
						if !a.adoptDependency(path, owners, a.mutableDependents[dependent], origin, value) {
							a.unknownResources[path] = true
							continue
						}
					}
					a.flow.Alias(path, sourcePath, origin)
					a.inheritOwnership(path, sourcePath, origin)
				} else if a.flow.Registered(sourcePath) || a.unknownResources[sourcePath] {
					a.unknownResources[path] = true
				}
			}
			return
		}
		unknownAll()
	}
}

// bindPathFrom gives a destination name or path the provenance of a
// tracked source path (a match binding taking a payload, a copied
// aggregate): an alias when the source is live, a use error when it was
// consumed, unknown provenance otherwise.
func (a *typedResourceAnalysis) bindPathFrom(destination, sourcePath string, origin ast.Node) {
	a.flow.Forget(destination)
	delete(a.unknownResources, destination)
	if a.flow.Registered(sourcePath) {
		if !a.flow.CanUse(sourcePath) {
			a.use(sourcePath, origin)
			a.unknownResources[destination] = true
			return
		}
		if dependent, owners, isDependent := a.dependentOf(sourcePath); isDependent {
			if !a.adoptDependency(destination, owners, a.mutableDependents[dependent], origin, origin) {
				a.unknownResources[destination] = true
				return
			}
		}
		a.flow.Alias(destination, sourcePath, origin)
		a.inheritOwnership(destination, sourcePath, origin)
		return
	}
	a.unknownResources[destination] = true
}

// bindPath gives a resource path (or name) the provenance of a value: an
// alias of a live named resource, a fresh authority from a fresh-return
// call, else unknown provenance.
func (a *typedResourceAnalysis) bindPath(path string, value ast.Expression, origin ast.Node) {
	if dependents := a.ownerDependents(path); len(dependents) > 0 {
		// Writing a field a borrowed result depends on (directly, or through
		// a whole-record write) would release what it depends on.
		a.reportDependent(origin, fmt.Sprintf("%q cannot be rebound while %q borrows from it", path, dependents[0]), dependents[0], a.dependents[dependents[0]])
		a.flow.Forget(path)
		a.unknownResources[path] = true
		return
	}
	a.flow.Forget(path)
	delete(a.unknownResources, path)
	// A borrowed result may live in a record field when the record's
	// binding does not outlive the owners the value depends on
	// (docs/spec/50-borrowing.md section 9, borrowed values in aggregates):
	// the field path becomes a dependent with the same owners and
	// permission. A destination that would outlive an owner is rejected.
	if source, ok := resourceName(value); ok {
		if dependent, owners, isDependent := a.dependentOf(source); isDependent {
			if a.adoptDependency(path, owners, a.mutableDependents[dependent], origin, value) {
				a.flow.Alias(path, source, origin)
			} else {
				a.unknownResources[path] = true
			}
			return
		}
	}
	if call, ok := value.(*ast.InvocationExpression); ok {
		if owners, isBorrow := a.borrowCalls[call]; isBorrow {
			if len(owners) == 0 {
				a.unknownResources[path] = true
				return
			}
			if a.adoptDependency(path, owners, a.mutableCalls[call], origin, value) {
				a.flow.Register(path, origin)
			} else {
				a.unknownResources[path] = true
			}
			return
		}
	}
	if source, ok := resourceName(value); ok && a.flow.Registered(source) {
		if a.flow.CanUse(source) {
			a.flow.Alias(path, source, origin)
			a.inheritOwnership(path, source, origin)
			return
		}
		a.unknownResources[path] = true
		return
	}
	if call, ok := value.(*ast.InvocationExpression); ok && a.freshCalls[call] {
		a.flow.Register(path, origin)
		a.markOwned(path, a.pathTypeName(path), origin)
		return
	}
	if typeName, constructed := a.isTypestateConstruction(value); constructed {
		a.flow.Register(path, origin)
		a.markOwned(path, typeName, origin)
		return
	}
	if call, ok := value.(*ast.InvocationExpression); ok {
		if source, aliased := a.aliasCalls[call]; aliased && source != "" && a.flow.CanUse(source) {
			a.flow.Alias(path, source, origin)
			return
		}
	}
	a.unknownResources[path] = true
}

// pathTypeName is the resource type a path holds, from its root binding's
// checked type; "" when unknown.
func (a *typedResourceAnalysis) pathTypeName(path string) string {
	if typeName, known := a.pathTypes[path]; known {
		return typeName
	}
	root, _, isPath := strings.Cut(path, ".")
	if !isPath || a.tc == nil || a.tc.env == nil {
		return ""
	}
	rootType, ok := a.tc.env.GetType(root)
	if !ok || rootType == nil {
		return ""
	}
	return a.tc.resourcePathTypesOf(root, rootType, a.model.ResourceTypes)[path]
}

// tailIdentifiers collects the identifiers an expression may evaluate to
// as a function's result: the expression itself, the last statement of a
// block, and every arm of a match. Calls and literals contribute nothing
// (their results are checked where they are built).
func tailIdentifiers(expr ast.Expression) []*ast.Identifier {
	switch e := expr.(type) {
	case *ast.Identifier:
		return []*ast.Identifier{e}
	case *ast.VariantExpression:
		// A resource returned inside a variant (.Ok(h)) is returned.
		return tailIdentifiers(e.Payload)
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

// destinationScope is the lexical scope of the binding a path is stored
// under: the root name's scope, or the current scope while that root's
// declaration is still in progress (its binding is deferred until the
// initializer has been evaluated).
func (a *typedResourceAnalysis) destinationScope(path string) int {
	root, _, _ := strings.Cut(path, ".")
	if scope := a.scopeOf(root); scope >= 0 {
		return scope
	}
	return len(a.scopes) - 1
}

// adoptDependency makes path a dependent of owners with the given
// permission, provided the record binding that holds path does not outlive
// any owner (an owner bound in an inner scope would be gone first). It
// reports OAK-B0118 and returns false otherwise.
func (a *typedResourceAnalysis) adoptDependency(path string, owners map[string]bool, mutable bool, origin ast.Node, value ast.Node) bool {
	destination := a.destinationScope(path)
	for _, owner := range sortedOwners(owners) {
		if a.scopeOf(owner) > destination {
			a.reportDependent(value, fmt.Sprintf("a borrowed result of %q cannot be stored in %q, which outlives its owner", owner, path), "", owners).
				AddHelp("store the borrowed result in a record bound no longer than its owner, or copy the value out")
			return false
		}
	}
	a.setDependent(path, owners, destination, origin, mutable)
	return true
}

// dependentPathsUnder lists the dependent field paths below a record name.
func (a *typedResourceAnalysis) dependentPathsUnder(name string) []string {
	var out []string
	for path := range a.dependents {
		if strings.HasPrefix(path, name+".") {
			out = append(out, path)
		}
	}
	sort.Strings(out)
	return out
}

// checkAggregateEscape rejects passing a record that holds a borrowed
// result to any call (docs/spec/50-borrowing.md section 9): the callee's
// contract cannot yet describe a dependency carried by a field, so the
// record could outlive or release what the field depends on. Both a named
// record and a record literal mentioning a dependent are rejected. It
// returns false when the call has not occurred.
func (a *typedResourceAnalysis) checkAggregateEscape(expr *ast.InvocationExpression) bool {
	ok := true
	for _, argument := range expr.Arguments {
		switch arg := argument.(type) {
		case *ast.Identifier:
			if arg == nil || a.isResourceValue(arg) {
				continue
			}
			if paths := a.dependentPathsUnder(arg.Value); len(paths) > 0 {
				ok = false
				a.reportDependent(arg, fmt.Sprintf("%q holds the borrowed result %q and cannot be passed to a call", arg.Value, paths[0]), paths[0], a.dependents[paths[0]]).
					AddHelp("pass the borrowed field itself under a contract, or the record without it")
			}
		case *ast.RecordLiteral:
			for _, name := range mentionedNames(arg) {
				if dependent, owners, isDependent := a.dependentOf(name); isDependent {
					ok = false
					a.reportDependent(arg, fmt.Sprintf("a record literal holding the borrowed result %q cannot be passed to a call", name), dependent, owners)
					break
				}
			}
		}
	}
	return ok
}

// typestateOf reports whether a checked type is an instantiation of a
// typestate-indexed resource (a record template with one type parameter
// governed by a protocol): the template and the state its index names.
func (a *typedResourceAnalysis) typestateOf(typ Type) (template, state string, ok bool) {
	record, isRecord := typ.(*RecordType)
	if !isRecord || record == nil || a.tc == nil {
		return "", "", false
	}
	inst, known := a.tc.RecordInstantiationOf(record.Name)
	if !known || len(inst.Args) != 1 || !a.model.ResourceTypes[inst.Template] {
		return "", "", false
	}
	tmpl := a.tc.recordTemplates[inst.Template]
	if tmpl == nil || len(tmpl.TypeParams) != 1 {
		return "", "", false
	}
	atom, isAtom := typeAtom(inst.Args[0])
	if !isAtom {
		return "", "", false
	}
	return inst.Template, atom, true
}

// isTypestateConstruction reports whether an expression is a literal of a
// typestate-indexed resource: construction, which is fresh authority where
// the construction rule admits it (checkTypestateConstruction reports the
// rest), and the type name of the resource.
func (a *typedResourceAnalysis) isTypestateConstruction(expr ast.Expression) (string, bool) {
	literal, isLiteral := expr.(*ast.RecordLiteral)
	if !isLiteral || literal == nil || a.tc == nil || a.tc.env == nil {
		return "", false
	}
	typ := a.tc.env.CheckedExpressionType(literal)
	if _, _, isTypestate := a.typestateOf(typ); !isTypestate {
		return "", false
	}
	return nominalTypeName(typ), true
}

// checkTypestateConstruction admits a literal of a typestate-indexed
// resource only in its protocol's initial state or, inside a transition,
// in a state that transition enters (OAK-B0121): a handle's state is a
// claim about the resource, and only the transition into a state may make
// it (docs/spec/112-protocols.md section 5a).
func (a *typedResourceAnalysis) checkTypestateConstruction(literal *ast.RecordLiteral) {
	if literal == nil || a.tc == nil || a.tc.env == nil {
		return
	}
	template, state, isTypestate := a.typestateOf(a.tc.env.CheckedExpressionType(literal))
	if !isTypestate {
		return
	}
	if initial, known := a.model.Initials[template]; known && initial == state {
		return
	}
	if a.hasOwn {
		for _, target := range a.own.Targets {
			if target == state {
				return
			}
		}
	}
	d := a.tc.addResourceDiagnosticWithCode(literal, CodeResourceTypestateConstruction, fmt.Sprintf("a %s[%s] cannot be constructed here: only the transition into %s may put a handle in that state", template, state, state))
	if initial, known := a.model.Initials[template]; known {
		d.AddNote(fmt.Sprintf("a %s may be constructed anywhere in its initial state %s; every other state is reached through the protocol's via callables (docs/spec/112-protocols.md section 5a)", template, initial))
	}
	d.AddHelp("construct the handle in its initial state and move it with the protocol's transitions, or make this function the via callable of a transition into " + state)
}

// tailCalls collects the invocation expressions an expression may evaluate
// to as a function's result, the way tailIdentifiers collects names: a
// wrapper that returns another operation's result directly is judged by
// that call's own result contract.
func tailCalls(expr ast.Expression) []*ast.InvocationExpression {
	switch e := expr.(type) {
	case *ast.InvocationExpression:
		return []*ast.InvocationExpression{e}
	case *ast.VariantExpression:
		return tailCalls(e.Payload)
	case *ast.BlockExpression:
		if e.Block == nil || len(e.Block.Statements) == 0 {
			return nil
		}
		if last, ok := e.Block.Statements[len(e.Block.Statements)-1].(*ast.ExpressionStatement); ok {
			return tailCalls(last.Expression)
		}
	case *ast.MatchExpression:
		var out []*ast.InvocationExpression
		for _, arm := range e.Arms {
			if arm != nil {
				out = append(out, tailCalls(arm.Body)...)
			}
		}
		return out
	}
	return nil
}

// tailLiterals collects the record literals an expression may evaluate to
// as a function's result.
func tailLiterals(expr ast.Expression) []*ast.RecordLiteral {
	switch e := expr.(type) {
	case *ast.RecordLiteral:
		return []*ast.RecordLiteral{e}
	case *ast.VariantExpression:
		return tailLiterals(e.Payload)
	case *ast.BlockExpression:
		if e.Block == nil || len(e.Block.Statements) == 0 {
			return nil
		}
		if last, ok := e.Block.Statements[len(e.Block.Statements)-1].(*ast.ExpressionStatement); ok {
			return tailLiterals(last.Expression)
		}
	case *ast.MatchExpression:
		var out []*ast.RecordLiteral
		for _, arm := range e.Arms {
			if arm != nil {
				out = append(out, tailLiterals(arm.Body)...)
			}
		}
		return out
	}
	return nil
}

// mentionedNames lists, sorted, the identifiers a record literal's field
// values mention anywhere (a superset of the resources the value can hold).
func mentionedNames(literal *ast.RecordLiteral) []string {
	seen := make(map[string]bool)
	var walk func(expr ast.Expression)
	walk = func(expr ast.Expression) {
		switch e := expr.(type) {
		case nil:
		case *ast.Identifier:
			if e != nil {
				seen[e.Value] = true
			}
		case *ast.IndexExpression:
			walk(e.Left)
			if !e.Dot {
				walk(e.Index)
			}
		case *ast.InfixExpression:
			walk(e.Left)
			walk(e.Right)
		case *ast.PrefixExpression:
			walk(e.Right)
		case *ast.InvocationExpression:
			for _, argument := range e.Arguments {
				walk(argument)
			}
		case *ast.RecordLiteral:
			for _, field := range e.FieldOrder {
				walk(field.Value)
			}
			for _, value := range e.Fields {
				walk(value)
			}
		case *ast.ArrayLiteral:
			for _, element := range e.Elements {
				walk(element)
			}
		case *ast.VariantExpression:
			walk(e.Payload)
		}
	}
	walk(literal)
	names := make([]string, 0, len(seen))
	for name := range seen {
		names = append(names, name)
	}
	sort.Strings(names)
	return names
}

// checkRetainedReturn rejects a body that returns a borrowed or
// borrowed-mut parameter (or an alias of one) as its result: the caller
// keeps custody of a borrowed resource, so handing it back would mint a
// second authority over the same resource (OAK-B0114, retention).
func (a *typedResourceAnalysis) checkRetainedReturn(fn *ast.FunctionStatement, own ResourceOperation, hasContract bool) {
	if fn == nil || fn.Body == nil {
		return
	}
	declared := make(map[string]bool)
	if hasContract && own.ReturnsAlias && own.AliasesArgument >= 0 && own.AliasesArgument < len(fn.Parameters) && fn.Parameters[own.AliasesArgument].Name != nil {
		declared[fn.Parameters[own.AliasesArgument].Name.Value] = true
	}
	if hasContract && own.ReturnsBorrow {
		declared = a.declaredParameters(fn, own.BorrowsArguments)
	}
	for _, ident := range tailIdentifiers(fn.Body) {
		// A result the contract declares as an alias or borrow of a
		// parameter hands the caller a dependent name for an authority it
		// already holds; the callee retains nothing.
		if len(declared) > 0 && a.flow.Registered(ident.Value) && a.ownersWithin(map[string]bool{ident.Value: true}, declared) {
			continue
		}
		if dependent, owners, isDependent := a.dependentOf(ident.Value); isDependent {
			// A borrowed result may leave the function only under a contract
			// that ties it to the parameters it depends on (a wrapper
			// preserves the dependency); otherwise it would outlive its scope.
			if hasContract && own.ReturnsBorrow && a.ownersWithin(owners, declared) {
				continue
			}
			a.reportDependent(ident, fmt.Sprintf("%q is a borrowed result of %s and cannot be returned as this function's result", ident.Value, describeOwners(owners)), dependent, owners).
				AddHelp("declare this function's result a borrow of the parameter the value depends on, or return a fresh resource")
			continue
		}
		if len(a.entryModes) == 0 {
			continue
		}
		a.checkRetention(ident, "returned as this function's result")
	}
	for _, ident := range tailIdentifiers(fn.Body) {
		if paths := a.dependentPathsUnder(ident.Value); len(paths) > 0 {
			a.reportDependent(ident, fmt.Sprintf("%q holds the borrowed result %q and cannot be returned as this function's result", ident.Value, paths[0]), paths[0], a.dependents[paths[0]]).
				AddHelp("return the borrowed field itself under a contract, or the record without it")
		}
	}
	for _, literal := range tailLiterals(fn.Body) {
		for _, name := range mentionedNames(literal) {
			if dependent, owners, isDependent := a.dependentOf(name); isDependent {
				a.reportDependent(literal, fmt.Sprintf("a record literal holding the borrowed result %q cannot be returned as this function's result", name), dependent, owners)
				break
			}
		}
	}
	for _, call := range tailCalls(fn.Body) {
		owners, isBorrow := a.borrowCalls[call]
		if !isBorrow {
			continue
		}
		if hasContract && own.ReturnsBorrow && a.ownersWithin(owners, declared) {
			continue
		}
		a.reportDependent(call, fmt.Sprintf("a borrowed result of %s cannot be returned as this function's result", describeOwners(owners)), "", owners).
			AddHelp("declare this function's result a borrow of the parameter the value depends on, or return a fresh resource")
	}
}

// declaredParameters names the function's parameters at the given indices.
func (a *typedResourceAnalysis) declaredParameters(fn *ast.FunctionStatement, indices []int) map[string]bool {
	names := make(map[string]bool, len(indices))
	for _, index := range indices {
		if index >= 0 && index < len(fn.Parameters) && fn.Parameters[index] != nil && fn.Parameters[index].Name != nil {
			names[fn.Parameters[index].Name.Value] = true
		}
	}
	return names
}

// ownersWithin reports whether every owner is one of the declared
// parameters or an alias of one: the dependency set claimed by the
// contract covers the dependency the value actually has.
func (a *typedResourceAnalysis) ownersWithin(owners map[string]bool, declared map[string]bool) bool {
	if len(owners) == 0 || len(declared) == 0 {
		return false
	}
	for owner := range owners {
		if declared[owner] {
			continue
		}
		covered := false
		for parameter := range declared {
			if a.flow.Registered(owner) && a.flow.Registered(parameter) && a.flow.Aliases(owner, parameter) {
				covered = true
				break
			}
		}
		if !covered {
			return false
		}
	}
	return true
}

// checkResultContract validates a body against its declared result
// identity (OAK-B0117): a fresh result may not be a parameter or an alias
// of one (freshness cannot be manufactured by renaming), and an alias
// result must be the declared parameter's authority on every path.
func (a *typedResourceAnalysis) checkResultContract(fn *ast.FunctionStatement, own ResourceOperation) {
	if fn == nil || fn.Body == nil || (!own.ReturnsFresh && !own.ReturnsAlias && !own.ReturnsBorrow) {
		return
	}
	report := func(node ast.Node, title string) {
		d := a.tc.addResourceDiagnosticWithCode(node, CodeResourceResultContract, title)
		d.AddNote("a result contract is a claim about the returned value's authority: fresh means a new class no caller name shares, alias means exactly the named argument's class (docs/spec/50-borrowing.md section 9)")
		d.AddHelp("declare the result identity the body actually produces, or return a value that has it")
	}
	tails := tailIdentifiers(fn.Body)
	calls := tailCalls(fn.Body)
	if own.ReturnsFresh {
		for _, call := range calls {
			if _, isBorrow := a.borrowCalls[call]; isBorrow {
				report(call, fmt.Sprintf("%s is declared to return fresh authority but returns a borrowed result", fn.Name.Value))
			} else if source, isAlias := a.aliasCalls[call]; isAlias {
				report(call, fmt.Sprintf("%s is declared to return fresh authority but returns an alias of %q", fn.Name.Value, source))
			}
		}
		for _, ident := range tails {
			if _, owners, isDependent := a.dependentOf(ident.Value); isDependent {
				report(ident, fmt.Sprintf("%s is declared to return fresh authority but returns %q, a borrowed result of %s", fn.Name.Value, ident.Value, describeOwners(owners)))
				continue
			}
			for parameter := range a.parameters {
				if ident.Value == parameter || a.flow.Aliases(ident.Value, parameter) {
					report(ident, fmt.Sprintf("%s is declared to return fresh authority but returns parameter %q (through %q)", fn.Name.Value, parameter, ident.Value))
					break
				}
			}
		}
		return
	}
	if own.ReturnsBorrow {
		// A borrow is the most conservative claim: it only restricts the
		// caller. The body may therefore return any declared parameter, an
		// alias or dependent of them, or a value with no provenance from any
		// other tracked resource (a fresh result, an independent local, a
		// record literal that mentions no other resource) — the primitive
		// that builds a cursor over an arena has nothing else to return.
		// What it may not return is authority derived from a different
		// parameter, a borrowed result of other owners, or a value of
		// unknown provenance, which the caller would then leave unprotected.
		declared := a.declaredParameters(fn, own.BorrowsArguments)
		if len(declared) == 0 {
			return
		}
		describeDeclared := strings.Join(quoteAll(sortedOwners(declared)), ", ")
		relatedToDeclared := func(name string) bool {
			if a.flow.Registered(name) && a.ownersWithin(map[string]bool{name: true}, declared) {
				return true
			}
			_, owners, isDependent := a.dependentOf(name)
			return isDependent && a.ownersWithin(owners, declared)
		}
		for _, call := range calls {
			if a.freshCalls[call] {
				continue
			}
			if owners, isBorrow := a.borrowCalls[call]; isBorrow {
				if a.ownersWithin(owners, declared) {
					if own.BorrowMutable && !a.mutableCalls[call] {
						report(call, fmt.Sprintf("%s is declared to return a mutable reborrow of %s but returns a shared borrowed result: a borrow cannot be widened", fn.Name.Value, describeDeclared))
					}
					continue
				}
				report(call, fmt.Sprintf("%s is declared to return a borrow of %s but returns a borrowed result of %s", fn.Name.Value, describeDeclared, describeOwners(owners)))
				continue
			}
			if source, isAlias := a.aliasCalls[call]; isAlias {
				if source != "" && relatedToDeclared(source) {
					continue
				}
				report(call, fmt.Sprintf("%s is declared to return a borrow of %s but returns an alias of %q", fn.Name.Value, describeDeclared, source))
				continue
			}
			if a.isResourceValue(call) {
				report(call, fmt.Sprintf("%s is declared to return a borrow of %s but returns a resource of unknown provenance", fn.Name.Value, describeDeclared))
			}
		}
		for _, ident := range tails {
			if dependent, owners, isDependent := a.dependentOf(ident.Value); isDependent && own.BorrowMutable && !a.mutableDependents[dependent] && a.ownersWithin(owners, declared) {
				report(ident, fmt.Sprintf("%s is declared to return a mutable reborrow of %s but returns %q, a shared borrowed result: a borrow cannot be widened", fn.Name.Value, describeDeclared, ident.Value))
				continue
			}
			if relatedToDeclared(ident.Value) {
				continue
			}
			if a.unknownResources[ident.Value] {
				report(ident, fmt.Sprintf("%s is declared to return a borrow of %s but returns %q, whose provenance is unknown", fn.Name.Value, describeDeclared, ident.Value))
				continue
			}
			if _, owners, isDependent := a.dependentOf(ident.Value); isDependent {
				report(ident, fmt.Sprintf("%s is declared to return a borrow of %s but returns %q, a borrowed result of %s", fn.Name.Value, describeDeclared, ident.Value, describeOwners(owners)))
				continue
			}
			for _, parameter := range sortedOwners(a.parameters) {
				if !declared[parameter] && a.flow.Registered(ident.Value) && a.flow.Aliases(ident.Value, parameter) {
					report(ident, fmt.Sprintf("%s is declared to return a borrow of %s but returns parameter %q (through %q)", fn.Name.Value, describeDeclared, parameter, ident.Value))
					break
				}
			}
		}
		for _, literal := range tailLiterals(fn.Body) {
			for _, name := range mentionedNames(literal) {
				if a.flow.Registered(name) && !relatedToDeclared(name) {
					report(literal, fmt.Sprintf("%s is declared to return a borrow of %s but its result literal mentions resource %q", fn.Name.Value, describeDeclared, name))
					break
				}
			}
		}
		return
	}
	if own.AliasesArgument < 0 || own.AliasesArgument >= len(fn.Parameters) || fn.Parameters[own.AliasesArgument].Name == nil {
		return
	}
	declared := fn.Parameters[own.AliasesArgument].Name.Value
	literals := tailLiterals(fn.Body)
	if len(tails) == 0 && len(calls) == 0 && len(literals) == 0 {
		report(fn.Name, fmt.Sprintf("%s is declared to return an alias of %q but its result is not a named resource", fn.Name.Value, declared))
		return
	}
	// A typestate transition rebuilds the handle in its new state: a record
	// literal that mentions no resource other than the aliased parameter is
	// that parameter's authority under its next state.
	for _, literal := range literals {
		for _, name := range mentionedNames(literal) {
			if a.flow.Registered(name) && name != declared && !a.flow.Aliases(name, declared) {
				report(literal, fmt.Sprintf("%s is declared to return an alias of %q but its result literal mentions resource %q", fn.Name.Value, declared, name))
				break
			}
		}
	}
	for _, call := range calls {
		if source, isAlias := a.aliasCalls[call]; isAlias && source != "" && (source == declared || a.flow.Aliases(source, declared)) {
			continue
		}
		report(call, fmt.Sprintf("%s is declared to return an alias of %q but returns an operation's result that is not that alias", fn.Name.Value, declared))
	}
	for _, ident := range tails {
		if ident.Value == declared || a.flow.Aliases(ident.Value, declared) {
			continue
		}
		report(ident, fmt.Sprintf("%s is declared to return an alias of %q but returns %q, which does not share its authority", fn.Name.Value, declared, ident.Value))
	}
}

// trackedName is the flow name an expression's authority is known by: an
// identifier, a record projection path, or the argument a checked
// alias-returning call aliases. ok is false when there is no tracked name.
func (a *typedResourceAnalysis) trackedName(expr ast.Expression) (string, bool) {
	if call, isCall := expr.(*ast.InvocationExpression); isCall {
		source, aliased := a.aliasCalls[call]
		return source, aliased && source != ""
	}
	name, ok := resourceName(expr)
	return name, ok && a.flow.Registered(name)
}

// checkRetention reports a borrowed or borrowed-mut parameter (or alias)
// being retained — returned, or stored in an aggregate — beyond the call
// that lent it.
func (a *typedResourceAnalysis) checkRetention(ident *ast.Identifier, how string) {
	if ident == nil || !a.flow.Registered(ident.Value) {
		return
	}
	if dependent, owners, isDependent := a.dependentOf(ident.Value); isDependent {
		a.reportDependent(ident, fmt.Sprintf("%q is a borrowed result of %s and cannot be %s", ident.Value, describeOwners(owners), how), dependent, owners)
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
	// aliasCalls maps a checked call whose contract declares an alias
	// result to the tracked name of the aliased argument ("" when that
	// argument had no tracked provenance).
	aliasCalls map[*ast.InvocationExpression]string
	// parameters are the function's resource parameter names, for result
	// contract validation.
	parameters map[string]bool
	// dependents maps a binding holding a declared borrowed result to the
	// root owner names it depends on (docs/spec/50-borrowing.md section 9,
	// borrowed results); dependentScope is the lexical scope the dependency
	// lives in and dependentDecl the binding that created it. borrowCalls
	// maps a checked borrow-returning call to the owners of its temporary
	// result (nil when the borrowed argument had no tracked provenance).
	dependents     map[string]map[string]bool
	dependentScope map[string]int
	dependentDecl  map[string]ast.Node
	borrowCalls    map[*ast.InvocationExpression]map[string]bool
	// expired keeps the dependencies whose scopes have ended, so that the
	// result checks run after the body can still see what a tail name
	// bound inside the body depended on.
	expired      map[string]map[string]bool
	expiredScope map[string]int
	expiredDecl  map[string]ast.Node
	// mutableDependents marks dependents that are mutable reborrows;
	// mutableCalls marks borrow-returning calls whose result is one.
	mutableDependents map[string]bool
	mutableCalls      map[*ast.InvocationExpression]bool
	// unprovenRoots marks aggregate parameters whose resource paths were
	// registered under a contract: the caller transferred or lent the whole
	// value, but nothing proves two of its paths denote distinct resources,
	// so an exclusive pairing of sibling paths fails closed.
	unprovenRoots map[string]bool
	// owned maps a name or path holding full custody of a resource whose
	// protocol declares terminal states to that resource type; ownedOrigin
	// is where custody was taken; transferred marks names the function
	// returns, whose custody passes to the caller.
	owned       map[string]string
	ownedOrigin map[string]ast.Node
	transferred map[string]bool
	// pathTypes caches the resource type each known aggregate path holds.
	pathTypes map[string]string
	// own is the contract of the function under analysis, when it has one.
	own    ResourceOperation
	hasOwn bool
	// diverged is set by a `break`: the state after it does not fall
	// through to the join of its branch but to the enclosing loop's exit,
	// collected in loopExits (one slice per open loop).
	diverged  bool
	loopExits [][]*resourceflow.Flow
	// entryModes records, per resource parameter of the function under
	// analysis, the authority its own contract grants on entry.
	entryModes map[string]entryAuthority
	// callableContracts maps a local function-value binding to the global
	// function it was initialized from, whose contract calls through the
	// binding carry; unknownCallables marks function-typed bindings whose
	// contract cannot be known (parameters, closures, reassigned values).
	callableContracts map[string]string
	unknownCallables  map[string]bool
	// parameterContracts holds, per function-typed parameter of the
	// function under analysis, the callable contract its own contract
	// declares: calls through the parameter use it instead of being
	// unknown, and forwarding the parameter compares it exactly.
	parameterContracts map[string]*ResourceCallableContract
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

// callableContract is the contract an operation requires of the function
// value passed as its index-th argument, or nil.
func (op ResourceOperation) callableContract(index int) *ResourceCallableContract {
	for _, declaration := range op.Parameters {
		if declaration.Index == index && declaration.Callable != nil {
			return declaration.Callable
		}
	}
	return nil
}

// argumentContract is the contract a function-valued argument carries: the
// operation of the global it names or was bound from, the declared contract
// of a function-typed parameter, or unknown. known is false for an unknown
// callable; an uncontracted global yields an empty, known contract.
func (a *typedResourceAnalysis) argumentContract(argument ast.Expression) (contract *ResourceCallableContract, known bool) {
	ident, isIdent := argument.(*ast.Identifier)
	if !isIdent || ident == nil {
		return nil, false
	}
	if declared, isParameter := a.parameterContracts[ident.Value]; isParameter {
		return declared, true
	}
	if a.unknownCallables[ident.Value] {
		return nil, false
	}
	global := ident.Value
	if a.isLocalBinding(ident.Value) {
		carried, isCarried := a.callableContracts[ident.Value]
		if !isCarried {
			return nil, false
		}
		global = carried
	} else if a.tc == nil || a.tc.globalEnv == nil {
		return nil, false
	} else if typ, exists := a.tc.globalEnv.GetType(global); !exists {
		return nil, false
	} else if _, isFunction := typ.(*FunctionType); !isFunction {
		return nil, false
	}
	op, contracted := a.contractOperation(global)
	if !contracted {
		return &ResourceCallableContract{}, true
	}
	contract = &ResourceCallableContract{ReturnsFresh: op.ReturnsFresh}
	for _, declaration := range op.Parameters {
		if declaration.Callable == nil {
			contract.Parameters = append(contract.Parameters, ResourceParameterDeclaration{Index: declaration.Index, Mode: declaration.Mode})
		}
	}
	return normalizeCallableContract(contract), true
}

// checkCallableArguments rejects a function value passed for a
// function-typed parameter whose required contract it does not carry
// exactly (OAK-B0116): a consuming function where a borrowed one is
// required, or an uncontracted or unknown value where any mode is
// required. The rejected call has not occurred.
func (a *typedResourceAnalysis) checkCallableArguments(expr *ast.InvocationExpression, op ResourceOperation) bool {
	ok := true
	for _, declaration := range op.Parameters {
		if declaration.Callable == nil || declaration.Index < 0 || declaration.Index >= len(expr.Arguments) {
			continue
		}
		argument := expr.Arguments[declaration.Index]
		required := declaration.Callable
		actual, known := a.argumentContract(argument)
		if known && sameCallableContract(normalizeCallableContract(required), actual) {
			continue
		}
		ok = false
		callee, _ := a.callableIdentity(expr)
		var d *diagnostic.Diagnostic
		if !known {
			d = a.tc.addResourceDiagnosticWithCode(argument, CodeResourceCallableContractMismatch,
				fmt.Sprintf("argument %d to %q must carry the callable contract %s, but its contract is unknown", declaration.Index+1, callee, describeCallableContract(required)))
		} else {
			d = a.tc.addResourceDiagnosticWithCode(argument, CodeResourceCallableContractMismatch,
				fmt.Sprintf("argument %d to %q must carry the callable contract %s, but %s carries %s", declaration.Index+1, callee, describeCallableContract(required), argument.String(), describeCallableContract(actual)))
		}
		d.AddNote("a function value satisfies a callable contract only by exact agreement of every parameter mode and the fresh-return fact; an uncontracted or unknown value satisfies no contract with a mode (docs/spec/50-borrowing.md section 9)")
		d.AddHelp("pass a function whose declared resource contract matches, or declare the required contract on the function you pass")
	}
	return ok
}

// describeCallableContract renders a callable contract for diagnostics.
func describeCallableContract(contract *ResourceCallableContract) string {
	if contract == nil || (len(contract.Parameters) == 0 && !contract.ReturnsFresh) {
		return "(no resource modes)"
	}
	parts := make([]string, 0, len(contract.Parameters)+1)
	for _, declaration := range contract.Parameters {
		parts = append(parts, fmt.Sprintf("parameter %d %s", declaration.Index+1, declaration.Mode))
	}
	if contract.ReturnsFresh {
		parts = append(parts, "fresh result")
	}
	return "(" + strings.Join(parts, ", ") + ")"
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
	type governed struct {
		argument ast.Expression
		required ResourceParameterMode
	}
	positions := make([]governed, 0, len(expr.Arguments)+1)
	if receiver := methodReceiver(expr); receiver != nil && op.Receiver != ResourceParameterUnspecified {
		positions = append(positions, governed{argument: receiver, required: op.Receiver})
	}
	for index, argument := range expr.Arguments {
		positions = append(positions, governed{argument: argument, required: op.parameterMode(index)})
	}
	for _, position := range positions {
		argument, required := position.argument, position.required
		if required == ResourceParameterUnspecified {
			continue
		}
		var names []string
		if ident, isIdent := argument.(*ast.Identifier); isIdent && ident != nil {
			if a.flow.Registered(ident.Value) {
				names = []string{ident.Value}
			} else {
				// An aggregate argument forwards every tracked path below it.
				names = a.aggregatePaths(argument)
			}
		}
		for _, name := range names {
			if !a.flow.Registered(name) {
				continue
			}
			parameter, entry, governed := a.entryAuthorityOf(name)
			if !governed || authorityRank(required) <= authorityRank(entry.mode) {
				continue
			}
			ok = false
			a.reportForwarding(expr, argument, name, parameter, entry, required)
		}
	}
	return ok
}

func (a *typedResourceAnalysis) reportForwarding(expr *ast.InvocationExpression, argument ast.Expression, name, parameter string, entry entryAuthority, required ResourceParameterMode) {
	{
		callee, _ := a.callableIdentity(expr)
		title := fmt.Sprintf("parameter %q enters with %s authority and cannot be passed to the %s parameter of %s", parameter, entry.mode, required, callee)
		d := a.tc.addResourceDiagnosticWithCode(argument, CodeResourceParameterForwarded, title)
		if entry.declaration != nil {
			d.AddSecondary(diagnostic.NodeToRange(entry.declaration), fmt.Sprintf("%q is declared %s by this function's resource contract", parameter, entry.mode))
		}
		if parameter != name {
			for _, edge := range a.flow.AliasPath(parameter, name) {
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
	// A borrowed result lives exactly as long as its binding's scope; the
	// owner is free again once the scope ends.
	leaving := len(a.scopes) - 1
	a.checkScopeExit(leaving)
	for name, scope := range a.dependentScope {
		if scope >= leaving {
			a.expired[name] = a.dependents[name]
			a.expiredScope[name] = scope
			a.expiredDecl[name] = a.dependentDecl[name]
			delete(a.dependents, name)
			delete(a.dependentScope, name)
			delete(a.dependentDecl, name)
		}
	}
	a.scopes = a.scopes[:len(a.scopes)-1]
}

// markOwned records that name holds full custody of a resource of typeName;
// only types whose protocol declares terminal states carry an obligation.
func (a *typedResourceAnalysis) markOwned(name, typeName string, origin ast.Node) {
	if name == "" || typeName == "" {
		return
	}
	if _, obliged := a.model.Obligations[typeName]; !obliged {
		return
	}
	a.owned[name] = typeName
	a.ownedOrigin[name] = origin
}

// inheritOwnership makes destination owned when source is: custody follows
// the class, and whichever name survives carries the obligation.
func (a *typedResourceAnalysis) inheritOwnership(destination, source string, origin ast.Node) {
	if typeName, isOwned := a.owned[source]; isOwned {
		a.owned[destination] = typeName
		a.ownedOrigin[destination] = origin
	}
}

func (a *typedResourceAnalysis) releaseOwned(name string) {
	delete(a.owned, name)
	delete(a.ownedOrigin, name)
}

// rootOf is the binding a name or path belongs to.
func rootOf(name string) string {
	root, _, _ := strings.Cut(name, ".")
	return root
}

// checkScopeExit enforces terminal-state obligations for the names bound
// in scope index as it ends (docs/spec/50-borrowing.md section 9): an owned
// name whose class is not consumed, is not returned, and has no live name
// outside the scope leaves its resource unclosed (OAK-B0120); a class
// consumed on some paths only fails closed the same way.
func (a *typedResourceAnalysis) checkScopeExit(index int) {
	if a == nil || a.flow == nil || index < 0 || index >= len(a.scopes) {
		return
	}
	leaving := a.scopes[index]
	names := make([]string, 0, len(a.owned))
	for name := range a.owned {
		if _, bound := leaving[rootOf(name)]; bound {
			names = append(names, name)
		}
	}
	sort.Strings(names)
	for _, name := range names {
		typeName := a.owned[name]
		if !a.flow.Registered(name) || a.transferred[rootOf(name)] || a.transferred[name] {
			continue
		}
		authority, _ := a.flow.AuthorityOf(name)
		if authority == resourceflow.AuthorityConsumed {
			continue
		}
		// Custody reachable through a name that survives the scope is not
		// lost; the surviving name carries the obligation.
		survives := false
		for _, mate := range a.flow.ClassMates(name) {
			if !a.flow.Registered(mate) {
				continue
			}
			if a.transferred[rootOf(mate)] || a.transferred[mate] {
				survives = true
				break
			}
			// Only a name bound in a scope that outlives this one keeps the
			// class reachable; a mate from an already-ended inner scope, or
			// from this scope, leaves with it.
			if outer := a.scopeOf(rootOf(mate)); outer >= 0 && outer < index && a.owned[mate] != "" {
				survives = true
				break
			}
		}
		if survives {
			continue
		}
		a.reportUnclosed(name, typeName, authority)
	}
}

func (a *typedResourceAnalysis) reportUnclosed(name, typeName string, authority resourceflow.Authority) {
	obligation := a.model.Obligations[typeName]
	closers := "a consuming transition into " + strings.Join(quoteAll(obligation.Terminal), " or ")
	if len(obligation.Closers) > 0 {
		closers = strings.Join(quoteAll(obligation.Closers), ", ")
	}
	title := fmt.Sprintf("resource %q of type %s leaves scope without reaching a terminal state (%s)", name, typeName, strings.Join(obligation.Terminal, ", "))
	if authority == resourceflow.AuthorityMaybeConsumed {
		title = fmt.Sprintf("resource %q of type %s reaches a terminal state on some paths only (%s)", name, typeName, strings.Join(obligation.Terminal, ", "))
	}
	node := a.ownedOrigin[name]
	d := a.tc.addResourceDiagnosticWithCode(node, CodeResourceUnclosed, title)
	if node != nil {
		d.AddSecondary(diagnostic.NodeToRange(node), fmt.Sprintf("%q took custody of the resource here", name))
	}
	d.AddNote(fmt.Sprintf("a resource whose protocol declares terminal states must reach one — through %s — before its last name leaves scope, or pass its custody on by being returned or consumed (docs/spec/50-borrowing.md section 9)", closers))
	d.AddHelp("close the resource on every path before the scope ends, return it, or hand it to a consuming operation")
}

// typeNameOf is the nominal name of a type expression, for obligations.
func (m ResourceModel) typeNameOf(expr ast.Expression) string {
	switch t := expr.(type) {
	case *ast.Identifier:
		return t.Value
	case *ast.IndexExpression:
		if ident, ok := t.Left.(*ast.Identifier); ok {
			return ident.Value
		}
	}
	if expr == nil {
		return ""
	}
	return expr.String()
}

// scopeOf is the index of the lexical scope that binds name, or -1 for a
// name bound outside the function (a global).
func (a *typedResourceAnalysis) scopeOf(name string) int {
	for i := len(a.scopes) - 1; i >= 0; i-- {
		if _, exists := a.scopes[i][name]; exists {
			return i
		}
	}
	return -1
}

func cloneOwnerSet(owners map[string]bool) map[string]bool {
	if owners == nil {
		return nil
	}
	cloned := make(map[string]bool, len(owners))
	for owner := range owners {
		cloned[owner] = true
	}
	return cloned
}

func sortedOwners(owners map[string]bool) []string {
	names := make([]string, 0, len(owners))
	for owner := range owners {
		names = append(names, owner)
	}
	sort.Strings(names)
	return names
}

// cloneDependents snapshots the dependency state before a branch;
// mergeDependents unions the states after the branches so that no
// dependency established on any path is dropped (a conservative set,
// never fresh authority).
func (a *typedResourceAnalysis) cloneDependents() (map[string]map[string]bool, map[string]int, map[string]ast.Node) {
	deps := make(map[string]map[string]bool, len(a.dependents))
	for name, owners := range a.dependents {
		deps[name] = cloneOwnerSet(owners)
	}
	scopes := make(map[string]int, len(a.dependentScope))
	for name, scope := range a.dependentScope {
		scopes[name] = scope
	}
	decls := make(map[string]ast.Node, len(a.dependentDecl))
	for name, decl := range a.dependentDecl {
		decls[name] = decl
	}
	return deps, scopes, decls
}

func (a *typedResourceAnalysis) mergeDependents(deps map[string]map[string]bool, scopes map[string]int, decls map[string]ast.Node) {
	for name, owners := range deps {
		if a.dependents[name] == nil {
			a.dependents[name] = make(map[string]bool)
		}
		for owner := range owners {
			a.dependents[name][owner] = true
		}
		if _, known := a.dependentScope[name]; !known {
			a.dependentScope[name] = scopes[name]
			a.dependentDecl[name] = decls[name]
		}
	}
}

// setDependent records name as a borrowed result depending on owners, bound
// in scope.
func (a *typedResourceAnalysis) setDependent(name string, owners map[string]bool, scope int, decl ast.Node, mutable bool) {
	a.dependents[name] = cloneOwnerSet(owners)
	a.dependentScope[name] = scope
	a.dependentDecl[name] = decl
	if mutable {
		a.mutableDependents[name] = true
	} else {
		delete(a.mutableDependents, name)
	}
}

func (a *typedResourceAnalysis) clearDependent(name string) {
	delete(a.dependents, name)
	delete(a.dependentScope, name)
	delete(a.dependentDecl, name)
	delete(a.mutableDependents, name)
}

// suspendedBy lists the live mutable reborrows whose owners include name
// or an alias of it: while any exists, name is suspended.
func (a *typedResourceAnalysis) suspendedBy(name string) []string {
	var out []string
	for _, dependent := range a.ownerDependents(name) {
		if a.mutableDependents[dependent] {
			out = append(out, dependent)
		}
	}
	return out
}

func (a *typedResourceAnalysis) reportSuspended(node ast.Node, name, dependent string, how string) {
	range_ := diagnostic.NodeToRange(node)
	key := fmt.Sprintf("suspended:%s@%d:%d", name, range_.Start.Line, range_.Start.Character)
	if a.reported[key] {
		return
	}
	a.reported[key] = true
	title := fmt.Sprintf("%q is suspended by a temporary mutable reborrow passed to the same call and cannot be %s", name, how)
	if dependent != "" {
		title = fmt.Sprintf("%q is suspended while the mutable reborrow %q lives and cannot be %s", name, dependent, how)
	}
	d := a.tc.addResourceDiagnosticWithCode(node, CodeResourceSuspendedOwner, title)
	if decl := a.dependentDecl[dependent]; dependent != "" && decl != nil {
		d.AddSecondary(diagnostic.NodeToRange(decl), fmt.Sprintf("%q was bound here as a mutable reborrow of %q", dependent, name))
	}
	d.AddNote("a mutable reborrow holds its owner's mutable authority for as long as its scope: the owner is suspended entirely — no reads, projections, calls, rebinding, or return — and usable again when the reborrow's scope ends (docs/spec/50-borrowing.md section 9)")
	d.AddHelp("finish with the reborrow in an inner scope before using its owner, or borrow it as shared instead")
}

// dependentOf reports whether name is a borrowed result (or an alias of
// one): the dependent binding and the owners it depends on.
func (a *typedResourceAnalysis) dependentOf(name string) (string, map[string]bool, bool) {
	if owners, direct := a.dependents[name]; direct {
		return name, owners, true
	}
	names := make([]string, 0, len(a.dependents))
	for dependent := range a.dependents {
		names = append(names, dependent)
	}
	sort.Strings(names)
	for _, dependent := range names {
		if a.flow.Registered(name) && a.flow.Registered(dependent) && a.flow.Aliases(name, dependent) {
			return dependent, a.dependents[dependent], true
		}
	}
	return "", nil, false
}

// ownerDependents lists the live borrowed results that depend on name (or
// on a name aliasing it), sorted for deterministic diagnostics.
func (a *typedResourceAnalysis) ownerDependents(name string) []string {
	var out []string
	for dependent, owners := range a.dependents {
		for owner := range owners {
			if owner == name || (a.flow.Registered(name) && a.flow.Registered(owner) && a.flow.Aliases(owner, name)) {
				out = append(out, dependent)
				break
			}
		}
	}
	sort.Strings(out)
	return out
}

// borrowOwners resolves the owners a borrow of argument would depend on:
// a temporary borrowed result's owners, a dependent's owners, or the
// argument's own tracked name. ok is false without tracked provenance.
func (a *typedResourceAnalysis) borrowOwners(argument ast.Expression) (map[string]bool, bool) {
	if call, isCall := argument.(*ast.InvocationExpression); isCall {
		if owners, borrowed := a.borrowCalls[call]; borrowed {
			return cloneOwnerSet(owners), len(owners) > 0
		}
	}
	name, ok := a.trackedName(argument)
	if !ok || !a.flow.CanUse(name) || a.unknownResources[name] {
		return nil, false
	}
	if _, owners, isDependent := a.dependentOf(name); isDependent {
		return cloneOwnerSet(owners), len(owners) > 0
	}
	return map[string]bool{name: true}, true
}

func (a *typedResourceAnalysis) reportDependent(node ast.Node, title string, dependent string, owners map[string]bool) *diagnostic.Diagnostic {
	d := a.tc.addResourceDiagnosticWithCode(node, CodeResourceDependentResult, title)
	if decl := a.dependentDecl[dependent]; decl != nil {
		d.AddSecondary(diagnostic.NodeToRange(decl), fmt.Sprintf("%q was bound here as a borrowed result of %s", dependent, strings.Join(quoteAll(sortedOwners(owners)), ", ")))
	}
	d.AddNote("a borrowed result holds shared authority that depends on its owner: while it lives the owner is readable but cannot be mutated, consumed, or rebound, and the result itself cannot be mutated, consumed, stored, or outlive its scope (docs/spec/50-borrowing.md section 9)")
	return d
}

func quoteAll(names []string) []string {
	out := make([]string, len(names))
	for i, name := range names {
		out[i] = fmt.Sprintf("%q", name)
	}
	return out
}

// checkDependentAccess enforces a live borrowed result's dependency at a
// call (OAK-B0118): neither the result nor a temporary borrowed result may
// be passed to a borrowed-mut or consuming position, and neither may its
// owner while the result lives. It reports every offending argument and
// returns false when any was found, so the call has not occurred.
func (a *typedResourceAnalysis) checkDependentAccess(expr *ast.InvocationExpression, op ResourceOperation) bool {
	type governed struct {
		argument ast.Expression
		required ResourceParameterMode
	}
	positions := make([]governed, 0, len(expr.Arguments)+1)
	if receiver := methodReceiver(expr); receiver != nil && op.Receiver != ResourceParameterUnspecified {
		positions = append(positions, governed{argument: receiver, required: op.Receiver})
	}
	for index, argument := range expr.Arguments {
		positions = append(positions, governed{argument: argument, required: op.parameterMode(index)})
	}
	// Owners borrowed by temporary results passed to this same call are
	// protected for the call's duration; owners of a temporary mutable
	// reborrow are suspended for it.
	temporaryOwners := make(map[string]bool)
	suspendedOwners := make(map[string]bool)
	for _, position := range positions {
		if call, isCall := position.argument.(*ast.InvocationExpression); isCall {
			for owner := range a.borrowCalls[call] {
				temporaryOwners[owner] = true
				if a.mutableCalls[call] {
					suspendedOwners[owner] = true
				}
			}
		}
	}
	callee, _ := a.callableIdentity(expr)
	ok := true
	for _, position := range positions {
		if _, isCall := position.argument.(*ast.InvocationExpression); isCall || len(suspendedOwners) == 0 {
			continue
		}
		name, tracked := a.trackedName(position.argument)
		if !tracked {
			continue
		}
		for owner := range suspendedOwners {
			if owner == name || (a.flow.Registered(owner) && a.flow.Aliases(owner, name)) {
				ok = false
				a.reportSuspended(position.argument, name, "", fmt.Sprintf("passed to %s", callee))
				break
			}
		}
	}
	for _, position := range positions {
		if position.required == ResourceParameterUnspecified || authorityRank(position.required) <= authorityRank(ResourceParameterBorrowed) {
			continue
		}
		if call, isCall := position.argument.(*ast.InvocationExpression); isCall {
			if owners, borrowed := a.borrowCalls[call]; borrowed {
				if a.mutableCalls[call] && position.required == ResourceParameterBorrowedMut {
					// A mutable reborrow carries mutable authority.
					continue
				}
				ok = false
				a.reportDependent(position.argument, fmt.Sprintf("a borrowed result cannot be passed to the %s parameter of %s: it holds %s authority borrowed from %s", position.required, callee, permissionWord(a.mutableCalls[call]), describeOwners(owners)), "", owners)
			}
			continue
		}
		name, tracked := a.trackedName(position.argument)
		if !tracked {
			continue
		}
		if dependent, owners, isDependent := a.dependentOf(name); isDependent {
			if a.mutableDependents[dependent] && position.required == ResourceParameterBorrowedMut {
				continue
			}
			ok = false
			a.reportDependent(position.argument, fmt.Sprintf("%q is a %s borrowed result of %s and cannot be passed to the %s parameter of %s", name, permissionWord(a.mutableDependents[dependent]), describeOwners(owners), position.required, callee), dependent, owners)
			continue
		}
		if dependents := a.ownerDependents(name); len(dependents) > 0 {
			ok = false
			a.reportDependent(position.argument, fmt.Sprintf("%q cannot be passed to the %s parameter of %s while %q borrows from it", name, position.required, callee, dependents[0]), dependents[0], a.dependents[dependents[0]])
			continue
		}
		for owner := range temporaryOwners {
			if owner == name || (a.flow.Registered(owner) && a.flow.Aliases(owner, name)) {
				ok = false
				a.reportDependent(position.argument, fmt.Sprintf("%q cannot be passed to the %s parameter of %s while a borrowed result of it is passed to the same call", name, position.required, callee), "", nil)
				break
			}
		}
	}
	return ok
}

func permissionWord(mutable bool) string {
	if mutable {
		return "mutable"
	}
	return "shared"
}

func describeOwners(owners map[string]bool) string {
	if len(owners) == 0 {
		return "an untracked resource"
	}
	return strings.Join(quoteAll(sortedOwners(owners)), " or ")
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
			// was initialized from, and nothing else; a contracted
			// function-typed parameter is named by itself.
			if global, carried := a.callableContracts[function.Value]; carried {
				return global, true
			}
			if _, declared := a.parameterContracts[function.Value]; declared {
				return function.Value, true
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
	if callee, isIdent := expr.Function.(*ast.Identifier); isIdent && callee != nil {
		if contract, declared := a.parameterContracts[callee.Value]; declared && a.isLocalBinding(callee.Value) {
			// A call through a function-typed parameter uses the contract
			// this function declared for it.
			op := ResourceOperation{ReturnsFresh: contract.ReturnsFresh}
			op.Parameters = append(op.Parameters, contract.Parameters...)
			for _, declaration := range contract.Parameters {
				if declaration.Mode == ResourceParameterConsumed {
					op.Consumes = append(op.Consumes, declaration.Index)
				}
			}
			return op, true
		}
	}
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
		a.reassign(s)
	case *ast.IndexAssignmentStatement:
		if s.Target != nil {
			if !s.Target.Dot {
				a.expression(s.Target.Left)
				a.expression(s.Target.Index)
			} else if _, isPath := resourceName(s.Target); !isPath {
				a.expression(s.Target.Left)
			}
		}
		a.expression(s.Value)
		// An aggregate write b.inner = v gives the field path v's
		// provenance (docs/spec/50-borrowing.md section 9); writes through
		// indices or to untracked records leave nothing tracked.
		if s.Target != nil && s.Target.Dot {
			if path, isPath := resourceName(s.Target); isPath && (a.flow.Registered(path) || a.unknownResources[path] || a.isResourceValue(s.Value)) {
				a.bindPath(path, s.Value, s.Target)
			}
		}
	case *ast.ExpressionStatement:
		a.expression(s.Expression)
	case *ast.BreakStatement:
		// Control leaves the loop here: this path's state joins the loop's
		// exit, not the fall-through of the enclosing branch.
		if n := len(a.loopExits); n > 0 {
			a.loopExits[n-1] = append(a.loopExits[n-1], a.flow.Clone())
		}
		a.diverged = true
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

	// An aggregate binding (a record or ADT holding resources) is bound
	// path by path, whatever its initializer's result fact.
	if stmt.Type != nil {
		if len(a.resourcePaths(stmt.Name.Value, a.tc.parseTypeExpression(stmt.Type))) > 0 {
			a.bindRecordFields(stmt)
			return
		}
	} else if a.tc.env != nil {
		if len(a.resourcePaths(stmt.Name.Value, a.tc.env.CheckedDeclarationType(stmt))) > 0 {
			a.bindRecordFields(stmt)
			return
		}
	}

	fresh := false
	borrowed := false
	if call, ok := stmt.Value.(*ast.InvocationExpression); ok {
		if a.freshCalls[call] {
			fresh = true
		}
		if _, isBorrow := a.borrowCalls[call]; isBorrow {
			borrowed = true
		}
	}
	isResource := a.model.isResourceType(stmt.Type) || fresh || borrowed
	if !isResource {
		a.bindRecordFields(stmt)
		return
	}

	if source, ok := stmt.Value.(*ast.Identifier); ok {
		if a.flow.Registered(source.Value) {
			if a.flow.CanUse(source.Value) {
				a.flow.Alias(stmt.Name.Value, source.Value, stmt.Name)
				a.inheritOwnership(stmt.Name.Value, source.Value, stmt.Name)
				if dependent, owners, isDependent := a.dependentOf(source.Value); isDependent {
					// An alias of a borrowed result carries its dependency
					// and its permission.
					a.setDependent(stmt.Name.Value, owners, len(a.scopes)-1, stmt.Name, a.mutableDependents[dependent])
				}
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
		// input resource consumed by the operation. Fresh authority is owned:
		// the binding owes its protocol's terminal state.
		a.flow.Register(stmt.Name.Value, stmt.Name)
		a.markOwned(stmt.Name.Value, a.declaredTypeName(stmt), stmt.Name)
		return
	}
	if call, ok := stmt.Value.(*ast.InvocationExpression); ok {
		if source, aliased := a.aliasCalls[call]; aliased {
			// A declared alias result gives the binding the argument's own
			// authority; an argument without provenance leaves it unknown.
			if source != "" && a.flow.CanUse(source) {
				a.flow.Alias(stmt.Name.Value, source, stmt.Name)
			} else {
				a.unknownResources[stmt.Name.Value] = true
			}
			return
		}
	}

	if call, ok := stmt.Value.(*ast.InvocationExpression); ok {
		if owners, isBorrow := a.borrowCalls[call]; isBorrow {
			// A declared borrowed result is its own authority (distinct from
			// its owner for exclusivity) that depends on the owner for as
			// long as this scope; an owner without provenance leaves it
			// unknown so exclusive and consuming use fail closed.
			if len(owners) == 0 {
				a.unknownResources[stmt.Name.Value] = true
				return
			}
			a.flow.Register(stmt.Name.Value, stmt.Name)
			a.setDependent(stmt.Name.Value, owners, len(a.scopes)-1, stmt.Name, a.mutableCalls[call])
			return
		}
	}

	if typeName, constructed := a.isTypestateConstruction(stmt.Value); constructed {
		// Constructing a typestate-indexed handle is fresh authority
		// (docs/spec/112-protocols.md section 5a, rule 4).
		a.flow.Register(stmt.Name.Value, stmt.Name)
		a.markOwned(stmt.Name.Value, typeName, stmt.Name)
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
	a.markOwned(stmt.Name.Value, a.declaredTypeName(stmt), stmt.Name)
}

// declaredTypeName is the nominal type of a variable declaration, from its
// annotation or the checked declaration type.
func (a *typedResourceAnalysis) declaredTypeName(stmt *ast.VariableDeclaration) string {
	if stmt == nil {
		return ""
	}
	if stmt.Type != nil {
		return a.model.typeNameOf(stmt.Type)
	}
	if a.tc != nil && a.tc.env != nil {
		return nominalTypeName(a.tc.env.CheckedDeclarationType(stmt))
	}
	return ""
}

func (a *typedResourceAnalysis) ifStatement(stmt *ast.IfStatement) {
	if stmt == nil {
		return
	}
	a.expression(stmt.Condition)
	incoming := a.flow.Clone()
	incomingDeps, incomingScopes, incomingDecls := a.cloneDependents()

	outerDiverged := a.diverged
	a.diverged = false
	a.flow = incoming.Clone()
	a.block(stmt.Consequence)
	consequence := a.flow.Clone()
	consequenceDiverged := a.diverged
	consequenceDeps, consequenceScopes, consequenceDecls := a.cloneDependents()

	a.diverged = false
	a.flow = incoming.Clone()
	a.dependents, a.dependentScope, a.dependentDecl = incomingDeps, incomingScopes, incomingDecls
	switch alternative := stmt.Alternative.(type) {
	case nil:
	case *ast.IfStatement:
		a.ifStatement(alternative)
	case *ast.BlockStatement:
		a.block(alternative)
	}
	alternative := a.flow.Clone()
	alternativeDiverged := a.diverged
	a.flow = joinReachable([]*resourceflow.Flow{consequence, alternative}, []bool{consequenceDiverged, alternativeDiverged}, incoming)
	a.diverged = outerDiverged || (consequenceDiverged && alternativeDiverged)
	// Every dependency established on either path survives the join.
	a.mergeDependents(consequenceDeps, consequenceScopes, consequenceDecls)
}

// joinReachable joins the branch states that fall through; a branch that
// left by `break` contributes to its loop's exit instead. When no branch
// falls through the result is the (unreachable) incoming state.
func joinReachable(branches []*resourceflow.Flow, diverged []bool, incoming *resourceflow.Flow) *resourceflow.Flow {
	reachable := make([]*resourceflow.Flow, 0, len(branches))
	for i, branch := range branches {
		if !diverged[i] {
			reachable = append(reachable, branch)
		}
	}
	if len(reachable) == 0 {
		return incoming.Clone()
	}
	return resourceflow.Join(reachable...)
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
	incomingDeps, incomingScopes, incomingDecls := a.cloneDependents()
	outerDiverged := a.diverged
	a.loopExits = append(a.loopExits, nil)

	a.diverged = false
	a.flow = incoming.Clone()
	a.expression(stmt.Condition)
	a.block(stmt.Body)
	oneIteration := a.flow.Clone()
	oneDiverged := a.diverged

	invariant := oneIteration
	if !oneDiverged {
		invariant = resourceflow.Join(incoming, oneIteration)
	} else {
		invariant = incoming
	}
	a.diverged = false
	a.flow = invariant.Clone()
	a.expression(stmt.Condition)
	a.block(stmt.Body)
	twoIterations := a.flow.Clone()
	twoDiverged := a.diverged

	// The loop exits when its condition fails (after zero, one, or two
	// probed iterations that fell through) or through any break.
	exits := []*resourceflow.Flow{incoming}
	if !oneDiverged {
		exits = append(exits, oneIteration)
	}
	if !twoDiverged {
		exits = append(exits, twoIterations)
	}
	exits = append(exits, a.loopExits[len(a.loopExits)-1]...)
	a.loopExits = a.loopExits[:len(a.loopExits)-1]
	a.flow = resourceflow.Join(exits...)
	a.diverged = outerDiverged
	// Dependencies established by any iteration, or by none, all survive.
	a.mergeDependents(incomingDeps, incomingScopes, incomingDecls)
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
		if path, isPath := resourceName(e); isPath && e.Dot && a.flow.Registered(path) {
			// A projection of a tracked record field is a use of that
			// field's authority, not of the whole record.
			a.use(path, e)
			return
		}
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
		a.checkTypestateConstruction(e)
		if len(e.FieldOrder) > 0 {
			for _, field := range e.FieldOrder {
				a.expression(field.Value)
				if ident, isIdent := field.Value.(*ast.Identifier); isIdent {
					// A borrowed result in a record field is judged by its
					// destination (bindPath); parameters keep the retention rule.
					if _, _, isDependent := a.dependentOf(ident.Value); !isDependent {
						a.checkRetention(ident, "stored in a record")
					}
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
	delete(a.aliasCalls, expr)
	delete(a.borrowCalls, expr)
	delete(a.mutableCalls, expr)
	diagnosticsBefore := len(a.tc.Diagnostics())
	// The callee identifier is not a resource value. Non-identifier callees
	// may themselves evaluate expressions, so preserve their effects.
	if _, simple := expr.Function.(*ast.Identifier); !simple {
		a.expression(expr.Function)
	}
	for _, argument := range expr.Arguments {
		a.expression(argument)
	}
	if !a.checkAggregateEscape(expr) {
		return
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
	if len(a.tc.Diagnostics()) != diagnosticsBefore || !a.checkDependentAccess(expr, op) || !a.checkCallResourceExclusivity(expr, op) {
		return
	}
	if !a.checkParameterForwarding(expr, op) {
		return
	}
	if !a.checkCallableArguments(expr, op) {
		return
	}
	if receiver := methodReceiver(expr); receiver != nil && op.Receiver == ResourceParameterConsumed {
		if ident, ok := receiver.(*ast.Identifier); ok && ident != nil && a.flow.Registered(ident.Value) && a.flow.CanUse(ident.Value) {
			a.flow.Consume(ident.Value, expr)
		}
	}
	for _, index := range op.Consumes {
		if index < 0 || index >= len(expr.Arguments) {
			continue
		}
		name, ok := a.trackedName(expr.Arguments[index])
		if !ok {
			// Consuming an aggregate moves the whole value: every tracked
			// resource path below it is consumed (partial states come later).
			for _, path := range a.aggregatePaths(expr.Arguments[index]) {
				if a.flow.Registered(path) && a.flow.CanUse(path) {
					a.flow.Consume(path, expr)
				}
			}
			continue
		}
		// Argument evaluation already performed the ordinary Use check. If it
		// failed, do not emit a second diagnostic for the consuming action.
		if a.flow.CanUse(name) {
			a.flow.Consume(name, expr)
		}
	}
	a.freshCalls[expr] = op.ReturnsFresh
	if op.ReturnsAlias {
		// The result is the aliased argument's authority under a new name.
		// When the operation also consumes that argument, every name the
		// class had is now dead and the result is its only surviving name,
		// which the caller cannot distinguish from a new class: track it as
		// fresh rather than as an alias of consumed names.
		consumed := false
		for _, index := range op.Consumes {
			consumed = consumed || index == op.AliasesArgument
		}
		if consumed {
			a.freshCalls[expr] = true
			return
		}
		source := ""
		if op.AliasesArgument >= 0 && op.AliasesArgument < len(expr.Arguments) {
			if name, ok := a.trackedName(expr.Arguments[op.AliasesArgument]); ok && a.flow.CanUse(name) && !a.unknownResources[name] {
				source = name
			}
		}
		a.aliasCalls[expr] = source
	}
	if op.ReturnsBorrow {
		// The result is a shared borrow dependent on the argument's root
		// owners (a borrow of a borrowed result depends on the same owners).
		// A multiple-origin result depends on every declared argument's
		// owners; one argument without provenance makes the whole result
		// unknown, since a dependency cannot be partially proven.
		owners := make(map[string]bool)
		for _, index := range op.BorrowsArguments {
			if index < 0 || index >= len(expr.Arguments) {
				owners = nil
				break
			}
			argumentOwners, ok := a.borrowOwners(expr.Arguments[index])
			if !ok {
				owners = nil
				break
			}
			for owner := range argumentOwners {
				owners[owner] = true
			}
		}
		a.borrowCalls[expr] = owners
		a.mutableCalls[expr] = op.BorrowMutable
	}
}

func (a *typedResourceAnalysis) match(expr *ast.MatchExpression) {
	if expr == nil {
		return
	}
	a.expression(expr.Scrutinee)
	scrutineeType := a.tc.env.CheckedExpressionType(expr.Scrutinee)
	incoming := a.flow.Clone()
	incomingDeps, incomingScopes, incomingDecls := a.cloneDependents()
	branches := make([]*resourceflow.Flow, 0, len(expr.Arms))
	divergences := make([]bool, 0, len(expr.Arms))
	outerDiverged := a.diverged
	mergedDeps, mergedScopes, mergedDecls := a.cloneDependents()
	for _, arm := range expr.Arms {
		if arm == nil {
			continue
		}
		a.diverged = false
		a.flow = incoming.Clone()
		a.dependents, a.dependentScope, a.dependentDecl = incomingDeps, incomingScopes, incomingDecls
		incomingDeps, incomingScopes, incomingDecls = a.cloneDependents()
		// A payload binding lives for its arm only.
		a.pushScope()
		a.bindPattern(arm.Pattern, expr.Scrutinee, "", scrutineeType)
		a.expression(arm.Body)
		a.popScope()
		branches = append(branches, a.flow.Clone())
		divergences = append(divergences, a.diverged)
		armDeps, armScopes, armDecls := a.cloneDependents()
		a.dependents, a.dependentScope, a.dependentDecl = mergedDeps, mergedScopes, mergedDecls
		a.mergeDependents(armDeps, armScopes, armDecls)
		mergedDeps, mergedScopes, mergedDecls = a.dependents, a.dependentScope, a.dependentDecl
	}
	a.dependents, a.dependentScope, a.dependentDecl = mergedDeps, mergedScopes, mergedDecls
	if len(branches) == 0 {
		a.flow = incoming
		a.diverged = outerDiverged
		return
	}
	a.flow = joinReachable(branches, divergences, incoming)
	allDiverged := true
	for _, d := range divergences {
		allDiverged = allDiverged && d
	}
	a.diverged = outerDiverged || allDiverged
}

// bindPattern gives the names a pattern binds the provenance of the
// scrutinee's corresponding paths (docs/spec/50-borrowing.md section 9,
// "Resources through aggregates"): a variant pattern descends into
// $Variant, a binding pattern aliases its name to the path it stands for
// — so inspecting the binding is a use of the payload's authority and
// consuming it consumes the payload's location — and a scrutinee that is a
// contracted call binds by the call's result fact. Wildcards and literals
// bind nothing.
func (a *typedResourceAnalysis) bindPattern(pattern ast.Pattern, scrutinee ast.Expression, relative string, typ Type) {
	switch p := pattern.(type) {
	case *ast.VariantPattern:
		if p == nil || p.Variant == nil || p.Payload == nil {
			return
		}
		a.bindPattern(p.Payload, scrutinee, relative+".$"+p.Variant.Value, a.tc.payloadTypeOfVariant(typ, p.Variant.Value))
	case *ast.BindingPattern:
		if p == nil || p.Name == nil {
			return
		}
		name := p.Name.Value
		a.bind(name)
		isResource := typ != nil && a.model.ResourceTypes[nominalTypeName(typ)]
		destinations := []string{name}
		if !isResource {
			destinations = a.resourcePaths(name, typ)
		}
		if len(destinations) == 0 {
			return
		}
		if source, ok := resourceName(scrutinee); ok {
			for _, destination := range destinations {
				a.bindPathFrom(destination, source+relative+destination[len(name):], p.Name)
			}
			return
		}
		if call, isCall := scrutinee.(*ast.InvocationExpression); isCall {
			for _, destination := range destinations {
				a.flow.Forget(destination)
				delete(a.unknownResources, destination)
				switch {
				case a.freshCalls[call]:
					a.flow.Register(destination, p.Name)
					if isResource {
						a.markOwned(destination, nominalTypeName(typ), p.Name)
					} else {
						a.markOwned(destination, a.tc.resourcePathTypesOf(name, typ, a.model.ResourceTypes)[destination], p.Name)
					}
				case a.aliasCalls[call] != "" && a.flow.CanUse(a.aliasCalls[call]):
					a.flow.Alias(destination, a.aliasCalls[call], p.Name)
				case len(a.borrowCalls[call]) > 0 && a.adoptDependency(destination, a.borrowCalls[call], a.mutableCalls[call], p.Name, scrutinee):
					a.flow.Register(destination, p.Name)
				default:
					a.unknownResources[destination] = true
				}
			}
			return
		}
		for _, destination := range destinations {
			a.unknownResources[destination] = true
		}
	}
}

func (a *typedResourceAnalysis) use(name string, node ast.Node) {
	if a == nil || a.flow == nil || name == "" || !a.flow.Registered(name) {
		return
	}
	if suspended := a.suspendedBy(name); len(suspended) > 0 {
		a.reportSuspended(node, name, suspended[0], "used")
		return
	}
	if a.flow.CanUse(name) {
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
