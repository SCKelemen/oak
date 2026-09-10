package typechecker

import (
	"strings"

	"github.com/SCKelemen/oak/ast"
)

// GeneralizationBarrier records one reason a locally inferred type must remain
// monomorphic. Inference may still determine a precise type; this gate controls
// only whether free type variables may be universally quantified for reuse.
type GeneralizationBarrier uint32

const (
	GeneralizationMutableAuthority GeneralizationBarrier = 1 << iota
	GeneralizationUniqueAuthority
	GeneralizationRegionBound
	GeneralizationExternalAuthority
	GeneralizationEffectfulCapture
	GeneralizationUnsafeAssumption
	GeneralizationUnknownAuthority
)

// GeneralizationFacts are supplied by ownership/effect/region analysis. Keeping
// these facts separate from Type preserves Oak's orthogonal semantic axes: a
// semantic type does not become a different type merely because one expression
// captures authority that prevents polymorphic generalization.
type GeneralizationFacts struct {
	Barriers GeneralizationBarrier
}

func (facts GeneralizationFacts) Safe() bool {
	return facts.Barriers == 0
}

func (facts GeneralizationFacts) Has(barrier GeneralizationBarrier) bool {
	return facts.Barriers&barrier != 0
}

func (facts GeneralizationFacts) With(barrier GeneralizationBarrier) GeneralizationFacts {
	facts.Barriers |= barrier
	return facts
}

// Reasons returns stable human-facing barrier names for diagnostics/tooling.
func (facts GeneralizationFacts) Reasons() []string {
	var reasons []string
	for _, entry := range []struct {
		barrier GeneralizationBarrier
		name    string
	}{
		{GeneralizationMutableAuthority, "mutable authority"},
		{GeneralizationUniqueAuthority, "unique authority"},
		{GeneralizationRegionBound, "region-bound value"},
		{GeneralizationExternalAuthority, "external authority"},
		{GeneralizationEffectfulCapture, "effectful capture"},
		{GeneralizationUnsafeAssumption, "unsafe assumption"},
		{GeneralizationUnknownAuthority, "unresolved authority"},
	} {
		if facts.Has(entry.barrier) {
			reasons = append(reasons, entry.name)
		}
	}
	return reasons
}

func (facts GeneralizationFacts) String() string {
	if facts.Safe() {
		return "safe to generalize"
	}
	return "cannot generalize: " + strings.Join(facts.Reasons(), ", ")
}

// GeneralizeWithFacts performs ordinary free-variable generalization only when
// the authority/effect/region facts prove that universal quantification is safe.
// A blocked binding remains fully inferred but monomorphic.
func GeneralizeWithFacts(typ Type, env *TypeEnvironment, facts GeneralizationFacts) *TypeScheme {
	if facts.Safe() {
		return Generalize(typ, env)
	}
	scheme := makeMonomorphicSchemeInEnv(typ, nil, env)
	scheme.GeneralizationBarriers = facts.Barriers
	return scheme
}

// factsFromType conservatively extracts authority and region evidence already
// represented by the checker type. It recurses through data containers, but not
// through function parameters/results: accepting a function value does not
// acquire the authority that a future caller may pass to it.
func factsFromType(typ Type) GeneralizationFacts {
	facts := GeneralizationFacts{}
	var visit func(Type)
	visit = func(current Type) {
		switch t := current.(type) {
		case *AtomicType:
			facts = facts.With(GeneralizationMutableAuthority).With(GeneralizationUniqueAuthority)
		case *PrimitiveType:
			if t.Name == "ptr" || t.Name == "uptr" {
				facts = facts.With(GeneralizationExternalAuthority).With(GeneralizationUnknownAuthority)
			}
		case *ArrayType:
			visit(t.ElementType)
			if t.IsSpan {
				facts = facts.With(GeneralizationMutableAuthority).
					With(GeneralizationUniqueAuthority).
					With(GeneralizationRegionBound)
			} else if t.IsSlice {
				facts = facts.With(GeneralizationRegionBound)
			} else {
				facts = facts.With(GeneralizationMutableAuthority).
					With(GeneralizationUniqueAuthority)
			}
		case *RecordType:
			for _, field := range t.Fields {
				visit(field)
			}
		case *GenericType:
			for _, arg := range t.TypeArgs {
				visit(arg)
			}
			switch t.Name {
			case "Arena":
				facts = facts.With(GeneralizationUniqueAuthority).With(GeneralizationRegionBound)
			case "View":
				facts = facts.With(GeneralizationRegionBound)
			case "Span":
				facts = facts.With(GeneralizationMutableAuthority).
					With(GeneralizationUniqueAuthority).
					With(GeneralizationRegionBound)
			case "Mmio", "MMIO":
				facts = facts.With(GeneralizationExternalAuthority)
			}
		case *NarrowedADTVariantType:
			for _, arg := range t.TypeArgs {
				visit(arg)
			}
		case *UnionType:
			for _, member := range t.Types {
				visit(member)
			}
		case *IntersectionType:
			for _, member := range t.Types {
				visit(member)
			}
		}
	}
	if typ != nil {
		visit(typ)
	}
	return facts
}

// functionCaptureFacts identifies outer bindings referenced by a closure.
// Oak bindings are assignable, so capturing one preserves mutable authority;
// contained view/span/raw-pointer types add their more specific evidence.
// Unsafe assumptions are lexically visible in the captured function body.
func functionCaptureFacts(fn *ast.FunctionLiteral, env *TypeEnvironment) GeneralizationFacts {
	return functionCaptureFactsWithBound(fn, env, nil)
}

// methodSelectorFacts propagates authority carried by the method implementation
// while keeping ordinary field selector names out of lexical binding lookup.
func methodSelectorFacts(selector *ast.IndexExpression, env *TypeEnvironment) GeneralizationFacts {
	if selector == nil || (!selector.Dot && selector.Token.Literal != ".") {
		return GeneralizationFacts{}
	}
	method, ok := selector.Index.(*ast.Identifier)
	if !ok {
		return GeneralizationFacts{Barriers: GeneralizationUnknownAuthority}
	}
	receiverType := generalizationExpressionType(selector.Left, env)
	adt, ok := receiverType.(*ADTType)
	if !ok {
		return GeneralizationFacts{Barriers: GeneralizationUnknownAuthority}
	}
	scheme, found := env.Get(adt.Name + "::" + method.Value)
	if !found || scheme == nil {
		return GeneralizationFacts{Barriers: GeneralizationUnknownAuthority}
	}
	return GeneralizationFacts{Barriers: scheme.GeneralizationBarriers}
}

func generalizationExpressionType(expr ast.Expression, env *TypeEnvironment) Type {
	switch e := expr.(type) {
	case *ast.Identifier:
		if scheme, found := env.Get(e.Value); found && scheme != nil {
			return scheme.Monomorphic.Apply(scheme.Type)
		}
		if typ, found := env.GetType(e.Value); found {
			return typ
		}
	case *ast.InvocationExpression:
		if ident, ok := e.Function.(*ast.Identifier); ok {
			if scheme, found := env.Get(ident.Value); found && scheme != nil {
				if fn, ok := scheme.Monomorphic.Apply(scheme.Type).(*FunctionType); ok {
					return fn.ReturnType
				}
			}
		}
		if selector, ok := e.Function.(*ast.IndexExpression); ok {
			if receiver, ok := generalizationExpressionType(selector.Left, env).(*ADTType); ok {
				if method, ok := selector.Index.(*ast.Identifier); ok {
					if scheme, found := env.Get(receiver.Name + "::" + method.Value); found && scheme != nil {
						if fn, ok := scheme.Monomorphic.Apply(scheme.Type).(*FunctionType); ok {
							return fn.ReturnType
						}
					}
				}
			}
		}
	}
	return nil
}

func functionCaptureFactsWithBound(fn *ast.FunctionLiteral, env *TypeEnvironment, outerBound map[string]bool) GeneralizationFacts {
	facts := GeneralizationFacts{}
	if fn == nil || fn.Body == nil {
		return facts
	}
	bound := make(map[string]bool, len(outerBound)+len(fn.Arguments))
	for name, isBound := range outerBound {
		if isBound {
			bound[name] = true
		}
	}
	for _, arg := range fn.Arguments {
		if arg != nil {
			bound[arg.Value] = true
		}
	}
	referenced := make(map[string]bool)
	var walkExpr func(ast.Expression)
	var walkStmt func(ast.Statement)
	var walkBlock func(*ast.BlockStatement)
	walkExpr = func(expr ast.Expression) {
		switch e := expr.(type) {
		case *ast.Identifier:
			if !bound[e.Value] {
				referenced[e.Value] = true
			}
		case *ast.PrefixExpression:
			walkExpr(e.Right)
		case *ast.InfixExpression:
			walkExpr(e.Left)
			walkExpr(e.Right)
		case *ast.IndexExpression:
			walkExpr(e.Left)
			// The identifier after '.' is a selector name, not a lexical
			// variable. Computed array indices still participate in capture.
			if !e.Dot && e.Token.Literal != "." {
				walkExpr(e.Index)
			}
		case *ast.SliceExpression:
			walkExpr(e.Seq)
			walkExpr(e.Low)
			walkExpr(e.High)
		case *ast.ArrayLiteral:
			for _, element := range e.Elements {
				walkExpr(element)
			}
		case *ast.RecordLiteral:
			for _, field := range e.OrderedFields() {
				walkExpr(field.Value)
			}
		case *ast.InvocationExpression:
			if selector, ok := e.Function.(*ast.IndexExpression); ok &&
				(selector.Dot || selector.Token.Literal == ".") {
				if library, ok := selector.Left.(*ast.Identifier); ok && CompilerKnownLibrary(library.Value) {
					// Compiler libraries are namespaces, not captured values or
					// authority-bearing method receivers. Their arguments still
					// participate in ordinary capture analysis.
					for _, argument := range e.Arguments {
						walkExpr(argument)
					}
					return
				}
				facts.Barriers |= methodSelectorFacts(selector, env).Barriers
			}
			walkExpr(e.Function)
			for _, argument := range e.Arguments {
				walkExpr(argument)
			}
		case *ast.BlockExpression:
			walkBlock(e.Block)
		case *ast.MatchExpression:
			walkExpr(e.Scrutinee)
			for _, arm := range e.Arms {
				if arm == nil {
					continue
				}
				names := patternBindingNames(arm.Pattern)
				previous := make(map[string]bool, len(names))
				for _, name := range names {
					previous[name] = bound[name]
					bound[name] = true
				}
				walkExpr(arm.Body)
				for _, name := range names {
					if previous[name] {
						bound[name] = true
					} else {
						delete(bound, name)
					}
				}
			}
		case *ast.VariantExpression:
			walkExpr(e.Payload)
		case *ast.FunctionLiteral:
			nested := functionCaptureFactsWithBound(e, env, bound)
			facts.Barriers |= nested.Barriers
		}
	}
	walkStmt = func(stmt ast.Statement) {
		switch s := stmt.(type) {
		case *ast.ExpressionStatement:
			walkExpr(s.Expression)
		case *ast.VariableDeclaration:
			walkExpr(s.Value)
			if s.Name != nil {
				bound[s.Name.Value] = true
				if typ := generalizationDeclaredType(s.Type, env); typ != nil {
					env.SetType(s.Name.Value, typ)
				}
			}
		case *ast.AssignmentStatement:
			if s.Name != nil && !bound[s.Name.Value] {
				referenced[s.Name.Value] = true
			}
			walkExpr(s.Value)
		case *ast.IndexAssignmentStatement:
			// Writes through parameters or fresh locals do not capture storage.
			// Writes rooted outside this function retain the outer authority.
			if s.Target == nil || !locallyBoundStorage(s.Target.Left, bound) {
				facts = facts.With(GeneralizationMutableAuthority).With(GeneralizationEffectfulCapture)
			}
			if s.Target != nil {
				walkExpr(s.Target)
			}
			walkExpr(s.Value)
		case *ast.IfStatement:
			walkExpr(s.Condition)
			walkBlock(s.Consequence)
			if s.Alternative != nil {
				walkStmt(s.Alternative)
			}
		case *ast.WhileStatement:
			walkExpr(s.Condition)
			walkBlock(s.Body)
		case *ast.BlockStatement:
			walkBlock(s)
		case *ast.FunctionStatement:
			if s.Name != nil {
				bound[s.Name.Value] = true
			}
			nested := functionStatementCaptureFactsWithBound(s, env, bound)
			facts.Barriers |= nested.Barriers
		case *ast.UnsafeBlock:
			facts = facts.With(GeneralizationUnsafeAssumption)
			walkBlock(s.Body)
		}
	}
	walkBlock = func(block *ast.BlockStatement) {
		if block == nil {
			return
		}
		outer := bound
		outerEnv := env
		bound = make(map[string]bool, len(outer))
		for name, isBound := range outer {
			bound[name] = isBound
		}
		env = NewEnclosedTypeEnvironment(outerEnv)
		for _, statement := range block.Statements {
			walkStmt(statement)
		}
		env = outerEnv
		bound = outer
	}
	walkBlock(fn.Body)
	for name := range referenced {
		scheme, ok := env.Get(name)
		if !ok || scheme == nil {
			// Type constructors and compiler intrinsics are stateless language
			// operations, not captured values. Other missing capture metadata
			// cannot prove safety during forward summary construction.
			if _, isType := env.GetType(name); isType || isNonCapturingBuiltin(name) {
				continue
			}
			facts = facts.With(GeneralizationUnknownAuthority)
			continue
		}
		// An ordinary named function is a direct code pointer, not an
		// environment capture. A blocked function scheme remains
		// conservative because it may carry captured authority.
		if _, isFunction := scheme.Type.(*FunctionType); isFunction && scheme.GeneralizationBarriers == 0 {
			continue
		}
		facts = facts.With(GeneralizationMutableAuthority)
		facts.Barriers |= scheme.GeneralizationBarriers
		facts.Barriers |= factsFromType(scheme.Type).Barriers
	}
	return facts
}

func generalizationDeclaredType(expr ast.Expression, env *TypeEnvironment) Type {
	switch e := expr.(type) {
	case *ast.Identifier:
		if typ, ok := env.GetType(e.Value); ok {
			return typ
		}
		switch e.Value {
		case "string":
			return &StringType{}
		case "Bool":
			return &BoolType{}
		case "i8", "i16", "i32", "i64", "u8", "u16", "u32", "u64",
			"int", "uint", "ptr", "uptr", "byte", "rune", "f32", "f64":
			return &PrimitiveType{Name: e.Value}
		default:
			if e.Value != "" {
				return &ADTType{Name: e.Value}
			}
		}
	case *ast.IndexExpression:
		element := generalizationDeclaredType(e.Left, env)
		if element == nil {
			return nil
		}
		switch marker := e.Index.(type) {
		case *ast.IntegerLiteral:
			return &ArrayType{Length: marker.Value, ElementType: element}
		case *ast.Identifier:
			if marker.Value == "" {
				return &ArrayType{Length: -1, IsSlice: true, ElementType: element}
			}
			if marker.Value == "*" {
				return &ArrayType{Length: -1, IsSpan: true, ElementType: element}
			}
		}
	}
	return nil
}

func isNonCapturingBuiltin(name string) bool {
	switch name {
	case "u8", "u16", "u32", "u64",
		"i8", "i16", "i32", "i64",
		"int", "uint", "ptr", "uptr", "byte", "rune", "string", "f32", "f64",
		"view_as", "span_as", "view", "span", "subslice",
		"len", "is_valid_utf8", "assert":
		return true
	}
	if FloatIntrinsicName(name) {
		return true
	}
	return splitNarrowingFunctionName(name) != nil
}

func patternBindingNames(pattern ast.Pattern) []string {
	var names []string
	var visit func(ast.Pattern)
	visit = func(current ast.Pattern) {
		switch p := current.(type) {
		case *ast.BindingPattern:
			if p.Name != nil {
				names = append(names, p.Name.Value)
			}
		case *ast.VariantPattern:
			visit(p.Payload)
		}
	}
	visit(pattern)
	return names
}

// functionStatementCaptureFacts treats a named function declaration as the
// closure value it creates. Its name, receiver, and parameters are local binders;
// references outside that set are captures from the surrounding environment.
func functionStatementCaptureFacts(fn *ast.FunctionStatement, env *TypeEnvironment) GeneralizationFacts {
	return functionStatementCaptureFactsWithBound(fn, env, nil)
}

func functionStatementCaptureFactsWithBound(fn *ast.FunctionStatement, env *TypeEnvironment, outerBound map[string]bool) GeneralizationFacts {
	if fn == nil {
		return GeneralizationFacts{}
	}
	arguments := make([]*ast.Identifier, 0, len(fn.Parameters)+2)
	if fn.Name != nil {
		arguments = append(arguments, fn.Name)
	}
	if fn.Receiver != nil && fn.Receiver.Name != nil {
		arguments = append(arguments, fn.Receiver.Name)
	}
	for _, parameter := range fn.Parameters {
		if parameter != nil && parameter.Name != nil {
			arguments = append(arguments, parameter.Name)
		}
	}
	var body *ast.BlockStatement
	if block, ok := fn.Body.(*ast.BlockExpression); ok {
		body = block.Block
	} else if fn.Body != nil {
		body = &ast.BlockStatement{Statements: []ast.Statement{
			&ast.ExpressionStatement{Expression: fn.Body},
		}}
	}
	return functionCaptureFactsWithBound(&ast.FunctionLiteral{Arguments: arguments, Body: body}, env, outerBound)
}

func conservativePatternBindingFacts(pattern ast.Pattern) map[string]GeneralizationFacts {
	result := make(map[string]GeneralizationFacts)
	unknown := GeneralizationFacts{Barriers: GeneralizationUnknownAuthority}
	for _, name := range patternBindingNames(pattern) {
		result[name] = unknown
	}
	return result
}

func (tc *TypeChecker) valueAuthorityFacts(typ Type, visiting map[string]bool) GeneralizationFacts {
	facts := factsFromType(typ)
	adtName, _, arguments, ok := adtInstantiation(typ)
	if !ok {
		return facts
	}
	// Recursive definitions can change their type arguments on every step
	// (for example Nest[T] -> Nest[[]T]); bound traversal by definition.
	if visiting[adtName] {
		return facts
	}
	visiting[adtName] = true
	defer delete(visiting, adtName)
	adt := tc.adtTypes[adtName]
	if adt == nil {
		return facts.With(GeneralizationUnknownAuthority)
	}
	for _, variant := range adt.Variants {
		bindings, _, reachable := tc.variantIndexBindings(adt, variant, arguments)
		if !reachable {
			continue
		}
		if payload := tc.instantiatedVariantPayload(adtName, variant, bindings); payload != nil {
			facts.Barriers |= tc.valueAuthorityFacts(payload, visiting).Barriers
		}
	}
	return facts
}

func (tc *TypeChecker) generalizationPatternBindingFacts(pattern ast.Pattern, expected Type) map[string]GeneralizationFacts {
	if expected == nil {
		return conservativePatternBindingFacts(pattern)
	}
	result := make(map[string]GeneralizationFacts)
	var visit func(ast.Pattern, Type)
	visit = func(current ast.Pattern, currentType Type) {
		switch p := current.(type) {
		case *ast.BindingPattern:
			if p.Name != nil {
				result[p.Name.Value] = tc.valueAuthorityFacts(currentType, make(map[string]bool))
			}
		case *ast.VariantPattern:
			adtName, _, arguments, ok := adtInstantiation(currentType)
			if !ok || p.Variant == nil {
				return
			}
			adt := tc.adtTypes[adtName]
			variant, found := tc.findADTVariant(adtName, p.Variant.Value)
			if adt == nil || !found {
				return
			}
			bindings, _, reachable := tc.variantIndexBindings(adt, variant, arguments)
			if !reachable {
				return
			}
			if p.Payload != nil {
				visit(p.Payload, tc.instantiatedVariantPayload(adtName, variant, bindings))
			}
		}
	}
	visit(pattern, expected)
	return result
}

// deriveGeneralizationFacts joins evidence from the inferred value shape and
// initializer evaluation. Unknown calls fail closed until effect summaries are
// carried in TypeScheme; closure bodies contribute captured authority rather
// than being treated as immediately executed effects.
func deriveGeneralizationFacts(typ Type, initializer ast.Expression, env *TypeEnvironment, checkers ...*TypeChecker) GeneralizationFacts {
	facts := factsFromType(typ)
	var checker *TypeChecker
	if len(checkers) > 0 {
		checker = checkers[0]
	}
	metadataBound := make(map[string]bool)
	localFacts := make(map[string]GeneralizationFacts)
	var captureScope func() (*TypeEnvironment, map[string]bool)
	var matchPatternFacts func(*ast.MatchExpression, ast.Pattern) map[string]GeneralizationFacts
	var bindingFacts func(ast.Expression) GeneralizationFacts
	var statementBindingFacts func(ast.Statement) GeneralizationFacts
	var visitExpr func(ast.Expression)
	var visitStmt func(ast.Statement)
	var visitBlock func(*ast.BlockStatement)

	captureScope = func() (*TypeEnvironment, map[string]bool) {
		scopedEnv := NewEnclosedTypeEnvironment(env)
		bound := make(map[string]bool, len(metadataBound))
		for name, isBound := range metadataBound {
			bound[name] = isBound
		}
		for name, local := range localFacts {
			if local.Safe() {
				continue
			}
			// Authority-bearing locals are genuine captures. Expose their
			// facts through a scoped synthetic scheme and stop suppressing
			// their names as mere lexical shadows.
			scopedEnv.Set(name, &TypeScheme{
				Type:                   &UnitType{},
				GeneralizationBarriers: local.Barriers,
			})
			delete(bound, name)
		}
		return scopedEnv, bound
	}

	matchPatternFacts = func(match *ast.MatchExpression, pattern ast.Pattern) map[string]GeneralizationFacts {
		// The compatibility entry point without a checker preserves the original
		// lexical-shadow behavior used by isolated fact-analysis callers.
		if checker == nil {
			return map[string]GeneralizationFacts{}
		}
		if match == nil {
			return conservativePatternBindingFacts(pattern)
		}
		identifier, ok := match.Scrutinee.(*ast.Identifier)
		if !ok {
			return conservativePatternBindingFacts(pattern)
		}
		if metadataBound[identifier.Value] {
			// A current lexical binder shadows any homonymous outer scheme. Until
			// local semantic types are retained here, fail closed on its payload.
			return conservativePatternBindingFacts(pattern)
		}
		scheme, ok := env.Get(identifier.Value)
		if !ok || scheme == nil {
			return conservativePatternBindingFacts(pattern)
		}
		return checker.generalizationPatternBindingFacts(pattern, scheme.Type)
	}

	bindingFacts = func(expr ast.Expression) GeneralizationFacts {
		switch e := expr.(type) {
		case *ast.Identifier:
			if local, ok := localFacts[e.Value]; ok {
				return local
			}
			if metadataBound[e.Value] {
				return GeneralizationFacts{}
			}
			if scheme, ok := env.Get(e.Value); ok && scheme != nil {
				result := factsFromType(scheme.Type)
				result.Barriers |= scheme.GeneralizationBarriers
				return result
			}
		case *ast.ArrayLiteral:
			result := GeneralizationFacts{Barriers: GeneralizationMutableAuthority}
			for _, element := range e.Elements {
				result.Barriers |= bindingFacts(element).Barriers
			}
			return result
		case *ast.RecordLiteral:
			result := GeneralizationFacts{}
			for _, field := range e.OrderedFields() {
				result.Barriers |= bindingFacts(field.Value).Barriers
			}
			return result
		case *ast.BlockExpression:
			result := GeneralizationFacts{}
			if e.Block != nil {
				for _, statement := range e.Block.Statements {
					result.Barriers |= statementBindingFacts(statement).Barriers
				}
			}
			return result
		case *ast.MatchExpression:
			result := bindingFacts(e.Scrutinee)
			namesByArm := make([][]string, len(e.Arms))
			for i, arm := range e.Arms {
				if arm == nil {
					continue
				}
				namesByArm[i] = patternBindingNames(arm.Pattern)
				armFacts := matchPatternFacts(e, arm.Pattern)
				previous := make(map[string]bool, len(namesByArm[i]))
				previousFacts := make(map[string]GeneralizationFacts, len(namesByArm[i]))
				hadFacts := make(map[string]bool, len(namesByArm[i]))
				for _, name := range namesByArm[i] {
					previous[name] = metadataBound[name]
					previousFacts[name], hadFacts[name] = localFacts[name]
					metadataBound[name] = true
					if payloadFacts, ok := armFacts[name]; ok {
						localFacts[name] = payloadFacts
					} else {
						delete(localFacts, name)
					}
				}
				result.Barriers |= bindingFacts(arm.Body).Barriers
				for _, name := range namesByArm[i] {
					if previous[name] {
						metadataBound[name] = true
					} else {
						delete(metadataBound, name)
					}
					if hadFacts[name] {
						localFacts[name] = previousFacts[name]
					} else {
						delete(localFacts, name)
					}
				}
			}
			return result
		case *ast.VariantExpression:
			return bindingFacts(e.Payload)
		case *ast.IndexExpression:
			result := bindingFacts(e.Left)
			if !e.Dot && e.Token.Literal != "." {
				result.Barriers |= bindingFacts(e.Index).Barriers
			}
			return result
		case *ast.InfixExpression:
			result := bindingFacts(e.Left)
			result.Barriers |= bindingFacts(e.Right).Barriers
			return result
		case *ast.SliceExpression:
			result := bindingFacts(e.Seq)
			result.Barriers |= GeneralizationRegionBound
			return result
		case *ast.PrefixExpression:
			result := bindingFacts(e.Right)
			if e.Operator == "&" {
				result.Barriers |= GeneralizationExternalAuthority
			}
			return result
		case *ast.FunctionLiteral:
			scopedEnv, bound := captureScope()
			return functionCaptureFactsWithBound(e, scopedEnv, bound)
		case *ast.InvocationExpression:
			return GeneralizationFacts{
				Barriers: GeneralizationEffectfulCapture | GeneralizationUnknownAuthority,
			}
		}
		return GeneralizationFacts{}
	}

	statementBindingFacts = func(stmt ast.Statement) GeneralizationFacts {
		switch s := stmt.(type) {
		case *ast.ExpressionStatement:
			return bindingFacts(s.Expression)
		case *ast.VariableDeclaration:
			return bindingFacts(s.Value)
		case *ast.AssignmentStatement:
			return bindingFacts(s.Value)
		case *ast.IndexAssignmentStatement:
			result := GeneralizationFacts{
				Barriers: GeneralizationMutableAuthority | GeneralizationEffectfulCapture,
			}
			if s.Target != nil {
				result.Barriers |= bindingFacts(s.Target).Barriers
			}
			result.Barriers |= bindingFacts(s.Value).Barriers
			return result
		case *ast.IfStatement:
			result := bindingFacts(s.Condition)
			if s.Consequence != nil {
				result.Barriers |= statementBindingFacts(s.Consequence).Barriers
			}
			if s.Alternative != nil {
				result.Barriers |= statementBindingFacts(s.Alternative).Barriers
			}
			return result
		case *ast.WhileStatement:
			result := bindingFacts(s.Condition)
			if s.Body != nil {
				for _, inner := range s.Body.Statements {
					result.Barriers |= statementBindingFacts(inner).Barriers
				}
			}
			return result
		case *ast.BlockStatement:
			result := GeneralizationFacts{}
			for _, inner := range s.Statements {
				result.Barriers |= statementBindingFacts(inner).Barriers
			}
			return result
		case *ast.UnsafeBlock:
			result := GeneralizationFacts{Barriers: GeneralizationUnsafeAssumption}
			if s.Body != nil {
				for _, inner := range s.Body.Statements {
					result.Barriers |= statementBindingFacts(inner).Barriers
				}
			}
			return result
		case *ast.FunctionStatement:
			scopedEnv, bound := captureScope()
			return functionStatementCaptureFactsWithBound(s, scopedEnv, bound)
		}
		return GeneralizationFacts{}
	}

	visitExpr = func(expr ast.Expression) {
		switch e := expr.(type) {
		case nil:
			return
		case *ast.Identifier:
			if metadataBound[e.Value] {
				if local, ok := localFacts[e.Value]; ok {
					facts.Barriers |= local.Barriers
				}
				return
			}
			if scheme, ok := env.Get(e.Value); ok && scheme != nil {
				facts.Barriers |= scheme.GeneralizationBarriers
			}
		case *ast.FunctionLiteral:
			scopedEnv, bound := captureScope()
			facts.Barriers |= functionCaptureFactsWithBound(e, scopedEnv, bound).Barriers
		case *ast.InvocationExpression:
			facts = facts.With(GeneralizationEffectfulCapture).With(GeneralizationUnknownAuthority)
			visitExpr(e.Function)
			for _, argument := range e.Arguments {
				visitExpr(argument)
			}
		case *ast.PrefixExpression:
			visitExpr(e.Right)
		case *ast.InfixExpression:
			visitExpr(e.Left)
			visitExpr(e.Right)
		case *ast.IndexExpression:
			visitExpr(e.Left)
			// A dotted identifier is a selector name, not a lexical binding.
			// Computed indices remain ordinary expressions and propagate metadata.
			if !e.Dot && e.Token.Literal != "." {
				visitExpr(e.Index)
			}
		case *ast.SliceExpression:
			visitExpr(e.Seq)
			visitExpr(e.Low)
			visitExpr(e.High)
		case *ast.ArrayLiteral:
			for _, element := range e.Elements {
				visitExpr(element)
			}
		case *ast.RecordLiteral:
			for _, field := range e.OrderedFields() {
				visitExpr(field.Value)
			}
		case *ast.BlockExpression:
			visitBlock(e.Block)
		case *ast.MatchExpression:
			visitExpr(e.Scrutinee)
			for _, arm := range e.Arms {
				if arm == nil {
					continue
				}
				names := patternBindingNames(arm.Pattern)
				armFacts := matchPatternFacts(e, arm.Pattern)
				previousBound := make(map[string]bool, len(names))
				previousFacts := make(map[string]GeneralizationFacts, len(names))
				hadFacts := make(map[string]bool, len(names))
				for _, name := range names {
					previousBound[name] = metadataBound[name]
					previousFacts[name], hadFacts[name] = localFacts[name]
					metadataBound[name] = true
					if payloadFacts, ok := armFacts[name]; ok {
						localFacts[name] = payloadFacts
					} else {
						delete(localFacts, name)
					}
				}
				visitExpr(arm.Body)
				for _, name := range names {
					if previousBound[name] {
						metadataBound[name] = true
					} else {
						delete(metadataBound, name)
					}
					if hadFacts[name] {
						localFacts[name] = previousFacts[name]
					} else {
						delete(localFacts, name)
					}
				}
			}
		case *ast.VariantExpression:
			visitExpr(e.Payload)
		}
	}
	visitStmt = func(stmt ast.Statement) {
		switch s := stmt.(type) {
		case *ast.ExpressionStatement:
			visitExpr(s.Expression)
		case *ast.VariableDeclaration:
			visitExpr(s.Value)
			if s.Name != nil {
				metadataBound[s.Name.Value] = true
				localFacts[s.Name.Value] = bindingFacts(s.Value)
			}
		case *ast.AssignmentStatement:
			visitExpr(s.Value)
			assigned := bindingFacts(s.Value)
			if s.Name != nil && metadataBound[s.Name.Value] {
				local := localFacts[s.Name.Value]
				local.Barriers |= assigned.Barriers
				localFacts[s.Name.Value] = local
				break
			}
			if s.Name != nil {
				// Updating an outer binding is itself an effectful mutable
				// capture, independently of the authority carried by the RHS.
				facts = facts.With(GeneralizationMutableAuthority).With(GeneralizationEffectfulCapture)
				facts.Barriers |= assigned.Barriers
				if scheme, ok := env.Get(s.Name.Value); ok && scheme != nil {
					facts.Barriers |= scheme.GeneralizationBarriers
					facts.Barriers |= factsFromType(scheme.Type).Barriers
				}
			}
		case *ast.IndexAssignmentStatement:
			facts = facts.With(GeneralizationMutableAuthority).With(GeneralizationEffectfulCapture)
			if s.Target != nil {
				visitExpr(s.Target)
				facts.Barriers |= bindingFacts(s.Target).Barriers
			}
			visitExpr(s.Value)
			facts.Barriers |= bindingFacts(s.Value).Barriers
		case *ast.IfStatement:
			visitExpr(s.Condition)
			visitBlock(s.Consequence)
			if s.Alternative != nil {
				visitStmt(s.Alternative)
			}
		case *ast.WhileStatement:
			visitExpr(s.Condition)
			visitBlock(s.Body)
		case *ast.BlockStatement:
			visitBlock(s)
		case *ast.UnsafeBlock:
			facts = facts.With(GeneralizationUnsafeAssumption)
			visitBlock(s.Body)
		case *ast.FunctionStatement:
			scopedEnv, bound := captureScope()
			functionFacts := functionStatementCaptureFactsWithBound(s, scopedEnv, bound)
			facts.Barriers |= functionFacts.Barriers
			if s.Name != nil {
				metadataBound[s.Name.Value] = true
				localFacts[s.Name.Value] = functionFacts
			}
		}
	}
	visitBlock = func(block *ast.BlockStatement) {
		if block == nil {
			return
		}
		outerBound := metadataBound
		outerFacts := localFacts
		metadataBound = make(map[string]bool, len(outerBound))
		localFacts = make(map[string]GeneralizationFacts, len(outerFacts))
		for name, isBound := range outerBound {
			metadataBound[name] = isBound
		}
		for name, local := range outerFacts {
			localFacts[name] = local
		}
		for _, statement := range block.Statements {
			visitStmt(statement)
		}
		// New nested declarations leave with the block, but authority updates
		// to inherited locals are monotone dataflow facts and survive scope exit.
		for name := range outerBound {
			if updated, ok := localFacts[name]; ok {
				outerFacts[name] = updated
			}
		}
		metadataBound = outerBound
		localFacts = outerFacts
	}
	visitExpr(initializer)
	return facts
}

func locallyBoundStorage(expr ast.Expression, bound map[string]bool) bool {
	switch e := expr.(type) {
	case *ast.Identifier:
		return bound[e.Value]
	case *ast.IndexExpression:
		return locallyBoundStorage(e.Left, bound)
	case *ast.SliceExpression:
		return locallyBoundStorage(e.Seq, bound)
	default:
		return false
	}
}
