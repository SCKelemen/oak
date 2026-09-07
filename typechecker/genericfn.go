package typechecker

// Generic function monomorphization (docs/spec/20-types.md §11.2): a
// declaration with type parameters (max[T]: (a: T, b: T): T = ...) is a
// TEMPLATE, never checked or emitted generically. Each call site infers
// type bindings from its argument types (or supplies them explicitly:
// max[u32](x, y)), the body is specialized through the single
// substitution authority (SubstituteTypeAST, the Oak.Monomorphization
// transliteration ADT payloads use), and the SPECIALIZED declaration is
// typechecked per instantiation and appended to the program before the
// borrow checker, discipline analysis, lowering, and codegen run — every
// safety gate sees only ordinary functions, and runs on every
// instantiation. Call sites are rewritten to the mangled name (oak_max_u32
// after the backend prefix). Anything unsubstitutable or uninferable
// fails closed with a diagnostic, never a guess.

import (
	"reflect"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/token"
)

// stampSemanticContext walks a freshly substituted declaration and sets
// SemanticContext on every token it contains — the clone is private to
// this instantiation, so the walk never touches the template.
func stampSemanticContext(value reflect.Value, context string) {
	switch value.Kind() {
	case reflect.Ptr, reflect.Interface:
		if value.IsNil() {
			return
		}
		stampSemanticContext(value.Elem(), context)
	case reflect.Struct:
		if value.Type() == reflect.TypeOf(token.Token{}) {
			if value.CanSet() {
				value.FieldByName("SemanticContext").SetString(context)
			}
			return
		}
		for i := 0; i < value.NumField(); i++ {
			field := value.Field(i)
			if field.CanSet() || field.Kind() == reflect.Ptr || field.Kind() == reflect.Interface || field.Kind() == reflect.Slice {
				stampSemanticContext(field, context)
			}
		}
	case reflect.Slice:
		for i := 0; i < value.Len(); i++ {
			stampSemanticContext(value.Index(i), context)
		}
	case reflect.Map:
		for _, key := range value.MapKeys() {
			stampSemanticContext(value.MapIndex(key), context)
		}
	}
}

// registerFunctionTemplate notes a generic function declaration and keeps
// it out of the ordinary checking path.
func (tc *TypeChecker) registerFunctionTemplate(stmt *ast.FunctionStatement) {
	if tc.functionTemplates == nil {
		tc.functionTemplates = make(map[string]*ast.FunctionStatement)
	}
	tc.functionTemplates[stmt.Name.Value] = stmt
}

// IsFunctionTemplate reports whether name is a registered generic function.
func (tc *TypeChecker) IsFunctionTemplate(name string) bool {
	_, ok := tc.functionTemplates[name]
	return ok
}

// resolveGenericInvocation recognizes and monomorphizes a call to a generic
// function. Reports (type, true) when the invocation was a generic call
// (even on error, so the caller does not double-diagnose).
func (tc *TypeChecker) resolveGenericInvocation(expr *ast.InvocationExpression) (Type, bool) {
	// Explicit instantiation: max[u32](x, y).
	if indexExpr, isIndex := expr.Function.(*ast.IndexExpression); isIndex && !indexExpr.Dot {
		name, argExprs, ok := lenientFlattenApplication(indexExpr)
		if !ok || len(argExprs) == 0 {
			return nil, false
		}
		template, isTemplate := tc.functionTemplates[name]
		if !isTemplate {
			return nil, false
		}
		if len(argExprs) != len(template.TypeParams) {
			tc.addError(expr, "%s takes %d type arguments, got %d", name, len(template.TypeParams), len(argExprs))
			return nil, true
		}
		args := make([]Type, 0, len(argExprs))
		for _, argExpr := range argExprs {
			argType := tc.parseTypeExpression(argExpr)
			if argType == nil {
				tc.addError(expr, "%s: cannot resolve type argument", name)
				return nil, true
			}
			args = append(args, argType)
		}
		return tc.invokeInstantiated(expr, template, args), true
	}

	ident, isIdent := expr.Function.(*ast.Identifier)
	if !isIdent {
		return nil, false
	}
	template, isTemplate := tc.functionTemplates[ident.Value]
	if !isTemplate {
		return nil, false
	}

	// Inference: match each argument's checked type against the parameter's
	// type expression; a bare type-parameter position binds directly.
	if len(expr.Arguments) != len(template.Parameters) {
		tc.addError(expr, "%s expects %d arguments, got %d", ident.Value, len(template.Parameters), len(expr.Arguments))
		return nil, true
	}
	paramSet := make(map[string]bool, len(template.TypeParams))
	for _, tp := range template.TypeParams {
		paramSet[tp.Name.Value] = true
	}
	bindings := make(map[string]Type)
	// First infer from ordinary arguments. A field accessor has no concrete
	// input type on its own, so it is resolved in the second pass after the
	// value/container arguments have established the record type.
	for i, param := range template.Parameters {
		if _, accessor := expr.Arguments[i].(*ast.FieldAccessorExpression); accessor {
			continue
		}
		argType := tc.checkExpression(expr.Arguments[i])
		if argType == nil {
			return nil, true
		}
		if !tc.bindTypeParams(param.Type, argType, paramSet, bindings, expr, i+1) {
			return nil, true
		}
	}
	for i, param := range template.Parameters {
		accessor, ok := expr.Arguments[i].(*ast.FieldAccessorExpression)
		if !ok {
			continue
		}
		if !tc.bindFieldAccessorTypeParams(param.Type, accessor, paramSet, bindings, expr, i+1) {
			return nil, true
		}
	}
	args := make([]Type, 0, len(template.TypeParams))
	for _, tp := range template.TypeParams {
		bound, ok := bindings[tp.Name.Value]
		if !ok {
			tc.addError(expr, "cannot infer type parameter %s of %s from the arguments; instantiate explicitly: %s[T](...)", tp.Name.Value, ident.Value, ident.Value)
			return nil, true
		}
		args = append(args, bound)
	}
	return tc.invokeInstantiated(expr, template, args), true
}

// bindFieldAccessorTypeParams relates .field to a generic unary function
// parameter (T) -> U. Bindings learned from other arguments resolve T to a
// concrete record; the selected field then binds U. This makes calls such
// as project(.name, person) independent of argument order.
func (tc *TypeChecker) bindFieldAccessorTypeParams(paramType ast.Expression, accessor *ast.FieldAccessorExpression, paramSet map[string]bool, bindings map[string]Type, at ast.Node, argPosition int) bool {
	fn, ok := paramType.(*ast.FunctionTypeExpression)
	if !ok || len(fn.Parameters) != 1 || fn.Return == nil {
		tc.addError(at, "argument %d: field accessor .%s requires a unary function parameter", argPosition, accessor.Field.Value)
		return false
	}
	spellings := make(map[string]ast.Expression, len(bindings))
	for name, bound := range bindings {
		spelling, ok := ArgumentSpelling(bound)
		if !ok {
			tc.addError(at, "argument %d: cannot specialize field accessor .%s for %s", argPosition, accessor.Field.Value, bound)
			return false
		}
		spellings[name] = spelling
	}
	inputExpr, ok := SubstituteTypeAST(fn.Parameters[0], spellings)
	if !ok {
		return false
	}
	inputType := tc.parseTypeExpression(inputExpr)
	record, ok := inputType.(*RecordType)
	if !ok || record.Name == "" || !record.Struct {
		tc.addError(at, "argument %d: cannot infer a concrete record input for .%s", argPosition, accessor.Field.Value)
		return false
	}
	fieldType, found := record.Fields[accessor.Field.Value]
	if !found {
		tc.addError(at, "argument %d: field %s not found in record type %s", argPosition, accessor.Field.Value, record)
		return false
	}
	return tc.bindTypeParams(fn.Return, fieldType, paramSet, bindings, at, argPosition)
}

// bindTypeParams walks a parameter's type expression beside the concrete
// argument type, binding bare type-parameter positions. Conflicting
// bindings are errors; positions the walk cannot relate contribute nothing
// (the per-instantiation body check catches any residual mismatch).
func (tc *TypeChecker) bindTypeParams(paramType ast.Expression, argType Type, paramSet map[string]bool, bindings map[string]Type, at ast.Node, argPosition int) bool {
	switch t := paramType.(type) {
	case *ast.Identifier:
		if !paramSet[t.Value] {
			return true
		}
		if existing, bound := bindings[t.Value]; bound {
			if !existing.Equals(argType) {
				tc.addError(at, "argument %d: type parameter %s bound to both %s and %s", argPosition, t.Value, existing, argType)
				return false
			}
			return true
		}
		bindings[t.Value] = argType
		return true
	case *ast.IndexExpression:
		// [N]T / []T / generic applications: descend into the element
		// against the argument's element type when the shapes align.
		if arr, isArr := argType.(*ArrayType); isArr {
			return tc.bindTypeParams(t.Left, arr.ElementType, paramSet, bindings, at, argPosition)
		}
		return true
	case *ast.FunctionTypeExpression:
		fn, ok := argType.(*FunctionType)
		if !ok || len(t.Parameters) != len(fn.Parameters) {
			return true
		}
		for i := range t.Parameters {
			if !tc.bindTypeParams(t.Parameters[i], fn.Parameters[i], paramSet, bindings, at, argPosition) {
				return false
			}
		}
		return tc.bindTypeParams(t.Return, fn.ReturnType, paramSet, bindings, at, argPosition)
	}
	return true
}

// invokeInstantiated monomorphizes the template for the given arguments,
// rewrites the call site to the mangled name, and returns the call's type.
func (tc *TypeChecker) invokeInstantiated(expr *ast.InvocationExpression, template *ast.FunctionStatement, args []Type) Type {
	mangled, ok := tc.instantiateFunctionTemplate(template, args)
	if !ok {
		tc.addError(expr, "cannot instantiate %s: type arguments must be mangleable concrete types", template.Name.Value)
		return nil
	}
	// Rewrite the call site: downstream stages see an ordinary call.
	expr.Function = &ast.Identifier{Token: template.Name.Token, Value: mangled}
	// Type the rewritten call through the ordinary path (checks argument
	// assignability against the specialized signature).
	return tc.checkInvocationExpression(expr)
}

// instantiateFunctionTemplate builds (or reuses) one specialization. The
// cache is registered before the body is checked, so recursive generic
// functions terminate.
func (tc *TypeChecker) instantiateFunctionTemplate(template *ast.FunctionStatement, args []Type) (string, bool) {
	if len(args) != len(template.TypeParams) {
		return "", false
	}
	atoms := make([]string, 0, len(args))
	for _, arg := range args {
		atom, ok := typeAtom(arg)
		if !ok {
			return "", false
		}
		atoms = append(atoms, atom)
	}
	mangled := Instantiation{ADT: template.Name.Value, Args: atoms}.MangledName()
	if _, cached := tc.functionInstantiations[mangled]; cached {
		return mangled, true
	}
	// The mangled name must be free: a user declaration spelled like an
	// instantiation (identity_i32) would silently merge with it in C.
	if tc.globalEnv != nil {
		if _, taken := tc.globalEnv.Get(mangled); taken {
			return "", false
		}
	}

	bindings := make(map[string]ast.Expression, len(args))
	for i, tp := range template.TypeParams {
		spelling, ok := ArgumentSpelling(args[i])
		if !ok {
			return "", false
		}
		bindings[tp.Name.Value] = spelling
	}

	specialized, ok := substituteFunctionAST(template, bindings, mangled)
	if !ok {
		return "", false
	}
	// Every instantiation shares the template's source positions; the
	// position-keyed resolution records (variants, matches, shift widths)
	// disambiguate through the token's SemanticContext, stamped with the
	// instantiation's name (the stdlib stamps "std" the same way).
	stampSemanticContext(reflect.ValueOf(specialized), mangled)
	if tc.functionInstantiations == nil {
		tc.functionInstantiations = make(map[string]*ast.FunctionStatement)
	}
	tc.functionInstantiations[mangled] = specialized
	tc.functionInstantiationOrder = append(tc.functionInstantiationOrder, mangled)

	// The specialized declaration is an ordinary function checked in the
	// GLOBAL scope (templates are top-level; a caller's locals must not
	// leak into the instantiation): predeclare its signature (recursion)
	// and check its body with concrete types.
	callerEnv := tc.env
	if tc.globalEnv != nil {
		tc.env = tc.globalEnv
	}
	tc.predeclareFunctionSignature(specialized)
	tc.checkFunctionStatement(specialized)
	tc.env = callerEnv
	return mangled, true
}

// InstantiatedFunctions returns the specialized declarations in creation
// order, for the program rewrite at the end of CheckProgram.
func (tc *TypeChecker) InstantiatedFunctions() []*ast.FunctionStatement {
	decls := make([]*ast.FunctionStatement, 0, len(tc.functionInstantiationOrder))
	for _, mangled := range tc.functionInstantiationOrder {
		decls = append(decls, tc.functionInstantiations[mangled])
	}
	return decls
}

// substituteFunctionAST clones the template with every type spelling
// substituted: parameter types, return type, variable-declaration
// annotations, and generic applications inside the body. Unknown node
// kinds fail closed — a construct the walk does not cover is a diagnosed
// non-instantiation, never a silently unsubstituted body.
func substituteFunctionAST(template *ast.FunctionStatement, bindings map[string]ast.Expression, mangled string) (*ast.FunctionStatement, bool) {
	specialized := &ast.FunctionStatement{
		Token:    template.Token,
		EndToken: template.EndToken,
		Name:     &ast.Identifier{Token: template.Name.Token, Value: mangled},
	}
	for _, param := range template.Parameters {
		if param.Name != nil {
			if _, shadows := bindings[param.Name.Value]; shadows {
				return nil, false
			}
		}
		paramType, ok := SubstituteTypeAST(param.Type, bindings)
		if !ok {
			return nil, false
		}
		specialized.Parameters = append(specialized.Parameters, &ast.FunctionParameter{
			Token: param.Token, Name: param.Name, Type: paramType, Variadic: param.Variadic,
		})
	}
	returnType, ok := SubstituteTypeAST(template.ReturnType, bindings)
	if !ok {
		return nil, false
	}
	specialized.ReturnType = returnType
	body, ok := substituteExpr(template.Body, bindings)
	if !ok {
		return nil, false
	}
	specialized.Body = body
	return specialized, true
}

func substituteStmt(stmt ast.Statement, bindings map[string]ast.Expression) (ast.Statement, bool) {
	switch s := stmt.(type) {
	case nil:
		return nil, true
	case *ast.VariableDeclaration:
		// A local named like a type parameter would be rewritten by the
		// identifier substitution: fail closed rather than mis-instantiate.
		if s.Name != nil {
			if _, shadows := bindings[s.Name.Value]; shadows {
				return nil, false
			}
		}
		declType, ok := SubstituteTypeAST(s.Type, bindings)
		if !ok {
			return nil, false
		}
		value, ok := substituteExpr(s.Value, bindings)
		if !ok {
			return nil, false
		}
		return &ast.VariableDeclaration{Token: s.Token, Name: s.Name, Type: declType, Value: value}, true
	case *ast.AssignmentStatement:
		value, ok := substituteExpr(s.Value, bindings)
		if !ok {
			return nil, false
		}
		return &ast.AssignmentStatement{Token: s.Token, Name: s.Name, Value: value}, true
	case *ast.IndexAssignmentStatement:
		target, ok := substituteExpr(s.Target, bindings)
		if !ok {
			return nil, false
		}
		targetIndex, isIndex := target.(*ast.IndexExpression)
		if !isIndex {
			return nil, false
		}
		value, ok := substituteExpr(s.Value, bindings)
		if !ok {
			return nil, false
		}
		return &ast.IndexAssignmentStatement{Token: s.Token, Target: targetIndex, Value: value}, true
	case *ast.ExpressionStatement:
		value, ok := substituteExpr(s.Expression, bindings)
		if !ok {
			return nil, false
		}
		return &ast.ExpressionStatement{Token: s.Token, Expression: value}, true
	case *ast.WhileStatement:
		condition, ok := substituteExpr(s.Condition, bindings)
		if !ok {
			return nil, false
		}
		body, ok := substituteBlock(s.Body, bindings)
		if !ok {
			return nil, false
		}
		return &ast.WhileStatement{Token: s.Token, Condition: condition, Body: body}, true
	case *ast.BlockStatement:
		return substituteBlockAsStmt(s, bindings)
	}
	return nil, false
}

func substituteBlockAsStmt(block *ast.BlockStatement, bindings map[string]ast.Expression) (ast.Statement, bool) {
	substituted, ok := substituteBlock(block, bindings)
	if !ok {
		return nil, false
	}
	return substituted, true
}

func substituteBlock(block *ast.BlockStatement, bindings map[string]ast.Expression) (*ast.BlockStatement, bool) {
	if block == nil {
		return nil, true
	}
	out := &ast.BlockStatement{Token: block.Token}
	for _, stmt := range block.Statements {
		substituted, ok := substituteStmt(stmt, bindings)
		if !ok {
			return nil, false
		}
		out.Statements = append(out.Statements, substituted)
	}
	return out, true
}

func substituteExpr(expr ast.Expression, bindings map[string]ast.Expression) (ast.Expression, bool) {
	switch e := expr.(type) {
	case nil:
		return nil, true
	// A type parameter never names a value, so an identifier matching a
	// binding in ANY expression position is a type reference (explicit
	// type arguments inner[T](x), constructors T(x)) and takes the concrete
	// spelling. Leaves are copied too, so the instantiation shares no node
	// with the template (token stamping must never touch the template).
	case *ast.Identifier:
		if replacement, bound := bindings[e.Value]; bound {
			if ident, isIdent := replacement.(*ast.Identifier); isIdent {
				clone := *ident
				clone.Token = e.Token
				return &clone, true
			}
			return replacement, true
		}
		clone := *e
		return &clone, true
	case *ast.IntegerLiteral:
		clone := *e
		return &clone, true
	case *ast.StringLiteral:
		clone := *e
		return &clone, true
	case *ast.Boolean:
		clone := *e
		return &clone, true
	case *ast.FieldAccessorExpression:
		clone := *e
		if e.Field != nil {
			field := *e.Field
			clone.Field = &field
		}
		return &clone, true
	case *ast.PrefixExpression:
		right, ok := substituteExpr(e.Right, bindings)
		if !ok {
			return nil, false
		}
		return &ast.PrefixExpression{Token: e.Token, Operator: e.Operator, Right: right}, true
	case *ast.InfixExpression:
		left, okL := substituteExpr(e.Left, bindings)
		right, okR := substituteExpr(e.Right, bindings)
		if !okL || !okR {
			return nil, false
		}
		return &ast.InfixExpression{Token: e.Token, Operator: e.Operator, Left: left, Right: right}, true
	case *ast.IndexExpression:
		left, okL := substituteExpr(e.Left, bindings)
		index, okI := substituteExpr(e.Index, bindings)
		if !okL || !okI {
			return nil, false
		}
		return &ast.IndexExpression{Token: e.Token, Left: left, Index: index, Dot: e.Dot}, true
	case *ast.InvocationExpression:
		// A bound type parameter in callee position becomes its concrete
		// spelling: T(x) instantiates to u32(x), and inner[T](y) to
		// inner[u32](y) — nested generic calls re-resolve concretely.
		function, ok := substituteExpr(e.Function, bindings)
		if !ok {
			return nil, false
		}
		if ident, isIdent := e.Function.(*ast.Identifier); isIdent {
			if replacement, bound := bindings[ident.Value]; bound {
				function = replacement
			}
		}
		out := &ast.InvocationExpression{Token: e.Token, Function: function}
		for _, arg := range e.Arguments {
			substituted, ok := substituteExpr(arg, bindings)
			if !ok {
				return nil, false
			}
			out.Arguments = append(out.Arguments, substituted)
		}
		return out, true
	case *ast.MatchExpression:
		scrutinee, ok := substituteExpr(e.Scrutinee, bindings)
		if !ok {
			return nil, false
		}
		out := &ast.MatchExpression{Token: e.Token, Scrutinee: scrutinee}
		for _, arm := range e.Arms {
			body, ok := substituteExpr(arm.Body, bindings)
			if !ok {
				return nil, false
			}
			out.Arms = append(out.Arms, &ast.MatchArm{Token: arm.Token, Pattern: arm.Pattern, Body: body})
		}
		return out, true
	case *ast.VariantExpression:
		payload, ok := substituteExpr(e.Payload, bindings)
		if !ok {
			return nil, false
		}
		return &ast.VariantExpression{Token: e.Token, TypeName: e.TypeName, Variant: e.Variant, Payload: payload}, true
	case *ast.BlockExpression:
		block, ok := substituteBlock(e.Block, bindings)
		if !ok {
			return nil, false
		}
		return &ast.BlockExpression{Token: e.Token, Block: block}, true
	case *ast.SliceExpression:
		seq, okS := substituteExpr(e.Seq, bindings)
		low, okLo := substituteExpr(e.Low, bindings)
		high, okH := substituteExpr(e.High, bindings)
		if !okS || !okLo || !okH {
			return nil, false
		}
		return &ast.SliceExpression{Token: e.Token, Seq: seq, Low: low, High: high}, true
	}
	return nil, false
}
