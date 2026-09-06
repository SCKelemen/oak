package evaluator

import (
	"fmt"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/object"
	"github.com/SCKelemen/oak/source"
)

var (
	NULL  = &object.Null{}
	TRUE  = &object.Boolean{Value: true}
	FALSE = &object.Boolean{Value: false}
)

func Eval(node ast.Node, env *object.Environment) object.Object {
	if env == nil {
		env = object.NewEnvironment()
	}

	switch node := node.(type) {

	case *ast.Program:
		return evalProgram(node, env)

	case *ast.ExpressionStatement:
		return Eval(node.Expression, env)

	case *ast.IntegerLiteral:
		return &object.Integer{Value: node.Value}

	case *ast.StringLiteral:
		return &object.String{Value: node.Value}

	case *ast.RecordLiteral:
		return evalRecordLiteral(node, env)

	case *ast.ArrayLiteral:
		return evalArrayLiteral(node, env)

	case *ast.Boolean:
		return mapBooleans(node.Value)

	case *ast.Identifier:
		return evalIdentifier(node, env)

	case *ast.VariantExpression:
		return evalVariantExpression(node, env)

	case *ast.PrefixExpression:
		right := Eval(node.Right, env)
		if isError(right) {
			return right
		}
		return evalPrefixExpression(node.Operator, right)

	case *ast.InfixExpression:
		left := Eval(node.Left, env)
		if isError(left) {
			return left
		}
		right := Eval(node.Right, env)
		if isError(right) {
			return right
		}
		return evalInfixExpression(node.Operator, left, right)

	case *ast.IndexAssignmentStatement:
		return evalIndexAssignmentStatement(node, env)

	case *ast.BlockStatement:
		return evalBlockStatement(node, env)

	case *ast.BlockExpression:
		if node.Block == nil {
			return nil
		}
		return evalBlockStatement(node.Block, env)

	case *ast.VariableDeclaration:
		return evalVariableDeclaration(node, env)

	case *ast.AssignmentStatement:
		return evalAssignmentStatement(node, env)

	case *ast.FunctionLiteral:
		return &object.Function{
			Parameters: node.Arguments,
			Body:       node.Body,
			Env:        env,
		}

	case *ast.InvocationExpression:
		// Check if this is a primitive type constructor: u32(x), u64(y), etc.
		if ident, ok := node.Function.(*ast.Identifier); ok {
			if result := evalPrimitiveConstructor(ident.Value, node.Arguments, env); result != nil {
				return result
			}
		}
		// Check if this is a method call: recv.method(args)
		// Method calls have an IndexExpression as the function
		if indexExpr, ok := node.Function.(*ast.IndexExpression); ok {
			if methodName, ok := indexExpr.Index.(*ast.Identifier); ok {
				// This is a method call: recv.method(args)
				return evalMethodCall(indexExpr.Left, methodName.Value, node.Arguments, env)
			}
		}
		// Regular function call
		function := Eval(node.Function, env)
		if isError(function) {
			return function
		}
		args := evalExpressions(node.Arguments, env)
		if len(args) == 1 && isError(args[0]) {
			return args[0]
		}
		return applyFunction(function, args)

	case *ast.IndexExpression:
		return evalIndexExpression(node, env)

	case *ast.MatchExpression:
		scrutinee := Eval(node.Scrutinee, env)
		if isError(scrutinee) {
			return scrutinee
		}
		return evalMatchExpression(scrutinee, node.Arms, env)

	case *ast.ADTType:
		return evalADTType(node, env)

	case *ast.FunctionStatement:
		return evalFunctionStatement(node, env)

	case *ast.PackageStatement:
		// Package statements are handled at top level, just return null
		return NULL

	case *ast.ImportStatement:
		// Import statements are handled at top level, just return null
		return NULL

	case *ast.WhileStatement:
		return evalWhileStatement(node, env)

	case *ast.UnsafeBlock:
		return evalUnsafeBlock(node, env)

	case *ast.REPLCommand:
		// REPL commands are handled in the REPL itself, not here
		// They terminate execution, so we just return NULL
		// The REPL will check for these and handle them appropriately
		return NULL

	default:
		return newError("unknown node type: %T", node)
	}
}

func evalProgram(program *ast.Program, env *object.Environment) object.Object {
	var result object.Object

	for _, statement := range program.Statements {
		// Handle REPL commands specially - they terminate evaluation
		if _, ok := statement.(*ast.REPLCommand); ok {
			// REPL commands are handled in the REPL itself, not here
			// But we can return a special marker object if needed
			// For now, just skip them in the evaluator
			continue
		}

		result = Eval(statement, env)

		switch result := result.(type) {
		case *object.Error:
			return result
		}
	}

	return result
}

func evalBlockStatement(block *ast.BlockStatement, env *object.Environment) object.Object {
	var result object.Object

	for _, statement := range block.Statements {
		result = Eval(statement, env)

		if result != nil {
			rt := result.Type()
			if rt == object.RETURN_VALUE_OBJ || rt == object.ERROR_OBJ {
				return result
			}
		}
	}

	return result
}

func mapBooleans(val bool) *object.Boolean {
	if val {
		return TRUE
	}
	return FALSE
}

func evalIdentifier(node *ast.Identifier, env *object.Environment) object.Object {
	// First check if it's an ADT type name - types are not values
	// We need to check this BEFORE looking in the value store, because
	// type names might have been incorrectly stored as empty records
	if _, ok := env.GetADTType(node.Value); ok {
		// This is a type name, not a value - return NULL
		// Don't look it up in the value store
		return NULL
	}

	val, ok := env.Get(node.Value)
	if !ok {
		// Check built-in functions
		if builtin, ok := getBuiltin(node.Value); ok {
			return builtin
		}
		return newError("identifier not found: %s", node.Value)
	}

	// If we got a value, check if it's an empty record that might be a type marker
	// This is a workaround for the bug where type names are stored as empty records
	if record, ok := val.(*object.Record); ok {
		if len(record.Fields) == 0 {
			// Empty record - check if this is actually a type name
			if _, ok := env.GetADTType(node.Value); ok {
				// This is a type, not a value - return NULL
				return NULL
			}
		}
	}

	return val
}

// Built-in functions
func getBuiltin(name string) (*object.Builtin, bool) {
	builtins := map[string]object.BuiltinFunction{
		"assert": func(args ...object.Object) object.Object {
			// docs/spec/85-discipline.md section 5: assertions are always
			// checked, in every mode.
			if len(args) != 1 {
				return newError("assert expects exactly one Bool argument, got %d", len(args))
			}
			cond, ok := args[0].(*object.Boolean)
			if !ok {
				return newError("assert condition must be Bool, got %s", args[0].Type())
			}
			if !cond.Value {
				return newError("assertion failed")
			}
			return NULL
		},
		"is_valid_utf8": func(args ...object.Object) object.Object {
			// docs/spec/70-strings.md: validate bytes against the well-formed
			// UTF-8 sequences (Oak.Utf8Validity) before trusting them as text.
			if len(args) != 1 {
				return newError("is_valid_utf8 expects exactly one []u8 argument, got %d", len(args))
			}
			arr, ok := args[0].(*object.Array)
			if !ok {
				return newError("is_valid_utf8 requires a []u8 view, got %s", args[0].Type())
			}
			bytes := make([]byte, 0, len(arr.Elements))
			for _, element := range arr.Elements {
				integer, ok := element.(*object.Integer)
				if !ok || integer.Value < 0 || integer.Value > 255 {
					return newError("is_valid_utf8 requires byte elements")
				}
				bytes = append(bytes, byte(integer.Value))
			}
			_, valid := source.ValidateUTF8(string(bytes))
			return nativeBoolToBooleanObject(valid)
		},
		"len": func(args ...object.Object) object.Object {
			if len(args) != 1 {
				return newError("wrong number of arguments. got=%d, want=1", len(args))
			}
			switch arg := args[0].(type) {
			case *object.Array:
				return &object.Integer{Value: int64(len(arg.Elements))}
			case *object.String:
				return &object.Integer{Value: int64(len(arg.Value))}
			default:
				return newError("argument to `len` not supported, got %s", args[0].Type())
			}
		},
		"get": func(args ...object.Object) object.Object {
			if len(args) != 2 {
				return newError("wrong number of arguments. got=%d, want=2", len(args))
			}
			arr, ok := args[0].(*object.Array)
			if !ok {
				return newError("first argument to `get` must be array, got %s", args[0].Type())
			}
			idx, ok := args[1].(*object.Integer)
			if !ok {
				return newError("second argument to `get` must be integer, got %s", args[1].Type())
			}
			if idx.Value < 0 || int64(len(arr.Elements)) <= idx.Value {
				// Return None
				return makeOptionNone()
			}
			// Return Some(value)
			return makeOptionSome(arr.Elements[idx.Value])
		},
		"try_slice": func(args ...object.Object) object.Object {
			if len(args) != 3 {
				return newError("wrong number of arguments. got=%d, want=3", len(args))
			}
			arr, ok := args[0].(*object.Array)
			if !ok {
				return newError("first argument to `try_slice` must be array, got %s", args[0].Type())
			}
			start, ok := args[1].(*object.Integer)
			if !ok {
				return newError("second argument to `try_slice` must be integer, got %s", args[1].Type())
			}
			end, ok := args[2].(*object.Integer)
			if !ok {
				return newError("third argument to `try_slice` must be integer, got %s", args[2].Type())
			}
			if start.Value < 0 || end.Value < start.Value || int64(len(arr.Elements)) < end.Value {
				// Return None
				return makeOptionNone()
			}
			// Create slice
			slice := &object.Array{
				Elements: arr.Elements[start.Value:end.Value],
			}
			// Return Some(slice)
			return makeOptionSome(slice)
		},
	}

	if fn, ok := builtins[name]; ok {
		return &object.Builtin{Fn: fn}, true
	}
	return nil, false
}

// evalPrimitiveConstructor evaluates primitive type constructors like u32(x), u64(y)
// These are widening conversions that are total and non-failing
func evalPrimitiveConstructor(typeName string, args []ast.Expression, env *object.Environment) object.Object {
	// Check if it's a primitive type name (including aliases and platform types)
	primitiveTypes := map[string]bool{
		"u8": true, "u16": true, "u32": true, "u64": true,
		"i8": true, "i16": true, "i32": true, "i64": true,
		"int": true, "uint": true, "ptr": true, "uptr": true, // platform types
		"byte": true, // alias of u8
		"rune": true, // alias of u32 (docs/spec/70-strings.md section 9)
	}
	if !primitiveTypes[typeName] {
		return nil // Not a primitive constructor
	}

	// Constructors take exactly one argument
	if len(args) != 1 {
		return newError("primitive constructor %s expects 1 argument, got %d", typeName, len(args))
	}

	// Evaluate the argument
	arg := Eval(args[0], env)
	if isError(arg) {
		return arg
	}

	// Get the integer value
	var value int64
	switch v := arg.(type) {
	case *object.Integer:
		value = v.Value
	default:
		return newError("primitive constructor %s requires an integer argument, got %s", typeName, arg.Type())
	}

	// For now, we just return the integer value
	// In a full implementation, we'd track the type information
	// But for the REPL, returning the integer is sufficient
	return &object.Integer{Value: value}
}

func evalPrefixExpression(operator string, right object.Object) object.Object {
	switch operator {
	case "!":
		return evalBangOperatorExpression(right)
	case "-":
		return evalMinusPrefixOperatorExpression(right)
	default:
		return newError("unknown operator: %s%s", operator, right.Type())
	}
}

func evalBangOperatorExpression(right object.Object) object.Object {
	switch right {
	case TRUE:
		return FALSE
	case FALSE:
		return TRUE
	case NULL:
		return TRUE
	default:
		return FALSE
	}
}

func evalMinusPrefixOperatorExpression(right object.Object) object.Object {
	if right.Type() != object.INTEGER_OBJ {
		return newError("unknown operator: -%s", right.Type())
	}

	value := right.(*object.Integer).Value
	return &object.Integer{Value: -value}
}

func evalInfixExpression(operator string, left, right object.Object) object.Object {
	switch {
	case left.Type() == object.INTEGER_OBJ && right.Type() == object.INTEGER_OBJ:
		return evalIntegerInfixExpression(operator, left, right)
	case left.Type() == object.STRING_OBJ && right.Type() == object.STRING_OBJ:
		return evalStringInfixExpression(operator, left, right)
	case operator == "==":
		return nativeBoolToBooleanObject(left == right)
	case operator == "!=":
		return nativeBoolToBooleanObject(left != right)
	case left.Type() != right.Type():
		return newError("type mismatch: %s %s %s", left.Type(), operator, right.Type())
	default:
		return newError("unknown operator: %s %s %s", left.Type(), operator, right.Type())
	}
}

func evalIntegerInfixExpression(operator string, left, right object.Object) object.Object {
	leftVal := left.(*object.Integer).Value
	rightVal := right.(*object.Integer).Value

	switch operator {
	case "+":
		return &object.Integer{Value: leftVal + rightVal}
	case "-":
		return &object.Integer{Value: leftVal - rightVal}
	case "*":
		return &object.Integer{Value: leftVal * rightVal}
	case "/":
		if rightVal == 0 {
			return newError("division by zero")
		}
		return &object.Integer{Value: leftVal / rightVal}
	case "<":
		return nativeBoolToBooleanObject(leftVal < rightVal)
	case ">":
		return nativeBoolToBooleanObject(leftVal > rightVal)
	case "<=":
		return nativeBoolToBooleanObject(leftVal <= rightVal)
	case ">=":
		return nativeBoolToBooleanObject(leftVal >= rightVal)
	case "==":
		return nativeBoolToBooleanObject(leftVal == rightVal)
	case "!=":
		return nativeBoolToBooleanObject(leftVal != rightVal)
	default:
		return newError("unknown operator: %s %s %s", left.Type(), operator, right.Type())
	}
}

func evalStringInfixExpression(operator string, left, right object.Object) object.Object {
	if operator != "+" {
		return newError("unknown operator: %s %s %s", left.Type(), operator, right.Type())
	}

	leftVal := left.(*object.String).Value
	rightVal := right.(*object.String).Value
	return &object.String{Value: leftVal + rightVal}
}

func nativeBoolToBooleanObject(input bool) *object.Boolean {
	if input {
		return TRUE
	}
	return FALSE
}

func isTruthy(obj object.Object) bool {
	switch obj {
	case NULL:
		return false
	case TRUE:
		return true
	case FALSE:
		return false
	default:
		return true
	}
}

func evalExpressions(exps []ast.Expression, env *object.Environment) []object.Object {
	result := []object.Object{}

	for _, e := range exps {
		evaluated := Eval(e, env)
		if isError(evaluated) {
			return []object.Object{evaluated}
		}
		result = append(result, evaluated)
	}

	return result
}

func applyFunction(fn object.Object, args []object.Object) object.Object {
	switch fn := fn.(type) {
	case *object.Function:
		extendedEnv := extendFunctionEnv(fn, args)
		evaluated := Eval(fn.Body, extendedEnv)
		return unwrapReturnValue(evaluated)
	case *object.Builtin:
		return fn.Fn(args...)
	default:
		return newError("not a function: %s", fn.Type())
	}
}

func extendFunctionEnv(fn *object.Function, args []object.Object) *object.Environment {
	env := object.NewEnclosedEnvironment(fn.Env)

	if fn.Variadic && len(fn.Parameters) > 0 {
		fixed := len(fn.Parameters) - 1
		for paramIdx := 0; paramIdx < fixed && paramIdx < len(args); paramIdx++ {
			env.Set(fn.Parameters[paramIdx].Value, args[paramIdx])
		}
		// Bundle the trailing arguments (possibly none) for the last name.
		rest := &object.Array{Elements: append([]object.Object(nil), args[fixed:]...)}
		env.Set(fn.Parameters[fixed].Value, rest)
		return env
	}

	for paramIdx, param := range fn.Parameters {
		if paramIdx < len(args) {
			env.Set(param.Value, args[paramIdx])
		}
	}

	return env
}

func unwrapReturnValue(obj object.Object) object.Object {
	if returnValue, ok := obj.(*object.ReturnValue); ok {
		return returnValue.Value
	}
	return obj
}

func evalMatchExpression(scrutinee object.Object, arms []*ast.MatchArm, env *object.Environment) object.Object {
	for _, arm := range arms {
		if matchesPattern(scrutinee, arm.Pattern) {
			// Create new environment for pattern bindings
			matchEnv := object.NewEnclosedEnvironment(env)
			bindPattern(scrutinee, arm.Pattern, matchEnv)
			return Eval(arm.Body, matchEnv)
		}
	}
	return newError("non-exhaustive pattern match")
}

func matchesPattern(obj object.Object, pattern ast.Pattern) bool {
	switch p := pattern.(type) {
	case *ast.WildcardPattern:
		return true
	case *ast.BindingPattern:
		return true
	case *ast.LiteralPattern:
		return matchesLiteral(obj, p.Value)
	case *ast.VariantPattern:
		return matchesVariant(obj, p)
	default:
		return false
	}
}

func matchesLiteral(obj object.Object, literal ast.Expression) bool {
	switch lit := literal.(type) {
	case *ast.IntegerLiteral:
		if intObj, ok := obj.(*object.Integer); ok {
			return intObj.Value == lit.Value
		}
	case *ast.StringLiteral:
		if strObj, ok := obj.(*object.String); ok {
			return strObj.Value == lit.Value
		}
	}
	return false
}

func matchesVariant(obj object.Object, pattern *ast.VariantPattern) bool {
	adtVal, ok := obj.(*object.ADTValue)
	if !ok {
		return false
	}

	// Simple variant name matching
	patternName := pattern.Variant.Value
	if adtVal.Variant == patternName || adtVal.Variant == "."+patternName {
		if pattern.Payload != nil {
			// Match payload
			return matchesPattern(adtVal.Value, pattern.Payload)
		}
		return true
	}

	return false
}

func bindPattern(obj object.Object, pattern ast.Pattern, env *object.Environment) {
	switch p := pattern.(type) {
	case *ast.BindingPattern:
		env.Set(p.Name.Value, obj)
	case *ast.VariantPattern:
		if p.Payload != nil {
			if adtVal, ok := obj.(*object.ADTValue); ok && adtVal.Value != nil {
				bindPattern(adtVal.Value, p.Payload, env)
			}
		}
	}
}

func isError(obj object.Object) bool {
	if obj != nil {
		return obj.Type() == object.ERROR_OBJ
	}
	return false
}

func newError(format string, a ...interface{}) *object.Error {
	return &object.Error{Message: fmt.Sprintf(format, a...)}
}

// Helper functions for Option[T] values
// Since we don't have full generic support yet, we create Option values dynamically
func makeOptionNone() *object.ADTValue {
	return &object.ADTValue{
		TypeName: "Option",
		Variant:  "None",
		Value:    nil,
	}
}

func makeOptionSome(value object.Object) *object.ADTValue {
	return &object.ADTValue{
		TypeName: "Option",
		Variant:  "Some",
		Value:    value,
	}
}

// Evaluate ADT type definition
func evalADTType(adt *ast.ADTType, env *object.Environment) object.Object {
	adtType := &object.ADTType{
		Name:     adt.Name.Value,
		Variants: []*object.ADTVariantDef{},
	}

	for _, variant := range adt.Variants {
		variantDef := &object.ADTVariantDef{
			Name: variant.Name.Value,
		}

		if variant.Payload != nil {
			if ident, ok := variant.Payload.(*ast.Identifier); ok {
				variantDef.Payload = ident.Value
			}
		}

		if variant.Literal != nil {
			// Check if this is a record type definition (record literal in type context)
			// In that case, the literal contains type annotations, not values
			if _, ok := variant.Literal.(*ast.RecordLiteral); ok {
				// This is a record type definition: { field: Type, ... }
				// Don't evaluate the field expressions as values - they're type annotations
				// Just store a marker that this is a record type
				variantDef.Literal = &object.Record{Fields: make(map[string]object.Object)}
			} else {
				// Regular literal (for ADT variants with literal tags)
				variantDef.Literal = Eval(variant.Literal, env)
			}
		}

		adtType.Variants = append(adtType.Variants, variantDef)
	}

	env.SetADTType(adt.Name.Value, adtType)
	return NULL
}

// Evaluate function statement (top-level function or method)
func evalFunctionStatement(fn *ast.FunctionStatement, env *object.Environment) object.Object {
	// Convert FunctionParameters to Identifiers
	params := make([]*ast.Identifier, len(fn.Parameters))
	for i, param := range fn.Parameters {
		params[i] = param.Name
	}

	function := &object.Function{
		Parameters: params,
		Body:       &ast.BlockStatement{Statements: []ast.Statement{&ast.ExpressionStatement{Expression: fn.Body}}},
		Env:        env,
		Variadic:   len(fn.Parameters) > 0 && fn.Parameters[len(fn.Parameters)-1].Variadic,
	}

	// If this is a method (has a receiver), store it with a special key: TypeName::methodName
	if fn.Receiver != nil {
		receiverType := fn.Receiver.Type
		if receiverTypeIdent, ok := receiverType.(*ast.Identifier); ok {
			methodKey := fmt.Sprintf("%s::%s", receiverTypeIdent.Value, fn.Name.Value)
			env.Set(methodKey, function)
		}
	}

	// Also store as regular function (methods can be called as regular functions too)
	env.Set(fn.Name.Value, function)
	return function
}

// evalMethodCall evaluates a method call: recv.method(args)
func evalMethodCall(recvExpr ast.Expression, methodName string, args []ast.Expression, env *object.Environment) object.Object {
	// Evaluate receiver
	recv := Eval(recvExpr, env)
	if isError(recv) {
		return recv
	}

	// Determine receiver type name
	var receiverTypeName string
	switch recv := recv.(type) {
	case *object.ADTValue:
		receiverTypeName = recv.TypeName
	case *object.Record:
		// For records, we need to know the record type name
		// This is tricky - records don't store their type name
		// For now, we'll need to infer it or store it
		// Let's use a placeholder approach - we'll need to enhance this
		return newError("method calls on records not yet fully supported")
	default:
		return newError("method calls not supported for type %s", recv.Type())
	}

	// Look up method: TypeName::methodName
	methodKey := fmt.Sprintf("%s::%s", receiverTypeName, methodName)
	method, ok := env.Get(methodKey)
	if !ok {
		return newError("method %s not found for type %s", methodName, receiverTypeName)
	}

	// Evaluate method arguments
	methodArgs := evalExpressions(args, env)
	if len(methodArgs) == 1 && isError(methodArgs[0]) {
		return methodArgs[0]
	}

	// Prepend receiver as first argument
	allArgs := append([]object.Object{recv}, methodArgs...)

	// Call the method
	return applyFunction(method, allArgs)
}

// Evaluate while statement
func evalWhileStatement(ws *ast.WhileStatement, env *object.Environment) object.Object {
	var result object.Object = NULL

	for {
		condition := Eval(ws.Condition, env)
		if isError(condition) {
			return condition
		}

		if !isTruthy(condition) {
			break
		}

		result = Eval(ws.Body, env)
		if isError(result) {
			return result
		}

		if result != nil && result.Type() == object.RETURN_VALUE_OBJ {
			return result
		}
	}

	return result
}

// Evaluate unsafe block
func evalUnsafeBlock(ub *ast.UnsafeBlock, env *object.Environment) object.Object {
	// For now, unsafe blocks just evaluate normally
	// In a real implementation, this would bypass certain checks
	return Eval(ub.Body, env)
}

// Evaluate variable declaration: a: type = value or a: type
func evalVariableDeclaration(vd *ast.VariableDeclaration, env *object.Environment) object.Object {
	// Check if variable already exists - if so, treat as assignment
	if _, exists := env.Get(vd.Name.Value); exists && vd.Type == nil {
		// This is actually an assignment, not a declaration
		if vd.Value != nil {
			val := Eval(vd.Value, env)
			if isError(val) {
				return val
			}
			env.Set(vd.Name.Value, val)
			return val
		}
		return newError("assignment requires a value")
	}

	// New variable declaration
	if vd.Value != nil {
		// Declaration with initialization: a: type = value or a = value (type inference)
		val := Eval(vd.Value, env)
		if isError(val) {
			return val
		}
		env.Set(vd.Name.Value, val)
		return val
	} else {
		// Declaration without initialization: a: type
		// Initialize to NULL for now (in a real implementation, this might be an error)
		env.Set(vd.Name.Value, NULL)
		return NULL
	}
}

// Evaluate assignment statement: a = b
func evalAssignmentStatement(as *ast.AssignmentStatement, env *object.Environment) object.Object {
	// Check if variable exists
	_, ok := env.Get(as.Name.Value)
	if !ok {
		return newError("variable not declared: %s", as.Name.Value)
	}

	val := Eval(as.Value, env)
	if isError(val) {
		return val
	}

	env.Set(as.Name.Value, val)
	return val
}

// Evaluate variant expression: .Ok or Status::Ok
func evalVariantExpression(ve *ast.VariantExpression, env *object.Environment) object.Object {
	var typeName string
	var variantName string

	if ve.TypeName != nil {
		// Type::Variant form
		typeName = ve.TypeName.Value
		variantName = ve.Variant.Value

		// Verify the ADT type exists
		_, ok := env.GetADTType(typeName)
		if !ok {
			return newError("unknown ADT type: %s", typeName)
		}
	} else {
		// .Variant form - try to find the type by searching all ADT types
		variantName = ve.Variant.Value
		typeName = findADTTypeForVariant(variantName, env)
		if typeName == "" {
			return newError("cannot infer type for variant: .%s", variantName)
		}
	}

	// Evaluate payload if present
	var payload object.Object = nil
	if ve.Payload != nil {
		payload = Eval(ve.Payload, env)
		if isError(payload) {
			return payload
		}
	}

	// Create ADT value
	adtValue := &object.ADTValue{
		TypeName: typeName,
		Variant:  variantName,
		Value:    payload,
	}

	return adtValue
}

// Find ADT type that contains the given variant name
func findADTTypeForVariant(variantName string, env *object.Environment) string {
	// Search current environment
	for name, adtType := range env.GetAllADTTypes() {
		for _, variant := range adtType.Variants {
			if variant.Name == variantName {
				return name
			}
		}
	}

	// Search outer environments
	if outer := env.GetOuter(); outer != nil {
		return findADTTypeForVariant(variantName, outer)
	}

	return ""
}

// Evaluate record literal: { field1: value1, field2: value2, ... }
// Also handles type-qualified literals: TypeName{ field1: value1, ... }
func evalRecordLiteral(rl *ast.RecordLiteral, env *object.Environment) object.Object {
	fields := make(map[string]object.Object)

	// Type-qualified literals are handled the same way as regular record literals
	// The typechecker ensures the types match, the evaluator just creates the record
	// If TypeName is set, we ignore it during evaluation - it's only for type checking
	// We must NOT look up the type name in the environment here, as that would
	// interfere with variable evaluation

	// For type-qualified literals, we just evaluate the fields normally
	// The TypeName is only used by the typechecker, not the evaluator

	for fieldName, fieldExpr := range rl.Fields {
		// Check if this looks like a type definition context
		// In type definitions, field expressions are type annotations (identifiers like u8, i32)
		// In value contexts, field expressions are values
		// If the field expression is an identifier that's a primitive type name, skip evaluation
		if ident, ok := fieldExpr.(*ast.Identifier); ok {
			primitiveTypes := map[string]bool{
				"i8": true, "i16": true, "i32": true, "i64": true,
				"u8": true, "u16": true, "u32": true, "u64": true,
				"string": true, "Bool": true, "byte": true, "()": true,
			}
			if primitiveTypes[ident.Value] {
				// This is a type annotation in a type definition context
				// Don't evaluate it as a value - just skip it
				// The type definition is handled by evalADTType()
				continue
			}
		}

		fieldValue := Eval(fieldExpr, env)
		if isError(fieldValue) {
			return fieldValue
		}
		fields[fieldName] = fieldValue
	}

	return &object.Record{Fields: fields}
}

// Evaluate field access: record.field or array indexing: array[index]
// evalIndexAssignmentStatement mutates one element, bounds-checked: parity
// with the trapping C store semantics (error, never silent wrap).
func evalIndexAssignmentStatement(stmt *ast.IndexAssignmentStatement, env *object.Environment) object.Object {
	seq := Eval(stmt.Target.Left, env)
	if isError(seq) {
		return seq
	}
	index := Eval(stmt.Target.Index, env)
	if isError(index) {
		return index
	}
	value := Eval(stmt.Value, env)
	if isError(value) {
		return value
	}
	array, ok := seq.(*object.Array)
	if !ok {
		return newError("cannot index-assign into %s", seq.Type())
	}
	idx, ok := index.(*object.Integer)
	if !ok {
		return newError("index must be an integer, got %s", index.Type())
	}
	if idx.Value < 0 || idx.Value >= int64(len(array.Elements)) {
		return newError("array index out of bounds: %d (length: %d)", idx.Value, len(array.Elements))
	}
	array.Elements[idx.Value] = value
	return NULL
}

func evalIndexExpression(ie *ast.IndexExpression, env *object.Environment) object.Object {
	// Check if this is Type.Variant (ADT constructor) rather than field access
	// If left is an identifier (type name) and we have an ADT with that name, treat as variant
	if leftIdent, ok := ie.Left.(*ast.Identifier); ok {
		adtTypeName := leftIdent.Value
		if _, ok := env.GetADTType(adtTypeName); ok {
			// This is Type.Variant - convert to VariantExpression for evaluation
			if variantIdent, ok := ie.Index.(*ast.Identifier); ok {
				// Create a VariantExpression and evaluate it
				ve := &ast.VariantExpression{
					Token:    ie.Token,
					TypeName: leftIdent,
					Variant:  variantIdent,
					Payload:  nil, // No payload for simple variants
				}
				return evalVariantExpression(ve, env)
			}
		}
	}

	// Not an ADT constructor, evaluate as normal index expression
	left := Eval(ie.Left, env)
	if isError(left) {
		return left
	}

	// Check if this is record field access (index is identifier) or array indexing
	if fieldName, ok := ie.Index.(*ast.Identifier); ok {
		// Special case: raw() method on ADT values
		if fieldName.Value == "raw" {
			if adtValue, ok := left.(*object.ADTValue); ok {
				return evalRawAccessor(adtValue, env)
			}
			return newError("raw() only works on ADT values, got %s", left.Type())
		}

		// Record field access: record.field
		if record, ok := left.(*object.Record); ok {
			if fieldValue, exists := record.Fields[fieldName.Value]; exists {
				return fieldValue
			}
			return newError("field '%s' not found in record", fieldName.Value)
		}

		// Field lifting: ADT with literal tags - access fields from raw type
		if adtValue, ok := left.(*object.ADTValue); ok {
			return evalFieldLifting(adtValue, fieldName.Value, env)
		}

		return newError("field access not supported for type %s", left.Type())
	}

	// Array indexing: array[index]
	indexObj := Eval(ie.Index, env)
	if isError(indexObj) {
		return indexObj
	}

	if array, ok := left.(*object.Array); ok {
		// Check if index is an integer
		index, ok := indexObj.(*object.Integer)
		if !ok {
			return newError("array index must be integer, got %s", indexObj.Type())
		}

		// Bounds check
		idx := index.Value
		if idx < 0 || int64(len(array.Elements)) <= idx {
			return newError("array index out of bounds: %d (length: %d)", idx, len(array.Elements))
		}

		return array.Elements[idx]
	}

	return newError("index operator not supported for type %s", left.Type())
}

// Evaluate array literal: [elem1, elem2, ...]
func evalArrayLiteral(al *ast.ArrayLiteral, env *object.Environment) object.Object {
	elements := []object.Object{}

	for _, elemExpr := range al.Elements {
		elem := Eval(elemExpr, env)
		if isError(elem) {
			return elem
		}
		elements = append(elements, elem)
	}

	return &object.Array{Elements: elements}
}

// evalRawAccessor implements the raw() accessor for ADT values with literal tags
func evalRawAccessor(adtValue *object.ADTValue, env *object.Environment) object.Object {
	// Get ADT type definition
	adtType, ok := env.GetADTType(adtValue.TypeName)
	if !ok {
		return newError("ADT type %s not found", adtValue.TypeName)
	}

	// Find the variant and its literal
	for _, variant := range adtType.Variants {
		if variant.Name == adtValue.Variant {
			if variant.Literal != nil {
				// Return the literal value
				return variant.Literal
			}
			return newError("variant %s of ADT %s has no literal tag", adtValue.Variant, adtValue.TypeName)
		}
	}

	return newError("variant %s not found in ADT %s", adtValue.Variant, adtValue.TypeName)
}

// evalFieldLifting implements field lifting for ADT values with record literal tags
// e.g., if Status has { code: 200, status: "Ok" }, then s.code returns 200
func evalFieldLifting(adtValue *object.ADTValue, fieldName string, env *object.Environment) object.Object {
	// Get the raw value first
	rawValue := evalRawAccessor(adtValue, env)
	if isError(rawValue) {
		return rawValue
	}

	// If raw value is a record, access the field
	if record, ok := rawValue.(*object.Record); ok {
		if fieldValue, exists := record.Fields[fieldName]; exists {
			return fieldValue
		}
		return newError("field '%s' not found in raw type of ADT %s", fieldName, adtValue.TypeName)
	}

	// If raw value is not a record, field lifting doesn't apply
	return newError("field lifting only works when ADT has record literal tags, got %s", rawValue.Type())
}
