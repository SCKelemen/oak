package evaluator

import (
	"fmt"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/object"
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

	case *ast.BlockStatement:
		return evalBlockStatement(node, env)

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
		function := Eval(node.Function, env)
		if isError(function) {
			return function
		}
		args := evalExpressions(node.Arguments, env)
		if len(args) == 1 && isError(args[0]) {
			return args[0]
		}
		return applyFunction(function, args)

	case *ast.MatchExpression:
		scrutinee := Eval(node.Scrutinee, env)
		if isError(scrutinee) {
			return scrutinee
		}
		return evalMatchExpression(scrutinee, node.Arms, env)

	case *ast.IfExpression:
		return evalIfExpression(node, env)

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

	default:
		return newError("unknown node type: %T", node)
	}
}

func evalProgram(program *ast.Program, env *object.Environment) object.Object {
	var result object.Object

	for _, statement := range program.Statements {
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
	val, ok := env.Get(node.Value)
	if !ok {
		return newError("identifier not found: %s", node.Value)
	}
	return val
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

func evalIfExpression(ie *ast.IfExpression, env *object.Environment) object.Object {
	condition := Eval(ie.Condition, env)
	if isError(condition) {
		return condition
	}

	if isTruthy(condition) {
		return Eval(ie.Consequence, env)
	} else if ie.Alternative != nil {
		return Eval(ie.Alternative, env)
	} else {
		return NULL
	}
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
	function, ok := fn.(*object.Function)
	if !ok {
		return newError("not a function: %s", fn.Type())
	}

	extendedEnv := extendFunctionEnv(function, args)
	evaluated := Eval(function.Body, extendedEnv)
	return unwrapReturnValue(evaluated)
}

func extendFunctionEnv(fn *object.Function, args []object.Object) *object.Environment {
	env := object.NewEnclosedEnvironment(fn.Env)

	for paramIdx, param := range fn.Parameters {
		env.Set(param.Value, args[paramIdx])
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
			variantDef.Literal = Eval(variant.Literal, env)
		}

		adtType.Variants = append(adtType.Variants, variantDef)
	}

	env.SetADTType(adt.Name.Value, adtType)
	return NULL
}

// Evaluate function statement (top-level function)
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
	}

	env.Set(fn.Name.Value, function)
	return function
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
	if vd.Value != nil {
		// Declaration with initialization: a: type = value
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
