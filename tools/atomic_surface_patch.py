#!/usr/bin/env python3
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

def text(path):
    return (ROOT / path).read_text()

def write(path, value):
    (ROOT / path).write_text(value)

def replace_once(path, old, new):
    s = text(path)
    count = s.count(old)
    if count != 1:
        raise SystemExit(f"{path}: expected one anchor, found {count}: {old[:100]!r}")
    write(path, s.replace(old, new, 1))

def replace_n(path, old, new, n):
    s = text(path)
    count = s.count(old)
    if count != n:
        raise SystemExit(f"{path}: expected {n} anchors, found {count}: {old[:100]!r}")
    write(path, s.replace(old, new))

# --- type elaboration: Atomic[T] is a special storage type, not a generic ADT.
replace_once(
    "typechecker/gadt.go",
    '''func (tc *TypeChecker) parseGenericTypeApplication(expr ast.Expression) (Type, bool) {
\tname, argExprs, ok := flattenTypeApplicationSyntax(expr)
\tif !ok || len(argExprs) == 0 {
\t\treturn nil, false
\t}
\targs := make([]Type, 0, len(argExprs))
''',
    '''func (tc *TypeChecker) parseGenericTypeApplication(expr ast.Expression) (Type, bool) {
\tname, argExprs, ok := flattenTypeApplicationSyntax(expr)
\tif !ok || len(argExprs) == 0 {
\t\treturn nil, false
\t}
\tif name == "Atomic" {
\t\tif len(argExprs) != 1 {
\t\t\ttc.addError(expr, "Atomic[...] expects exactly one fixed-width integer carrier")
\t\t\treturn nil, true
\t\t}
\t\telement := tc.parseTypeExpression(argExprs[0])
\t\tif element == nil {
\t\t\treturn nil, true
\t\t}
\t\tatomicType, err := NewAtomicType(element)
\t\tif err != nil {
\t\t\ttc.addError(expr, "%v", err)
\t\t\treturn nil, true
\t\t}
\t\treturn atomicType, true
\t}
\targs := make([]Type, 0, len(argExprs))
''')

# --- typechecker: compiler-known atomic calls and non-copy storage rules.
replace_once(
    "typechecker/typechecker.go",
    '''func (tc *TypeChecker) checkInvocationExpression(expr *ast.InvocationExpression) Type {
\t// Check if this is a primitive type constructor: u32(x), u64(y), etc.
''',
    '''func (tc *TypeChecker) checkInvocationExpression(expr *ast.InvocationExpression) Type {
\tif ident, ok := expr.Function.(*ast.Identifier); ok {
\t\tif atomicType, recognized := tc.checkAtomicInvocation(ident.Value, expr); recognized {
\t\t\treturn atomicType
\t\t}
\t}
\t// Check if this is a primitive type constructor: u32(x), u64(y), etc.
''')

replace_once(
    "typechecker/typechecker.go",
    '''\tcase *ast.ExpressionStatement:
\t\t// Expression statements don't need type checking beyond checking the expression
\t\ttc.checkExpression(s.Expression)
''',
    '''\tcase *ast.ExpressionStatement:
\t\tresultType := tc.checkExpression(s.Expression)
\t\tif ContainsAtomicStorage(resultType) {
\t\t\ttc.addError(s.Expression, "Atomic[T] is storage identity, not a value; use an atomic_load_* operation")
\t\t}
''')

replace_once(
    "typechecker/typechecker.go",
    '''\trightType := tc.checkExpression(expr.Right)
\tif rightType == nil {
\t\treturn nil
\t}

\tswitch expr.Operator {
''',
    '''\trightType := tc.checkExpression(expr.Right)
\tif rightType == nil {
\t\treturn nil
\t}
\tif ContainsAtomicStorage(rightType) {
\t\ttc.addError(expr.Right, "Atomic[T] cannot be used with prefix operators; load the cell explicitly")
\t\treturn nil
\t}

\tswitch expr.Operator {
''')

replace_once(
    "typechecker/typechecker.go",
    '''\tif leftType == nil || rightType == nil {
\t\treturn nil
\t}

\tswitch expr.Operator {
''',
    '''\tif leftType == nil || rightType == nil {
\t\treturn nil
\t}
\tif ContainsAtomicStorage(leftType) || ContainsAtomicStorage(rightType) {
\t\ttc.addError(expr, "Atomic[T] cells cannot participate in ordinary operators; use explicit atomic_load_*/store_*/fetch_add_* operations")
\t\treturn nil
\t}

\tswitch expr.Operator {
''')

replace_once(
    "typechecker/typechecker.go",
    '''\tscrutineeType := tc.checkExpression(expr.Scrutinee)
\tif scrutineeType == nil {
\t\treturn nil
\t}

\t// Check that match expression has at least one arm
''',
    '''\tscrutineeType := tc.checkExpression(expr.Scrutinee)
\tif scrutineeType == nil {
\t\treturn nil
\t}
\tif ContainsAtomicStorage(scrutineeType) {
\t\ttc.addError(expr.Scrutinee, "Atomic[T] cells cannot be matched as values; load the cell explicitly")
\t\treturn nil
\t}

\t// Check that match expression has at least one arm
''')

replace_once(
    "typechecker/typechecker.go",
    '''\t// Variable exists - this is a real assignment
\t// Instantiate the scheme to get the actual type
\tunifier := NewUnifier()
\tvarType := Instantiate(varScheme, unifier)

\t// Check that assigned value matches variable type (with coercion)
''',
    '''\t// Variable exists - this is a real assignment
\t// Instantiate the scheme to get the actual type
\tunifier := NewUnifier()
\tvarType := Instantiate(varScheme, unifier)
\tif _, atomic := varType.(*AtomicType); atomic {
\t\ttc.addError(stmt, "Atomic[T] cells are not assignable; use an atomic_store_* operation")
\t\treturn
\t}

\t// Check that assigned value matches variable type (with coercion)
''')

replace_once(
    "typechecker/typechecker.go",
    '''\t\t// If there's an initializer, check that it matches the type (with coercion)
''',
    '''\t\tif _, atomic := varType.(*AtomicType); atomic {
\t\t\tif stmt.Value != nil {
\t\t\t\ttc.addError(stmt, "Atomic[T] cells are zero-initialized storage in v1; initialize with atomic_store_* after declaration")
\t\t\t\treturn
\t\t\t}
\t\t} else if ContainsAtomicStorage(varType) {
\t\t\ttc.addError(stmt.Type, "Atomic[T] cannot be embedded in arrays, records, or generic values in v1")
\t\t\treturn
\t\t}

\t\t// If there's an initializer, check that it matches the type (with coercion)
''')

replace_once(
    "typechecker/typechecker.go",
    '''\t\t\tif inferredType != nil {
\t\t\t\t// Generalize: convert to a type scheme
\t\t\t\tscheme := Generalize(inferredType, tc.env)
''',
    '''\t\t\tif inferredType != nil {
\t\t\t\tif ContainsAtomicStorage(inferredType) {
\t\t\t\t\ttc.addError(stmt.Value, "Atomic[T] storage cannot be inferred/copied into a value binding; declare a named Atomic[T] cell")
\t\t\t\t\treturn
\t\t\t\t}
\t\t\t\t// Generalize: convert to a type scheme
\t\t\t\tscheme := Generalize(inferredType, tc.env)
''')

replace_once(
    "typechecker/typechecker.go",
    '''\t\tif paramType == nil {
\t\t\t// Default to i32 if type parsing fails
\t\t\tparamType = &PrimitiveType{Name: "i32"}
\t\t}
\t\tif param.Variadic {
''',
    '''\t\tif paramType == nil {
\t\t\t// Default to i32 if type parsing fails
\t\t\tparamType = &PrimitiveType{Name: "i32"}
\t\t}
\t\tif ContainsAtomicStorage(paramType) {
\t\t\ttc.addError(param.Type, "Atomic[T] storage cannot be passed by value in v1; use package/local cells until an AtomicRef borrowing contract exists")
\t\t\treturn
\t\t}
\t\tif param.Variadic {
''')

replace_once(
    "typechecker/typechecker.go",
    '''\t// Parse return type
\treturnType := tc.parseTypeExpressionInEnv(stmt.ReturnType, funcEnv)
\tif returnType == nil {
\t\treturnType = &UnitType{}
\t}

\t// Pre-bind the declared signature so the body can reference itself:
''',
    '''\t// Parse return type
\treturnType := tc.parseTypeExpressionInEnv(stmt.ReturnType, funcEnv)
\tif returnType == nil {
\t\treturnType = &UnitType{}
\t}
\tif ContainsAtomicStorage(returnType) {
\t\ttc.addError(stmt.ReturnType, "Atomic[T] storage cannot be returned by value in v1")
\t\treturn
\t}

\t// Pre-bind the declared signature so the body can reference itself:
''')

replace_once(
    "typechecker/typechecker.go",
    '''\t\t\tpayloadType := tc.parseTypeExpression(variant.Payload)
\t\t\tif payloadType == nil {
''',
    '''\t\t\tpayloadType := tc.parseTypeExpression(variant.Payload)
\t\t\tif ContainsAtomicStorage(payloadType) {
\t\t\t\ttc.addError(variant.Payload, "Atomic[T] cannot be embedded in ADT payloads in v1")
\t\t\t}
\t\t\tif payloadType == nil {
''')

replace_once(
    "typechecker/typechecker.go",
    '''\t\tfieldType := tc.parseTypeExpression(fieldExpr)
\t\tif fieldType == nil {
\t\t\t// fieldExpr might be an expression, try to use it as a node
''',
    '''\t\tfieldType := tc.parseTypeExpression(fieldExpr)
\t\tif ContainsAtomicStorage(fieldType) {
\t\t\ttc.addError(fieldExpr, "Atomic[T] cannot be embedded in record values in v1")
\t\t}
\t\tif fieldType == nil {
\t\t\t// fieldExpr might be an expression, try to use it as a node
''')

replace_n(
    "typechecker/typechecker.go",
    '''\t\tcase "any":
\t\t\treturn &AnyType{}
\t\tdefault:
''',
    '''\t\tcase "any":
\t\t\treturn &AnyType{}
\t\tcase "Atomic":
\t\t\ttc.addError(ident, "Atomic requires exactly one carrier: Atomic[u8|u16|u32|u64|i8|i16|i32|i64]")
\t\t\treturn nil
\t\tdefault:
''',
    2,
)

# --- codegen integration.
replace_once(
    "codegen/codegen.go",
    '''\tcg.write("#include <stddef.h>\\n")
\tcg.write("\\n")
''',
    '''\tcg.write("#include <stddef.h>\\n")
\tcg.write("#include <stdatomic.h>\\n")
\tcg.write("\\n")
''')

replace_once(
    "codegen/codegen.go",
    '''\tcg.emitUtf8Helper()
\tcg.emitIntrinsicHelpers(program)

\t// Container typedefs''',
    '''\tcg.emitUtf8Helper()
\tcg.emitIntrinsicHelpers(program)
\tcg.emitAtomicGlobals(program)

\t// Container typedefs''')

replace_once(
    "codegen/codegen.go",
    '''\tcase *ast.InvocationExpression:
\t\t// Function or method call.''',
    '''\tcase *ast.InvocationExpression:
\t\tif cg.emitAtomicInvocation(e, tc) {
\t\t\treturn
\t\t}
\t\t// Function or method call.''')

replace_once(
    "codegen/codegen.go",
    '''\tif indexExpr, ok := expr.(*ast.IndexExpression); ok {
\t\t// Phantom-encoded strings share one representation:''',
    '''\tif indexExpr, ok := expr.(*ast.IndexExpression); ok {
\t\tif cType, atomic := atomicTypeC(indexExpr); atomic {
\t\t\treturn cType
\t\t}
\t\t// Phantom-encoded strings share one representation:''')

replace_once(
    "codegen/codegen.go",
    '''func (cg *CodeGenerator) emitVariableDeclaration(stmt *ast.VariableDeclaration, tc *typechecker.TypeChecker) {
\tvarName := stmt.Name.Value

\t// Owned arrays use C declarator syntax;''',
    '''func (cg *CodeGenerator) emitVariableDeclaration(stmt *ast.VariableDeclaration, tc *typechecker.TypeChecker) {
\tvarName := stmt.Name.Value

\tif stmt.Type != nil {
\t\tif cType, atomic := atomicTypeC(stmt.Type); atomic {
\t\t\tif stmt.Value != nil {
\t\t\t\tcg.write("  OAK_ATOMIC_INITIALIZER_MUST_BE_ZERO_INIT;\\n")
\t\t\t\treturn
\t\t\t}
\t\t\tcg.write(fmt.Sprintf("  %s %s = 0;\\n", cType, varName))
\t\t\treturn
\t\t}
\t}

\t// Owned arrays use C declarator syntax;''')

# --- evaluator integration.
replace_once(
    "evaluator/evaluator.go",
    '''\tcase *ast.InvocationExpression:
\t\t// Check if this is a primitive type constructor:''',
    '''\tcase *ast.InvocationExpression:
\t\tif ident, ok := node.Function.(*ast.Identifier); ok {
\t\t\tif result, recognized := evalAtomicInvocation(ident.Value, node.Arguments, env); recognized {
\t\t\t\treturn result
\t\t\t}
\t\t}
\t\t// Check if this is a primitive type constructor:''')

replace_once(
    "evaluator/evaluator.go",
    '''func evalVariableDeclaration(vd *ast.VariableDeclaration, env *object.Environment) object.Object {
\t// Check if variable already exists - if so, treat as assignment
''',
    '''func evalVariableDeclaration(vd *ast.VariableDeclaration, env *object.Environment) object.Object {
\tif isAtomicTypeExpression(vd.Type) {
\t\tif vd.Value != nil {
\t\t\treturn newError("Atomic[T] cells are zero-initialized in v1; initialize with atomic_store_*")
\t\t}
\t\tcell := &object.AtomicCell{}
\t\tenv.Set(vd.Name.Value, cell)
\t\treturn cell
\t}
\t// Check if variable already exists - if so, treat as assignment
''')

replace_once(
    "evaluator/evaluator.go",
    '''func evalAssignmentStatement(as *ast.AssignmentStatement, env *object.Environment) object.Object {
\t// Check if variable exists
\t_, ok := env.Get(as.Name.Value)
\tif !ok {
\t\treturn newError("variable not declared: %s", as.Name.Value)
\t}
''',
    '''func evalAssignmentStatement(as *ast.AssignmentStatement, env *object.Environment) object.Object {
\t// Check if variable exists
\texisting, ok := env.Get(as.Name.Value)
\tif !ok {
\t\treturn newError("variable not declared: %s", as.Name.Value)
\t}
\tif _, atomic := existing.(*object.AtomicCell); atomic {
\t\treturn newError("Atomic[T] cells are not directly assignable; use atomic_store_*")
\t}
''')

print("atomic surface compiler patch applied")
