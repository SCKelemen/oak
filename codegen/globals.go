package codegen

// Static globals (docs/spec/60-effects-allocation.md): top-level bindings
// lower to C file-scope statics with constant initializers — the same
// judgment the type checker enforces (typechecker/globals.go,
// OAK-T0501). Anything non-constant fails closed here; runtime
// initialization belongs at the top of main. Names follow the local
// convention (unmangled), which Oak's no-shadowing rule keeps unambiguous.

import (
	"fmt"
	"github.com/SCKelemen/oak/token"
	"math"
	"reflect"
	"strconv"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/evaluator"
	"github.com/SCKelemen/oak/object"
	"github.com/SCKelemen/oak/typechecker"
)

// emitGlobals emits every top-level declaration as a file-scope static.
// Atomic cells are emitted by emitAtomicGlobals and skipped here.
func (cg *CodeGenerator) emitGlobals(program *ast.Program, tc *typechecker.TypeChecker) {
	cg.globalTypes = make(map[string]localContainer)
	cg.mutatedGlobals = mutatedGlobals(program)
	cg.foldEnv = object.NewEnvironment()
	cg.foldEnv.SetArithmeticWidths(tc.ArithmeticType)
	cg.constantGlobals = make(map[string]bool)
	emitted := false
	for _, stmt := range program.Statements {
		decl, isDecl := stmt.(*ast.VariableDeclaration)
		if !isDecl || decl.Name == nil {
			continue
		}
		if decl.Type != nil {
			cg.globalTypes[decl.Name.Value] = cg.classifyContainer(decl.Type)
		}
		if decl.Type != nil {
			if _, atomic := atomicTypeC(decl.Type); atomic {
				continue
			}
		}
		if !emitted {
			cg.write("/* static globals: constant-initialized, zero otherwise */\n")
			emitted = true
		}
		cg.emitGlobal(decl, tc)
	}
	if emitted {
		cg.write("\n")
	}
}

func (cg *CodeGenerator) emitGlobal(decl *ast.VariableDeclaration, tc *typechecker.TypeChecker) {
	name := cIdent(decl.Name.Value)

	// Declarator. Owned arrays are wrapper-struct values (codegen/arrays.go),
	// so they take the ordinary type-then-name form.
	declarator := ""
	if decl.Type != nil {
		if fn, isFunction := decl.Type.(*ast.FunctionTypeExpression); isFunction {
			declarator = "static " + cg.cFunctionPointer(fn, name)
		}
		if indexExpr, isIndex := decl.Type.(*ast.IndexExpression); isIndex {
			// Generic instantiations (Ring[u8, 8]) are struct types, not
			// arrays — the template's arity disambiguates (codegen/mono.go).
			if mangled, isGeneric := cg.genericAnnotationName(indexExpr); isGeneric {
				declarator = fmt.Sprintf("static %s %s", cg.cTypeName(mangled), name)
			}
		}
		if declarator == "" {
			storage := "static"
			if cg.isConstantGlobal(decl) {
				// A global no statement writes, borrows, or addresses is a
				// C constant (docs/spec/90-backend.md section 8a): the C
				// compiler folds it — `x / page_size` becomes a shift where
				// a mutable static would divide (the OS pilot's R2).
				storage = "static const"
			}
			declarator = fmt.Sprintf("%s %s %s", storage, cg.parseTypeExpression(decl.Type), name)
		}
	} else {
		// Inferred globals need an annotation for static storage.
		cg.write(fmt.Sprintf("OAK_GLOBAL_NEEDS_TYPE_ANNOTATION(%s);\n", name))
		cg.globalError(decl, "global %s needs a type annotation for static storage", decl.Name.Value)
		return
	}

	// Declared placement (docs/spec/65-machine-memory.md): the linker
	// section; the parser admitted only a plain section spelling.
	if decl.Section != "" {
		declarator = fmt.Sprintf("__attribute__((section(\"%s\"))) %s", decl.Section, declarator)
	}

	if constant, isTargetConstant := cg.targetConstants[decl.Name.Value]; isTargetConstant {
		// A target constant (docs/spec/92-ffi.md section 2.11): the C
		// identifier the header defines, resolved by the C compiler per
		// target; a constant expression there, never folded here. The
		// identifier passed ValidCSymbol at check time and is re-validated
		// before it reaches the generated source.
		if !typechecker.ValidCSymbol(constant.Identifier) {
			cg.write(fmt.Sprintf("OAK_INVALID_TARGET_CONSTANT(%s);\n", name))
			cg.globalError(decl, "target constant %s names an invalid C identifier", decl.Name.Value)
			return
		}
		// The binding's C name carries a prefix: the Oak name is usually
		// the C identifier itself (CLOCK_MONOTONIC), and on Darwin that is
		// a macro over an enumerator, so the bare name as a declarator
		// would be rewritten by the preprocessor. Reads use the same
		// prefixed name (targetConstantCName).
		cg.write(fmt.Sprintf("static const %s %s = %s;\n", cg.parseTypeExpression(decl.Type), targetConstantCName(decl.Name.Value), constant.Identifier))
		return
	}

	if decl.Value == nil {
		// Zero initialization: explicit for aggregates, zero for scalars.
		if info := cg.classifyContainer(decl.Type); info.kind == containerOwnedArray {
			cg.write(declarator + zeroArrayInitializer(info.length) + ";\n")
		} else if _, isIndex := decl.Type.(*ast.IndexExpression); isIndex {
			cg.write(declarator + " = {0};\n")
		} else if cg.isAggregateType(decl.Type) {
			cg.write(declarator + " = {0};\n")
		} else {
			cg.write(declarator + " = 0;\n")
		}
		return
	}

	if !typechecker.IsConstantInitializerIn(decl.Value, cg.constantGlobals) {
		// Fail closed, as an Oak error rather than a C one (ml finding F19):
		// never a hidden global constructor. OAK-T0501 warned at check time;
		// emission is where the C backend's rule becomes binding.
		cg.write(fmt.Sprintf("OAK_GLOBAL_INITIALIZER_NOT_CONSTANT(%s);\n", name))
		cg.globalError(decl, "global %s has an initializer that is not a compile-time constant; static storage is initialized before any code runs (literals, arithmetic over literals, conversions of constants, record/array literals of constants); initialize runtime values at the top of main", decl.Name.Value)
		return
	}

	cg.write(declarator + " = ")
	if typeName, isIdent := decl.Type.(*ast.Identifier); isIdent {
		cg.foldTypeHint = typeName.Value
	}
	cg.emitFileScopeInitializer(decl.Value, tc)
	cg.foldTypeHint = ""
	cg.output.WriteString(";\n")
	// A constant global is readable by the constant initializers after it:
	// bind its value in the fold environment.
	cg.constantGlobals[decl.Name.Value] = true
	if result := evaluator.Eval(decl, cg.foldEnv); result != nil {
		if e, isErr := result.(*object.Error); isErr {
			cg.globalError(decl, "global %s does not fold for later initializers: %s", decl.Name.Value, e.Message)
		}
	}
}

// targetConstantCName is the C identifier of a target constant's static:
// prefixed, because the Oak name is typically the C macro's own name.
func targetConstantCName(name string) string {
	return "oak_const_" + cIdent(name)
}

// isAggregateType reports whether the annotation names a struct-like type
// (records, ADTs, strings) that zero-initializes with {0}.
func (cg *CodeGenerator) isAggregateType(typeExpr ast.Expression) bool {
	ident, isIdent := typeExpr.(*ast.Identifier)
	if !isIdent {
		return false
	}
	if ident.Value == "string" {
		return true
	}
	_, isADT := cg.adtTypes[ident.Value]
	return isADT
}

// emitFileScopeInitializer emits a constant initializer valid in static
// storage: designated initializers without compound-literal casts (strict
// C99 constness), string literals as address-constant field initializers.
func (cg *CodeGenerator) emitFileScopeInitializer(expr ast.Expression, tc *typechecker.TypeChecker) {
	switch e := expr.(type) {
	case *ast.StringLiteral:
		idx, exists := cg.stringLiteralMap[e.Value]
		if !exists {
			idx = len(cg.stringLiterals)
			cg.stringLiterals = append(cg.stringLiterals, e.Value)
			cg.stringLiteralMap[e.Value] = idx
		}
		cg.output.WriteString(fmt.Sprintf("{ .data = (u8*)str_lit_%d, .len = %d }", idx, len(e.Value)))
	case *ast.RecordLiteral:
		cg.output.WriteString("{ ")
		for i, field := range e.FieldOrder {
			if i > 0 {
				cg.output.WriteString(", ")
			}
			cg.output.WriteString(fmt.Sprintf(".%s = ", cIdent(field.Name)))
			cg.emitFileScopeInitializer(field.Value, tc)
		}
		cg.output.WriteString(" }")
	case *ast.ArrayLiteral:
		// The wrapper struct, then its array member (codegen/arrays.go).
		cg.output.WriteString("{ { ")
		for i, element := range e.Elements {
			if i > 0 {
				cg.output.WriteString(", ")
			}
			cg.emitFileScopeInitializer(element, tc)
		}
		cg.output.WriteString(" } }")
	default:
		if typechecker.ContainsFoldedConversion(expr) {
			// A conversion of constants has no C constant-expression form;
			// fold it (docs/spec/60-effects-allocation.md section 10a).
			cg.emitFoldedConstant(expr, tc)
			return
		}
		// Scalar constant expressions share the ordinary fragment emitter,
		// in constant context so arithmetic stays a C constant expression.
		cg.emitConstantExpression(expr, tc)
	}
}

// globalError records a top-level initializer the backend cannot place in
// static storage, positioned at the declaration.
func (cg *CodeGenerator) globalError(decl *ast.VariableDeclaration, format string, args ...any) {
	position := ""
	if decl.Name != nil {
		position = fmt.Sprintf("%d:%d: ", decl.Name.Token.Line, decl.Name.Token.Column)
	}
	cg.globalErrors = append(cg.globalErrors,
		fmt.Errorf("error[%s]: %s%s", typechecker.CodeGlobalInitializerNotConstant, position, fmt.Sprintf(format, args...)))
}

// emitFoldedConstant evaluates a constant initializer that contains a named
// conversion or float constructor and emits the resulting scalar as a C
// literal of the initializer's type. The interpreter is the first witness of
// every conversion's bit-exact semantics (docs/spec/20-types.md section
// 11.3.4), and the differential tests hold it to the C helpers, so the
// folded constant is the value the program would compute at run time.
func (cg *CodeGenerator) emitFoldedConstant(expr ast.Expression, tc *typechecker.TypeChecker) {
	typeName, typed := tc.FoldedConstantType(expr)
	if !typed && cg.foldTypeHint != "" {
		// The declaration's own annotation, when the whole initializer is
		// the folded expression.
		typeName, typed = cg.foldTypeHint, true
	}
	env := cg.foldEnv
	if env == nil {
		env = object.NewEnvironment()
		env.SetArithmeticWidths(tc.ArithmeticType)
	}
	value := evaluator.Eval(expr, env)
	fail := func(format string, args ...any) {
		cg.output.WriteString("OAK_GLOBAL_INITIALIZER_NOT_FOLDED")
		cg.globalErrors = append(cg.globalErrors,
			fmt.Errorf("error[%s]: %s", typechecker.CodeGlobalInitializerNotConstant, fmt.Sprintf(format, args...)))
	}
	switch v := value.(type) {
	case *object.Integer:
		if !typed {
			fail("global initializer %s: cannot name the folded constant's type", expr.String())
			return
		}
		if v.Value == math.MinInt64 {
			cg.output.WriteString(fmt.Sprintf("((%s)(-9223372036854775807LL - 1))", typeName))
			return
		}
		cg.output.WriteString(fmt.Sprintf("((%s)(%d))", typeName, v.Value))
	case *object.Float:
		switch {
		case v.Bits == 8 || v.Bits == 16:
			cg.output.WriteString(fmt.Sprintf("((%s)0x%Xu)", v.Format, evaluator.StorageBits(v)))
		case typeName == "f32" || (v.Bits == 32 && !typed):
			cg.output.WriteString(cFloatConstant("f32", float64(float32(v.Value))))
		default:
			cg.output.WriteString(cFloatConstant("f64", v.Value))
		}
	case *object.Boolean:
		if v.Value {
			cg.output.WriteString("oak_Bool_True")
		} else {
			cg.output.WriteString("oak_Bool_False")
		}
	case *object.Error:
		fail("global initializer %s does not fold: %s", expr.String(), v.Message)
	default:
		fail("global initializer %s folds to %s, which static storage cannot hold", expr.String(), value.Type())
	}
}

// cFloatConstant spells a float as an exact C constant expression: a
// hexadecimal literal, or the builtin infinity and NaN, which clang and gcc
// accept in static initializers.
func cFloatConstant(name string, value float64) string {
	suffix := ""
	bits := 64
	if name == "f32" {
		suffix = "f"
		bits = 32
	}
	switch {
	case math.IsNaN(value):
		return fmt.Sprintf("((%s)__builtin_nan%s(\"\"))", name, suffix)
	case math.IsInf(value, 1):
		return fmt.Sprintf("((%s)__builtin_inf%s())", name, suffix)
	case math.IsInf(value, -1):
		return fmt.Sprintf("((%s)-__builtin_inf%s())", name, suffix)
	}
	return fmt.Sprintf("((%s)%s%s)", name, strconv.FormatFloat(value, 'x', -1, bits), suffix)
}

// isConstantGlobal reports whether a typed scalar global with a constant
// initializer is never written, borrowed, or addressed anywhere in the
// program, so it may be emitted as a C constant.
func (cg *CodeGenerator) isConstantGlobal(decl *ast.VariableDeclaration) bool {
	if decl == nil || decl.Name == nil || decl.Value == nil || decl.Type == nil || cg.mutatedGlobals[decl.Name.Value] {
		return false
	}
	typeName, isIdent := decl.Type.(*ast.Identifier)
	if !isIdent || !scalarGlobalTypes[typeName.Value] {
		return false
	}
	if _, isTargetConstant := cg.targetConstants[decl.Name.Value]; isTargetConstant {
		return false
	}
	return typechecker.IsConstantInitializerIn(decl.Value, cg.constantGlobals)
}

// scalarGlobalTypes are the global types emitted as C constants when never
// written: the fixed-width integers, floats, and Bool.
var scalarGlobalTypes = map[string]bool{
	"u8": true, "u16": true, "u32": true, "u64": true, "i8": true, "i16": true, "i32": true, "i64": true,
	"f32": true, "f64": true, "Bool": true, "byte": true,
}

// mutatedGlobals names every top-level binding some statement assigns,
// index-assigns, or takes the address of (`&g`, the operand of span, view,
// and address_of): the globals that must stay mutable statics.
func mutatedGlobals(program *ast.Program) map[string]bool {
	mutated := map[string]bool{}
	var walk func(v reflect.Value)
	walk = func(v reflect.Value) {
		switch v.Kind() {
		case reflect.Interface, reflect.Pointer:
			if v.IsNil() {
				return
			}
			switch node := v.Interface().(type) {
			case *ast.AssignmentStatement:
				if node.Name != nil {
					mutated[node.Name.Value] = true
				}
			case *ast.IndexAssignmentStatement:
				if root, ok := pathRootIdentifier(node.Target); ok {
					mutated[root] = true
				}
			case *ast.PrefixExpression:
				if node.Operator == "&" {
					if root, ok := pathRootIdentifier(node.Right); ok {
						mutated[root] = true
					}
				}
			}
			walk(v.Elem())
		case reflect.Struct:
			if v.Type() == reflect.TypeOf(token.Token{}) {
				return
			}
			for i := 0; i < v.NumField(); i++ {
				if v.Type().Field(i).IsExported() {
					walk(v.Field(i))
				}
			}
		case reflect.Slice, reflect.Array:
			for i := 0; i < v.Len(); i++ {
				walk(v.Index(i))
			}
		case reflect.Map:
			for _, key := range v.MapKeys() {
				walk(v.MapIndex(key))
			}
		}
	}
	walk(reflect.ValueOf(program))
	return mutated
}

// pathRootIdentifier names the binding a field or element path starts at.
func pathRootIdentifier(expr ast.Expression) (string, bool) {
	for {
		switch e := expr.(type) {
		case *ast.Identifier:
			return e.Value, true
		case *ast.IndexExpression:
			expr = e.Left
		default:
			return "", false
		}
	}
}
