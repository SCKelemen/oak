package codegen

// Static globals (docs/spec/60-effects-allocation.md): top-level bindings
// lower to C file-scope statics with constant initializers — the same
// judgment the type checker enforces (typechecker/globals.go,
// OAK-T0501). Anything non-constant fails closed here; runtime
// initialization belongs at the top of main. Names follow the local
// convention (unmangled), which Oak's no-shadowing rule keeps unambiguous.

import (
	"fmt"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/typechecker"
)

// emitGlobals emits every top-level declaration as a file-scope static.
// Atomic cells are emitted by emitAtomicGlobals and skipped here.
func (cg *CodeGenerator) emitGlobals(program *ast.Program, tc *typechecker.TypeChecker) {
	cg.globalTypes = make(map[string]localContainer)
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

	// Declarator: owned arrays put the length after the name.
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
			} else if length, isFixed := indexExpr.Index.(*ast.IntegerLiteral); isFixed {
				element := cg.parseTypeExpression(indexExpr.Left)
				declarator = fmt.Sprintf("static %s %s[ %d ]", element, name, length.Value)
			}
		}
		if declarator == "" {
			declarator = fmt.Sprintf("static %s %s", cg.parseTypeExpression(decl.Type), name)
		}
	} else {
		// Inferred globals need an annotation for static storage.
		cg.write(fmt.Sprintf("OAK_GLOBAL_NEEDS_TYPE_ANNOTATION(%s);\n", name))
		return
	}

	// Declared placement (docs/spec/65-machine-memory.md): the linker
	// section; the parser admitted only a plain section spelling.
	if decl.Section != "" {
		declarator = fmt.Sprintf("__attribute__((section(\"%s\"))) %s", decl.Section, declarator)
	}

	if decl.Value == nil {
		// Zero initialization: explicit for aggregates, zero for scalars.
		if _, isIndex := decl.Type.(*ast.IndexExpression); isIndex {
			cg.write(declarator + " = {0};\n")
		} else if cg.isAggregateType(decl.Type) {
			cg.write(declarator + " = {0};\n")
		} else {
			cg.write(declarator + " = 0;\n")
		}
		return
	}

	if !typechecker.IsConstantInitializer(decl.Value) {
		// Fail closed: never a hidden global constructor (OAK-T0501 warned).
		cg.write(fmt.Sprintf("OAK_GLOBAL_INITIALIZER_NOT_CONSTANT(%s);\n", name))
		return
	}

	cg.write(declarator + " = ")
	cg.emitFileScopeInitializer(decl.Value, tc)
	cg.output.WriteString(";\n")
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
		cg.output.WriteString("{ ")
		for i, element := range e.Elements {
			if i > 0 {
				cg.output.WriteString(", ")
			}
			cg.emitFileScopeInitializer(element, tc)
		}
		cg.output.WriteString(" }")
	default:
		// Scalar constant expressions share the ordinary fragment emitter,
		// in constant context so arithmetic stays a C constant expression.
		cg.emitConstantExpression(expr, tc)
	}
}
