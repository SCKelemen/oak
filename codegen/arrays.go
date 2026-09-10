package codegen

import (
	"fmt"
	"strings"

	"github.com/SCKelemen/oak/ast"
)

// Owned arrays as C values (docs/spec/90-backend.md section 10).
//
// An owned array [N]T is represented as a struct carrying the array,
// typedef struct oak_arr_T_N { T v[ N ]; } oak_arr_T_N;, so that C's own
// struct semantics give the value semantics the language specifies: a
// parameter is a copy, a return is a copy, whole-array assignment and
// record-field initialization from a binding are plain assignments. The
// wrapper has exactly the size and alignment of the raw array (no padding
// can follow an array whose size is a multiple of its alignment), so record
// layouts are unchanged; every element access spells .v before the index
// and keeps its bounds check.

// arrayWrapperName mangles an element's C spelling and a length into the
// wrapper typedef name. Element spellings are not always identifier
// fragments (_Atomic u32, void *, const char *, a nested oak_arr_u8_16), so
// the mangling maps * to ptr and every other non-identifier character to an
// underscore, collapsing and trimming runs.
func arrayWrapperName(element string, length int64) string {
	var mangled strings.Builder
	pendingUnderscore := false
	for _, r := range element {
		isIdent := r == '_' || (r >= '0' && r <= '9') || (r >= 'a' && r <= 'z') || (r >= 'A' && r <= 'Z')
		switch {
		case r == '*':
			if mangled.Len() > 0 {
				mangled.WriteByte('_')
			}
			mangled.WriteString("ptr")
			pendingUnderscore = false
		case isIdent && r != '_':
			if pendingUnderscore && mangled.Len() > 0 {
				mangled.WriteByte('_')
			}
			mangled.WriteRune(r)
			pendingUnderscore = false
		default:
			pendingUnderscore = true
		}
	}
	return fmt.Sprintf("oak_arr_%s_%d", mangled.String(), length)
}

// arrayTypeName returns the wrapper typedef name for [length]element,
// emitting the typedef at the current output position the first time it is
// requested. Type positions are pre-walked (preEmitContainerTypes) and record
// and union emitters resolve their member types before opening the struct,
// so the first request always lands at file scope; a request that would
// land inside a function body fails closed with a marker instead of
// emitting a typedef where C forbids one.
func (cg *CodeGenerator) arrayTypeName(element string, length int64) string {
	name := arrayWrapperName(element, length)
	if cg.types[name] {
		return name
	}
	if cg.emittingBodies {
		return fmt.Sprintf("OAK_UNSUPPORTED_ARRAY_TYPE_POSITION(%s)", name)
	}
	cg.types[name] = true
	cg.write(fmt.Sprintf("typedef struct %s { %s v[ %d ]; } %s;\n\n", name, element, length, name))
	return name
}

// walkTypePositions visits every type expression written in the program
// outside type declarations: parameter, receiver, and return types, local
// and global declaration types, and the type annotations of array literals
// wherever they appear in expressions. Type declarations (records, tagged
// unions) resolve their own member types when they are emitted, in
// dependency order (codegen/mono.go).
func walkTypePositions(program *ast.Program, visit func(ast.Expression)) {
	var walkStmt func(stmt ast.Statement)
	var walkExpr func(expr ast.Expression)
	walkBlock := func(block *ast.BlockStatement) {
		if block == nil {
			return
		}
		for _, inner := range block.Statements {
			walkStmt(inner)
		}
	}
	walkExpr = func(expr ast.Expression) {
		switch e := expr.(type) {
		case nil:
		case *ast.ArrayLiteral:
			if e.Type != nil {
				visit(e.Type)
			}
			for _, element := range e.Elements {
				walkExpr(element)
			}
		case *ast.RecordLiteral:
			for _, field := range e.FieldOrder {
				walkExpr(field.Value)
			}
		case *ast.PrefixExpression:
			walkExpr(e.Right)
		case *ast.InfixExpression:
			walkExpr(e.Left)
			walkExpr(e.Right)
		case *ast.IndexExpression:
			walkExpr(e.Left)
			walkExpr(e.Index)
		case *ast.SliceExpression:
			walkExpr(e.Seq)
			walkExpr(e.Low)
			walkExpr(e.High)
		case *ast.InvocationExpression:
			walkExpr(e.Function)
			for _, argument := range e.Arguments {
				walkExpr(argument)
			}
		case *ast.BlockExpression:
			walkBlock(e.Block)
		case *ast.FunctionLiteral:
			walkBlock(e.Body)
		case *ast.MatchExpression:
			walkExpr(e.Scrutinee)
			for _, arm := range e.Arms {
				walkExpr(arm.Body)
			}
		case *ast.VariantExpression:
			walkExpr(e.Payload)
		}
	}
	walkStmt = func(stmt ast.Statement) {
		switch s := stmt.(type) {
		case nil:
		case *ast.VariableDeclaration:
			if s.Type != nil {
				visit(s.Type)
			}
			walkExpr(s.Value)
		case *ast.ExpressionStatement:
			walkExpr(s.Expression)
		case *ast.AssignmentStatement:
			walkExpr(s.Value)
		case *ast.IndexAssignmentStatement:
			walkExpr(s.Target)
			walkExpr(s.Value)
		case *ast.FunctionStatement:
			if s.Receiver != nil && s.Receiver.Type != nil {
				visit(s.Receiver.Type)
			}
			for _, param := range s.Parameters {
				if param.Type != nil && !param.Variadic {
					visit(param.Type)
				}
			}
			if s.ReturnType != nil {
				visit(s.ReturnType)
			}
			walkExpr(s.Body)
		case *ast.WhileStatement:
			walkExpr(s.Condition)
			walkBlock(s.Body)
		case *ast.IfStatement:
			walkExpr(s.Condition)
			walkBlock(s.Consequence)
			walkStmt(s.Alternative)
		case *ast.BlockStatement:
			walkBlock(s)
		case *ast.UnsafeBlock:
			walkBlock(s.Body)
		}
	}
	for _, stmt := range program.Statements {
		walkStmt(stmt)
	}
}

// zeroArrayInitializer is the zero initializer of an owned-array wrapper:
// {0} zeroes the first element and, by C's rule, the rest; a zero-length
// array has no first element, so its wrapper takes the empty braces.
func zeroArrayInitializer(length int64) string {
	if length == 0 {
		return " = { { } }"
	}
	return " = {0}"
}
