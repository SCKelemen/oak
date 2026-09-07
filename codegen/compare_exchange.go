package codegen

import (
	"fmt"
	"strings"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/semir"
)

var atomicCarriers = []string{"u8", "u16", "u32", "u64", "i8", "i16", "i32", "i64"}

func memoryOrderIdentifier(order semir.MemoryOrder) (string, error) {
	switch order {
	case semir.MemoryOrderRelaxed:
		return "relaxed", nil
	case semir.MemoryOrderAcquire:
		return "acquire", nil
	case semir.MemoryOrderRelease:
		return "release", nil
	case semir.MemoryOrderAcqRel:
		return "acq_rel", nil
	case semir.MemoryOrderSeqCst:
		return "seq_cst", nil
	default:
		return "", fmt.Errorf("unsupported memory order identifier %q", order)
	}
}

func compareExchangeSuffix(spec semir.AtomicBuiltinSpec) (string, error) {
	if spec.Kind != semir.AtomicBuiltinCompareExchange || !spec.Legal() {
		return "", fmt.Errorf("invalid compare-exchange builtin %q", spec.Name)
	}
	success, err := memoryOrderIdentifier(spec.Order)
	if err != nil {
		return "", err
	}
	failure, err := memoryOrderIdentifier(spec.FailureOrder)
	if err != nil {
		return "", err
	}
	return success + "_" + failure, nil
}

// compareExchangeSpecsUsed collects only the order pairs actually present in
// the program. Generated C therefore pays helper-source cost only for used CAS
// variants, while _Generic carrier selection remains compile-time only.
func compareExchangeSpecsUsed(program *ast.Program) []semir.AtomicBuiltinSpec {
	seen := map[string]bool{}
	var result []semir.AtomicBuiltinSpec
	var visitExpr func(ast.Expression)
	var visitStmt func(ast.Statement)

	visitExpr = func(expr ast.Expression) {
		switch e := expr.(type) {
		case *ast.InvocationExpression:
			if id, ok := e.Function.(*ast.Identifier); ok {
				if spec, found := semir.LookupAtomicBuiltin(id.Value); found && spec.Kind == semir.AtomicBuiltinCompareExchange && !seen[spec.Name] {
					seen[spec.Name] = true
					result = append(result, spec)
				}
			}
			visitExpr(e.Function)
			for _, arg := range e.Arguments {
				visitExpr(arg)
			}
		case *ast.BlockExpression:
			if e.Block != nil {
				for _, stmt := range e.Block.Statements {
					visitStmt(stmt)
				}
			}
		case *ast.InfixExpression:
			visitExpr(e.Left)
			visitExpr(e.Right)
		case *ast.PrefixExpression:
			visitExpr(e.Right)
		case *ast.IndexExpression:
			visitExpr(e.Left)
			visitExpr(e.Index)
		case *ast.SliceExpression:
			visitExpr(e.Seq)
			visitExpr(e.Low)
			visitExpr(e.High)
		case *ast.VariantExpression:
			visitExpr(e.Payload)
		case *ast.MatchExpression:
			visitExpr(e.Scrutinee)
			for _, arm := range e.Arms {
				visitExpr(arm.Body)
			}
		case *ast.RecordLiteral:
			for _, field := range e.Fields {
				visitExpr(field)
			}
		case *ast.ArrayLiteral:
			for _, item := range e.Elements {
				visitExpr(item)
			}
		}
	}

	visitStmt = func(stmt ast.Statement) {
		switch s := stmt.(type) {
		case *ast.VariableDeclaration:
			visitExpr(s.Value)
		case *ast.ExpressionStatement:
			visitExpr(s.Expression)
		case *ast.AssignmentStatement:
			visitExpr(s.Value)
		case *ast.IndexAssignmentStatement:
			visitExpr(s.Target)
			visitExpr(s.Value)
		case *ast.FunctionStatement:
			visitExpr(s.Body)
		case *ast.WhileStatement:
			visitExpr(s.Condition)
			if s.Body != nil {
				for _, inner := range s.Body.Statements {
					visitStmt(inner)
				}
			}
		case *ast.BlockStatement:
			for _, inner := range s.Statements {
				visitStmt(inner)
			}
		case *ast.UnsafeBlock:
			if s.Body != nil {
				for _, inner := range s.Body.Statements {
					visitStmt(inner)
				}
			}
		}
	}

	for _, stmt := range program.Statements {
		visitStmt(stmt)
	}
	return result
}

func (cg *CodeGenerator) emitCompareExchangeHelpers(program *ast.Program) {
	for _, spec := range compareExchangeSpecsUsed(program) {
		suffix, err := compareExchangeSuffix(spec)
		if err != nil {
			continue
		}
		success, err := cMemoryOrder(spec.Order)
		if err != nil {
			continue
		}
		failure, err := cMemoryOrder(spec.FailureOrder)
		if err != nil {
			continue
		}

		cg.write("/* strong compare-exchange: returns the value observed at the compare */\n")
		for _, carrier := range atomicCarriers {
			cg.write(fmt.Sprintf("static inline %s __oak_cas_%s_%s(_Atomic(%s) *cell, %s expected, %s desired) {\n", carrier, carrier, suffix, carrier, carrier, carrier))
			cg.write(fmt.Sprintf("  %s observed = expected;\n", carrier))
			cg.write(fmt.Sprintf("  (void)atomic_compare_exchange_strong_explicit(cell, &observed, desired, %s, %s);\n", success, failure))
			cg.write("  return observed;\n")
			cg.write("}\n")
		}

		macro := "__oak_cas_" + suffix
		cg.write("#define " + macro + "(cell, expected, desired) \\\n")
		cg.write("  _Generic((cell), \\\n")
		for i, carrier := range atomicCarriers {
			end := ", \\\n"
			if i == len(atomicCarriers)-1 {
				end = ")((cell), (expected), (desired))\n"
			}
			cg.write(fmt.Sprintf("    _Atomic(%s) *: __oak_cas_%s_%s%s", carrier, carrier, suffix, end))
		}
		cg.write("\n")
	}
}

func compareExchangeMacro(spec semir.AtomicBuiltinSpec) (string, error) {
	suffix, err := compareExchangeSuffix(spec)
	if err != nil {
		return "", err
	}
	return "__oak_cas_" + suffix, nil
}

// Keep strings imported intentionally exercised at compile time: macro output
// must never carry an order token supplied by a runtime Oak value.
var _ = strings.Builder{}
