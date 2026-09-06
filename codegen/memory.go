package codegen

import (
	"fmt"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/semir"
	"github.com/SCKelemen/oak/typechecker"
)

// cMemoryOrder is the checked refinement from Oak's semantic memory orders to
// C11. There is deliberately no default: a new language order must teach the
// backend how to preserve it before code generation can succeed.
func cMemoryOrder(order semir.MemoryOrder) (string, error) {
	switch order {
	case semir.MemoryOrderRelaxed:
		return "memory_order_relaxed", nil
	case semir.MemoryOrderAcquire:
		return "memory_order_acquire", nil
	case semir.MemoryOrderRelease:
		return "memory_order_release", nil
	case semir.MemoryOrderAcqRel:
		return "memory_order_acq_rel", nil
	case semir.MemoryOrderSeqCst:
		return "memory_order_seq_cst", nil
	default:
		return "", fmt.Errorf("unsupported Oak memory order %q", order)
	}
}

// atomicCType lowers an already validated fixed-width carrier to exact C11
// atomic storage. It does not use implementation-sized convenience typedefs.
func atomicCType(carrier string) (string, error) {
	if !semir.AtomicCarrierAllowed(carrier) {
		return "", fmt.Errorf("unsupported atomic carrier %q", carrier)
	}
	return "_Atomic(" + carrier + ")", nil
}

// atomicTypeCarrier recognizes the parser's Atomic[T] IndexExpression and
// returns the exact fixed-width carrier spelling. Invalid forms fail closed.
func atomicTypeCarrier(expr ast.Expression) (string, bool) {
	index, ok := expr.(*ast.IndexExpression)
	if !ok || index == nil {
		return "", false
	}
	base, ok := index.Left.(*ast.Identifier)
	if !ok || base.Value != "Atomic" {
		return "", false
	}
	carrier, ok := index.Index.(*ast.Identifier)
	if !ok || !semir.AtomicCarrierAllowed(carrier.Value) {
		return "", false
	}
	return carrier.Value, true
}

func atomicTypeC(expr ast.Expression) (string, bool) {
	carrier, ok := atomicTypeCarrier(expr)
	if !ok {
		return "", false
	}
	cType, err := atomicCType(carrier)
	return cType, err == nil
}

// emitAtomicGlobals emits package-scope Atomic[T] cells as zero-initialized
// static-duration C11 atomic storage. They have no wrapper object and no heap
// allocation. Non-atomic globals remain outside this v1 slice.
func (cg *CodeGenerator) emitAtomicGlobals(program *ast.Program) {
	emitted := false
	for _, stmt := range program.Statements {
		decl, ok := stmt.(*ast.VariableDeclaration)
		if !ok || decl.Type == nil || decl.Name == nil {
			continue
		}
		cType, atomic := atomicTypeC(decl.Type)
		if !atomic {
			continue
		}
		if !emitted {
			cg.write("/* package-scope atomic cells: inline, zero initialized */\n")
			emitted = true
		}
		if decl.Value != nil {
			cg.write("OAK_ATOMIC_INITIALIZER_MUST_BE_ZERO_INIT;\n")
			continue
		}
		cg.write(fmt.Sprintf("static %s %s = 0;\n", cType, decl.Name.Value))
	}
	if emitted {
		cg.write("\n")
	}
}

// emitAtomicInvocation emits one source builtin directly as one C11 atomic
// primitive. The order is compile-time semantic data: there is no runtime
// order switch, wrapper allocation, or helper call in the generated hot path.
func (cg *CodeGenerator) emitAtomicInvocation(call *ast.InvocationExpression, tc *typechecker.TypeChecker) bool {
	ident, ok := call.Function.(*ast.Identifier)
	if !ok {
		return false
	}
	spec, ok := semir.LookupAtomicBuiltin(ident.Value)
	if !ok {
		return false
	}
	if len(call.Arguments) != int(spec.Arity) || !semir.LegalAtomicOrder(spec.Operation, spec.Order) {
		cg.output.WriteString("OAK_INVALID_ATOMIC_OPERATION")
		return true
	}
	order, err := cMemoryOrder(spec.Order)
	if err != nil {
		cg.output.WriteString("OAK_INVALID_ATOMIC_ORDER")
		return true
	}

	if spec.Kind == semir.AtomicBuiltinFence {
		cg.output.WriteString("atomic_thread_fence(")
		cg.output.WriteString(order)
		cg.output.WriteString(")")
		return true
	}

	cell, isCell := call.Arguments[0].(*ast.Identifier)
	if !isCell || cell == nil {
		cg.output.WriteString("OAK_ATOMIC_CELL_MUST_BE_NAMED")
		return true
	}
	address := "&(" + cell.Value + ")"

	switch spec.Kind {
	case semir.AtomicBuiltinLoad:
		cg.output.WriteString("atomic_load_explicit(")
		cg.output.WriteString(address)
		cg.output.WriteString(", ")
		cg.output.WriteString(order)
		cg.output.WriteString(")")
	case semir.AtomicBuiltinStore:
		cg.output.WriteString("atomic_store_explicit(")
		cg.output.WriteString(address)
		cg.output.WriteString(", ")
		cg.emitExpressionFragment(call.Arguments[1], tc)
		cg.output.WriteString(", ")
		cg.output.WriteString(order)
		cg.output.WriteString(")")
	case semir.AtomicBuiltinFetchAdd:
		cg.output.WriteString("atomic_fetch_add_explicit(")
		cg.output.WriteString(address)
		cg.output.WriteString(", ")
		cg.emitExpressionFragment(call.Arguments[1], tc)
		cg.output.WriteString(", ")
		cg.output.WriteString(order)
		cg.output.WriteString(")")
	default:
		cg.output.WriteString("OAK_INVALID_ATOMIC_BUILTIN")
	}
	return true
}

// The string helpers below are retained for direct backend unit tests and for
// future Semantic-IR-only compilation paths.
func atomicLoadC(address string, order semir.MemoryOrder) (string, error) {
	if !semir.LegalAtomicOrder(semir.AtomicLoad, order) {
		return "", fmt.Errorf("illegal atomic load order %q", order)
	}
	cOrder, err := cMemoryOrder(order)
	if err != nil {
		return "", err
	}
	return fmt.Sprintf("atomic_load_explicit(%s, %s)", address, cOrder), nil
}

func atomicStoreC(address, value string, order semir.MemoryOrder) (string, error) {
	if !semir.LegalAtomicOrder(semir.AtomicStore, order) {
		return "", fmt.Errorf("illegal atomic store order %q", order)
	}
	cOrder, err := cMemoryOrder(order)
	if err != nil {
		return "", err
	}
	return fmt.Sprintf("atomic_store_explicit(%s, %s, %s)", address, value, cOrder), nil
}

func atomicExchangeC(address, value string, order semir.MemoryOrder) (string, error) {
	if !semir.LegalAtomicOrder(semir.AtomicRMW, order) {
		return "", fmt.Errorf("illegal atomic exchange order %q", order)
	}
	cOrder, err := cMemoryOrder(order)
	if err != nil {
		return "", err
	}
	return fmt.Sprintf("atomic_exchange_explicit(%s, %s, %s)", address, value, cOrder), nil
}

func atomicFetchAddC(address, value string, order semir.MemoryOrder) (string, error) {
	if !semir.LegalAtomicOrder(semir.AtomicRMW, order) {
		return "", fmt.Errorf("illegal atomic fetch-add order %q", order)
	}
	cOrder, err := cMemoryOrder(order)
	if err != nil {
		return "", err
	}
	return fmt.Sprintf("atomic_fetch_add_explicit(%s, %s, %s)", address, value, cOrder), nil
}

func atomicFenceC(order semir.MemoryOrder) (string, error) {
	if !semir.LegalAtomicOrder(semir.AtomicFence, order) {
		return "", fmt.Errorf("illegal atomic fence order %q", order)
	}
	cOrder, err := cMemoryOrder(order)
	if err != nil {
		return "", err
	}
	return fmt.Sprintf("atomic_thread_fence(%s)", cOrder), nil
}

func volatileReadC(carrier, address string) (string, error) {
	if !semir.AtomicCarrierAllowed(carrier) {
		return "", fmt.Errorf("unsupported volatile carrier %q", carrier)
	}
	return fmt.Sprintf("(*(volatile %s *)(%s))", carrier, address), nil
}

func volatileWriteC(carrier, address, value string) (string, error) {
	if !semir.AtomicCarrierAllowed(carrier) {
		return "", fmt.Errorf("unsupported volatile carrier %q", carrier)
	}
	return fmt.Sprintf("(*(volatile %s *)(%s) = (%s))", carrier, address, value), nil
}
