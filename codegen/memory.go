package codegen

import (
	"fmt"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/semir"
	"github.com/SCKelemen/oak/typechecker"
)

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

func atomicCType(carrier string) (string, error) {
	if !semir.AtomicCarrierAllowed(carrier) {
		return "", fmt.Errorf("unsupported atomic carrier %q", carrier)
	}
	return "_Atomic(" + carrier + ")", nil
}

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

// atomicPathShape mirrors the checker's atomicCellPath: identifier-rooted
// access paths only. Lowered element accesses arrive as core_index calls,
// which emitLvaluePath re-emits as checked lvalue accesses.
func atomicPathShape(expr ast.Expression) bool {
	switch e := expr.(type) {
	case *ast.Identifier:
		return true
	case *ast.IndexExpression:
		return atomicPathShape(e.Left)
	case *ast.InvocationExpression:
		ident, isIdent := e.Function.(*ast.Identifier)
		return isIdent && ident.Value == "core_index" && len(e.Arguments) == 2 && atomicPathShape(e.Arguments[0])
	default:
		return false
	}
}

func atomicTypeC(expr ast.Expression) (string, bool) {
	carrier, ok := atomicTypeCarrier(expr)
	if !ok {
		return "", false
	}
	cType, err := atomicCType(carrier)
	return cType, err == nil
}

func programUsesAtomics(program *ast.Program) bool {
	var exprUses func(ast.Expression) bool
	var stmtUses func(ast.Statement) bool

	exprUses = func(expr ast.Expression) bool {
		switch e := expr.(type) {
		case *ast.InvocationExpression:
			if id, ok := e.Function.(*ast.Identifier); ok {
				if _, atomic := semir.LookupAtomicBuiltin(id.Value); atomic {
					return true
				}
			}
			if exprUses(e.Function) {
				return true
			}
			for _, arg := range e.Arguments {
				if exprUses(arg) {
					return true
				}
			}
		case *ast.BlockExpression:
			if e.Block != nil {
				for _, stmt := range e.Block.Statements {
					if stmtUses(stmt) {
						return true
					}
				}
			}
		case *ast.InfixExpression:
			return exprUses(e.Left) || exprUses(e.Right)
		case *ast.PrefixExpression:
			return exprUses(e.Right)
		case *ast.IndexExpression:
			if _, atomic := atomicTypeC(e); atomic {
				return true
			}
			return exprUses(e.Left) || exprUses(e.Index)
		case *ast.SliceExpression:
			return exprUses(e.Seq) || exprUses(e.Low) || exprUses(e.High)
		case *ast.VariantExpression:
			return exprUses(e.Payload)
		case *ast.MatchExpression:
			if exprUses(e.Scrutinee) {
				return true
			}
			for _, arm := range e.Arms {
				if exprUses(arm.Body) {
					return true
				}
			}
		case *ast.RecordLiteral:
			for _, field := range e.Fields {
				if exprUses(field) {
					return true
				}
			}
		case *ast.ArrayLiteral:
			for _, element := range e.Elements {
				if exprUses(element) {
					return true
				}
			}
		}
		return false
	}

	stmtUses = func(stmt ast.Statement) bool {
		switch s := stmt.(type) {
		case *ast.VariableDeclaration:
			if _, atomic := atomicTypeC(s.Type); atomic {
				return true
			}
			return exprUses(s.Value)
		case *ast.ExpressionStatement:
			return exprUses(s.Expression)
		case *ast.AssignmentStatement:
			return exprUses(s.Value)
		case *ast.IndexAssignmentStatement:
			return exprUses(s.Target) || exprUses(s.Value)
		case *ast.FunctionStatement:
			return exprUses(s.Body)
		case *ast.WhileStatement:
			if exprUses(s.Condition) {
				return true
			}
			if s.Body != nil {
				for _, inner := range s.Body.Statements {
					if stmtUses(inner) {
						return true
					}
				}
			}
		case *ast.BlockStatement:
			for _, inner := range s.Statements {
				if stmtUses(inner) {
					return true
				}
			}
		case *ast.UnsafeBlock:
			if s.Body != nil {
				for _, inner := range s.Body.Statements {
					if stmtUses(inner) {
						return true
					}
				}
			}
		}
		return false
	}

	for _, stmt := range program.Statements {
		if stmtUses(stmt) {
			return true
		}
	}
	return false
}

// emitAtomicGlobals emits the C11 dependency only for programs that use
// atomics, package-scope inline cells, and any used CAS helper family.
func (cg *CodeGenerator) emitAtomicGlobals(program *ast.Program) {
	if !programUsesAtomics(program) {
		return
	}
	cg.write("#include <stdatomic.h>\n\n")
	cg.atomicsIncluded = true

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
		cg.noteAtomicCarrier(decl.Type)
		if !emitted {
			cg.write("/* package-scope atomic cells: inline, zero initialized */\n")
			emitted = true
		}
		if decl.Value != nil {
			cg.write("OAK_ATOMIC_INITIALIZER_MUST_BE_ZERO_INIT;\n")
			continue
		}
		cg.write(fmt.Sprintf("static %s %s = 0;\n", cType, cIdent(decl.Name.Value)))
	}
	if emitted {
		cg.write("\n")
	}
	cg.emitCompareExchangeHelpers(program)
}

// emitAtomicInvocation emits each source builtin directly as a C11 atomic
// primitive. Order data is compile-time semantic data. Compare-exchange uses a
// C11 _Generic-selected static inline helper so it can return the observed
// value without a mutable Oak out-parameter or runtime order dispatch.
func (cg *CodeGenerator) emitAtomicInvocation(call *ast.InvocationExpression, tc *typechecker.TypeChecker) bool {
	ident, ok := call.Function.(*ast.Identifier)
	if !ok {
		return false
	}
	spec, ok := semir.LookupAtomicBuiltin(ident.Value)
	if !ok {
		return false
	}
	if len(call.Arguments) != int(spec.Arity) || !spec.Legal() {
		cg.output.WriteString("OAK_INVALID_ATOMIC_OPERATION")
		return true
	}

	if spec.Kind == semir.AtomicBuiltinFence {
		order, err := cMemoryOrder(spec.Order)
		if err != nil {
			cg.output.WriteString("OAK_INVALID_ATOMIC_ORDER")
			return true
		}
		cg.output.WriteString("atomic_thread_fence(")
		cg.output.WriteString(order)
		cg.output.WriteString(")")
		return true
	}

	// The cell argument is a storage path: a named cell, a record field
	// (nodes[i].next), or an element of an atomic array — emitted in
	// lvalue position with checked indices, then addressed.
	cellPath := call.Arguments[0]
	if !atomicPathShape(cellPath) {
		cg.output.WriteString("OAK_ATOMIC_CELL_MUST_BE_NAMED")
		return true
	}
	emitAddress := func() {
		cg.output.WriteString("&(")
		cg.emitLvaluePath(cellPath, tc)
		cg.output.WriteString(")")
	}

	if spec.Kind == semir.AtomicBuiltinCompareExchange {
		macro, err := compareExchangeMacro(spec)
		if err != nil {
			cg.output.WriteString("OAK_INVALID_COMPARE_EXCHANGE")
			return true
		}
		cg.output.WriteString(macro)
		cg.output.WriteString("(")
		emitAddress()
		cg.output.WriteString(", ")
		cg.emitExpressionFragment(call.Arguments[1], tc)
		cg.output.WriteString(", ")
		cg.emitExpressionFragment(call.Arguments[2], tc)
		cg.output.WriteString(")")
		return true
	}

	order, err := cMemoryOrder(spec.Order)
	if err != nil {
		cg.output.WriteString("OAK_INVALID_ATOMIC_ORDER")
		return true
	}
	switch spec.Kind {
	case semir.AtomicBuiltinLoad:
		cg.output.WriteString("atomic_load_explicit(")
		emitAddress()
		cg.output.WriteString(", ")
		cg.output.WriteString(order)
		cg.output.WriteString(")")
	case semir.AtomicBuiltinStore:
		cg.output.WriteString("atomic_store_explicit(")
		emitAddress()
		cg.output.WriteString(", ")
		cg.emitExpressionFragment(call.Arguments[1], tc)
		cg.output.WriteString(", ")
		cg.output.WriteString(order)
		cg.output.WriteString(")")
	case semir.AtomicBuiltinFetchAdd:
		cg.output.WriteString("atomic_fetch_add_explicit(")
		emitAddress()
		cg.output.WriteString(", ")
		cg.emitExpressionFragment(call.Arguments[1], tc)
		cg.output.WriteString(", ")
		cg.output.WriteString(order)
		cg.output.WriteString(")")
	case semir.AtomicBuiltinExchange:
		cg.output.WriteString("atomic_exchange_explicit(")
		emitAddress()
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

func atomicCompareExchangeC(cellType, address, expected, desired string, success, failure semir.MemoryOrder) (string, error) {
	if !semir.AtomicCarrierAllowed(cellType) || !semir.LegalCompareExchangeOrders(success, failure) {
		return "", fmt.Errorf("invalid compare-exchange lowering for %s success=%s failure=%s", cellType, success, failure)
	}
	spec := semir.AtomicBuiltinSpec{Kind: semir.AtomicBuiltinCompareExchange, Operation: semir.AtomicCompareExchange, Order: success, FailureOrder: failure, Arity: 3}
	macro, err := compareExchangeMacro(spec)
	if err != nil {
		return "", err
	}
	return fmt.Sprintf("%s(%s, %s, %s)", macro, address, expected, desired), nil
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

// noteAtomicCarrier records the carrier of one Atomic[T] type expression the
// program declares storage for; emitAtomicAdmission asserts each recorded
// carrier is lock-free on the compiling target.
func (cg *CodeGenerator) noteAtomicCarrier(typeExpr ast.Expression) {
	carrier, ok := atomicTypeCarrier(typeExpr)
	if !ok {
		return
	}
	if cg.atomicCarriers == nil {
		cg.atomicCarriers = make(map[string]bool)
	}
	cg.atomicCarriers[carrier] = true
}

// lockFreeConditionC is the C integer constant expression that holds when
// every C11 atomic of the carrier's width is always lock-free on the
// compiling target. The width, not the C type name, is the contract: a
// 4-byte carrier is `int` on every supported ABI and also `long` on ILP32,
// so both macros are consulted where the width matches, and skipped where
// it does not. The value 2 is C11's "always lock-free"; 1 ("sometimes")
// and 0 both mean a libatomic fallback that may take a lock.
func lockFreeConditionC(carrier string) (string, error) {
	switch carrier {
	case "u8", "i8":
		return "ATOMIC_CHAR_LOCK_FREE == 2", nil
	case "u16", "i16":
		return "ATOMIC_SHORT_LOCK_FREE == 2", nil
	case "u32", "i32":
		return "(sizeof(int) != 4 || ATOMIC_INT_LOCK_FREE == 2) && (sizeof(long) != 4 || ATOMIC_LONG_LOCK_FREE == 2)", nil
	case "u64", "i64":
		return "(sizeof(long) != 8 || ATOMIC_LONG_LOCK_FREE == 2) && (sizeof(long long) != 8 || ATOMIC_LLONG_LOCK_FREE == 2)", nil
	}
	return "", fmt.Errorf("unsupported atomic carrier %q", carrier)
}

// emitAtomicAdmission emits the lock-free admission block
// (docs/spec/65-machine-memory.md §6): one C99 static assertion per atomic
// carrier the program declares, failing the C build on a target where that
// carrier's C11 atomics fall back to a locked libatomic implementation — a
// hidden lock is a hidden runtime, and on a Cortex-M0 it is also the
// difference between an ISR-safe counter and a deadlock. A build that has
// audited and accepted the fallback defines OAK_ATOMIC_ACCEPT_LOCKED.
func (cg *CodeGenerator) emitAtomicAdmission() {
	if !cg.atomicsIncluded || len(cg.atomicCarriers) == 0 {
		return
	}
	carriers := make([]string, 0, len(cg.atomicCarriers))
	for _, carrier := range atomicCarriers {
		if cg.atomicCarriers[carrier] {
			carriers = append(carriers, carrier)
		}
	}
	cg.write("\n/* lock-free admission (docs/spec/65-machine-memory.md section 6): every\n")
	cg.write("   atomic carrier this program declares must be always lock-free on the\n")
	if cg.strictAdmission {
		cg.write("   target; a libatomic fallback would be a hidden lock. Strict profile:\n")
		cg.write("   no opt-out (docs/spec/85-discipline.md section 7). */\n")
	} else {
		cg.write("   target; a libatomic fallback would be a hidden lock. Define\n")
		cg.write("   OAK_ATOMIC_ACCEPT_LOCKED to accept one knowingly. */\n")
		cg.write("#if !defined(OAK_ATOMIC_ACCEPT_LOCKED)\n")
	}
	for _, carrier := range carriers {
		condition, err := lockFreeConditionC(carrier)
		if err != nil {
			continue
		}
		cg.write(fmt.Sprintf("typedef char oak_atomic_lock_free_%s[ (%s) ? 1 : -1 ];\n", carrier, condition))
	}
	if !cg.strictAdmission {
		cg.write("#endif\n")
	}
}
