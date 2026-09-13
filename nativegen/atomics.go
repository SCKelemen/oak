package nativegen

import (
	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/semir"
)

// The atomics of the native subset (docs/spec/65-machine-memory.md; the OS
// pilot's N7). A cell is reached by storage path through a writable span
// — an element of `[*]Atomic[T]`, or an atomic field of a `[*]Record`
// element — and its address is computed into a register the checker
// knows as an element region (`add xE, xB, wI, uxtw #s`, then `add xC,
// xE, #off`); the operation is then one instruction on that base, or the
// exclusive loop for a read-modify-write:
//
//	load   relaxed → ldr      acquire, seq-cst → ldar
//	store  relaxed → str      release, seq-cst → stlr
//	fence  acquire → dmb ishld   release, acq-rel, seq-cst → dmb ish
//	rmw    ldxr/ldaxr (acquire when the order acquires) … stxr/stlxr
//	       (release when the order releases), retried on the status
//
// The b/h forms serve the one- and two-byte carriers. A stronger form than
// the order asks for is never chosen except for compare-exchange, whose
// one load serves both the success and the failure order and takes the
// acquire form when either acquires (a refinement of the weaker order).
// Local cells and the rv64 lane are left to the C backend.

// atomicCarrier reads `Atomic[T]` as its carrier scalar.
func atomicCarrier(expr ast.Expression) (scalar, bool) {
	index, ok := expr.(*ast.IndexExpression)
	if !ok || index.Dot {
		return scalar{}, false
	}
	head, isIdent := index.Left.(*ast.Identifier)
	if !isIdent || head.Value != "Atomic" {
		return scalar{}, false
	}
	carrier, ok := scalarOf(index.Index)
	if !ok || carrier.isBool || carrier.isFloat {
		return scalar{}, false
	}
	return carrier, true
}

// atomicCellType is the carrier of the cell a storage path names, resolved
// without emitting code (typeOf runs before lowering).
func (g *generator) atomicCellType(path ast.Expression) (scalar, error) {
	e, isIndex := path.(*ast.IndexExpression)
	if !isIndex {
		return scalar{}, unsupported("the atomic cell %s (a local cell is outside the native subset; atomics reach cells through a span)", path.String())
	}
	if !e.Dot {
		if ident, isIdent := e.Left.(*ast.Identifier); isIdent {
			if sp, isSpan := g.spans[ident.Value]; isSpan && sp.atomic {
				return sp.elem, nil
			}
		}
		return scalar{}, unsupported("the atomic cell %s (cells are reached through a span of cells or a span element's field)", path.String())
	}
	layout, err := g.recordLayoutOfExpr(e.Left)
	if err != nil {
		return scalar{}, err
	}
	name, isName := e.Index.(*ast.Identifier)
	if !isName {
		return scalar{}, unsupported("the atomic cell %s", path.String())
	}
	field, has := layout.fields[name.Value]
	if !has || !field.atomic {
		return scalar{}, unsupported("the field %s of %s is not an atomic cell", name.Value, layout.name)
	}
	return field.typ, nil
}

// atomicAddress computes a cell's address into an x register: the span
// element's, or the element's plus the field offset. The returned temps
// are released by the caller after the operation.
func (g *generator) atomicAddress(path ast.Expression) (addr int, elem scalar, temps []int, err error) {
	e, isIndex := path.(*ast.IndexExpression)
	if !isIndex {
		return 0, scalar{}, nil, unsupported("the atomic cell %s (a local cell is outside the native subset; atomics reach cells through a span)", path.String())
	}
	if !e.Dot {
		ident, isIdent := e.Left.(*ast.Identifier)
		sp, isSpan := span{}, false
		if isIdent {
			sp, isSpan = g.spans[ident.Value]
		}
		if !isSpan || !sp.atomic {
			return 0, scalar{}, nil, unsupported("the atomic cell %s (cells are reached through a span of cells or a span element's field)", path.String())
		}
		if !sp.writable {
			return 0, scalar{}, nil, unsupported("an atomic through the view %s", ident.Value)
		}
		r, err := g.guardedIndex(sp, e.Index)
		if err != nil {
			return 0, scalar{}, nil, err
		}
		addr, err = g.alloc(scalars["u64"])
		if err != nil {
			return 0, scalar{}, nil, err
		}
		g.emit("add", xr(addr), xr(sp.baseReg), asm.Extended{Reg: wr(r), Kind: "uxtw", Amount: int64(log2Bytes(sp.elem.bits / 8))})
		g.release(r)
		return addr, sp.elem, []int{addr}, nil
	}
	elem, err = g.atomicCellType(path)
	if err != nil {
		return 0, scalar{}, nil, err
	}
	p, err := g.placeOf(path)
	if err != nil {
		return 0, scalar{}, nil, err
	}
	if p.sc == nil {
		return 0, scalar{}, nil, unsupported("the atomic cell %s", path.String())
	}
	if !p.sc.inReg {
		return 0, scalar{}, nil, unsupported("the atomic cell %s in the frame (atomics reach cells through a span)", path.String())
	}
	if p.sc.readOnly {
		return 0, scalar{}, nil, unsupported("an atomic through a view element (%s)", path.String())
	}
	addr, err = g.alloc(scalars["u64"])
	if err != nil {
		return 0, scalar{}, nil, err
	}
	g.emit("add", xr(addr), xr(p.sc.reg), imm(p.sc.offset))
	return addr, elem, append(append([]int{}, p.sc.temps...), addr), nil
}

func acquires(order semir.MemoryOrder) bool {
	return order == semir.MemoryOrderAcquire || order == semir.MemoryOrderAcqRel || order == semir.MemoryOrderSeqCst
}

func releases(order semir.MemoryOrder) bool {
	return order == semir.MemoryOrderRelease || order == semir.MemoryOrderAcqRel || order == semir.MemoryOrderSeqCst
}

// widthSuffix is the b/h suffix of the one- and two-byte carriers.
func widthSuffix(elem scalar) string {
	switch elem.bits {
	case 8:
		return "b"
	case 16:
		return "h"
	}
	return ""
}

// atomic lowers one atomic builtin; the result register (the loaded or
// prior value) is returned, or -1 for a store or fence. With discard the
// prior value of a read-modify-write is still produced (the exclusive
// loop needs it) and released by the caller.
func (g *generator) atomic(e *ast.InvocationExpression, spec semir.AtomicBuiltinSpec, discard bool) (int, error) {
	if g.rvLane {
		return -1, unsupported("the atomic %s on the rv64 lane", spec.Name)
	}
	if len(e.Arguments) != int(spec.Arity) {
		return -1, unsupported("the atomic %s with %d arguments", spec.Name, len(e.Arguments))
	}
	if spec.Kind == semir.AtomicBuiltinFence {
		option := "ish"
		if spec.Order == semir.MemoryOrderAcquire {
			option = "ishld"
		}
		g.emit("dmb", asm.Option{Name: option})
		return -1, nil
	}
	addr, elem, temps, err := g.atomicAddress(e.Arguments[0])
	if err != nil {
		return -1, err
	}
	mem := asm.Memory{Base: xr(addr)}
	sfx := widthSuffix(elem)
	switch spec.Kind {
	case semir.AtomicBuiltinLoad:
		dst, err := g.alloc(elem)
		if err != nil {
			return -1, err
		}
		mnemonic := "ldr"
		if acquires(spec.Order) {
			mnemonic = "ldar"
		}
		g.emit(mnemonic+sfx, reg(dst, elem), mem)
		g.releaseTemps(temps)
		return dst, nil
	case semir.AtomicBuiltinStore:
		value, err := g.expr(e.Arguments[1], &elem)
		if err != nil {
			return -1, err
		}
		mnemonic := "str"
		if releases(spec.Order) {
			mnemonic = "stlr"
		}
		g.emit(mnemonic+sfx, reg(value, elem), mem)
		g.release(value)
		g.releaseTemps(temps)
		return -1, nil
	case semir.AtomicBuiltinFetchAdd, semir.AtomicBuiltinExchange:
		value, err := g.expr(e.Arguments[1], &elem)
		if err != nil {
			return -1, err
		}
		prior, err := g.alloc(elem)
		if err != nil {
			return -1, err
		}
		status, err := g.alloc(scalars["u32"])
		if err != nil {
			return -1, err
		}
		next := value
		if spec.Kind == semir.AtomicBuiltinFetchAdd {
			if next, err = g.alloc(elem); err != nil {
				return -1, err
			}
		}
		load, store := "ldxr", "stxr"
		if acquires(spec.Order) {
			load = "ldaxr"
		}
		if releases(spec.Order) {
			store = "stlxr"
		}
		retry := g.newLabel("atomic")
		g.label(retry)
		g.emit(load+sfx, reg(prior, elem), mem)
		if spec.Kind == semir.AtomicBuiltinFetchAdd {
			g.emit("add", reg(next, elem), reg(prior, elem), reg(value, elem))
		}
		g.emit(store+sfx, wr(status), reg(next, elem), mem)
		g.emit("cbnz", wr(status), asm.Symbol{Name: retry})
		g.release(status)
		if next != value {
			g.release(next)
		}
		g.release(value)
		g.releaseTemps(temps)
		return prior, nil
	case semir.AtomicBuiltinCompareExchange:
		expected, err := g.expr(e.Arguments[1], &elem)
		if err != nil {
			return -1, err
		}
		desired, err := g.expr(e.Arguments[2], &elem)
		if err != nil {
			return -1, err
		}
		observed, err := g.alloc(elem)
		if err != nil {
			return -1, err
		}
		status, err := g.alloc(scalars["u32"])
		if err != nil {
			return -1, err
		}
		load, store := "ldxr", "stxr"
		if acquires(spec.Order) || acquires(spec.FailureOrder) {
			load = "ldaxr"
		}
		if releases(spec.Order) {
			store = "stlxr"
		}
		retry, done := g.newLabel("cas"), g.newLabel("cas_done")
		g.label(retry)
		g.emit(load+sfx, reg(observed, elem), mem)
		g.emit("cmp", reg(observed, elem), reg(expected, elem))
		g.branch("ne", done)
		g.emit(store+sfx, wr(status), reg(desired, elem), mem)
		g.emit("cbnz", wr(status), asm.Symbol{Name: retry})
		g.label(done)
		g.release(status)
		g.release(desired)
		g.release(expected)
		g.releaseTemps(temps)
		return observed, nil
	}
	return -1, unsupported("the atomic %s", spec.Name)
}
