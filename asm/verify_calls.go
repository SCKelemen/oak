package asm

// Call summaries and ABI state transitions for the native symbolic executor.
//
// Architecture-specific register preservation, parameter/result placement,
// floating-point and vector calling conventions live here. Certificate and
// semantic decision procedures live elsewhere. This is a verbatim extraction
// of the established verifier call logic; it neither broadens admission nor
// changes the verification policy.

import (
	"fmt"
	"strings"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/typechecker"
)

// summarizeCall takes a call to a program function at the callee's Oak
// body (docs/spec/94-assembler.md §8, call summaries). The arguments are
// the contract registers' terms at the parameters' widths; the callee's
// body lowers to a term over them, with its own calls inlined the same
// way and recursion refused; the result register receives the term in
// the lane's canonical form — on RV64 widened as the psABI does, on
// AArch64 with the bits above the result's width (above the low word for
// a Bool, the C enum) a fresh unknown, since AAPCS64 leaves them
// unspecified; and every caller-saved register and the flags are
// forgotten, as after any call. The caller's verdict is then relative to
// the callee's Oak body, which the callee's own verdict covers, and it
// names the callees taken so. A call the summary cannot take — no callee
// known, a span or record in the signature, a body outside the term
// language — leaves the function trusted with the reason, as before.
// forgetCallerSaved drops the registers a call may clobber: x0–x17, x30
// and the flags, v0–v7 and v16–v31 (the low halves of v8–v15 are
// preserved, kept whole as they were) on AArch64; ra, t0–t6, a0–a7 and
// ft0–ft11, fa0–fa7 (f0–f7, f10–f17, f28–f31) on RV64, where the vector
// file and its configuration are forgotten as the arguments are read.
func (x *pathExecutor) forgetCallerSaved(state *symbolicState) {
	isa, ok := verifierISAFor(x.arch)
	if !ok {
		// No assumptions about the clobber set are valid on an unknown ISA.
		// Public seam checking/verification refuse this architecture first.
		state.regs = nil
		state.bounds = nil
		state.fregs = nil
		state.vregs = nil
		state.rvcfg = nil
		state.flags = nil
		return
	}
	isa.forgetCallerSaved(state)
}

func (x *pathExecutor) summarizeCall(instr Instruction, state *symbolicState) (string, bool) {
	if _, ok := verifierISAFor(x.arch); !ok {
		return fmt.Sprintf("unsupported native verifier architecture %q", x.arch), false
	}
	opaque := "instruction " + instr.Mnemonic
	if x.arch == ArchRV64 {
		opaque = "a call"
	}
	if len(instr.Operands) == 0 || x.fn == nil {
		return opaque, false
	}
	sym, isSym := instr.Operands[0].(Symbol)
	if !isSym {
		return opaque, false
	}
	callee, resolved := ResolveNativeCallee(x.arch, sym.Name, x.fn.Callees)
	if !resolved {
		return opaque, false
	}
	name := callee.Name.Value
	// A unit callee (no result) is summarized for the package state and
	// the span memory it writes.
	unit := unitFunction(callee)
	var resultWidth int
	var resultSigned bool
	// A record or union result of up to two register chunks (x0 and x1,
	// a0 and a1) is summarized chunk by chunk from the callee's aggregate
	// value; its padding bits are fresh unknowns, as the ABI leaves them.
	var aggLeaves []compositeLeaf
	aggChunks := 0
	// A record result beyond two chunks is stored leaf by leaf into the
	// caller's frame at the address x8 held (memResultBase).
	memResult := false
	memResultBase := int64(0)
	// A fixed-vector result comes back whole in the lane's vector result
	// register (v0 on AArch64, v8 on RV64 — the RVV psABI; docs/spec/
	// 94-assembler.md §9, vectors across the call boundary): the callee's
	// lanes packed as the register holds them.
	var vecResult *typechecker.SimdShape
	if shape, isVector := vectorShape(callee.ReturnType); isVector && !unit {
		vecResult = &shape
	}
	// An f32/f64 result comes back in the lane's float result register:
	// the low lane of v0 (AAPCS64), fa0 (LP64D); the callee's body lowers
	// as a float at that width (docs/spec/94-assembler.md §8, floats).
	floatResult := 0
	if !unit && vecResult == nil {
		switch typeText(callee.ReturnType) {
		case "f32":
			floatResult = 32
		case "f64":
			floatResult = 64
		}
	}
	if !unit && vecResult == nil {
		w, signed, ok := contractBits(callee.ReturnType)
		if class, isClass := contractClass(callee.ReturnType); !ok || !isClass || (class == ClassV && floatResult == 0) {
			returned := typeText(callee.ReturnType)
			comp, isComposite := x.fn.Composites[returned]
			if !isComposite || len(comp.Fields) == 0 {
				return fmt.Sprintf("a call to %s returning %s", name, returned), false
			}
			leaves, _, ok := compositeLeaves(x.fn.Composites, returned, "", 0, nil)
			if !ok {
				return fmt.Sprintf("a call to %s returning %s (no layout)", name, returned), false
			}
			if comp.Size > 16 {
				// Returned through memory: the caller passed the address of
				// a frame area in x8 (nativegen: `add x8, sp, #off` before
				// the call), and the callee's leaves land there at their
				// offsets and widths; the caller's later loads read them
				// as frame slots (docs/spec/94-assembler.md §9). RV64
				// passes the area in a0, shifting the arguments, outside
				// the subset; a union's inactive payload bytes are left as
				// they were, which the leaf-wise store cannot express.
				if x.arch == ArchRV64 {
					return fmt.Sprintf("a call to %s returning %s through memory on RV64", name, returned), false
				}
				addr, isFrame := frameAddressOf(state.regs[8])
				if !isFrame {
					return fmt.Sprintf("a call to %s returning %s through an area x8 does not address in the frame", name, returned), false
				}
				for _, leaf := range leaves {
					if len(leaf.guards) > 0 {
						return fmt.Sprintf("a call to %s returning %s holding a union", name, returned), false
					}
				}
				memResultBase, memResult = addr, true
			}
			aggLeaves, aggChunks = leaves, int((comp.Size+7)/8)
		}
		resultWidth, resultSigned = w, signed
	}
	// More parameters than the registers hold are read from the caller's
	// outgoing area below (the shared layout), so their count is no bar.
	lo := newLowering(callee)
	lo.arch = x.arch
	lo.records, lo.adts, lo.constants = x.fn.Records, x.fn.ADTs, x.fn.Constants
	// The span arguments bound to the caller's owned frame arrays, written
	// back after the body (asm/span_args.go).
	var frameBorrows []frameBorrow
	lo.functions = x.fn.Callees
	lo.externs = x.fn.Externs
	lo.declareTables(x.fn.Tables)
	lo.declareGlobalArrays(x.fn.Globals)
	lo.inlining = map[string]bool{name: true}
	lo.externSite = instr.Line // the externs met in the callee are named by this call's line (lowerExternCall)
	// The callee sees the cells as this path holds them — a store on the
	// path, else the entry value — and its writes come back into the path
	// (docs/spec/94-assembler.md §9).
	lo.globals = x.globals
	lo.declareCells()
	seeds := map[string]*term{}
	for cellName, cell := range lo.cells {
		if written, has := state.globals[cellName]; has {
			cell.value = written
		}
		seeds[cellName] = cell.value
	}
	argBase := 0
	if x.arch == ArchRV64 {
		argBase = 10 // a0
	}
	lo.concrete = x.env // a witness run: the callee's leaves are the caller's constants
	lo.writes = cloneWrites(state.writes)
	// The callee's loop events take the indices this call site's events
	// took the first time the site was reached (loopSite): a second path
	// through the same call merges its events with the first's below. A
	// site is one call instruction (x.callAt): keyed by the source line,
	// two calls on one line — `c ? f(…) | g(…)`, `f(…) || g(…)` — shared a
	// site, the second's loops merged into the first's or stood as an
	// unrolled instance, and the machine side's loop count was not the
	// Oak side's (the prover's variable_node, is_float_lean).
	callSite := fmt.Sprintf("call@%d", x.callAt)
	priorSite, siteSeen := x.sites[callSite]
	if siteSeen && !priorSite.diverged(state.path) {
		// The same path reaching the call again (an unrolled counted
		// loop's body): a distinct instance, its events its own.
		siteSeen = false
	}
	if siteSeen {
		lo.loopBase = priorSite.base
	} else {
		lo.loopBase = len(x.loops)
	}
	lo.loopStack = append([]int(nil), x.loopStack...)
	lo.writableSpans = map[string]bool{}
	lo.rootContracts = map[string]spanContract{}
	for _, span := range writableSpanParams(x.fn, x.spans, x.recordSpans) {
		lo.writableSpans[span] = true
		if elem, scalar := x.spans[span]; scalar {
			lo.rootContracts[span] = spanContract{elemWidth: int(elem) * 8}
		}
	}
	// The arguments by the shared layout (asm/abi.go): registers while
	// they fit, then the caller's outgoing area — slots of this path's
	// frame at the call's sp, which the executor holds as the caller
	// stored them.
	args := classifyArguments(callee.Parameters, x.fn.Composites)
	classes := make([]ArgClass, 0, len(args))
	ints := make([]int, 0, len(args)) // the index into places of each integer-class argument
	for _, arg := range args {
		if arg.param.Variadic {
			return fmt.Sprintf("a call to %s: parameter %s is variadic", name, arg.param.Name.Value), false
		}
		if arg.kind == argRecord && arg.comp.HFA {
			return fmt.Sprintf("a call to %s: parameter %s is a record passed in floating-point registers", name, arg.param.Name.Value), false
		}
		if arg.problem != "" {
			return fmt.Sprintf("a call to %s: parameter %s is not a fixed-width integer", name, arg.param.Name.Value), false
		}
		if arg.kind == argVector && x.arch == ArchRV64 {
			ints = append(ints, -1) // RV64: v8–v23 by count, outside the layout
			continue
		}
		ints = append(ints, len(classes))
		classes = append(classes, arg.class)
	}
	places, _ := LayoutArguments(classes, x.fn.PackedStackArgs)
	// Vector arguments travel in the vector file's argument registers, in
	// declaration order: v0–v7 on AArch64, v8–v23 on RV64.
	vecArg0, vecArgs := 0, 8
	if x.arch == ArchRV64 {
		vecArg0, vecArgs = rv64VectorResultRegister, 16
	}
	nextVec := 0
	// word reads word k of an argument: its register, or its bytes in the
	// outgoing area (a span's length is the 4-byte word after its base;
	// a scalar its natural size, zero-extended as the callee's load is).
	word := func(place ArgPlace, k int, size int64) (*term, bool) {
		if !place.OnStack {
			value, has := state.regs[argBase+place.Reg+k]
			return value, has
		}
		if x.arch == ArchRV64 {
			return nil, false
		}
		value, ok := state.loadSlot(-state.disp+place.Offset+int64(k)*8, size)
		if !ok {
			return nil, false
		}
		return zeroExtend(value, 64), true
	}
	// f32/f64 arguments share v0–v7 with the vector arguments on AArch64
	// and travel in fa0–fa7 (f10–f17) on RV64, in declaration order.
	nextFloat := 0
	for i, arg := range args {
		param := arg.param
		if floatWidth, isFloat := map[string]int{"f32": 32, "f64": 64}[typeText(param.Type)]; isFloat {
			var value *term
			var has bool
			if x.arch == ArchRV64 {
				if nextFloat >= 8 {
					return fmt.Sprintf("a call to %s with floating-point arguments beyond the registers", name), false
				}
				value, has = state.read(Register{Class: ClassRV64F, Num: 10 + nextFloat})
				nextFloat++
				if !has {
					return "unbound floating-point register read", false
				}
			} else if place := places[ints[i]]; place.OnStack {
				// Past v0–v7: its bit pattern in the outgoing area.
				value, has = word(place, 0, int64(floatWidth)/8)
				if !has {
					return "unbound stack argument read", false
				}
			} else {
				vec, bound := state.readVec(place.Reg)
				if !bound {
					return "unbound vector register read", false
				}
				value, has = vec.lanesAt(floatWidth)[0], true
			}
			lo.locals[param.Name.Value] = &oakLocal{value: truncate(value, floatWidth), width: floatWidth}
			lo.floats[param.Name.Value] = floatWidth
			continue
		}
		if arg.kind == argVector {
			shape, _ := vectorShape(param.Type)
			var value vecValue
			switch {
			case x.arch == ArchRV64:
				if nextVec >= vecArgs {
					return fmt.Sprintf("a call to %s with vector arguments beyond the registers", name), false
				}
				var has bool
				value, has = state.readVec(vecArg0 + nextVec)
				nextVec++
				if !has {
					return "unbound vector register read", false
				}
			case places[ints[i]].OnStack:
				// Past v0–v7: sixteen bytes in the outgoing area, the two
				// eight-byte words the caller's `str q` left.
				place := places[ints[i]]
				lo64, hasLo := word(place, 0, 8)
				hi64, hasHi := word(place, 1, 8)
				if !hasLo || !hasHi {
					return "unbound stack argument read", false
				}
				value = vecOfLanes([]*term{lo64, hi64}, 64)
			default:
				var has bool
				value, has = state.readVec(places[ints[i]].Reg)
				if !has {
					return "unbound vector register read", false
				}
			}
			lanes := value.lanesAt(laneWidth(shape))[:shape.Lanes]
			lo.locals[param.Name.Value] = &oakLocal{agg: vectorOfLanes(lanes, lo.vectorType(shape))}
			continue
		}
		place := places[ints[i]]
		switch arg.kind {
		case argRecord:
			// A record argument: by value in one or two register chunks,
			// the callee's parameter is the aggregate unpacked from them;
			// by reference beyond 16 bytes, the word holding the caller's
			// own record parameter's address — the callee's leaves are
			// then the caller's leaves by name.
			if !arg.indirect {
				if place.OnStack {
					return fmt.Sprintf("a call to %s: parameter %s is a record passed by value on the stack", name, param.Name.Value), false
				}
				if _, reason, ok := x.bindAggregateArgument(lo, param, arg.comp, argBase+place.Reg, argBase, state, name); !ok {
					return reason, false
				}
				continue
			}
			base, has := word(place, 0, 8)
			if !has {
				return fmt.Sprintf("a call to %s: the record argument %s is not a record parameter of the caller", name, param.Name.Value), false
			}
			if addr, isFrame := frameAddressOf(base); isFrame || func() bool { addr, isFrame = rvFrameAddrOf(base); return isFrame }() {
				// The caller's copy of the record in its frame (the rv64
				// lane copies a by-reference record it passes on, and a
				// record local passed by reference): the callee's parameter
				// is the aggregate read from the frame slots.
				if reason, ok := x.frameRecordArgument(lo, param, arg.comp, addr, state, name); !ok {
					return reason, false
				}
				continue
			}
			owner, offset, isBase := spanBaseOf(base)
			record, isRecord := x.records[owner]
			if !isBase || !isRecord {
				return fmt.Sprintf("a call to %s: the record argument %s is not a record parameter of the caller", name, param.Name.Value), false
			}
			typ, ok := lo.oakTypeOf(param.Type)
			if !ok || typ.kind == oakScalar {
				return fmt.Sprintf("a call to %s: parameter %s has a type without a model", name, param.Name.Value), false
			}
			// The address of the caller's record parameter, or of a field
			// inside it (`state.cv` handed to a callee taking `[8]u32`):
			// the callee's leaves are the caller's leaves at those offsets,
			// by the caller's names — naming them `owner[k]` made the same
			// word two symbols and refuted hash.blake3_chunk_cv where the
			// machine and the C oracle agree (docs/spec/94-assembler.md §9
			// "Call summaries").
			agg, reason, ok := x.aggregateAtOffset(lo, param, typ, record, offset)
			if !ok {
				return fmt.Sprintf("a call to %s: parameter %s: %s", name, param.Name.Value, reason), false
			}
			lo.locals[param.Name.Value] = &oakLocal{agg: agg, param: true}
		case argSpan:
			// A span argument: the {base, len} pair of one of the caller's
			// span parameters, whole — the callee's parameter is an alias
			// of the caller's span and shares its memory (asm/effects.go).
			base, hasBase := word(place, 0, 8)
			length, hasLen := word(place, 1, 4)
			whole := hasBase && hasLen
			var owner string
			if whole {
				var offset int64
				owner, offset, whole = spanBaseOf(base)
				_, isRecord := x.records[owner]
				whole = whole && !isRecord && offset == 0 && x.spans[owner] == arg.elem && (x.isSpanLength(length, owner) || x.isTableLength(length, owner))
			}
			if !whole && hasBase && hasLen {
				// A derived span of one of the caller's spans (`subslice(v,
				// start, n)`): the base is the span's plus scaled index
				// terms, the length any term — the callee's parameter is an
				// alias at that offset with that length
				// (asm/derived_spans.go).
				if root, offset, isDerived := spanAddressOf(base, arg.elem); isDerived && x.spans[root] == arg.elem {
					if _, isRecord := x.records[root]; !isRecord {
						elemType := typeText(param.Type.(*ast.IndexExpression).Left)
						lo.spans[param.Name.Value] = spanContract{elemWidth: int(arg.elem) * 8, signed: strings.HasPrefix(elemType, "i")}
						if lo.spanAlias == nil {
							lo.spanAlias = map[string]string{}
						}
						lo.spanAlias[param.Name.Value] = root
						if lo.spanOffset == nil {
							lo.spanOffset, lo.spanLen = map[string]*term{}, map[string]*term{}
						}
						if offset != nil {
							lo.spanOffset[param.Name.Value] = offset
						}
						lo.spanLen[param.Name.Value] = truncate(length, 32)
						break
					}
				}
			}
			if !whole && hasBase && hasLen {
				// A view or span of an array field of a record span's
				// element (`view(&stages[k].coeffs)`, docs/spec/50-borrowing.md
				// §2): the base is the element's address plus the field's
				// offset, the length the field's constant element count —
				// the callee's parameter is an alias of the field's leaf
				// memory (`stages.coeffs`) at the linear offset k·N.
				if span, index, offset, isElement := x.recordElementOf(base, 0); isElement {
					if recordArg, isRecordSpan := x.recordSpans[span]; isRecordSpan {
						prefix, count, stride, isField := recordArg.arrayFieldAt(offset)
						if !isField || stride != arg.elem || length.kind != termConst || int64(length.value) != count {
							return fmt.Sprintf("a call to %s: the span argument %s borrows %s's element at offset %d, which is not an array field of %d-byte elements passed whole", name, param.Name.Value, span, offset, arg.elem), false
						}
						elemType := typeText(param.Type.(*ast.IndexExpression).Left)
						lo.spans[param.Name.Value] = spanContract{elemWidth: int(arg.elem) * 8, signed: strings.HasPrefix(elemType, "i")}
						if lo.spanAlias == nil {
							lo.spanAlias = map[string]string{}
						}
						lo.spanAlias[param.Name.Value] = span + prefix
						if lo.spanOffset == nil {
							lo.spanOffset, lo.spanLen = map[string]*term{}, map[string]*term{}
						}
						lo.spanOffset[param.Name.Value] = binaryTerm("mul", truncate(index, 32), constTerm(uint64(count), 32))
						lo.spanLen[param.Name.Value] = constTerm(uint64(count), 32)
						break
					}
				}
			}
			if !whole && hasBase && hasLen {
				// A view or subslice of the caller's large owned array,
				// which both sides read as the span named by the local
				// (frameSpanAccess): the callee's parameter is an alias of
				// that span at the byte offset's element with the length
				// term, as a derived span of a parameter is; the callee's
				// reads and writes land in the caller's log.
				if addr, isFrame := frameAddressOf(base); isFrame {
					if fs, off, in := x.spanRegionAt(state, addr); in && fs.elem == arg.elem && off%fs.elem == 0 {
						elemType := typeText(param.Type.(*ast.IndexExpression).Left)
						lo.spans[param.Name.Value] = spanContract{elemWidth: int(arg.elem) * 8, signed: strings.HasPrefix(elemType, "i")}
						if lo.spanAlias == nil {
							lo.spanAlias = map[string]string{}
						}
						lo.spanAlias[param.Name.Value] = fs.name
						if lo.spanOffset == nil {
							lo.spanOffset, lo.spanLen = map[string]*term{}, map[string]*term{}
						}
						if off != 0 {
							lo.spanOffset[param.Name.Value] = constTerm(uint64(off/fs.elem), 32)
						}
						lo.spanLen[param.Name.Value] = truncate(length, 32)
						if isWritableSpan(param.Type) {
							lo.writableSpans[param.Name.Value] = true
						}
						break
					}
				}
			}
			if !whole {
				// A span or view over the caller's owned frame array
				// (`span(&buf)`): the callee's parameter is the array's
				// contents as an aggregate local, written back after the
				// body when the span is writable (asm/span_args.go).
				borrow, reason, ok := x.frameArrayArgument(state, lo, name, param.Name.Value, param.Type, arg.elem, base, length, hasBase && hasLen)
				if !ok {
					return reason, false
				}
				frameBorrows = append(frameBorrows, borrow)
				break
			}
			if lo.spanAlias == nil {
				lo.spanAlias = map[string]string{}
			}
			if recordArg, isRecordSpan := x.recordSpans[owner]; isRecordSpan {
				// A span of records passed on: the callee's parameter is an
				// alias of the caller's, its leaf memories the caller's.
				if lo.recordSpans == nil {
					lo.recordSpans = map[string]recordSpanArg{}
				}
				lo.recordSpans[param.Name.Value] = recordArg
				lo.spanAlias[param.Name.Value] = owner
				break
			}
			elemType := typeText(param.Type.(*ast.IndexExpression).Left)
			lo.spans[param.Name.Value] = spanContract{elemWidth: int(arg.elem) * 8, signed: strings.HasPrefix(elemType, "i")}
			lo.spanAlias[param.Name.Value] = owner
		default:
			w, signed, _ := contractBits(param.Type)
			value, has := word(place, 0, arg.scalarSz)
			if !has {
				return "unbound register read", false
			}
			lo.locals[param.Name.Value] = &oakLocal{value: truncate(value, w), width: w, signed: signed}
		}
	}
	if x.arch == ArchRV64 {
		// Every vector register is caller-saved and the configuration is
		// not preserved (the RVV psABI): the arguments are read, the file
		// is forgotten, and a vector result is written to v8 below.
		state.vregs, state.rvcfg = nil, nil
	}
	body := callee.Body
	if loop, isTail := tailRecursionAsLoop(callee, body); isTail {
		body = loop
	}
	var result *term
	var aggregate *oakValue
	var vecLanes []*term
	applicationArgs, application := lo.callApplicationArguments(callee)
	switch {
	case application && aggLeaves != nil:
		typ, ok := lo.oakTypeOf(callee.ReturnType)
		if !ok || typ.kind == oakScalar {
			return fmt.Sprintf("a call to %s returning %s (no application model)", name, typeText(callee.ReturnType)), false
		}
		aggregate, ok = callApplicationValue(name, typ, applicationArgs)
		if !ok {
			return fmt.Sprintf("a call to %s returning %s (incomplete application model)", name, typeText(callee.ReturnType)), false
		}
	case application:
		result = applyTerm(callApplicationName(name, ""), resultWidth, applicationArgs...)
	case unit:
		if reason, ok := lo.lowerUnitBody(body); !ok {
			return fmt.Sprintf("a call to %s whose body contains %s", name, reason), false
		}
	case vecResult != nil:
		var reason string
		var ok bool
		vecLanes, reason, ok = lo.vectorLanes(body, *vecResult)
		if !ok {
			return fmt.Sprintf("a call to %s whose body contains %s", name, reason), false
		}
	case aggLeaves != nil:
		typ, ok := lo.oakTypeOf(callee.ReturnType)
		if !ok || typ.kind == oakScalar {
			return fmt.Sprintf("a call to %s returning %s (no model)", name, typeText(callee.ReturnType)), false
		}
		var reason string
		aggregate, reason, ok = lo.aggregateValue(body, typ)
		if !ok {
			return fmt.Sprintf("a call to %s whose body contains %s", name, reason), false
		}
	default:
		var reason string
		var ok bool
		result, reason, ok = lo.lower(body, resultWidth)
		if !ok {
			return fmt.Sprintf("a call to %s whose body contains %s", name, reason), false
		}
	}
	// The callee's data-dependent loops are the caller's events: numbered
	// after the caller's (loopBase), nested under the loop being executed,
	// their fresh symbols declared for the verdict; the Oak side inlines
	// the same body and creates the same events, which the coupling pairs
	// by identity (asm/loops.go). Their reaching condition is the caller's
	// path to this call together with the callee's path to the loop. Keeping
	// both is essential for the induction base: stores before a loop inside
	// a conditional are equal only on the paths that actually enter it.
	for _, ev := range lo.loops {
		ev.oakDerived = true
		ev.at = x.callAt
		// The callee's loop is reached where the machine's path reached
		// the call and the callee's own Oak path reached the loop (an arm
		// inside the callee): the coupling's premises assume both — a
		// store before the loop inside `ok ? { … }` is unguarded on the
		// machine's side and guarded by ok on the Oak side, and the two
		// agree exactly there (walk_leaf calling alloc_table).
		if len(ev.entry) == 0 && len(ev.writes) == 0 {
			// A loop that stores nothing couples on its values alone: the
			// same summary stands on both sides, and the call's result is
			// under each side's own path in the terms the verdict compares.
			// The caller's path — a select over sixteen lanes in
			// literals.oak's verify_first — would only weigh on every
			// premise of the nest (docs/spec/94-assembler.md §8).
			continue
		}
		ev.reached = ev.oakPath
		if callPath := state.pathCondition(); callPath != nil {
			if ev.reached != nil {
				ev.reached = binaryTerm("and", truncate(callPath, 1), truncate(ev.reached, 1))
			} else {
				ev.reached = callPath
			}
		}
	}
	if siteSeen {
		if len(lo.loops) != priorSite.count {
			return fmt.Sprintf("a call to %s whose loops differ between two paths", name), false
		}
		for k, ev := range lo.loops {
			merged, reason, ok := mergeLoopEvents(state.pathCondition(), ev, x.loops[priorSite.base+k])
			if !ok {
				return fmt.Sprintf("a call to %s %s", name, reason), false
			}
			x.loops[priorSite.base+k] = merged
		}
		priorSite.paths = append(priorSite.paths, state.path)
		x.sites[callSite] = priorSite
	} else {
		if len(lo.loops) > 0 && x.sites[callSite].count == 0 {
			if x.sites == nil {
				x.sites = map[string]loopSite{}
			}
			x.sites[callSite] = loopSite{base: len(x.loops), count: len(lo.loops), paths: []*pathNode{state.path}}
		}
		x.loops = append(x.loops, lo.loops...)
	}
	for symbol, width := range lo.fresh {
		if x.freshSyms == nil {
			x.freshSyms = map[string]int{}
		}
		if _, known := x.freshSyms[symbol]; !known {
			x.freshSyms[symbol] = width
			x.declared[symbol] = width
		}
	}
	state.writes = lo.writes // the callee's stores through the caller's spans
	for name := range lo.localSpans {
		// The callee's own large arrays (its frame, gone at return): their
		// logs are not the caller's memory — left in, a caller's loop
		// summary read them as stores through a span it does not know
		// (write_flush's chunk inside write_bytes).
		delete(state.writes, name)
	}
	for _, borrow := range frameBorrows {
		if reason, ok := borrow.writeBack(state, lo); !ok {
			return fmt.Sprintf("a call to %s: %s", name, reason), false
		}
	}
	for cellName, cell := range lo.cells {
		if cell.value != seeds[cellName] {
			if state.globals == nil {
				state.globals = map[string]*term{}
			}
			state.globals[cellName] = cell.value
		}
	}
	if unit {
		// x0–x17 (a0–a7, t0–t6 on rv64) and the caller-saved float and
		// vector registers are dead after the call; no result.
		x.forgetCallerSaved(state)
		for _, seen := range x.summarized {
			if seen == name {
				return "", true
			}
		}
		x.summarized = append(x.summarized, name)
		return "", true
	}
	if vecResult != nil {
		// The caller-saved registers are dead after the call: on RV64 the
		// whole vector file and its configuration, on AArch64 v0–v7 and
		// v16–v31 (the low halves of v8–v15 are preserved, kept as they
		// were). The result register receives the callee's lanes.
		if x.arch == ArchRV64 {
			for _, r := range []int{1, 5, 6, 7, 10, 11, 12, 13, 14, 15, 16, 17, 28, 29, 30, 31} {
				state.clobberGPR(r)
			}
		} else {
			for r := 0; r <= 17; r++ {
				state.clobberGPR(r)
			}
			state.clobberGPR(30)
			state.flags = nil
			for r := 0; r <= 31; r++ {
				if r < 8 || r >= 16 {
					delete(state.vregs, r)
				}
			}
		}
		state.writeVec(vecArg0, vecOfLanes(vecLanes, laneWidth(*vecResult)))
		for _, seen := range x.summarized {
			if seen == name {
				return "", true
			}
		}
		x.summarized = append(x.summarized, name)
		return "", true
	}
	if aggregate != nil && memResult {
		terms := map[string]*term{}
		leafTerms(aggregate, "", terms)
		for _, leaf := range aggLeaves {
			t, has := terms[leaf.name]
			if !has {
				return fmt.Sprintf("a call to %s returning %s with a leaf the layout lacks", name, typeText(callee.ReturnType)), false
			}
			// A Bool leaf is its 4-byte C enum cell holding 0 or 1; every
			// other leaf is stored at its width. The padding bytes between
			// leaves keep what the frame held: the callee's contract says
			// nothing about them and the Oak body never reads them.
			cell := leaf.width
			if cell == 1 {
				cell = 32
			}
			if fs, off, in := x.resultSpanAt(memResultBase + leaf.offset); in && off%fs.elem == 0 && int64(leaf.width) == fs.elem*8 {
				// A leaf inside a result span (the caller's `next =
				// f(next)` into the area it builds): the span's log.
				state.writes = appendWrite(state.writes, fs.name, constTerm(uint64(off/fs.elem), 32), truncate(adaptWidth(t, leaf.width), leaf.width), nil)
				continue
			}
			state.storeSlot(memResultBase+leaf.offset, zeroExtend(adaptWidth(t, leaf.width), cell), int64(cell/8))
		}
		x.forgetCallerSaved(state)
		for _, seen := range x.summarized {
			if seen == name {
				return "", true
			}
		}
		x.summarized = append(x.summarized, name)
		return "", true
	}
	if aggregate != nil {
		chunks := make([]*term, aggChunks)
		for k := range chunks {
			chunk, ok := packAggregateChunk(aggregate, aggLeaves, int64(k))
			if !ok {
				return fmt.Sprintf("a call to %s returning %s with a leaf the layout lacks", name, typeText(callee.ReturnType)), false
			}
			if m := definedMask(aggLeaves, int64(k)); m != ^uint64(0) {
				// The padding bytes: unspecified by the ABI, zero in a
				// witness run (the callee's own code cleared them).
				var pad *term
				if x.concrete {
					pad = constTerm(0, 64)
				} else {
					x.callSites++
					padName := fmt.Sprintf("call%d#pad%d", x.callSites, k)
					if x.freshSyms == nil {
						x.freshSyms = map[string]int{}
					}
					x.freshSyms[padName] = 64
					x.declared[padName] = 64
					pad = paramTerm(padName, 64)
				}
				chunk = binaryTerm("or", binaryTerm("and", chunk, constTerm(m, 64)), binaryTerm("and", pad, constTerm(^m, 64)))
			}
			chunks[k] = chunk
		}
		if x.arch == ArchRV64 {
			for _, r := range []int{1, 5, 6, 7, 11, 12, 13, 14, 15, 16, 17, 28, 29, 30, 31} {
				state.clobberGPR(r)
			}
			for k, chunk := range chunks {
				state.write(Register{Class: ClassRV64X, Num: 10 + k}, chunk)
			}
		} else {
			for r := 0; r <= 17; r++ {
				state.clobberGPR(r)
			}
			state.clobberGPR(30)
			state.flags = nil
			for k, chunk := range chunks {
				state.write(Register{Class: ClassX, Num: k}, chunk)
			}
		}
		for _, seen := range x.summarized {
			if seen == name {
				return "", true
			}
		}
		x.summarized = append(x.summarized, name)
		return "", true
	}
	if floatResult != 0 {
		// The caller-saved registers are dead after the call; the float
		// result register receives the callee's pattern at its width — on
		// AArch64 the low lane of v0, its upper bits unspecified (fresh),
		// the upper half zero as every scalar write leaves it.
		x.forgetCallerSaved(state)
		if x.arch == ArchRV64 {
			state.write(rv64FloatResultRegister, result)
		} else {
			low := zeroExtend(result, 64)
			if floatResult < 64 {
				var upper *term
				if x.concrete {
					upper = constTerm(0, 64-floatResult) // a witness run: the callee's own scalar write cleared them
				} else {
					x.callSites++
					hi := fmt.Sprintf("call%d#hi", x.callSites)
					if x.freshSyms == nil {
						x.freshSyms = map[string]int{}
					}
					x.freshSyms[hi] = 64 - floatResult
					x.declared[hi] = 64 - floatResult
					upper = paramTerm(hi, 64-floatResult)
				}
				low = binaryTerm("or", low, binaryTerm("shl", zeroExtend(upper, 64), constTerm(uint64(floatResult), 64)))
			}
			state.writeVec(0, vecFromLow(low))
		}
		for _, seen := range x.summarized {
			if seen == name {
				return "", true
			}
		}
		x.summarized = append(x.summarized, name)
		return "", true
	}
	value := zeroExtend(result, resultWidth)
	value = zeroExtend(value, 64)
	if x.arch == ArchRV64 {
		for _, r := range []int{1, 5, 6, 7, 11, 12, 13, 14, 15, 16, 17, 28, 29, 30, 31} {
			state.clobberGPR(r) // ra, t0–t6, a1–a7: dead after a call
		}
		switch {
		case resultSigned:
			value = extendTerm(value, resultWidth, 64, true)
		case resultWidth == 32:
			value = extendTerm(value, 32, 64, true) // a u32 arrives sign-extended (Oak.RiscV.widen)
		}
		state.write(Register{Class: ClassRV64X, Num: 10}, value)
	} else {
		for r := 1; r <= 17; r++ {
			state.clobberGPR(r)
		}
		state.clobberGPR(30)
		state.flags = nil
		defined := resultWidth
		if typeText(callee.ReturnType) == "Bool" {
			defined = 32 // the C enum: the whole low word holds 0 or 1
		}
		if defined < 64 {
			x.callSites++
			hi := fmt.Sprintf("call%d#hi", x.callSites)
			var upper *term
			if x.concrete {
				upper = constTerm(0, 64-defined) // a witness run: the callee's own code cleared them
			} else {
				if x.freshSyms == nil {
					x.freshSyms = map[string]int{}
				}
				x.freshSyms[hi] = 64 - defined
				x.declared[hi] = 64 - defined
				upper = paramTerm(hi, 64-defined)
			}
			value = binaryTerm("or", value, binaryTerm("shl", zeroExtend(upper, 64), constTerm(uint64(defined), 64)))
		}
		state.write(Register{Class: ClassX, Num: 0}, value)
	}
	for _, seen := range x.summarized {
		if seen == name {
			return "", true
		}
	}
	x.summarized = append(x.summarized, name)
	return "", true
}
