package asm

// The RV64 lane's frame array element at a data-dependent index
// (docs/spec/94-assembler.md §8, frame loads at a data-dependent index).
// The backend addresses `buf[i]` as `addi b, sp, off; li k, N; bgeu i, k,
// trap; slli i, i, s; add i, b, i` (nativegen/rv64.go arrayAddress), so
// the executor sees a load or store through a register holding
// add(frameAddr(off), shl(index, s)) — or add(frameAddr(off), index) for
// byte elements — with the guard's bound recorded on the index term
// (symbolicState.termBounds, noteTrapGuard). A load reads the bound's
// elements merged under the index (mergedFrameElements, the fold shared
// with the AArch64 lane, Oak.FrameIndex); a store is the bounded frame
// store (boundedFrameStoreAt), or forgets the array when a slot is not
// held whole.

// rv64FrameElement recognizes the element address: the array's
// entry-relative base, the 32-bit index term, its guard bound, and the
// element size the scaling spells (1 << shift).
func rv64FrameElement(state *symbolicState, mem Memory) (base int64, index *term, bound uint64, size int64, ok bool) {
	address, held := state.regs[mem.Base.Num]
	if !held || mem.Offset != 0 || address.kind != termBinary || address.op != "add" {
		return 0, nil, 0, 0, false
	}
	frame, scaled := address.left, address.right
	if _, isFrame := rvFrameAddrOf(frame); !isFrame {
		frame, scaled = address.right, address.left
	}
	base, isFrame := rvFrameAddrOf(frame)
	if !isFrame {
		return 0, nil, 0, 0, false
	}
	size = 1
	idx := scaled
	if scaled.kind == termBinary && scaled.op == "shl" && scaled.right.kind == termConst && scaled.right.value < 4 {
		size = int64(1) << scaled.right.value
		idx = scaled.left
	}
	bound, guarded := state.termBounds[idx]
	if !guarded {
		return 0, nil, 0, 0, false
	}
	return base, truncate(idx, 32), bound, size, true
}

// rv64FrameElementLoad executes a load through a frame element address at
// a guarded index: the merged elements, extended as the load spells.
func (x *pathExecutor) rv64FrameElementLoad(dest Register, width int, name string, base int64, index *term, bound uint64, size int64, state *symbolicState) (string, bool) {
	if int64(width) != size {
		return "a frame load at a data-dependent index whose scaling is not the access width", false
	}
	merged, reason, ok := x.mergedFrameElements(state, base, index, bound, size)
	if !ok {
		return reason, false
	}
	value := zeroExtend(merged, 64)
	switch name {
	case "lw", "lh", "lb":
		value = extendTerm(value, 8*width, 64, true)
	}
	state.write(dest, value)
	return "", true
}

// rv64FrameElementStore executes a store through a frame element address
// at a guarded index: each element takes the value under `index == e`;
// an element the frame does not hold whole forgets the array from its
// base, as the AArch64 lane does.
func (x *pathExecutor) rv64FrameElementStore(src Register, width int, base int64, index *term, bound uint64, size int64, state *symbolicState) (string, bool) {
	if int64(width) != size {
		return "a frame store at a data-dependent index whose scaling is not the access width", false
	}
	value, ok := state.read(src)
	if !ok {
		return "unbound register read", false
	}
	if state.frame == nil {
		state.frame = map[int64]frameSlot{}
	}
	if bound > 0 && bound <= 64 && state.boundedFrameStoreAt(base, index, bound, size, truncate(value, int(size)*8)) {
		return "", true
	}
	state.forgetFrameFrom(base)
	return "", true
}
