package asm

import "fmt"

// The RV64 lane's vector file as terms under a fixed configuration
// (docs/spec/94-assembler.md §8, §9). A `vsetivli zero, K, eS, m1, ta, ma`
// with K·S = 128 configures K lanes of S bits filling one register — the
// configuration the native lowering of the fixed vectors emits
// (nativegen/rv64_simd.go) — and under it the vector instructions are the
// lane functions of asm/verify_vector.go over vecValue lanes, so the RV64
// unit and the NEON unit of one Oak body decide against the same lane
// terms. A register AVL (`vsetvli`), a configuration whose vl depends on
// VLEN (K·S ≠ 128), masked forms, and the widening forms are outside the
// model: such a unit stays checked and trusted. What the ISA leaves
// unspecified is a fresh unknown: a reduction's tail lanes, a mask's bits
// past vl, the elements a gather or slide reads past vl (they lie in the
// tail of a wider VLEN's register) — so a lowering that reads them is a
// mismatch, and one that masks them out is proven.

// rvVectorConfigVerify is the executor's configuration: K lanes of bits.
type rvVectorConfigVerify struct {
	lanes int
	bits  int
}

// rvFrameAddrPrefix names a register-held frame address (`addi rD, sp,
// imm`): the entry-relative address is the name's suffix.
const rvFrameAddrPrefix = "sp@"

func rvFrameAddrTerm(addr int64) *term { return paramTerm(fmt.Sprintf("%s%d", rvFrameAddrPrefix, addr), 64) }

func rvFrameAddrOf(t *term) (int64, bool) {
	if t == nil || t.kind != termParam || len(t.name) <= len(rvFrameAddrPrefix) || t.name[:len(rvFrameAddrPrefix)] != rvFrameAddrPrefix {
		return 0, false
	}
	var addr int64
	if _, err := fmt.Sscanf(t.name[len(rvFrameAddrPrefix):], "%d", &addr); err != nil {
		return 0, false
	}
	return addr, true
}

// freshLane is an unspecified lane value: a parameter of the verification
// no law may pin down.
func (x *pathExecutor) freshLane(what string, bits int) *term {
	x.freshCount++
	name := fmt.Sprintf("%s#%d", what, x.freshCount)
	if x.freshSyms == nil {
		x.freshSyms = map[string]int{}
	}
	x.freshSyms[name] = bits
	if x.declared != nil {
		x.declared[name] = bits
	}
	return paramTerm(name, bits)
}

// stepRV64Vector executes one vector instruction under the configuration.
func (x *pathExecutor) stepRV64Vector(instr Instruction, state *symbolicState) (string, bool) {
	ops := instr.Operands
	name := instr.Mnemonic
	refuse := func(why string) (string, bool) { return "a vector instruction (" + name + ": " + why + ")", false }
	if rv64Masked(instr) {
		return refuse("a masked form")
	}
	reg := func(i int) Register { return ops[i].(Register) }
	switch name {
	case "vsetivli":
		avl := ops[1].(Immediate).Value
		sew := rv64VTypeSEW[ops[2].(Option).Name] * 8
		if ops[3].(Option).Name != "m1" || avl <= 0 || avl*sew > vecBits {
			// vl = min(AVL, VLMAX) is AVL exactly when AVL ≤ VLMAX on every
			// VLEN ≥ 128, i.e. K·S ≤ 128 (Oak.RiscV.vsetvl_min_ok).
			return refuse("a configuration whose vl depends on VLEN (the model takes K lanes of S bits with K·S ≤ 128 under m1)")
		}
		state.rvcfg = &rvVectorConfigVerify{lanes: int(avl), bits: int(sew)}
		return "", true
	case "vsetvli":
		return refuse("a register AVL")
	}
	cfg := state.rvcfg
	if cfg == nil {
		return refuse("no fixed configuration in effect")
	}
	K, bits := cfg.lanes, cfg.bits
	lanesOf := func(r Register) ([]*term, bool) {
		value, ok := state.readVec(r.Num)
		if !ok {
			return nil, false
		}
		return value.lanesAt(bits)[:K], true
	}
	// A write under vl = K leaves the lanes past K agnostic: unspecified.
	write := func(r Register, lanes []*term) {
		full := vecBits / bits
		for len(lanes) < full {
			lanes = append(lanes, x.freshLane("vtail", bits))
		}
		state.writeVec(r.Num, vecOfLanes(lanes, bits))
	}
	// A mask register holds one bit per lane in its low bits; the bits
	// past vl are unspecified.
	maskOf := func(r Register) (*term, bool) {
		value, ok := state.readVec(r.Num)
		if !ok {
			return nil, false
		}
		return value.halves()[0], true
	}
	writeMask := func(r Register, bitsOf func(k int) *term) {
		packed := constTerm(0, 64)
		for k := 0; k < K; k++ {
			bit := zeroExtend(bitsOf(k), 64)
			if k > 0 {
				bit = binaryTerm("shl", bit, constTerm(uint64(k), 64))
			}
			packed = binaryTerm("or", packed, bit)
		}
		tail := binaryTerm("shl", x.freshLane("vmask.tail", 64), constTerm(uint64(K), 64))
		if K >= 64 {
			tail = constTerm(0, 64)
		}
		state.writeVec(r.Num, vecValue{bits: 64, lanes: []*term{binaryTerm("or", packed, tail), x.freshLane("vmask.hi", 64)}})
	}
	maskBit := func(packed *term, k int) *term {
		return truncate(binaryTerm("shr", packed, constTerm(uint64(k), 64)), 1)
	}
	if width, isLoad := rv64VectorLoads[name]; isLoad {
		if int(width*8) != bits {
			return refuse("an element width other than the configured SEW")
		}
		return x.rv64VectorLoad(reg(0), ops[1].(Memory), K, bits, state)
	}
	if width, isStore := rv64VectorStores[name]; isStore {
		if int(width*8) != bits {
			return refuse("an element width other than the configured SEW")
		}
		return x.rv64VectorStore(reg(0), ops[1].(Memory), K, bits, state)
	}
	switch name {
	case "vadd.vv", "vsub.vv", "vand.vv", "vor.vv", "vxor.vv", "vminu.vv", "vmaxu.vv", "vssubu.vv", "vfadd.vv", "vfsub.vv", "vfmul.vv":
		a, okA := lanesOf(reg(1))
		b, okB := lanesOf(reg(2))
		if !okA || !okB {
			return "unbound vector register read", false
		}
		out := make([]*term, K)
		for k := range out {
			switch name {
			case "vfadd.vv", "vfsub.vv", "vfmul.vv":
				out[k] = floatTerm(map[string]string{"vfadd.vv": "fadd", "vfsub.vv": "fsub", "vfmul.vv": "fmul"}[name], bits, a[k], b[k])
			default:
				op := map[string]string{"vadd.vv": "add", "vsub.vv": "sub", "vand.vv": "and", "vor.vv": "or", "vxor.vv": "xor", "vminu.vv": "umin", "vmaxu.vv": "umax", "vssubu.vv": "uqsub"}[name]
				out[k] = laneBinary(op, a[k], b[k])
			}
		}
		write(reg(0), out)
		return "", true
	case "vfmacc.vv":
		// vd = vs1 * vs2 + vd, one rounding per lane.
		a, okA := lanesOf(reg(1))
		b, okB := lanesOf(reg(2))
		c, okC := lanesOf(reg(0))
		if !okA || !okB || !okC {
			return "unbound vector register read", false
		}
		out := make([]*term, K)
		for k := range out {
			out[k] = floatTerm("fma", bits, a[k], b[k], c[k])
		}
		write(reg(0), out)
		return "", true
	case "vfcvt.f.xu.v":
		a, okA := lanesOf(reg(1))
		if !okA {
			return "unbound vector register read", false
		}
		out := make([]*term, K)
		for k := range out {
			out[k] = floatTerm("ucvtf", bits, a[k])
		}
		write(reg(0), out)
		return "", true
	case "vsrl.vx":
		a, okA := lanesOf(reg(1))
		count, okC := state.read(reg(2))
		if !okA || !okC {
			return "unbound register read", false
		}
		out := make([]*term, K)
		for k := range out {
			out[k] = binaryTerm("shr", a[k], narrowLane(count, bits))
		}
		write(reg(0), out)
		return "", true
	case "vmv.v.x":
		value, ok := state.read(reg(1))
		if !ok {
			return "unbound register read", false
		}
		lane := narrowLane(value, bits)
		out := make([]*term, K)
		for k := range out {
			out[k] = lane
		}
		write(reg(0), out)
		return "", true
	case "vfmv.v.f":
		value, ok := state.read(reg(1))
		if !ok {
			return "unbound floating-point register read", false
		}
		lane := truncate(value, bits)
		out := make([]*term, K)
		for k := range out {
			out[k] = lane
		}
		write(reg(0), out)
		return "", true
	case "vmv.x.s":
		// Element 0 sign-extended to XLEN.
		a, okA := lanesOf(reg(1))
		if !okA {
			return "unbound vector register read", false
		}
		state.write(reg(0), extendTerm(a[0], bits, 64, true))
		return "", true
	case "vfmv.f.s":
		a, okA := lanesOf(reg(1))
		if !okA {
			return "unbound vector register read", false
		}
		state.write(reg(0), a[0])
		return "", true
	case "vmseq.vv", "vmsne.vx", "vmslt.vx", "vmsltu.vx":
		a, okA := lanesOf(reg(1))
		if !okA {
			return "unbound vector register read", false
		}
		var b []*term
		if name == "vmseq.vv" {
			var okB bool
			if b, okB = lanesOf(reg(2)); !okB {
				return "unbound vector register read", false
			}
		} else {
			value, okX := state.read(reg(2))
			if !okX {
				return "unbound register read", false
			}
			lane := narrowLane(value, bits)
			b = make([]*term, K)
			for k := range b {
				b[k] = lane
			}
		}
		code := map[string]string{"vmseq.vv": "eq", "vmsne.vx": "ne", "vmslt.vx": "lt", "vmsltu.vx": "lo"}[name]
		writeMask(reg(0), func(k int) *term { return truncate(cmpTerm(code, a[k], b[k]), 1) })
		return "", true
	case "vmerge.vvm":
		// vd = mask ? vs1 : vs2, lane by lane, from v0.
		a, okA := lanesOf(reg(1))
		b, okB := lanesOf(reg(2))
		packed, okM := maskOf(reg(3))
		if !okA || !okB || !okM {
			return "unbound vector register read", false
		}
		out := make([]*term, K)
		for k := range out {
			out[k] = iteTerm(maskBit(packed, k), b[k], a[k])
		}
		write(reg(0), out)
		return "", true
	case "vcpop.m":
		packed, okM := maskOf(reg(1))
		if !okM {
			return "unbound vector register read", false
		}
		low := binaryTerm("and", packed, constTerm(mask(K), 64))
		state.write(reg(0), binaryTerm("cnt", low, constTerm(0, 64)))
		return "", true
	case "vredsum.vs", "vfredosum.vs":
		// vd[0] = vs1[0] (+) vs2[0] (+) … (+) vs2[K-1]: the integer sum in
		// any order, the ordered float sum left to right
		// (Oak.RiscV.ordered_strips_fold); the tail is unspecified.
		a, okA := lanesOf(reg(1))
		s, okS := lanesOf(reg(2))
		if !okA || !okS {
			return "unbound vector register read", false
		}
		total := s[0]
		for k := 0; k < K; k++ {
			if name == "vredsum.vs" {
				total = laneBinary("add", total, a[k])
			} else {
				total = floatTerm("fadd", bits, total, a[k])
			}
		}
		out := make([]*term, K)
		out[0] = total
		for k := 1; k < K; k++ {
			out[k] = x.freshLane("vred.tail", bits)
		}
		write(reg(0), out)
		return "", true
	case "vrgather.vv":
		// vd[i] = vs2[vs1[i]] for an index below vl; an index at or past vl
		// reads the register's tail (or zero past VLMAX): unspecified.
		table, okT := lanesOf(reg(1))
		index, okI := lanesOf(reg(2))
		if !okT || !okI {
			return "unbound vector register read", false
		}
		if K != 16 || bits != 8 {
			return refuse("a gather over lanes other than sixteen bytes")
		}
		out := make([]*term, K)
		for k := range out {
			inRange := truncate(cmpTerm("lo", index[k], constTerm(uint64(K), bits)), 1)
			out[k] = iteTerm(inRange, laneTable(table, index[k]), x.freshLane("vgather.tail", bits))
		}
		write(reg(0), out)
		return "", true
	case "vslidedown.vi", "vslideup.vi":
		src, okS := lanesOf(reg(1))
		if !okS {
			return "unbound vector register read", false
		}
		n := int(ops[2].(Immediate).Value)
		out := make([]*term, K)
		if name == "vslidedown.vi" {
			// vd[i] = vs2[i + n]; past vl the tail (unspecified).
			for k := range out {
				if k+n < K {
					out[k] = src[k+n]
				} else {
					out[k] = x.freshLane("vslide.tail", bits)
				}
			}
		} else {
			// vd[i] = vs2[i - n] for i >= n; the lanes below n keep vd's.
			old, okD := lanesOf(reg(0))
			if !okD {
				return "unbound vector register read", false
			}
			for k := range out {
				if k < n {
					out[k] = old[k]
				} else {
					out[k] = src[k-n]
				}
			}
		}
		write(reg(0), out)
		return "", true
	}
	return refuse("outside the modeled subset")
}

// rv64SpanElementAddress decodes a register-held address as a span element:
// `&v + K` (K a multiple of the element size) or `&v + (idx << s)` with 2^s
// the element size — the checker's guarded-index idiom (§9); byte spans
// take the index unscaled.
func (x *pathExecutor) rv64SpanElementAddress(address *term, offset int64) (span string, index *term, reason string, ok bool) {
	if param, base, isBase := spanBaseOf(address); isBase {
		elem := x.spans[param]
		base += offset
		if elem == 0 || base%elem != 0 || base < 0 {
			return "", nil, "a span offset not aligned to an element", false
		}
		return param, constTerm(uint64(base/elem), 32), "", true
	}
	if address.kind == termBinary && address.op == "add" {
		base, scaled := address.left, address.right
		if _, _, isBase := spanBaseOf(base); !isBase {
			base, scaled = address.right, address.left
		}
		param, off, isBase := spanBaseOf(base)
		if !isBase || off != 0 || offset != 0 {
			return "", nil, "a load through an address that is not a span element", false
		}
		switch {
		case x.spans[param] == 1:
			return param, scaled, "", true
		case scaled.kind == termBinary && scaled.op == "shl" && scaled.right.kind == termConst && int64(1)<<scaled.right.value == x.spans[param]:
			return param, scaled.left, "", true
		}
		return "", nil, "an element address whose scale is not the element size", false
	}
	return "", nil, "a load through a register that is not a span base", false
}

// rv64VectorLoad reads K elements of bits from a span element address or
// a frame address held in the base register.
func (x *pathExecutor) rv64VectorLoad(dest Register, mem Memory, K, bits int, state *symbolicState) (string, bool) {
	address, bound := state.regs[mem.Base.Num]
	if !bound {
		return "a vector load through a register that is not bound", false
	}
	if addr, isFrame := rvFrameAddrOf(address); isFrame {
		return x.rv64VectorFrame(dest, addr+mem.Offset, K, bits, false, state)
	}
	span, index, reason, ok := x.rv64SpanElementAddress(address, mem.Offset)
	if !ok {
		return reason, false
	}
	if int64(bits/8) != x.spans[span] {
		return fmt.Sprintf("%d-bit vector elements over %d-byte span elements", bits, x.spans[span]), false
	}
	lanes := make([]*term, K)
	for k := range lanes {
		position := index
		if k > 0 {
			position = binaryTerm("add", index, constTerm(uint64(k), 32))
		}
		lanes[k] = x.element(span, position, bits)
	}
	state.writeLanes(dest, lanes, bits)
	return "", true
}

// rv64VectorStore writes K elements to a frame address; a store through a
// span is a memory effect the verifier does not follow.
func (x *pathExecutor) rv64VectorStore(src Register, mem Memory, K, bits int, state *symbolicState) (string, bool) {
	address, bound := state.regs[mem.Base.Num]
	if !bound {
		return "a vector store through a register that is not bound", false
	}
	if addr, isFrame := rvFrameAddrOf(address); isFrame {
		return x.rv64VectorFrame(src, addr+mem.Offset, K, bits, true, state)
	}
	return "a vector store through a span (the verifier decides results, not memory effects)", false
}

// rv64VectorFrame is a whole-register spill or reload at an entry-relative
// frame address: two 8-byte slots, the low half at the lower address (as
// the AArch64 lane's q views, asm/verify_vector.go).
func (x *pathExecutor) rv64VectorFrame(reg Register, addr int64, K, bits int, store bool, state *symbolicState) (string, bool) {
	if state.frame == nil {
		state.frame = map[int64]frameSlot{}
	}
	if store {
		value, ok := state.readVec(reg.Num)
		if !ok {
			return "unbound vector register read", false
		}
		halves := value.halves()
		state.frame[addr] = frameSlot{value: halves[0], width: 8}
		state.frame[addr+8] = frameSlot{value: halves[1], width: 8}
		return "", true
	}
	lo, okLo := state.frame[addr]
	hi, okHi := state.frame[addr+8]
	if !okLo || !okHi || lo.width != 8 || hi.width != 8 {
		return "a vector load from frame slots not stored whole on this path", false
	}
	state.writeVec(reg.Num, vecValue{bits: 64, lanes: []*term{zeroExtend(lo.value, 64), zeroExtend(hi.value, 64)}})
	return "", true
}
