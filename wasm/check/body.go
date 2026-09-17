package check

type frame struct {
	kind        byte
	height      int
	result      ValueType // empty for no result
	unreachable bool
}

type bodyValidator struct {
	r       *reader
	values  []ValueType
	control []frame
}

func (v *bodyValidator) pop(want ValueType) {
	if v.r.err != nil {
		return
	}
	f := v.control[len(v.control)-1]
	if len(v.values) == f.height {
		if !f.unreachable {
			v.r.fail("operand stack underflow")
		}
		return // polymorphic bottom, only at the unreachable frame's height
	}
	got := v.values[len(v.values)-1]
	v.values = v.values[:len(v.values)-1]
	if want != "" && got != want {
		v.r.fail("operand type %s, expected %s", got, want)
	}
}

func (v *bodyValidator) push(t ValueType) {
	if t == "" || v.r.err != nil {
		return
	}
	if len(v.values) >= maxStack {
		v.r.fail("operand stack limit exceeded")
		return
	}
	v.values = append(v.values, t)
}

func (v *bodyValidator) unreachable() {
	f := &v.control[len(v.control)-1]
	v.values = v.values[:f.height]
	f.unreachable = true
}

func (v *bodyValidator) finishFrame() frame {
	f := v.control[len(v.control)-1]
	if f.result != "" {
		v.pop(f.result)
	}
	if len(v.values) != f.height {
		v.r.fail("extra operands at end of control frame")
	}
	v.control = v.control[:len(v.control)-1]
	return f
}

func validateBody(r *reader, sig signature, functions []signature, totalLocals, instructions *int) error {
	if len(sig.parameters) > maxTotalLocals-*totalLocals {
		r.fail("module local count limit exceeded")
		return r.err
	}
	locals := append([]ValueType(nil), sig.parameters...)
	for i, groups := 0, r.count(maxLocals); i < groups && r.err == nil; i++ {
		n := r.count(maxLocals)
		t := r.valueType()
		if n > maxLocals-len(locals) {
			r.fail("local count limit exceeded")
			break
		}
		if n > maxTotalLocals-*totalLocals-len(locals) {
			r.fail("module local count limit exceeded")
			break
		}
		for j := 0; j < n && r.err == nil; j++ {
			locals = append(locals, t)
		}
	}
	*totalLocals += len(locals)
	if *totalLocals > maxTotalLocals {
		r.fail("module local count limit exceeded")
	}
	result := ValueType("")
	if len(sig.results) != 0 {
		result = sig.results[0]
	}
	v := bodyValidator{r: r, control: []frame{{kind: 0xff, result: result}}}
	for r.err == nil && len(v.control) != 0 {
		*instructions++
		if *instructions > maxInstructions {
			r.fail("instruction limit exceeded")
			break
		}
		op := r.byte()
		switch op {
		case 0x00: // unreachable
			v.unreachable()
		case 0x01: // nop
		case 0x02, 0x03, 0x04: // block, loop, if; no block parameters/type indices
			if op == 0x04 {
				v.pop(I32)
			}
			var end ValueType
			switch r.byte() {
			case 0x40:
			case 0x7f:
				end = I32
			case 0x7e:
				end = I64
			default:
				r.fail("unsupported block type")
			}
			if len(v.control) >= maxControlDepth {
				r.fail("control depth limit exceeded")
				break
			}
			v.control = append(v.control, frame{kind: op, height: len(v.values), result: end})
		case 0x05: // else validates the then arm, then starts a fresh arm
			f := v.finishFrame()
			if f.kind != 0x04 {
				r.fail("else without matching if")
				break
			}
			v.control = append(v.control, frame{kind: 0x05, height: f.height, result: f.result})
		case 0x0b: // end
			f := v.finishFrame()
			if f.kind == 0x04 && f.result != "" {
				r.fail("result-producing if requires else")
			}
			if len(v.control) != 0 {
				v.push(f.result)
			}
		case 0x0c, 0x0d: // br / br_if
			depth := r.u32()
			if uint64(depth) >= uint64(len(v.control)) {
				r.fail("unknown branch depth %d", depth)
				break
			}
			if op == 0x0d {
				v.pop(I32)
			}
			label := v.control[len(v.control)-1-int(depth)]
			if label.kind != 0x03 && label.result != "" {
				v.pop(label.result)
			}
			if op == 0x0c {
				v.unreachable()
			} else if label.kind != 0x03 {
				v.push(label.result)
			}
		case 0x0f: // return
			if result != "" {
				v.pop(result)
			}
			v.unreachable()
		case 0x10: // call, including forward and recursive references
			idx := r.u32()
			if uint64(idx) >= uint64(len(functions)) {
				r.fail("unknown call index %d", idx)
				break
			}
			callee := functions[idx]
			for i := len(callee.parameters) - 1; i >= 0; i-- {
				v.pop(callee.parameters[i])
			}
			for _, t := range callee.results {
				v.push(t)
			}
		case 0x1a:
			v.pop("") // drop
		case 0x20, 0x21, 0x22: // local.get / set / tee
			idx := r.u32()
			if uint64(idx) >= uint64(len(locals)) {
				r.fail("unknown local index %d", idx)
				break
			}
			if op != 0x20 {
				v.pop(locals[idx])
			}
			if op != 0x21 {
				v.push(locals[idx])
			}
		case 0x41:
			r.integer(32, true)
			v.push(I32)
		case 0x42:
			r.integer(64, true)
			v.push(I64)
		case 0x45: // i32.eqz
			v.pop(I32)
			v.push(I32)
		case 0x46, 0x47, 0x48, 0x49, 0x4a, 0x4b, 0x4c, 0x4d, 0x4e, 0x4f:
			v.pop(I32)
			v.pop(I32)
			v.push(I32)
		case 0x51, 0x52, 0x53, 0x54, 0x55, 0x56, 0x57, 0x58, 0x59, 0x5a:
			v.pop(I64)
			v.pop(I64)
			v.push(I32)
		case 0x6a, 0x6b, 0x6c, 0x71, 0x72, 0x73:
			v.pop(I32)
			v.pop(I32)
			v.push(I32)
		case 0x7c, 0x7d, 0x7e, 0x83, 0x84, 0x85:
			v.pop(I64)
			v.pop(I64)
			v.push(I64)
		default:
			r.fail("unsupported opcode 0x%02x", op)
		}
	}
	return r.done()
}
