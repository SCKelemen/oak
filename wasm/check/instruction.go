package check

// Instruction is the independently decoded scalar-profile instruction.
// Immediate is a signed constant, unsigned index, or block-type byte. It is
// zero for instructions without an immediate. Delimiters remain explicit.
type Instruction struct {
	Opcode    byte
	Immediate int64
}

// DecodeInstruction reads exactly one instruction prefix. It does not validate
// a function's stack, nesting, or indices; Validate performs those checks. On
// failure it returns no instruction and zero consumption. Legal padded LEBs
// are accepted, as required by the pinned Core binary grammar.
func DecodeInstruction(data []byte) (Instruction, int, error) {
	r := reader{data: data}
	i := r.instruction()
	if r.err != nil {
		return Instruction{}, 0, r.err
	}
	return i, r.pos, nil
}

func (r *reader) instruction() Instruction {
	i := Instruction{Opcode: r.byte()}
	switch i.Opcode {
	case 0x02, 0x03, 0x04:
		i.Immediate = int64(r.byte())
		if i.Immediate != 0x40 && i.Immediate != 0x7f && i.Immediate != 0x7e {
			r.fail("unsupported block type")
		}
	case 0x0c, 0x0d, 0x10, 0x20, 0x21, 0x22:
		i.Immediate = int64(r.u32())
	case 0x41:
		i.Immediate = int64(r.integer(32, true))
	case 0x42:
		i.Immediate = int64(r.integer(64, true))
	case 0x00, 0x01, 0x05, 0x0b, 0x0f, 0x1a,
		0x45, 0x46, 0x47, 0x48, 0x49, 0x4a, 0x4b, 0x4c, 0x4d, 0x4e, 0x4f,
		0x51, 0x52, 0x53, 0x54, 0x55, 0x56, 0x57, 0x58, 0x59, 0x5a,
		0x6a, 0x6b, 0x6c, 0x6d, 0x6e, 0x6f, 0x70, 0x71, 0x72, 0x73,
		0x7c, 0x7d, 0x7e, 0x7f, 0x80, 0x81, 0x82, 0x83, 0x84, 0x85:
	default:
		r.fail("unsupported opcode 0x%02x", i.Opcode)
	}
	return i
}
