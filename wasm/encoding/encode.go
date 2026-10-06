// Package encoding assembles the instruction vocabulary of oak.wasm.scalar.v1.
// It validates immediate domains, not stack types, control nesting or indices
// against a module. Final modules must pass the independent wasm/check validator.
package encoding

import "fmt"

// Instruction is one opcode and its mathematical immediate. Instructions with
// no immediate require zero. Constants use signed Wasm carriers; u32/u64 Oak
// constants are passed by reinterpreting their bits as int32/int64.
type Instruction struct {
	Opcode    byte
	Immediate int64
}

// AppendUnsigned emits canonical unsigned LEB128, including all uint64 values.
// Wasm section lengths and indices use the narrower uint32 domain.
func AppendUnsigned(dst []byte, value uint64) []byte {
	for {
		b := byte(value & 127)
		value >>= 7
		if value != 0 {
			b |= 128
		}
		dst = append(dst, b)
		if value == 0 {
			return dst
		}
	}
}

// AppendSigned emits canonical signed LEB128, not Go's zig-zag varint.
func AppendSigned(dst []byte, value int64) []byte {
	for {
		b := byte(value & 127)
		value >>= 7
		last := (value == 0 && b&64 == 0) || (value == -1 && b&64 != 0)
		if !last {
			b |= 128
		}
		dst = append(dst, b)
		if last {
			return dst
		}
	}
}

// AppendInstruction leaves dst and its backing storage unchanged on refusal.
func AppendInstruction(dst []byte, ins Instruction) ([]byte, error) {
	v := ins.Immediate
	switch ins.Opcode {
	case 0x02, 0x03, 0x04: // block, loop, if: empty/i32/i64, no type indices
		if v != 0x40 && v != 0x7f && v != 0x7e {
			return dst, fmt.Errorf("wasm assemble: unsupported block type %d", v)
		}
		return append(dst, ins.Opcode, byte(v)), nil
	case 0x0c, 0x0d, 0x10, 0x20, 0x21, 0x22: // depth/function/local index
		if v < 0 || v > 1<<32-1 {
			return dst, fmt.Errorf("wasm assemble: index out of u32 range: %d", v)
		}
		return AppendUnsigned(append(dst, ins.Opcode), uint64(v)), nil
	case 0x41:
		if v < -1<<31 || v > 1<<31-1 {
			return dst, fmt.Errorf("wasm assemble: i32 constant out of range: %d", v)
		}
		return AppendSigned(append(dst, ins.Opcode), v), nil
	case 0x42:
		return AppendSigned(append(dst, ins.Opcode), v), nil
	default:
		plain := ins.Opcode == 0 || ins.Opcode == 1 || ins.Opcode == 5 ||
			ins.Opcode == 0x0b || ins.Opcode == 0x0f || ins.Opcode == 0x1a ||
			(ins.Opcode >= 0x45 && ins.Opcode <= 0x4f) ||
			(ins.Opcode >= 0x51 && ins.Opcode <= 0x5a) ||
			(ins.Opcode >= 0x6a && ins.Opcode <= 0x73) ||
			(ins.Opcode >= 0x7c && ins.Opcode <= 0x85)
		if !plain || v != 0 {
			return dst, fmt.Errorf("wasm assemble: unsupported opcode/immediate 0x%02x/%d", ins.Opcode, v)
		}
		return append(dst, ins.Opcode), nil
	}
}

// Assemble is all-or-nothing, returning no partial instruction stream on error.
// Else/end are explicit delimiters; module validation checks their nesting.
func Assemble(instructions []Instruction) ([]byte, error) {
	var out []byte
	for i, ins := range instructions {
		var err error
		out, err = AppendInstruction(out, ins)
		if err != nil {
			return nil, fmt.Errorf("instruction %d: %w", i, err)
		}
	}
	return out, nil
}
