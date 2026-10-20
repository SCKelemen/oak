package asm

import "fmt"

// NativeTarget is the closed native target contract shared by generation,
// machine optimization, encoding, and verification. Its zero value is invalid.
// It identifies a lane, not proof coverage: encoding never implies verification.
// ISA-specific ABI and semantics remain owned by their existing implementations.
type NativeTarget struct{ arch string }

// ResolveNativeTarget accepts only canonical assembler lane names. Platform
// spellings (riscv64), aliases, and empty names must be resolved by the caller.
func ResolveNativeTarget(arch string) (NativeTarget, error) {
	switch arch {
	case ArchArm64, ArchRV64:
		return NativeTarget{arch: arch}, nil
	default:
		return NativeTarget{}, fmt.Errorf("unsupported native target %q", arch)
	}
}

// Arch returns the canonical assembler lane, or empty for an invalid target.
func (t NativeTarget) Arch() string { return t.arch }

// Encode encodes only functions explicitly bound to this target. No metadata
// is rewritten, and neither successful encoding nor target membership is a
// seam-check or semantic proof. Call Check and Verify independently.
func (t NativeTarget) Encode(fn *Function) ([]byte, []Relocation, error) {
	if _, err := ResolveNativeTarget(t.arch); err != nil {
		return nil, nil, err
	}
	if fn == nil || fn.Arch != t.arch {
		return nil, nil, fmt.Errorf("native target %s: missing function or architecture mismatch", t.arch)
	}
	switch t.arch {
	case ArchArm64:
		return encodeARM64Function(fn)
	case ArchRV64:
		return encodeRV64Function(fn)
	default:
		return nil, nil, fmt.Errorf("native target %q has no encoder", t.arch)
	}
}

// AcceptsRelocation checks lane ownership only. Container support, footprint,
// opcode/register identity, range, alignment, and decoded destination checks
// remain mandatory at their existing object/image boundaries.
func (t NativeTarget) AcceptsRelocation(kind string) bool {
	if _, known := relocationFootprint(kind); !known {
		return false
	}
	switch t.arch {
	case ArchArm64:
		switch kind {
		case "call26", "jump26", "branch26", "condbr19", "tbz14", "adr21", "adrp21", "lo12", "adrl21":
			return true
		}
		return false
	case ArchRV64:
		return rv64Reloc(kind)
	default:
		return false
	}
}
