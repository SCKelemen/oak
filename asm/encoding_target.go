package asm

import "fmt"

// encodingArchitecture is the admission boundary shared by function encoding
// and relocatable object layout. Empty architecture is the legacy ARM64
// spelling; new callers should supply an explicit target. No other spelling
// may inherit ARM64 encoding or container metadata.
func encodingArchitecture(arch string) (string, error) {
	switch arch {
	case "", ArchArm64:
		return ArchArm64, nil
	case ArchRV64:
		return ArchRV64, nil
	default:
		return "", fmt.Errorf("unsupported native encoding architecture %q", arch)
	}
}

// EncodeFunction encodes a checked function for its admitted native target,
// resolving local labels and returning relocations for external symbols.
// Empty Arch retains the legacy ARM64 spelling. Unknown targets and nil
// functions fail before either target encoder runs.
func EncodeFunction(fn *Function) ([]byte, []Relocation, error) {
	if fn == nil {
		return nil, nil, fmt.Errorf("encode: nil function")
	}
	arch, err := encodingArchitecture(fn.Arch)
	if err != nil {
		return nil, nil, fmt.Errorf("encode %s: %w", fn.Name, err)
	}
	switch arch {
	case ArchArm64:
		return encodeARM64Function(fn)
	case ArchRV64:
		return encodeRV64Function(fn)
	default:
		return nil, nil, fmt.Errorf("encode %s: no encoder for architecture %q", fn.Name, arch)
	}
}
