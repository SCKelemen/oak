package asm

import "fmt"

// encodingArchitecture is the admission boundary shared by function encoding
// and relocatable object layout. Empty architecture is the legacy ARM64
// spelling; new callers should supply an explicit target. No other spelling
// may inherit ARM64 encoding or container metadata.
func encodingArchitecture(arch string) (string, error) {
	if arch == "" {
		arch = ArchArm64
	}
	target, err := ResolveNativeTarget(arch)
	if err != nil {
		return "", err
	}
	return target.Arch(), nil
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
	target, err := ResolveNativeTarget(arch)
	if err != nil {
		return nil, nil, err
	}
	bound := *fn
	bound.Arch = arch
	return target.Encode(&bound)
}
