package nativegen

import "testing"

func TestCompileForRejectsUnknownTargetBeforeSource(t *testing.T) {
	for _, arch := range []string{"unknown", "riscv64", "aarch64", "wasm32", "ARM64"} {
		fn, err := CompileFor(Lane{Arch: arch}, nil, nil, nil, nil, nil, nil)
		if err == nil || fn != nil {
			t.Fatalf("%q admitted: %v", arch, err)
		}
	}
}
