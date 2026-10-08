package compiler

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/target"
	"github.com/SCKelemen/oak/typechecker"
)

// The common frontend gate must fire before any target admits or emits an
// uninitialized/null code pointer. These are diagnostic tests, not claims
// of formal source-to-machine correspondence for indirect calls.
func TestCallableInitializationFailsBeforeEmission(t *testing.T) {
	sources := map[string]string{
		"direct": `main: (): i32 { f: (i32) -> i32; f(42) }`,
		"nested": `Holder: type = struct { callback: (i32) -> i32 }
Box[T]: type = struct { value: T }
main: (): i32 { b: Box[Box[Holder]]; 0 }`,
	}
	for name, source := range sources {
		t.Run(name, func(t *testing.T) {
			for _, arch := range []string{target.ArchArm64, target.ArchRiscv64, target.ArchWasm32} {
				t.Run(arch, func(t *testing.T) {
					os := target.OSFreestanding
					if arch == target.ArchWasm32 {
						os = target.OSCore
					}
					c := New().WithSource("callable.oak", source).WithTarget(target.Target{OS: os, Arch: arch})
					_, err := c.Check().Get()
					requireCallableInitError(t, err)
					if arch == target.ArchWasm32 {
						_, err = c.EmitWasm().Get()
						requireCallableInitError(t, err)
						return
					}
					_, err = c.EmitC().Get()
					requireCallableInitError(t, err)
					_, err = c.WithNativeBodies().WithNativeAsm().EmitNativeObject(asm.ELF).Get()
					requireCallableInitError(t, err)
				})
			}
		})
	}
}
func requireCallableInitError(t *testing.T, err error) {
	t.Helper()
	if err == nil || !strings.Contains(err.Error(), typechecker.CodeCallableInitializer) {
		t.Fatalf("want %s, got %v", typechecker.CodeCallableInitializer, err)
	}
}

func TestExplicitCallableInitializerStillEmits(t *testing.T) {
	const source = `identity: (x: i32): i32 = x
main: (): i32 { f: (i32) -> i32 = identity; f(42) }`
	generated, err := New().WithSource("callable.oak", source).EmitC().Get()
	if err != nil {
		t.Fatal(err)
	}
	if !strings.Contains(generated, "(*f)(i32)") || !strings.Contains(generated, "oak_identity") {
		t.Fatalf("missing initialized callable:\n%s", generated)
	}
}
