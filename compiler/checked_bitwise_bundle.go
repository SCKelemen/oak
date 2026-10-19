package compiler

import (
	"context"
	"fmt"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/bitwisecheck"
	"github.com/SCKelemen/oak/target"
)

// EmitKernelCheckedBitwiseBundle compiles one original source snapshot into a
// complete core/wasm32 module and Linux ARM64 and RV64 ELF relocatable objects,
// then admits the exact four byte strings together with the pinned Lean kernel.
// Its deliberately narrow canonical two-u32 AND/OR/XOR profile is defined by
// bitwisecheck; successful ordinary compilation alone grants no checked bundle.
//
// Each target uses a fresh default Compilation. No package, overlay, assembly,
// rewrite, ABI, or verification options can enter this API. It does not change
// native verdicts, the verified profile, or Wasm TranslationVerified authority.
// The caller owns installation and must Close it when no longer needed.
//
// Cancellation is checked between synchronous compiler stages and is passed to
// the independent checker. It cannot interrupt the existing emitter internals.
func EmitKernelCheckedBitwiseBundle(ctx context.Context, installation *bitwisecheck.Installation, original SourceText) Stage[*bitwisecheck.CheckedBundle] {
	fail := func(stage string, err error) Stage[*bitwisecheck.CheckedBundle] {
		return Failure[*bitwisecheck.CheckedBundle](fmt.Errorf("checked bitwise bundle: %s: %w", stage, err))
	}
	if ctx == nil {
		return fail("context", fmt.Errorf("nil context"))
	}
	if err := ctx.Err(); err != nil {
		return fail("context", err)
	}
	if !installation.Valid() {
		return fail("checker", bitwisecheck.ErrInvalidInstallation)
	}
	if len(original.Text) == 0 || len(original.Text) > bitwisecheck.MaxSourceBytes {
		return fail("source", bitwisecheck.ErrBounds)
	}
	// SourceText is immutable Go text. Take its original bytes once, then use
	// only the owned snapshot for all compilations and independent admission.
	source := []byte(original.Text)
	text := string(source)
	wasm, err := New().WithSource(original.Path, text).
		WithTarget(target.Target{OS: target.OSCore, Arch: target.ArchWasm32}).EmitWasm().Get()
	if err != nil {
		return fail("core/wasm32 emission", err)
	}
	wasmBytes := append([]byte(nil), wasm.Bytes...)
	if err := ctx.Err(); err != nil {
		return fail("after core/wasm32 emission", err)
	}
	arm, err := New().WithSource(original.Path, text).
		WithTarget(target.Target{OS: target.OSLinux, Arch: target.ArchArm64}).EmitNativeObject(asm.ELF).Get()
	if err != nil {
		return fail("linux/arm64 emission", err)
	}
	armBytes := append([]byte(nil), arm...)
	if err := ctx.Err(); err != nil {
		return fail("after linux/arm64 emission", err)
	}
	rv, err := New().WithSource(original.Path, text).
		WithTarget(target.Target{OS: target.OSLinux, Arch: target.ArchRiscv64}).EmitNativeObject(asm.ELF).Get()
	if err != nil {
		return fail("linux/riscv64 emission", err)
	}
	rvBytes := append([]byte(nil), rv...)
	if err := ctx.Err(); err != nil {
		return fail("after linux/riscv64 emission", err)
	}
	bundle, err := installation.CheckBundle(ctx, source, wasmBytes, armBytes, rvBytes)
	if err != nil {
		return fail("kernel admission", err)
	}
	if err := ctx.Err(); err != nil {
		return fail("after kernel admission", err)
	}
	if !bundle.Valid() {
		return fail("kernel admission", bitwisecheck.ErrInvalidBundle)
	}
	return Value(bundle)
}
