package compiler

import (
	"bytes"
	"context"
	"debug/elf"
	"encoding/binary"
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"
	"time"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/target"
)

// This extraction is operational evidence, not a proved ELF-loader refinement.
// The Lean theorem consumes the entire returned function byte sequence and
// records the native entry/fetch boundary separately from the full Wasm loader.
func sourceBitwiseFunctionBytes(t *testing.T, original, name, arch string) []byte {
	t.Helper()
	out, err := New().WithSource("source-bound.oak", original).
		WithTarget(target.Target{OS: target.OSLinux, Arch: arch}).WithNativeBodies().EmitNative(asm.ELF).Get()
	if err != nil {
		t.Fatal(err)
	}
	f, err := elf.NewFile(bytes.NewReader(out.Object))
	if err != nil {
		t.Fatal(err)
	}
	defer f.Close()
	machine := elf.EM_AARCH64
	if arch == target.ArchRiscv64 {
		machine = elf.EM_RISCV
	}
	if f.Machine != machine || f.Type != elf.ET_REL || f.Class != elf.ELFCLASS64 || f.Data != elf.ELFDATA2LSB {
		t.Fatalf("wrong artifact profile: %+v", f.FileHeader)
	}
	if arch == target.ArchRiscv64 && binary.LittleEndian.Uint32(out.Object[48:52]) != 4 {
		t.Fatal("expected LP64D object")
	}
	symbols, err := f.Symbols()
	if err != nil {
		t.Fatal(err)
	}
	var code []byte
	found := false
	for _, symbol := range symbols {
		if symbol.Name != "oak_"+name {
			continue
		}
		if found {
			t.Fatal("duplicate named function")
		}
		found = true
		if elf.ST_TYPE(symbol.Info) != elf.STT_FUNC || symbol.Section == elf.SHN_UNDEF || int(symbol.Section) >= len(f.Sections) {
			t.Fatal("invalid named function symbol")
		}
		section, err := f.Sections[symbol.Section].Data()
		if err != nil {
			t.Fatal(err)
		}
		if symbol.Value > uint64(len(section)) || symbol.Size > uint64(len(section))-symbol.Value {
			t.Fatal("function extent outside section")
		}
		code = append([]byte(nil), section[symbol.Value:symbol.Value+symbol.Size]...)
		for _, rel := range f.Sections {
			if rel.Info != uint32(symbol.Section) {
				continue
			}
			if rel.Type == elf.SHT_REL {
				t.Fatal("unsupported implicit relocations in function section")
			}
			if rel.Type != elf.SHT_RELA {
				continue
			}
			data, err := rel.Data()
			if err != nil {
				t.Fatal(err)
			}
			if len(data)%24 != 0 {
				t.Fatal("malformed relocations")
			}
			for at := 0; at < len(data); at += 24 {
				offset := binary.LittleEndian.Uint64(data[at : at+8])
				if offset >= symbol.Value && offset < symbol.Value+symbol.Size {
					t.Fatal("unresolved relocation in function")
				}
			}
		}
	}
	if !found || len(code) == 0 {
		t.Fatal("named function absent")
	}
	return code
}

// Called from the already required OAK_REQUIRE_WASM_LEAN execution lane. All
// three compilers receive the identical original source bytes, with no appended
// main, reconstructed AST, or alternate arrow-signature fixture.
func testBitwiseSourceParityLean(t *testing.T) {
	t.Helper()
	lake := findLake()
	if lake == "" {
		t.Fatal("source-bound parity requires lake")
	}
	root, err := filepath.Abs(filepath.Join("..", "spec", "lean"))
	if err != nil {
		t.Fatal(err)
	}
	run := func(args ...string) {
		t.Helper()
		ctx, cancel := context.WithTimeout(t.Context(), 4*time.Minute)
		defer cancel()
		cmd := exec.CommandContext(ctx, lake, args...)
		cmd.Dir = root
		if output, err := cmd.CombinedOutput(); err != nil {
			t.Fatalf("lake %v: %v\n%s", args, err, output)
		}
	}
	run("build", "Oak.BitwiseSourceParity", "Oak.BitwiseSourceLowering")
	var proof strings.Builder
	proof.WriteString("import Oak.BitwiseSourceParity\nimport Oak.BitwiseSourceLowering\nopen Oak Oak.BitwiseFunction\nset_option maxRecDepth 8192\n")
	list := func(b []byte) string { return strings.Replace(wasmLeanArray(b), "#[", "[", 1) }
	for _, tc := range []struct{ op, symbol string }{{"and", "&"}, {"or", "|"}, {"xor", "^"}} {
		original := fmt.Sprintf("mix: (a: u32, b: u32): u32 = a %s b\n", tc.symbol)
		wasm, err := New().WithSource("source-bound.oak", original).EmitWasm().Get()
		if err != nil {
			t.Fatal(err)
		}
		if wasm.TranslationVerified || wasm.ByteValidation == nil {
			t.Fatal("production verification authority changed")
		}
		arm := sourceBitwiseFunctionBytes(t, original, "mix", target.ArchArm64)
		rv := sourceBitwiseFunctionBytes(t, original, "mix", target.ArchRiscv64)
		if len(arm) != 8 || len(rv) != 36 {
			t.Fatalf("profile changed: ARM=%d RV=%d", len(arm), len(rv))
		}
		fmt.Fprintf(&proof, "namespace Actual_%s\ndef source : List UInt8 := %s\ndef wasm : List UInt8 := %s\ndef arm : List UInt8 := %s\ndef rv : RiscVBitwiseFunction.Bytes := %s\ndef claim : BitwiseSource.Decl := ⟨[109,105,120], [97], [98], .%s⟩\n", tc.op, list([]byte(original)), list(wasm.Bytes), list(arm), list(rv), tc.op)
		proof.WriteString(`theorem checked : BitwiseSourceParity.accepts source claim wasm arm rv = true := by decide +kernel
 theorem all_inputs (left right : BitVec 32) (a : AArch64BitwiseFunction.State)
  (ha : (a.regs 0#5).extractLsb' 0 32 = left)
  (hb : (a.regs 1#5).extractLsb' 0 32 = right)
  (pc : BitVec 64) (caller : BitVec 5 → BitVec 64)
  (mem : AArch64SpillMemory.Memory) (mapped : Nat → Nat → Bool)
  (safe : RiscVFramedBitwise.frameSafe mapped (RiscVFramedBitwise.entry left right pc caller mem) = true) :
  BitwiseSource.Means source claim left right (eval claim.op left right) ∧
  BitwiseModule.invokeModule claim.name wasm left right = .ok (eval claim.op left right) ∧
  BitwiseSourceParity.armResult arm a = some (eval claim.op left right) ∧
  BitwiseSourceParity.rvResult rv (RiscVFramedBitwise.entry left right pc caller mem) mapped = some (eval claim.op left right) :=
  BitwiseSourceParity.accepted_all_input_success checked left right a ha hb pc caller mem mapped safe
`)
		proof.WriteString(`theorem existing_source_semantics (left right : BitVec 32) (fuel : Nat) :
  BitwiseSource.Grammar source claim ∧
  LoweringRefinement.evalX (BitwiseSourceLowering.toExpr claim)
    (BitwiseSourceLowering.inputs left right) (fun _ => 0) fuel = some (eval claim.op left right) ∧
  BitwiseModule.invokeModule claim.name wasm left right = .ok (eval claim.op left right) :=
  BitwiseSourceLowering.accepted_module_existing (by decide +kernel : BitwiseSource.accepts source claim .wasm .wasmLocals wasm = true) left right fuel
`)
		fmt.Fprintf(&proof, "end Actual_%s\n", tc.op)
		t.Logf("%s original source -> Wasm %d bytes, ARM %x, RV %x", tc.op, len(wasm.Bytes), arm, rv)
	}
	path := filepath.Join(t.TempDir(), "SourceBoundAll3.lean")
	if err := os.WriteFile(path, []byte(proof.String()), 0600); err != nil {
		t.Fatal(err)
	}
	run("env", "lean", path)
}
