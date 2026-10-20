package main

import (
	"bytes"
	"debug/elf"
	"encoding/binary"
	"fmt"
	"strings"
	"testing"

	"github.com/SCKelemen/oak/compiler"
	"github.com/SCKelemen/oak/target"
)

// Compile the production preflight prefix, without the later checker/FFI
// bodies. Inspect linked call instructions and destination symbol bytes.
func lratRV64CallContract(t *testing.T) string {
	t.Helper()
	var c strings.Builder
	for _, compressed := range []bool{false, true} {
		cpu, module, bodyModule := "generic_rv64+m", "RV64", "LRATRV64Bytes"
		if compressed {
			cpu, module, bodyModule = "", "RV64Compressed", "LRATRV64Compressed"
		}
		symbolBytes := lratPreflightExecutable(t, target.ArchRiscv64, "rv64", oakLRATRV64Source, cpu)
		destinations := map[uint64]string{}
		for _, name := range []string{"lrat_fits", "lrat_alloc_fits"} {
			sym, code := symbolBytes(name)
			destinations[sym.Value] = name
			proof := "fitsBytes"
			if name == "lrat_alloc_fits" {
				proof = "allocBytes"
			}
			fmt.Fprintf(&c, "example : %s = Oak.%s.%s := by decide\n", lratByteLiteral(code), bodyModule, proof)
		}
		for _, caller := range []string{"lrat_header_fits", "lrat_record_fits"} {
			sym, code := symbolBytes(caller)
			counts := map[string]int{}
			for at := 0; at < len(code); {
				if len(code)-at < 2 {
					t.Fatal("truncated instruction")
				}
				if code[at]&3 != 3 {
					at += 2
					continue
				}
				if len(code)-at < 4 {
					t.Fatal("truncated word")
				}
				upper := binary.LittleEndian.Uint32(code[at:])
				if upper&0x7f != 0x17 {
					at += 4
					continue
				}
				if len(code)-at < 8 {
					t.Fatal("truncated AUIPC pair")
				}
				lower := binary.LittleEndian.Uint32(code[at+4:])
				if lower&0x707f != 0x67 {
					at += 4
					continue
				}
				place := sym.Value + uint64(at)
				destination := uint64(int64(place)+int64(int32(upper&0xfffff000))+int64(int32(lower)>>20)) &^ 1
				name, guard := destinations[destination]
				if !guard {
					at += 8
					continue
				}
				if (upper>>7)&31 != 1 || (lower>>7)&31 != 1 || (lower>>15)&31 != 1 {
					t.Fatal("guard call does not use ra")
				}
				counts[name]++
				pair := fmt.Sprintf("(%d#32,%d#32)", upper, lower)
				kind := "fits"
				if name == "lrat_alloc_fits" {
					kind = "alloc"
				}
				fmt.Fprintf(&c, "example : Oak.RV64Relocation.pairMatches true %d#32 %d#32 = true := by decide\n", upper, lower)
				fmt.Fprintf(&c, "example (regs : Oak.RiscVCallExecution.Reg → Oak.RiscVCallExecution.X) : (Oak.RiscVCallExecution.executePatched true 1 %s ⟨%d,regs⟩).pc = %d := by rw [Oak.RiscVCallExecution.executePatched, Oak.RiscVCallExecution.pair_target_sum _ _ (by decide)]; dsimp only; decide\n", pair, place, destination)
				fmt.Fprintf(&c, "example (s : Oak.RiscVCallExecution.State) : (Oak.LRATRV64GuardCalls.%s.%sCall %s s).map Oak.RiscVCallExecution.State.pc = some (Oak.RiscVCallExecution.clearLow (s.pc + 8)) := Oak.LRATRV64GuardCalls.%s.%s_return %s s (by decide) (by decide)\n", module, kind, pair, module, kind, pair)
				// A mismatched JALR destination must fail the pair-shape check.
				fmt.Fprintf(&c, "example : Oak.RV64Relocation.pairMatches true %d#32 %d#32 = false := by decide\n", upper, lower&^0xf80|5<<7)
				// Wrong link-register fields are outside this call contract.
				fmt.Fprintf(&c, "example : ((%d#32).extractLsb' 7 5 == 1#5) = false := by decide\n", upper&^0xf80|5<<7)
				at += 8
			}
			wantAlloc := 0
			if caller == "lrat_header_fits" {
				wantAlloc = 3
			}
			if counts["lrat_fits"] != 1 || counts["lrat_alloc_fits"] != wantAlloc {
				t.Fatalf("%s guard calls: %v", caller, counts)
			}
		}
		for _, name := range []string{"fits_result", "alloc_result", "fits_return", "alloc_return", "fits_refines", "alloc_refines"} {
			fmt.Fprintf(&c, "#print axioms Oak.LRATRV64GuardCalls.%s.%s\n", module, name)
		}
	}
	return c.String()
}

// Shared production prefix and linked symbol extraction for both ISA contracts.
func lratPreflightExecutable(t *testing.T, arch, lane, unit, cpu string) func(string) (elf.Symbol, []byte) {
	t.Helper()
	source, _, ok := strings.Cut(oakLRATSource, "// lrat_true_value")
	if !ok {
		t.Fatal("preflight extraction boundary lost")
	}
	data, err := compiler.New().WithSource("lrat.oak", source+"\nmain: (): i32 = i32(0)\n").
		WithAsmUnit("lrat."+lane+".oakasm", unit).
		WithTarget(target.Target{OS: target.OSLinux, Arch: arch}).WithCPU(cpu).EmitExecutable().Get()
	if err != nil {
		t.Fatal(err)
	}
	f, err := elf.NewFile(bytes.NewReader(data))
	if err != nil {
		t.Fatal(err)
	}
	machine := elf.EM_RISCV
	if arch == target.ArchArm64 {
		machine = elf.EM_AARCH64
	}
	if f.Machine != machine || f.Type != elf.ET_EXEC {
		t.Fatal("expected linked executable for requested target")
	}
	t.Cleanup(func() { f.Close() })
	symbols, err := f.Symbols()
	if err != nil {
		t.Fatal(err)
	}
	byName := map[string]elf.Symbol{}
	for _, sym := range symbols {
		byName[sym.Name] = sym
	}
	symbolBytes := func(name string) (elf.Symbol, []byte) {
		sym, ok := byName["oak_"+name]
		if !ok || sym.Section == elf.SHN_UNDEF || int(sym.Section) >= len(f.Sections) {
			t.Fatalf("missing/invalid %s", name)
		}
		sec := f.Sections[sym.Section]
		code, e := sec.Data()
		if e != nil {
			t.Fatal(e)
		}
		if sym.Value < sec.Addr {
			t.Fatal("invalid address")
		}
		at := sym.Value - sec.Addr
		if at > uint64(len(code)) || sym.Size > uint64(len(code))-at {
			t.Fatal("invalid range")
		}
		return sym, code[at : at+sym.Size]
	}

	return symbolBytes
}
