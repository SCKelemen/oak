package main

import (
	"bytes"
	"debug/elf"
	"fmt"
	"strings"
	"testing"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/compiler"
	"github.com/SCKelemen/oak/target"
)

// Pin the proof to actual encoded function bytes and independently extracted
// ELF symbol contents. No disassembly or expected words come from the encoder.
func lratRV64ByteContract(t *testing.T) string {
	return lratRV64ByteProfile(t, false) + lratRV64ByteProfile(t, true)
}

func lratRV64ByteProfile(t *testing.T, compressed bool) string {
	t.Helper()
	literal := func(code []byte) string {
		items := make([]string, len(code))
		for i, b := range code {
			items[i] = fmt.Sprintf("%d#8", b)
		}
		return "[" + strings.Join(items, ",") + "]"
	}
	encode := func(source string) map[string][]byte {
		unit, errs := asm.ParseUnit("lrat.rv64.oakasm", source)
		if len(errs) != 0 {
			t.Fatal(errs)
		}
		result := map[string][]byte{}
		for _, fn := range unit.Functions {
			fn.Compressed = compressed
			code, relocs, err := asm.EncodeFunction(fn)
			if err != nil || len(relocs) != 0 {
				t.Fatalf("guard encoding: %v, %v", err, relocs)
			}
			result[fn.Name] = code
		}
		return result
	}
	encoded := encode(oakLRATRV64Source)
	comp := compiler.New().WithSource("lrat.oak", oakLRATSource+"\nmain: (): i32 { i32(0) }\n").
		WithAsmUnit("lrat.rv64.oakasm", oakLRATRV64Source).
		WithTarget(target.Target{OS: target.OSLinux, Arch: target.ArchRiscv64})
	if !compressed {
		comp = comp.WithCPU("generic_rv64+m")
	}
	object, err := comp.EmitAsmObject(asm.ELF).Get()
	if err != nil {
		t.Fatal(err)
	}
	f, err := elf.NewFile(bytes.NewReader(object))
	if err != nil {
		t.Fatal(err)
	}
	defer f.Close()
	symbols, err := f.Symbols()
	if err != nil {
		t.Fatal(err)
	}
	var contract strings.Builder
	module := "Oak.LRATRV64Bytes"
	returnSize := 4
	if compressed {
		module = "Oak.LRATRV64Compressed"
		returnSize = 2
	}
	fmt.Fprintf(&contract, "\nsection\nopen %s Oak.RiscVCallExecution\n", module)
	for name, code := range encoded {
		found := false
		for _, sym := range symbols {
			if sym.Name != "oak_"+name {
				continue
			}
			if found || int(sym.Section) >= len(f.Sections) || sym.Section == elf.SHN_UNDEF {
				t.Fatal("invalid guard symbol")
			}
			found = true
			section := f.Sections[sym.Section]
			data, err := section.Data()
			if err != nil {
				t.Fatal(err)
			}
			if sym.Value < section.Addr {
				t.Fatal("invalid symbol address")
			}
			start := sym.Value - section.Addr
			if start > uint64(len(data)) || sym.Size > uint64(len(data))-start {
				t.Fatal("invalid symbol range")
			}
			if !bytes.Equal(data[start:start+sym.Size], code) {
				t.Fatalf("ELF bytes differ for %s: got %x want %x", name, data[start:start+sym.Size], code)
			}
		}
		if !found {
			t.Fatalf("missing %s", name)
		}
		proof := "fitsBytes"
		if name == "lrat_alloc_fits" {
			proof = "allocBytes"
		}
		fmt.Fprintf(&contract, "example : %s = %s := by decide\n", literal(code), proof)
		// Truncation and a corrupt final RET must be refused by execution itself.
		fmt.Fprintf(&contract, "example : (executeBytes %s ⟨0, fun _ => 0⟩).isNone = true := by decide\n", literal(code[:len(code)-1]))
		bad := append([]byte(nil), code...)
		bad[len(bad)-returnSize] = 0
		fmt.Fprintf(&contract, "example : (executeBytes %s ⟨0, fun _ => 0⟩).isNone = true := by decide\n", literal(bad))
		trailing := append(append([]byte(nil), code...), code[len(code)-returnSize:]...)
		fmt.Fprintf(&contract, "example : (executeBytes %s ⟨0, fun _ => 0⟩).isNone = true := by decide\n", literal(trailing))
	}
	mutations := []struct {
		old, new, name, state string
		want                  int
	}{
		{"li t0, 1073741823", "li t0, 1073741824", "lrat_alloc_fits", "fun r => if r = 10 then 1073741823 else 0", 1},
		{"  srli a0, a0, 32\n", "", "lrat_alloc_fits", "fun r => if r = 10 then 1 else 0", 0},
		{"sltu a0, t1, a1", "sltu a0, a1, t1", "lrat_fits", "fun r => if r = 12 then 1 else 0", 0},
	}
	for _, m := range mutations {
		if !strings.Contains(oakLRATRV64Source, m.old) {
			t.Fatal("mutation site lost")
		}
		bad := encode(strings.ReplaceAll(oakLRATRV64Source, m.old, m.new))[m.name]
		good := encoded[m.name]
		fmt.Fprintf(&contract, "example : (executeBytes %s ⟨0, %s⟩).map (fun s => read s 10) = some %d := by decide\n", literal(bad), m.state, m.want)
		fmt.Fprintf(&contract, "example : (executeBytes %s ⟨0, %s⟩).map (fun s => read s 10) = some %d := by decide\n", literal(good), m.state, 1-m.want)
	}
	extra := `
example (s : State) (h : (executeBytes fitsBytes s).map (fun out => read out 10) = some 1) :
 ((read s 10).truncate 32).toNat + ((read s 11).truncate 32).toNat ≤ ((read s 12).truncate 32).toNat := fits_bytes_sound s h
example (s : State) (h : (executeBytes allocBytes s).map (fun out => read out 10) = some 1) :
 (((read s 10).truncate 32).toNat + 1) * 4 < 4294967296 := alloc_bytes_sound s h
#print axioms Oak.LRATRV64Bytes.fits_bytes_sound
#print axioms Oak.LRATRV64Bytes.alloc_bytes_sound
#print axioms Oak.LRATRV64Bytes.fits_return
#print axioms Oak.LRATRV64Bytes.alloc_return
#print axioms Oak.LRATRV64Bytes.fits_frame
#print axioms Oak.LRATRV64Bytes.alloc_frame
`
	if compressed {
		extra = strings.ReplaceAll(extra, "Oak.LRATRV64Bytes", module)
		extra += `
example : expand 0x0000 = none := by decide
example : expand 0x1002 = none := by decide
example : expand 0x2001 = none := by decide
example : expand 0x9002 = none := by decide
example : decode [0x13, 0x15] = none := by decide
example (s : State) : (advance (0x02051513, 2) s).map State.pc = some (s.pc + 2) := by rfl
example (s : State) : (advance (0x02035313, 4) s).map State.pc = some (s.pc + 4) := by rfl
`
	}
	contract.WriteString(extra)
	contract.WriteString("\nend\n")
	return contract.String()
}
