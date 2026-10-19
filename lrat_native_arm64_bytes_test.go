package main

import (
	"encoding/binary"
	"fmt"
	"strings"
	"testing"

	"github.com/SCKelemen/oak/target"
)

func lratARM64ByteContract(t *testing.T) string {
	t.Helper()
	encode := func(source string) map[string][]byte { return lratEncodeGuards(t, "arm64", source, false) }
	encoded := encode(oakLRATArm64Source)
	lratCheckGuardELF(t, target.ArchArm64, "arm64", oakLRATArm64Source, "", encoded)
	var c strings.Builder
	c.WriteString("\nsection\nopen Oak.LRATARM64Bytes\nopen Oak.AArch64BitwiseFunction (readW)\n")
	state := "⟨fun _ => 0, 0, 0, ⟨false,false,false,false⟩⟩"
	for name, code := range encoded {
		proof := "fitsBytes"
		if name == "lrat_alloc_fits" {
			proof = "allocBytes"
		}
		fmt.Fprintf(&c, "example : %s = %s := by decide\n", lratByteLiteral(code), proof)
		controls := [][]byte{code[:len(code)-1], append(append([]byte(nil), code...), code[len(code)-4:]...)}
		bad := append([]byte(nil), code...)
		binary.LittleEndian.PutUint32(bad[len(bad)-4:], 0xd65f0000) // RET X0
		controls = append(controls, bad)
		for _, bad := range controls {
			fmt.Fprintf(&c, "example : (executeBytes %s %s).isNone = true := by decide\n", lratByteLiteral(bad), state)
		}
	}
	mutations := []struct {
		old, new, name, regs string
		want                 int
	}{
		{"cset w0, ls", "cset w0, lo", "lrat_fits", "fun _ => 0", 0},
		{"#1073741823", "#1073741824", "lrat_alloc_fits", "fun r => if r = 0 then 1073741823 else 0", 1},
	}
	for _, m := range mutations {
		if !strings.Contains(oakLRATArm64Source, m.old) {
			t.Fatal("mutation site lost")
		}
		bad := encode(strings.Replace(oakLRATArm64Source, m.old, m.new, 1))[m.name]
		for _, test := range []struct {
			code []byte
			want int
		}{{bad, m.want}, {encoded[m.name], 1 - m.want}} {
			fmt.Fprintf(&c, "example : (executeBytes %s ⟨%s,0,0,⟨true,true,true,true⟩⟩).map (fun s => s.regs 0) = some %d := by decide\n", lratByteLiteral(test.code), m.regs, test.want)
		}
	}
	// A 64-bit CMP or shifted SUB must not silently enter the W-register proof.
	for _, m := range []struct {
		offset int
		mask   uint32
	}{{0, 0x80000000}, {8, 0x400}} {
		bad := append([]byte(nil), encoded["lrat_fits"]...)
		word := binary.LittleEndian.Uint32(bad[m.offset:])
		binary.LittleEndian.PutUint32(bad[m.offset:], word|m.mask)
		fmt.Fprintf(&c, "example : (executeBytes %s %s).isNone = true := by decide\n", lratByteLiteral(bad), state)
	}
	c.WriteString(`
example (s : State) (h : (executeBytes fitsBytes s).map (fun out => out.regs 0) = some 1) :
 (readW s.regs 0).toNat + (readW s.regs 1).toNat ≤ (readW s.regs 2).toNat := fits_bytes_sound s h
example (s : State) (h : (executeBytes allocBytes s).map (fun out => out.regs 0) = some 1) :
 ((readW s.regs 0).toNat + 1) * 4 < 4294967296 := alloc_bytes_sound s h
example (s : State) : (run fitsWords s).map State.pc = some (s.regs 30) := fits_return s
example (s : State) : (run allocWords s).map State.sp = some s.sp := alloc_sp s
#print axioms Oak.LRATARM64Bytes.fits_bytes_sound
#print axioms Oak.LRATARM64Bytes.alloc_bytes_sound
#print axioms Oak.LRATARM64Bytes.fits_return
#print axioms Oak.LRATARM64Bytes.alloc_return
#print axioms Oak.LRATARM64Bytes.fits_frame
#print axioms Oak.LRATARM64Bytes.alloc_frame
#print axioms Oak.LRATARM64Bytes.fits_sp
#print axioms Oak.LRATARM64Bytes.alloc_sp
end
`)
	return c.String()
}
