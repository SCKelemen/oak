package main

import (
	"encoding/binary"
	"fmt"
	"strings"
	"testing"

	"github.com/SCKelemen/oak/target"
)

func lratARM64CallContract(t *testing.T) string {
	t.Helper()
	symbolBytes := lratPreflightExecutable(t, target.ArchArm64, "arm64", oakLRATArm64Source, "")
	var c strings.Builder
	destinations := map[uint64]string{}
	for _, name := range []string{"lrat_fits", "lrat_alloc_fits"} {
		sym, code := symbolBytes(name)
		destinations[sym.Value] = name
		proof := "fitsBytes"
		if name == "lrat_alloc_fits" {
			proof = "allocBytes"
		}
		fmt.Fprintf(&c, "example : %s = Oak.LRATARM64Bytes.%s := by decide\n", lratByteLiteral(code), proof)
	}
	for _, caller := range []string{"lrat_header_fits", "lrat_record_fits"} {
		sym, code := symbolBytes(caller)
		if len(code)%4 != 0 {
			t.Fatal("truncated ARM64 instruction")
		}
		counts := map[string]int{}
		for at := 0; at < len(code); at += 4 {
			word := binary.LittleEndian.Uint32(code[at:])
			if word&0xfc000000 != 0x94000000 {
				continue
			}
			place := sym.Value + uint64(at)
			destination := uint64(int64(place) + int64(int32(word<<6)>>4))
			name, guard := destinations[destination]
			if !guard {
				continue
			}
			counts[name]++
			kind := "fits"
			if name == "lrat_alloc_fits" {
				kind = "alloc"
			}
			fmt.Fprintf(&c, "example : %d#32 &&& 0xfc000000#32 = 0x94000000#32 := by decide\n", word)
			fmt.Fprintf(&c, "example (s : Oak.LRATARM64Bytes.State) : (Oak.LRATARM64GuardCalls.transfer %d#32 {s with pc := %d}).pc = %d := by unfold Oak.LRATARM64GuardCalls.transfer; dsimp only; decide\n", word, place, destination)
			fmt.Fprintf(&c, "example (s : Oak.LRATARM64Bytes.State) : (Oak.LRATARM64GuardCalls.%sCall %d#32 s).map Oak.LRATARM64Bytes.State.pc = some (s.pc + 4) := Oak.LRATARM64GuardCalls.%s_return %d#32 s (by decide)\n", kind, word, kind, word)
			// B has the same displacement but does not write X30; BR/BLR are
			// outside this direct-call contract as well.
			for _, bad := range []uint32{word &^ 0x80000000, 0xd61f0000, 0xd63f0000} {
				fmt.Fprintf(&c, "example (s : Oak.LRATARM64Bytes.State) : Oak.LRATARM64GuardCalls.enter %d#32 s = none := by simp [Oak.LRATARM64GuardCalls.enter]\n", bad)
			}
		}
		want := 0
		if caller == "lrat_header_fits" {
			want = 3
		}
		if counts["lrat_fits"] != 1 || counts["lrat_alloc_fits"] != want {
			t.Fatalf("%s guard calls: %v", caller, counts)
		}
	}
	for _, name := range []string{"enter_eq", "transfer_arguments", "fits_result", "alloc_result", "fits_return", "alloc_return", "fits_sp", "alloc_sp", "fits_refines", "alloc_refines"} {
		fmt.Fprintf(&c, "#print axioms Oak.LRATARM64GuardCalls.%s\n", name)
	}
	return c.String()
}
