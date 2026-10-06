package asm

import (
	"bytes"
	"encoding/binary"
	"fmt"
	"math/big"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"
)

func TestRV64PCRelMatchesLean(t *testing.T) {
	var pins []string
	for _, call := range []bool{false, true} {
		kind := "riscv_pcrel"
		rd := uint32(31)
		op := uint32(0x13)
		if call {
			kind = "riscv_call_plt"
			rd = 1
			op = 0x67
		}
		first, second := rd<<7|0x17, rd<<15|rd<<7|op
		for _, d := range []int64{-2147485697, -2147485696, -2147483648, -4097, -2049, -2048, -1, 0, 1, 2047, 2048, 4096, 2147481598, 2147481599, 2147481600, 2147483647} {
			place := uint64(1) << 33
			target := uint64(int64(place) + d)
			want := d >= -2147485696 && d <= 2147481599 && (!call || target&1 == 0)
			patch, err := patchRV64PCRel(kind, first, second, place, target)
			if (err == nil) != want {
				t.Fatalf("%s delta %d: patch %+v, err %v, want %v", kind, d, patch, err, want)
			}
			result := "none"
			if err == nil {
				result = fmt.Sprintf("some (0x%08x#32, 0x%08x#32)", patch.upper, patch.lower)
				// Independent arbitrary-precision architectural target calculation.
				hi := big.NewInt(int64(int32(patch.upper & 0xfffff000)))
				lo := big.NewInt(int64(int32(patch.lower) >> 20))
				reached := new(big.Int).Add(new(big.Int).SetUint64(place), new(big.Int).Add(hi, lo))
				if reached.Cmp(new(big.Int).SetUint64(target)) != 0 {
					t.Fatalf("%s %d: decoded %s, target %d", kind, d, reached, target)
				}
				if patch.upper&0xfff != first&0xfff || patch.lower&0xfffff != second&0xfffff {
					t.Fatal("changed fixed fields")
				}
			} else if patch != (rv64PCRelPatch{}) {
				t.Fatal("refusal returned a partial patch")
			}
			pins = append(pins, fmt.Sprintf("example : relocate %v 0x%08x#32 0x%08x#32 %d %d = %s := by decide", call, first, second, place, target, result))
		}
	}
	source := "import Oak.RV64Relocation\nnamespace Oak.RV64Relocation\n" + strings.Join(pins, "\n") + "\nend Oak.RV64Relocation\n"
	path := filepath.Join(t.TempDir(), "RV64RelocationPins.lean")
	if err := os.WriteFile(path, []byte(source), 0600); err != nil {
		t.Fatal(err)
	}
	lake, err := exec.LookPath("lake")
	if err != nil {
		t.Skip("lake not on PATH; formal CI checks these production pins")
	}
	buildLeanImports(t, lake, path)
	cmd := exec.Command(lake, "env", "lean", path)
	cmd.Dir = filepath.Join("..", "spec", "lean")
	if out, err := cmd.CombinedOutput(); err != nil {
		t.Fatalf("Lean RV64 pins: %v\n%s", err, out)
	}
}

func TestRV64PCRelRejectsMalformedPairs(t *testing.T) {
	for _, tc := range []struct {
		first, second uint32
		place, target uint64
	}{
		{0x97, 0x80e7, 1, 4}, {0x97, 0x80e7, 0, 3},
		{0x97, 0x80e7, ^uint64(0) - 3, ^uint64(0) - 3},
		{0x97, 0x80e7, 0, ^uint64(0) - 7},
		{0x97, 0x80e7, ^uint64(0) - 7, 0},
		{0x93, 0x80e7, 0, 4}, {0x97, 0x90e7, 0, 4},
		{0x97, 0x8067, 0, 4}, {0x97, 0x100e7, 0, 4},
		{0x17, 0x67, 0, 4},
	} {
		text := binary.LittleEndian.AppendUint32(nil, tc.first)
		text = binary.LittleEndian.AppendUint32(text, tc.second)
		before := bytes.Clone(text)
		layout := &textLayout{text: text, relocs: []placedReloc{{kind: "riscv_call_plt", symbol: "target"}}}
		if err := resolveRelocations(layout, tc.place, map[string]uint64{"target": tc.target}); err == nil {
			t.Fatalf("accepted %+v", tc)
		}
		if !bytes.Equal(text, before) {
			t.Fatal("mutated a refused pair")
		}
	}
	// Complete high-address pairs and RVC halfword addresses remain valid.
	for _, place := range []uint64{2, ^uint64(0) - 7} {
		if _, err := patchRV64PCRel("riscv_call_plt", 0x97, 0x80e7, place, place); err != nil {
			t.Fatal(err)
		}
	}
}
