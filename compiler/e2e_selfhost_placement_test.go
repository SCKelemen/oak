package compiler

import (
	"encoding/binary"
	"fmt"
	"math/big"
	"math/rand"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"
)

// Compare actual Oak results against a separate arbitrary-precision oracle,
// then ask Lean's kernel to check the same concrete decisions against the
// model whose universal placement laws are proved in Oak.LinkerLayout.
func TestE2ESelfHostedPlacement(t *testing.T) {
	type input struct {
		base                              uint64
		cursor, size, alignment, capacity uint32
	}
	var inputs []input
	for a := uint32(1); a <= 4096; a *= 2 {
		for _, base := range []uint64{0, 1, 65536, 65539, ^uint64(0) - 4095, ^uint64(0)} {
			for _, cursor := range []uint32{0, 1, 4095, ^uint32(0) - 3} {
				inputs = append(inputs, input{base, cursor, 4, a, ^uint32(0)})
			}
		}
	}
	inputs = append(inputs, input{65536, 12, 8, 16, 24}, input{65536, 12, 8, 16, 23},
		input{0, 0, 0, 4, 32}, input{0, 0, 4, 0, 32}, input{0, 0, 4, 3, 32},
		input{0, 0, 4, 8192, 32}, input{0, 0, ^uint32(0), 1, ^uint32(0)})
	rng := rand.New(rand.NewSource(643))
	for i := 0; i < 128; i++ {
		inputs = append(inputs, input{rng.Uint64(), rng.Uint32(), rng.Uint32(), 1 << uint(i%13), rng.Uint32()})
	}
	var oak strings.Builder
	for _, name := range []string{"native.oak", "objects.oak"} {
		data, err := os.ReadFile(filepath.Join("..", "asm", "selfhost", name))
		if err != nil {
			t.Fatal(err)
		}
		oak.Write(data)
		oak.WriteByte('\n')
	}
	oak.WriteString(`putchar: (ch: c.Int): c.Int = c.extern("putchar")
emit: (word: u32): () {
  i: u32 = 0
  while i < u32(4) { putchar(c.Int(i32_bits_u32((word >> (i * u32(8))) & u32(255))))
    i = i + u32(1) }
}
main: (): i32 {
`)
	for _, c := range inputs {
		fmt.Fprintf(&oak, "true ? { p: NativePlacement = native_place(u64(%d), u32(%d), u32(%d), u32(%d), u32(%d))\n emit(p.status)\n emit(p.start)\n emit(p.end) }\n", c.base, c.cursor, c.size, c.alignment, c.capacity)
	}
	oak.WriteString("0\n}\n")
	out, code, abnormal := buildAndRunOutput(t, "linker_placement", oak.String())
	if code != 0 || abnormal || len(out) != 12*len(inputs) {
		t.Fatalf("Oak placement exit (%d,%v), bytes %d, want %d", code, abnormal, len(out), 12*len(inputs))
	}
	var lean strings.Builder
	lean.WriteString("import Oak.LinkerLayout\nopen Oak.LinkerLayout\n")
	limit := new(big.Int).Lsh(big.NewInt(1), 64)
	for i, c := range inputs {
		r := []byte(out[i*12 : (i+1)*12])
		status, start, stop := binary.LittleEndian.Uint32(r), binary.LittleEndian.Uint32(r[4:]), binary.LittleEndian.Uint32(r[8:])
		wantStatus, wantStart, wantStop := uint32(1), uint32(0), uint32(0)
		if c.size > 0 && c.alignment > 0 && c.alignment <= 4096 && c.alignment&(c.alignment-1) == 0 {
			// Independent formula: round up the absolute address with big.Int
			// division, then subtract the base. No modulo-sum implementation.
			a := new(big.Int).SetUint64(uint64(c.alignment))
			b := new(big.Int).SetUint64(c.base)
			abs := new(big.Int).Add(b, new(big.Int).SetUint64(uint64(c.cursor)))
			abs.Add(abs, new(big.Int).Sub(a, big.NewInt(1))).Div(abs, a).Mul(abs, a)
			s := new(big.Int).Sub(abs, b)
			e := new(big.Int).Add(s, new(big.Int).SetUint64(uint64(c.size)))
			endAddress := new(big.Int).Add(b, e)
			if e.Cmp(new(big.Int).SetUint64(uint64(c.capacity))) <= 0 && endAddress.Cmp(limit) < 0 {
				wantStatus, wantStart, wantStop = 0, uint32(s.Uint64()), uint32(e.Uint64())
			}
		}
		if status != wantStatus || start != wantStart || stop != wantStop {
			t.Fatalf("case %d %+v: Oak {%d,%d,%d}, oracle {%d,%d,%d}", i, c, status, start, stop, wantStatus, wantStart, wantStop)
		}
		result := "none"
		if status == 0 {
			result = fmt.Sprintf("some (%d, %d)", start, stop)
		}
		fmt.Fprintf(&lean, "example : place %d %d %d %d %d = %s := by decide\n", c.base, c.cursor, c.size, c.alignment, c.capacity, result)
	}
	t.Logf("%d compiled Oak placement decisions match the independent oracle", len(inputs))
	lake := findLake()
	if lake == "" {
		if os.Getenv("OAK_REQUIRE_LINKER_LEAN") == "1" {
			t.Fatal("Lean correspondence required but lake unavailable")
		}
		t.Log("Lean correspondence not run: lake unavailable")
		return
	}
	root, err := filepath.Abs(filepath.Join("..", "spec", "lean"))
	if err != nil {
		t.Fatal(err)
	}
	build := exec.Command(lake, "build", "Oak.LinkerLayout")
	build.Dir = root
	if out, err := build.CombinedOutput(); err != nil {
		t.Fatalf("Lean model build: %v\n%s", err, out)
	}
	driver := filepath.Join(t.TempDir(), "LinkerPlacementPins.lean")
	if err := os.WriteFile(driver, []byte(lean.String()), 0600); err != nil {
		t.Fatal(err)
	}
	run := exec.Command(lake, "env", "lean", driver)
	run.Dir = root
	if out, err := run.CombinedOutput(); err != nil {
		t.Fatalf("Lean correspondence: %v\n%s", err, out)
	}
}
