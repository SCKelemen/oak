package encoding_test

import (
	"bytes"
	"math"
	"math/rand"
	"testing"

	"github.com/SCKelemen/oak/wasm/check"
	"github.com/SCKelemen/oak/wasm/encoding"
)

func TestInstructionRoundTrip(t *testing.T) {
	values := []int64{math.MinInt64, math.MinInt32 - 1, math.MinInt32, -8193, -8192, -65, -64, -1, 0, 1, 63, 64, 65, 126, 127, 128, 8191, 8192, math.MaxInt32, math.MaxInt32 + 1, math.MaxUint32, math.MaxUint32 + 1, math.MaxInt64}
	rng := rand.New(rand.NewSource(20261006))
	for i := 0; i < 64; i++ {
		values = append(values, int64(rng.Uint64()))
	}
	accepted := 0
	for op := 0; op < 256; op++ {
		for _, v := range values {
			ins := encoding.Instruction{Opcode: byte(op), Immediate: v}
			// An error must leave even spare backing-array capacity untouched.
			storage := bytes.Repeat([]byte{0xa5}, 32)
			got, err := encoding.AppendInstruction(storage[:2], ins)
			if err != nil {
				if !bytes.Equal(storage, bytes.Repeat([]byte{0xa5}, 32)) || len(got) != 2 {
					t.Fatalf("failed encoding mutated output: %v", ins)
				}
				continue
			}
			accepted++
			encoded := append(bytes.Clone(got[2:]), 0xff, 0x42)
			decoded, n, err := check.DecodeInstruction(encoded)
			if err != nil || decoded.Opcode != ins.Opcode || decoded.Immediate != v || n != len(got)-2 {
				t.Fatalf("%v -> %x -> %v/%d: %v", ins, got[2:], decoded, n, err)
			}
			for end := 0; end < n; end++ {
				if _, consumed, err := check.DecodeInstruction(encoded[:end]); err == nil || consumed != 0 {
					t.Fatalf("accepted truncated instruction %x", encoded[:end])
				}
			}
		}
	}
	t.Logf("checked %d accepted instruction/immediate combinations and all refusals", accepted)
}

func TestInstructionKnownBytes(t *testing.T) {
	for _, tt := range []struct {
		instruction encoding.Instruction
		bytes       []byte
	}{
		{encoding.Instruction{0x41, -624485}, []byte{0x41, 0x9b, 0xf1, 0x59}},
		{encoding.Instruction{0x20, 624485}, []byte{0x20, 0xe5, 0x8e, 0x26}},
		{encoding.Instruction{0x41, math.MinInt32}, []byte{0x41, 0x80, 0x80, 0x80, 0x80, 0x78}},
		{encoding.Instruction{0x42, math.MinInt64}, []byte{0x42, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x7f}},
		{encoding.Instruction{0x0c, math.MaxUint32}, []byte{0x0c, 0xff, 0xff, 0xff, 0xff, 0x0f}},
		{encoding.Instruction{0x04, 0x7e}, []byte{0x04, 0x7e}},
	} {
		got, err := encoding.Assemble([]encoding.Instruction{tt.instruction})
		if err != nil || !bytes.Equal(got, tt.bytes) {
			t.Fatalf("%v: %x, want %x: %v", tt.instruction, got, tt.bytes, err)
		}
	}
	if got, err := encoding.Assemble([]encoding.Instruction{{Opcode: 1}, {Opcode: 0xff}}); err == nil || got != nil {
		t.Fatal("assembly exposed partial bytes", got, err)
	}
}

func TestInstructionDecoderRefusalsAndPadding(t *testing.T) {
	for _, bad := range [][]byte{
		nil, {0xff}, {0x50}, {0x02, 0}, {0x02, 0x7d},
		{0x20, 0xff, 0xff, 0xff, 0xff, 0x10},
		{0x20, 0x80, 0x80, 0x80, 0x80, 0x80, 0},
		{0x41, 0xff, 0xff, 0xff, 0xff, 0x0f},
		{0x42, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 1},
	} {
		if ins, n, err := check.DecodeInstruction(bad); err == nil || n != 0 || ins != (check.Instruction{}) {
			t.Fatalf("malformed bytes %x: %v/%d, %v", bad, ins, n, err)
		}
	}
	for _, padded := range [][]byte{{0x20, 0x80, 0x00, 0xff}, {0x41, 0xff, 0x7f, 0xff}} {
		ins, n, err := check.DecodeInstruction(padded)
		want := int64(0)
		if padded[0] == 0x41 {
			want = -1
		}
		if err != nil || ins.Immediate != want || n != 3 {
			t.Fatalf("legal padding %x: %v/%d, %v", padded, ins, n, err)
		}
	}
}

func FuzzInstructionDecode(f *testing.F) {
	for _, seed := range [][]byte{{0x41, 0x7f}, {0x20, 0xff, 0xff, 0xff, 0xff, 0x0f}, {0x04, 0x40}, {0xff}} {
		f.Add(seed)
	}
	f.Fuzz(func(t *testing.T, data []byte) {
		i, n, err := check.DecodeInstruction(data)
		if err != nil {
			return
		}
		if n < 1 || n > 11 || n > len(data) {
			t.Fatalf("invalid consumption %d", n)
		}
		canonical, err := encoding.Assemble([]encoding.Instruction{{Opcode: i.Opcode, Immediate: i.Immediate}})
		if err != nil {
			t.Fatal(err)
		}
		j, m, err := check.DecodeInstruction(canonical)
		if err != nil || i != j || m != len(canonical) {
			t.Fatalf("unstable decoding: %v %v %v", i, j, err)
		}
	})
}
