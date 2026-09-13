package asm

import (
	"bytes"
	"encoding/binary"
	"strings"
	"testing"
)

// RVC (docs/spec/94-assembler.md §9): under `option rvc` the encoder
// chooses the 16-bit form GNU as chooses, for every compressible spelling
// of the lane and for the branches whose offsets fit, so the bytes agree
// with `riscv64-elf-as -march=rv64imc`. The body mixes compressible and
// uncompressible operands of each form, a branch within the compressed
// range and one beyond it (sixty-six four-byte instructions apart), and a
// 32-bit li whose lui half compresses.
const rv64RVCDecl = "cenc: (v: [*]u32, k: u32) -> u32"

func rv64RVCBody() string {
	var b strings.Builder
	b.WriteString(`
  bind a0, a1 = v
  bind a2 = k
  clobber t0, t1, t2, a3, a4, a5
  option rvc
  frame 32
  addi sp, sp, -32
  sd s0, 24(sp)
  sw a2, 20(sp)
  lw a3, 20(sp)
  ld s0, 24(sp)
  addi a0, a0, 5
  addi a0, a0, 100
  addi a3, sp, 16
  li t0, 0
  li t0, 40
  li t1, 74565
  li a4, -7
  mv s0, t0
  nop
  slli t1, t1, 7
  srli t1, a0, 3
  srli a3, a3, 3
  srai a4, a4, 2
  andi a4, a4, 15
  andi t0, t0, 15
  add t0, t0, t1
  add t0, t1, t0
  add t0, t1, t2
  sub a3, a3, a4
  xor a3, a4, a3
  or a3, a3, t0
  and a4, a4, a3
  addw t0, a0, a1
  subw a3, a3, a4
  addw a4, a3, a4
  addiw a3, a3, 1
  sext.w a4, a4
  lw a4, 8(a1)
  lw a4, 128(a1)
  ld a5, 16(a1)
  sw a4, 4(a1)
  sd a5, 8(a1)
  lw t2, 0(a1)
  lui a4, 5
  lui a5, 40
  lui sp, 5
  beq a0, zero, near
  bne zero, a3, near
  beq a1, a2, near
  beqz t0, near
near:
  j far
`)
	for i := 0; i < 66; i++ {
		b.WriteString("  mul t0, a0, a1\n")
	}
	b.WriteString(`far:
  bnez a4, near
  beqz a5, done
  j near
done:
  add a0, t1, s0
  addi sp, sp, 32
  ret`)
	return b.String()
}

func TestRV64RVCEncoderAgreesWithGNUAs(t *testing.T) {
	requireRV64Tools(t, "riscv64-elf-as", "riscv64-elf-objcopy")
	fn, errs := rv64Unit(t, rv64RVCDecl, rv64RVCBody())
	if len(errs) != 0 {
		t.Fatal(errs)
	}
	if !fn.Compressed {
		t.Fatal("option rvc not recorded")
	}
	ours, _, err := EncodeFunction(fn)
	if err != nil {
		t.Fatal(err)
	}
	theirs := gnuAssembleWith(t, rv64GNUText(fn), "rv64imc", "lp64")
	if !bytes.Equal(ours, theirs) {
		offset := 0
		for offset < len(ours) && offset < len(theirs) && ours[offset] == theirs[offset] {
			offset++
		}
		t.Fatalf("encodings differ at byte %d (ours %d bytes, GNU as %d): ours %x, GNU as %x", offset, len(ours), len(theirs), ours[offset:min(offset+8, len(ours))], theirs[offset:min(offset+8, len(theirs))])
	}
	// The same function without the option is the four-byte layout.
	plain, errs := rv64Unit(t, rv64RVCDecl, strings.Replace(rv64RVCBody(), "  option rvc\n", "", 1))
	if len(errs) != 0 {
		t.Fatal(errs)
	}
	wide, _, err := EncodeFunction(plain)
	if err != nil {
		t.Fatal(err)
	}
	if len(wide) <= len(ours) || len(wide)%4 != 0 {
		t.Fatalf("uncompressed %d bytes, compressed %d", len(wide), len(ours))
	}
}

// The strip-mined sum under option rvc: checker-clean, so it runs in the
// differentials compressed and carries the object flag.
const rv64RVCSumDecl = "vsumc: (v: []u32, k: u32) -> u32"
const rv64RVCSumBody = `
  bind a0, a1 = v
  bind a2 = k
  clobber t0, t1, t2, t3
  option rvc
  slli t1, a1, 32
  srli t1, t1, 32
  li t0, 0
  mv t3, a2
loop:
  bgeu t0, t1, done
  slli t2, t0, 2
  add t2, a0, t2
  lw t2, 0(t2)
  addw t3, t3, t2
  addi t0, t0, 1
  j loop
done:
  mv a0, t3
  ret`

// The compressed object flags RVC in the ELF header, and the checker sees
// the same unit whether or not it is compressed.
func TestRV64RVCObjectFlag(t *testing.T) {
	fn, errs := rv64Unit(t, rv64RVCSumDecl, rv64RVCSumBody)
	if len(errs) != 0 {
		t.Fatal(errs)
	}
	sig, _ := parseSignature(rv64RVCSumDecl)
	if findings := Check(fn, sig, nil); len(findings) != 0 {
		t.Fatalf("checker: %v", findings)
	}
	encoded, err := EncodeFunctions([]*Function{fn}, func(s string) string { return s })
	if err != nil {
		t.Fatal(err)
	}
	object, err := WriteObjectWith(ELF, encoded, ObjectOptions{})
	if err != nil {
		t.Fatal(err)
	}
	if flags := binary.LittleEndian.Uint32(object[48:52]); flags&0x1 == 0 {
		t.Fatalf("e_flags %#x lacks EF_RISCV_RVC", flags)
	}
	// option applies to rv64 units only, and takes rvc or norvc.
	if _, errs := ParseUnit("u.arm64.oakasm", "f: (a: u32) -> u32 = {\n  bind w0 = a\n  option rvc\n  ret\n}\n"); len(errs) == 0 {
		t.Error("option rvc on an arm64 unit parsed")
	}
	if _, errs := rv64Unit(t, rv64RVCDecl, "  option compress\n  ret"); len(errs) == 0 {
		t.Error("option compress parsed")
	}
	// Compression is an encoding: the verifier proves the compressed unit
	// against the same Oak body as the four-byte one.
	v := rv64Verify(t, rv64RVCSumDecl, "{\n  total: u32 = k\n  i: u32 = u32(0)\n  while i < len(v) {\n    total = total + v[i]\n    i = i + u32(1)\n  }\n  total\n}", rv64RVCSumBody)
	if v.Kind != VerdictProven {
		t.Errorf("compressed sum: %s (%s)", v.Kind, v.Message)
	}
}
