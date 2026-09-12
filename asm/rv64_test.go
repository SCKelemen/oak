package asm

import (
	"bytes"
	"encoding/binary"
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"
)

// The RV64 lane (docs/spec/94-assembler.md §9): parsing, the seam
// checker, the verifier, the encoder against GNU as, the ELF writer, and
// the C emitter. The differential tests skip without the riscv64-elf
// toolchain.

func rv64Unit(t *testing.T, decl, body string) (*Function, []error) {
	t.Helper()
	unit, errs := ParseUnit("u.rv64.oakasm", decl+" = {\n"+body+"\n}\n")
	if unit == nil || len(unit.Functions) == 0 {
		return nil, errs
	}
	return unit.Functions[0], errs
}

func rv64Check(t *testing.T, decl, body string) []string {
	t.Helper()
	fn, errs := rv64Unit(t, decl, body)
	if len(errs) != 0 {
		t.Fatalf("parse: %v", errs)
	}
	sig, err := parseSignature(decl)
	if err != nil {
		t.Fatal(err)
	}
	return Check(fn, sig, map[string]bool{"helper": true})
}

func rv64Verify(t *testing.T, decl, oakBody, asmBody string) Verdict {
	t.Helper()
	fn, errs := rv64Unit(t, decl, asmBody)
	if len(errs) != 0 {
		t.Fatalf("parse: %v", errs)
	}
	sig, err := parseSignature(decl)
	if err != nil {
		t.Fatal(err)
	}
	if findings := Check(fn, sig, nil); len(findings) != 0 {
		t.Fatalf("checker: %v", findings)
	}
	spec, err := parseSignatureWithBody(decl + " = " + oakBody)
	if err != nil {
		t.Fatal(err)
	}
	return Verify(fn, sig, spec.Body)
}

const rv64AddDecl = "add_rv: (left, right: u32) -> u32"
const rv64AddBody = `
  bind a0 = left
  bind a1 = right
  addw a0, a0, a1
  ret`

func TestRV64ParseLane(t *testing.T) {
	fn, errs := rv64Unit(t, rv64AddDecl, rv64AddBody)
	if len(errs) != 0 {
		t.Fatal(errs)
	}
	if fn.Arch != ArchRV64 {
		t.Fatalf("arch %q from the unit path", fn.Arch)
	}
	if got := fn.Bindings[0].Register; got.Class != ClassRV64X || got.Num != 10 {
		t.Fatalf("a0 parsed as %+v", got)
	}
	// The directive form, and sp as the frame register.
	unit, errs := ParseUnit("u.oakasm", "f: (x: u64) -> u64 = {\n  arch rv64\n  bind a0 = x\n  frame 16\n  addi sp, sp, -16\n  sd a0, 8(sp)\n  ld a0, 8(sp)\n  addi sp, sp, 16\n  ret\n}\n")
	if len(errs) != 0 {
		t.Fatal(errs)
	}
	if unit.Functions[0].Arch != ArchRV64 {
		t.Fatal("arch directive not honored")
	}
	mem := unit.Functions[0].Items[2].(Instruction).Operands[1].(Memory)
	if mem.Base.Class != ClassSP || mem.Offset != 8 {
		t.Fatalf("8(sp) parsed as %+v", mem)
	}
	// call stays one item; the encoder spends two words on it.
	unit, errs = ParseUnit("u.rv64.oakasm", "g: (x: u64) -> u64 = {\n  bind a0 = x\n  call helper\n  ret\n}\n")
	if len(errs) != 0 {
		t.Fatal(errs)
	}
	if call := unit.Functions[0].Items[0].(Instruction); call.Mnemonic != "call" || rv64Words(call) != 2 {
		t.Fatalf("call parsed as %+v", call)
	}
	// Rejections at parse time.
	for _, bad := range []string{"  vadd.vv v0, v1, v2", "  add a0, a0", "  ld a0, [sp]", "  addi a0, a0, a1", "  x32 a0"} {
		if _, errs := rv64Unit(t, rv64AddDecl, "  bind a0 = left\n  bind a1 = right\n"+bad+"\n  ret"); len(errs) == 0 {
			t.Errorf("%q parsed", strings.TrimSpace(bad))
		}
	}
}

func TestRV64CheckerAccepts(t *testing.T) {
	cases := map[string][2]string{
		"add": {rv64AddDecl, rv64AddBody},
		"frame save/restore": {"acc: (a, b: u64) -> u64", `
  bind a0 = a
  bind a1 = b
  frame 16
  addi sp, sp, -16
  sd s0, 8(sp)
  mv s0, a0
  add a0, s0, a1
  ld s0, 8(sp)
  addi sp, sp, 16
  ret`},
		"counted loop with clobber": {"trip: (x, y: u32) -> u32", `
  bind a0 = x
  bind a1 = y
  clobber t0
  li t0, 3
loop:
  addw a0, a0, a1
  addi t0, t0, -1
  bnez t0, loop
  ret`},
		"comparison branch": {"pick: (x, y: u64) -> u64", `
  bind a0 = x
  bind a1 = y
  bltu a0, a1, small
  mv a0, a1
small:
  ret`},
		"call with ra saved": {"twice: (x: u64) -> u64", `
  bind a0 = x
  frame 16
  addi sp, sp, -16
  sd ra, 8(sp)
  call helper
  ld ra, 8(sp)
  addi sp, sp, 16
  ret`},
		"span pair": {"first: (v: [*]u32) -> u32", `
  bind a0, a1 = v
  mv a0, a1
  ret`},
	}
	for name, c := range cases {
		if findings := rv64Check(t, c[0], c[1]); len(findings) != 0 {
			t.Errorf("%s: %v", name, findings)
		}
	}
}

func TestRV64CheckerRejects(t *testing.T) {
	cases := map[string][3]string{
		"unbound write":           {rv64AddDecl, "  bind a0 = left\n  bind a1 = right\n  add t1, a0, a1\n  mv a0, t1\n  ret", "write to t1"},
		"wrong contract register": {rv64AddDecl, "  bind a1 = left\n  bind a0 = right\n  ret", "must be bound to a0"},
		"unbound parameter":       {rv64AddDecl, "  bind a0 = left\n  ret", "right is not bound"},
		"ret inside frame":        {"f: (x: u64) -> u64", "  bind a0 = x\n  frame 16\n  addi sp, sp, -16\n  ret", "sp displacement 16"},
		"frame overflow":          {"f: (x: u64) -> u64", "  bind a0 = x\n  frame 16\n  addi sp, sp, -16\n  sd a0, 16(sp)\n  addi sp, sp, 16\n  ret", "outside the declared frame"},
		"misaligned slot":         {"f: (x: u64) -> u64", "  bind a0 = x\n  frame 16\n  addi sp, sp, -16\n  sd a0, 4(sp)\n  addi sp, sp, 16\n  ret", "not aligned"},
		"callee-saved unsaved":    {"f: (x: u64) -> u64", "  bind a0 = x\n  mv s1, a0\n  ret", "callee-saved"},
		"restore wrong slot":      {"f: (x: u64) -> u64", "  bind a0 = x\n  frame 16\n  addi sp, sp, -16\n  sd s0, 8(sp)\n  mv s0, a0\n  ld s0, 0(sp)\n  addi sp, sp, 16\n  ret", "was saved at"},
		"not restored":            {"f: (x: u64) -> u64", "  bind a0 = x\n  frame 16\n  addi sp, sp, -16\n  sd s0, 8(sp)\n  mv s0, a0\n  addi sp, sp, 16\n  ret", "not restored"},
		"memory through a0":       {"f: (x: u64) -> u64", "  bind a0 = x\n  ld a0, 0(a0)\n  ret", "only the sp frame"},
		"fall-through":            {rv64AddDecl, "  bind a0 = left\n  bind a1 = right\n  addw a0, a0, a1", "falls through"},
		"call without saving ra":  {"f: (x: u64) -> u64", "  bind a0 = x\n  call helper\n  ret", "overwrites ra"},
		"clobber ra":              {"f: (x: u64) -> u64", "  bind a0 = x\n  clobber ra\n  ret", "return address"},
		"clobber callee-saved":    {"f: (x: u64) -> u64", "  bind a0 = x\n  clobber s2\n  ret", "callee-saved"},
		"sp by non-multiple":      {"f: (x: u64) -> u64", "  bind a0 = x\n  frame 32\n  addi sp, sp, -8\n  addi sp, sp, 8\n  ret", "multiple of 16"},
		"unreachable":             {"f: (x: u64) -> u64", "  bind a0 = x\n  ret\n  mv a0, a0", "unreachable"},
		"disp disagreement":       {"f: (x: u64) -> u64", "  bind a0 = x\n  frame 16\n  beqz a0, out\n  addi sp, sp, -16\nout:\n  ret", "disagrees"},
		"read unwritten":          {"f: (x: u64) -> u64", "  bind a0 = x\n  clobber t0\n  add a0, a0, t0\n  ret", "neither bound nor written"},
		"caller-saved after call": {"f: (x, y: u64) -> u64", "  bind a0 = x\n  bind a1 = y\n  frame 16\n  addi sp, sp, -16\n  sd ra, 8(sp)\n  call helper\n  add a0, a0, a1\n  ld ra, 8(sp)\n  addi sp, sp, 16\n  ret", "neither bound nor written"},
		"never returns":           {"f: (x: u64) -> never", "  bind a0 = x\n  ret", "never-returning"},
		"immediate range":         {"f: (x: u64) -> u64", "  bind a0 = x\n  addi a0, a0, 4096\n  ret", "12-bit"},
		"shift range":             {"f: (x: u64) -> u64", "  bind a0 = x\n  slli a0, a0, 64\n  ret", "0..63"},
	}
	for name, c := range cases {
		findings := rv64Check(t, c[0], c[1])
		if len(findings) == 0 {
			t.Errorf("%s: accepted", name)
			continue
		}
		if !strings.Contains(strings.Join(findings, "\n"), c[2]) {
			t.Errorf("%s: findings %v lack %q", name, findings, c[2])
		}
	}
}

func TestRV64Verify(t *testing.T) {
	proven := func(name string, v Verdict) {
		if v.Kind != VerdictProven {
			t.Errorf("%s: %s (%s)", name, v.Kind, v.Message)
		}
	}
	proven("addw", rv64Verify(t, rv64AddDecl, "{ left + right }", rv64AddBody))
	proven("sub64", rv64Verify(t, "d: (a, b: u64) -> u64", "{ a - b }", "  bind a0 = a\n  bind a1 = b\n  sub a0, a0, a1\n  ret"))
	proven("xor/shift", rv64Verify(t, "m: (a, b: u64) -> u64", "{ (a ^ b) << u64(3) }", "  bind a0 = a\n  bind a1 = b\n  xor a0, a0, a1\n  slli a0, a0, 3\n  ret"))
	proven("frame round trip", rv64Verify(t, "acc: (a, b: u64) -> u64", "{ a + b }", `
  bind a0 = a
  bind a1 = b
  frame 16
  addi sp, sp, -16
  sd s0, 8(sp)
  mv s0, a0
  add a0, s0, a1
  ld s0, 8(sp)
  addi sp, sp, 16
  ret`))
	proven("counted loop", rv64Verify(t, "trip: (x, y: u32) -> u32", "{ x + y + y + y }", `
  bind a0 = x
  bind a1 = y
  clobber t0
  li t0, 3
loop:
  addw a0, a0, a1
  addi t0, t0, -1
  bnez t0, loop
  ret`))
	proven("unsigned min", rv64Verify(t, "umin: (x, y: u64) -> u64", "{ x < y ? x | y }", `
  bind a0 = x
  bind a1 = y
  bltu a0, a1, small
  mv a0, a1
small:
  ret`))
	proven("signed select", rv64Verify(t, "smax: (x, y: i64) -> i64", "{ x < y ? y | x }", `
  bind a0 = x
  bind a1 = y
  bge a0, a1, keep
  mv a0, a1
keep:
  ret`))
	proven("sltu as Bool", rv64Verify(t, "below: (x, y: u64) -> Bool", "{ x < y }", "  bind a0 = x\n  bind a1 = y\n  sltu a0, a0, a1\n  ret"))
	proven("narrow sign extension", rv64Verify(t, "neg8: (x: i8) -> i8", "{ i8(0) - x }", "  bind a0 = x\n  negw a0, a0\n  ret"))
	proven("li 32-bit", rv64Verify(t, "k: (x: u32) -> u32", "{ x + u32(305419896) }", "  bind a0 = x\n  clobber t0\n  li t0, 305419896\n  addw a0, a0, t0\n  ret"))
	if v := rv64Verify(t, rv64AddDecl, "{ left - right }", rv64AddBody); v.Kind != VerdictMismatch {
		t.Errorf("mismatch not reported: %s (%s)", v.Kind, v.Message)
	}
	if v := rv64Verify(t, "q: (a, b: u64) -> u64", "{ a + b }", "  bind a0 = a\n  bind a1 = b\n  mulhu a0, a0, a1\n  ret"); v.Kind != VerdictMismatch {
		t.Errorf("mulhu mismatch not reported: %s (%s)", v.Kind, v.Message)
	}
	// Division carries RISC-V's total semantics.
	term := binaryTerm("rv.divu", paramTerm("a", 64), constTerm(0, 64))
	if got := term.eval(map[string]uint64{"a": 7}); got != ^uint64(0) {
		t.Errorf("divu by zero = %x", got)
	}
	term = binaryTerm("rv.rem", paramTerm("a", 32), constTerm(uint64(0xffffffff), 32))
	if got := term.eval(map[string]uint64{"a": 0x80000000}); got != 0 {
		t.Errorf("rem overflow = %x", got)
	}
}

// rv64GNUText renders a function body as GNU assembler input.
func rv64GNUText(fn *Function) string {
	var b strings.Builder
	b.WriteString(".option norelax\n.text\n")
	numbers := map[string]int{}
	for _, item := range fn.Items {
		if label, ok := item.(Label); ok {
			numbers[label.Name] = len(numbers) + 1
		}
	}
	defined := map[string]bool{}
	for _, item := range fn.Items {
		switch it := item.(type) {
		case Label:
			defined[it.Name] = true
			fmt.Fprintf(&b, "%d:\n", numbers[it.Name])
		case Instruction:
			fmt.Fprintf(&b, "  %s\n", renderRV64Instruction(it, nil, numbers, defined))
		}
	}
	return b.String()
}

func requireRV64Tools(t *testing.T, tools ...string) {
	t.Helper()
	for _, tool := range tools {
		if _, err := exec.LookPath(tool); err != nil {
			t.Skipf("%s not present", tool)
		}
	}
}

// gnuAssemble assembles GNU text with riscv64-elf-as and returns the raw
// text section.
func gnuAssemble(t *testing.T, text string) []byte {
	t.Helper()
	dir := t.TempDir()
	src := filepath.Join(dir, "u.s")
	obj := filepath.Join(dir, "u.o")
	bin := filepath.Join(dir, "u.bin")
	if err := os.WriteFile(src, []byte(text), 0o644); err != nil {
		t.Fatal(err)
	}
	if out, err := exec.Command("riscv64-elf-as", "-march=rv64im", "-mabi=lp64", "-o", obj, src).CombinedOutput(); err != nil {
		t.Fatalf("riscv64-elf-as: %v\n%s\n%s", err, out, text)
	}
	if out, err := exec.Command("riscv64-elf-objcopy", "-O", "binary", "-j", ".text", obj, bin).CombinedOutput(); err != nil {
		t.Fatalf("objcopy: %v\n%s", err, out)
	}
	data, err := os.ReadFile(bin)
	if err != nil {
		t.Fatal(err)
	}
	return data
}

// The encoder agrees with GNU as on every instruction of the lane: each
// table entry with representative operands, the pseudo-instructions, and
// the branch, load, store, and call forms.
func TestRV64EncoderAgreesWithGNUAs(t *testing.T) {
	requireRV64Tools(t, "riscv64-elf-as", "riscv64-elf-objcopy")
	body := `
  bind a0 = x
  bind a1 = y
  clobber t0, t1, t2, t3, a2
  frame 32
  addi sp, sp, -32
  sd ra, 24(sp)
  sd s0, 16(sp)
  sw a0, 8(sp)
  sh a1, 4(sp)
  sb a1, 0(sp)
  ld s0, 16(sp)
  lw t0, 8(sp)
  lwu t1, 8(sp)
  lh t2, 4(sp)
  lhu t3, 4(sp)
  lb t0, 0(sp)
  lbu t1, 0(sp)
  add t0, a0, a1
  sub t1, a0, a1
  and t2, a0, a1
  or t3, a0, a1
  xor t0, a0, a1
  sll t1, a0, a1
  srl t2, a0, a1
  sra t3, a0, a1
  slt t0, a0, a1
  sltu t1, a0, a1
  addw t2, a0, a1
  subw t3, a0, a1
  sllw t0, a0, a1
  srlw t1, a0, a1
  sraw t2, a0, a1
  mul t3, a0, a1
  mulh t0, a0, a1
  mulhsu t1, a0, a1
  mulhu t2, a0, a1
  div t3, a0, a1
  divu t0, a0, a1
  rem t1, a0, a1
  remu t2, a0, a1
  mulw t3, a0, a1
  divw t0, a0, a1
  divuw t1, a0, a1
  remw t2, a0, a1
  remuw t3, a0, a1
  addi t0, a0, -2048
  andi t1, a0, 2047
  ori t2, a0, 255
  xori t3, a0, -1
  slti t0, a0, -7
  sltiu t1, a0, 7
  slli t2, a0, 63
  srli t3, a0, 1
  srai t0, a0, 32
  addiw t1, a0, 100
  slliw t2, a0, 31
  srliw t3, a0, 3
  sraiw t0, a0, 5
  lui t1, 1048575
  lui t2, 305419
  li t3, 305419896
  li t0, -1
  li t1, 4096
  li t2, 2047
  mv a2, a0
  not t3, a0
  neg t0, a0
  negw t1, a0
  sext.w t2, a0
  nop
  call helper
loop:
  beq a0, a1, loop
  bne a0, a1, loop
  blt a0, a1, done
  bge a0, a1, done
  bltu a0, a1, loop
  bgeu a0, a1, done
  beqz a0, done
  bnez a0, loop
  bgez a0, done
  bltz a0, done
  blez a0, done
  bgtz a0, done
  j done
done:
  ld ra, 24(sp)
  addi sp, sp, 32
  ret`
	fn, errs := rv64Unit(t, "enc: (x, y: u64) -> u64", body)
	if len(errs) != 0 {
		t.Fatal(errs)
	}
	ours, relocs, err := EncodeFunction(fn)
	if err != nil {
		t.Fatal(err)
	}
	theirs := gnuAssemble(t, rv64GNUText(fn))
	if !bytes.Equal(ours, theirs) {
		offset := 0
		for offset < len(ours) && offset < len(theirs) && bytes.Equal(ours[offset:offset+4], theirs[offset:offset+4]) {
			offset += 4
		}
		t.Fatalf("encodings differ at byte %d: ours %x, GNU as %x (ours %d bytes, theirs %d)", offset, ours[offset:min(offset+4, len(ours))], theirs[offset:min(offset+4, len(theirs))], len(ours), len(theirs))
	}
	if len(relocs) != 1 || relocs[0].Kind != "riscv_call_plt" || relocs[0].Symbol != "helper" {
		t.Fatalf("relocations %+v", relocs)
	}
}

// The ELF object is EM_RISCV with the call relocation, and links with the
// GNU linker against a definition of the callee.
func TestRV64ObjectELF(t *testing.T) {
	fn, errs := rv64Unit(t, "twice: (x: u64) -> u64", `
  bind a0 = x
  frame 16
  addi sp, sp, -16
  sd ra, 8(sp)
  call helper
  ld ra, 8(sp)
  addi sp, sp, 16
  ret`)
	if len(errs) != 0 {
		t.Fatal(errs)
	}
	encoded, err := EncodeFunctions([]*Function{fn}, func(s string) string { return s })
	if err != nil {
		t.Fatal(err)
	}
	object, err := WriteObject(ELF, encoded)
	if err != nil {
		t.Fatal(err)
	}
	if machine := binary.LittleEndian.Uint16(object[18:20]); machine != 243 {
		t.Fatalf("e_machine %d, want EM_RISCV (243)", machine)
	}
	if _, err := WriteObject(MachO, encoded); err == nil {
		t.Fatal("Mach-O accepted an rv64 object")
	}
	requireRV64Tools(t, "riscv64-elf-gcc", "riscv64-elf-objdump")
	dir := t.TempDir()
	if err := os.WriteFile(filepath.Join(dir, "unit.o"), object, 0o644); err != nil {
		t.Fatal(err)
	}
	if err := os.WriteFile(filepath.Join(dir, "helper.c"), []byte("unsigned long helper(unsigned long x) { return x + x; }\nvoid _start(void) {}\n"), 0o644); err != nil {
		t.Fatal(err)
	}
	if out, err := exec.Command("riscv64-elf-gcc", "-march=rv64im", "-mabi=lp64", "-nostdlib", "-o", filepath.Join(dir, "out.elf"), filepath.Join(dir, "helper.c"), filepath.Join(dir, "unit.o")).CombinedOutput(); err != nil {
		t.Fatalf("link: %v\n%s", err, out)
	}
	out, err := exec.Command("riscv64-elf-objdump", "-d", filepath.Join(dir, "out.elf")).CombinedOutput()
	if err != nil {
		t.Fatalf("objdump: %v\n%s", err, out)
	}
	if !strings.Contains(string(out), "<twice>:") || !strings.Contains(string(out), "jalr") {
		t.Fatalf("linked image lacks the unit:\n%s", out)
	}
}

func TestRV64EmitC(t *testing.T) {
	fn, errs := rv64Unit(t, "pick: (x, y: u64) -> u64", "  bind a0 = x\n  bind a1 = y\n  bltu a0, a1, small\n  mv a0, a1\nsmall:\n  ret")
	if len(errs) != 0 {
		t.Fatal(errs)
	}
	c := EmitC(fn, "oak_pick", func(s string) string { return "oak_" + s })
	for _, want := range []string{"#if (defined(__riscv) && (__riscv_xlen == 64)) && !defined(OAK_PORTABLE_INTRINSICS)", `"  bltu a0, a1, 1f\n"`, `"  mv a0, a1\n"`, `"1:\n"`, "requires an RV64 target"} {
		if !strings.Contains(c, want) {
			t.Errorf("emitted C lacks %q:\n%s", want, c)
		}
	}
	extern := EmitCExtern(fn, "oak_pick")
	if !strings.Contains(extern, "#if !(defined(__riscv) && (__riscv_xlen == 64)) || defined(OAK_PORTABLE_INTRINSICS)") {
		t.Errorf("extern guard:\n%s", extern)
	}
}

// Span element memory (docs/spec/94-assembler.md §9): the LP64 length
// register carries padding above bit 31, so a bound needs the normalized
// copy; an element is addressed through a guarded index scaled by the
// element size, or at a constant offset below a proven minimum length.
const rv64SumDecl = "sum_rv: (v: []u32) -> u32"
const rv64SumBody = `
  bind a0, a1 = v
  clobber t0, t1, t2, t3
  slli t1, a1, 32
  srli t1, t1, 32
  li t0, 0
  li t3, 0
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

const rv64FirstDecl = "first_rv: (v: []u32) -> u32"
const rv64FirstBody = `
  bind a0, a1 = v
  clobber t0, t1
  slli t1, a1, 32
  srli t1, t1, 32
  li t0, 1
  bltu t1, t0, empty
  lw a0, 0(a0)
  ret
empty:
  ebreak`

func TestRV64SpanMemoryChecker(t *testing.T) {
	for name, c := range map[string][2]string{
		"guarded loop":   {rv64SumDecl, rv64SumBody},
		"minimum length": {rv64FirstDecl, rv64FirstBody},
		"store through a span": {"zero_rv: (s: [*]u32) -> u32", `
  bind a0, a1 = s
  clobber t0, t1
  slli t1, a1, 32
  srli t1, t1, 32
  li t0, 1
  bltu t1, t0, empty
  sw zero, 0(a0)
  li a0, 0
  ret
empty:
  ebreak`},
		"constant bound within the minimum": {"third_rv: (v: []u64) -> u64", `
  bind a0, a1 = v
  clobber t0, t1, t2
  slli t1, a1, 32
  srli t1, t1, 32
  li t0, 4
  bltu t1, t0, empty
  li t2, 2
  li t0, 4
  bgeu t2, t0, empty
  slli t2, t2, 3
  add t2, a0, t2
  ld a0, 0(t2)
  ret
empty:
  ebreak`},
	} {
		if findings := rv64Check(t, c[0], c[1]); len(findings) != 0 {
			t.Errorf("%s: %v", name, findings)
		}
	}
	rejections := map[string][3]string{
		"no guard":                    {rv64FirstDecl, "  bind a0, a1 = v\n  lw a0, 0(a0)\n  ret", "without a length guard"},
		"raw length as bound":         {rv64SumDecl, strings.Replace(rv64SumBody, "  bgeu t0, t1, done", "  bgeu t0, a1, done", 1), "only the sp frame, a bound span base under a length guard, or a guarded element address"},
		"wrong scale":                 {rv64SumDecl, strings.Replace(rv64SumBody, "  slli t2, t0, 2", "  slli t2, t0, 3", 1), "guarded element address"},
		"width mismatch":              {rv64SumDecl, strings.Replace(rv64SumBody, "  lw t2, 0(t2)", "  ld t2, 0(t2)", 1), "outside its 4-byte element"},
		"offset past element":         {rv64SumDecl, strings.Replace(rv64SumBody, "  lw t2, 0(t2)", "  lw t2, 4(t2)", 1), "outside its 4-byte element"},
		"store to a view":             {rv64FirstDecl, strings.Replace(rv64FirstBody, "  lw a0, 0(a0)", "  sw t0, 0(a0)\n  li a0, 0", 1), "read-only view"},
		"guard lost at label":         {rv64FirstDecl, strings.Replace(rv64FirstBody, "  lw a0, 0(a0)", "again:\n  lw a0, 0(a0)", 1), "without a length guard"},
		"past the minimum":            {rv64FirstDecl, strings.Replace(rv64FirstBody, "  lw a0, 0(a0)", "  lw a0, 4(a0)", 1), "reaches past the 1 elements"},
		"guard on the wrong register": {rv64SumDecl, strings.Replace(rv64SumBody, "  slli t2, t0, 2", "  slli t2, t3, 2", 1), "guarded element address"},
	}
	for name, c := range rejections {
		findings := rv64Check(t, c[0], c[1])
		if len(findings) == 0 {
			t.Errorf("%s: accepted", name)
			continue
		}
		if !strings.Contains(strings.Join(findings, "\n"), c[2]) {
			t.Errorf("%s: findings %v lack %q", name, findings, c[2])
		}
	}
}

func TestRV64SpanMemoryVerify(t *testing.T) {
	v := rv64Verify(t, rv64FirstDecl, "{ v[0] }", rv64FirstBody)
	if v.Kind != VerdictProven {
		t.Errorf("first element: %s (%s)", v.Kind, v.Message)
	}
	v = rv64Verify(t, rv64FirstDecl, "{ v[0] + u32(1) }", rv64FirstBody)
	if v.Kind != VerdictMismatch {
		t.Errorf("first element mismatch not reported: %s (%s)", v.Kind, v.Message)
	}
	// The data-dependent element loop is coupled inductively: the 64-bit
	// counter is the zero-extended i, the W-form accumulator the
	// sign-extended total (docs/spec/94-assembler.md §9).
	v = rv64Verify(t, rv64SumDecl, "{\n  total: u32 = u32(0)\n  i: u32 = u32(0)\n  while i < len(v) {\n    total = total + v[i]\n    i = i + u32(1)\n  }\n  total\n}", rv64SumBody)
	if v.Kind != VerdictProven {
		t.Errorf("span sum: %s (%s)", v.Kind, v.Message)
	}
}
