package asm

import (
	"strings"
	"testing"
)

// Package globals through the native lane (docs/spec/94-assembler.md §9,
// the OS pilot's N3): `adrp xA, G` then `add xA, xA, :lo12:G` name a
// global's cell, and the checker admits exactly one access to it — `[xA]`
// at the scalar's width — when G is one of the function's declared
// globals.
func TestCheckerGlobals(t *testing.T) {
	decl := "read_st: (k: u32) -> u32"
	globals := map[string]Global{"st": {Type: "u32", Bits: 32}, "level": {Type: "u8", Bits: 8}}
	check := func(body string) []string {
		unit, errs := ParseUnit("globals.oakasm", decl+" = {\n"+body+"\n}\n")
		if len(errs) != 0 {
			t.Fatal(errs)
		}
		unit.Functions[0].Globals = globals
		sig, _ := parseSignature(decl)
		return Check(unit.Functions[0], sig, nil)
	}
	accept := "  bind w0 = k\n  clobber x9, x10\n  adrp x9, st\n  add x9, x9, :lo12:st\n  ldr w10, [x9]\n  add w10, w10, w0\n  str w10, [x9]\n  adrp x9, level\n  add x9, x9, :lo12:level\n  ldrb w0, [x9]\n  add w0, w0, w10\n  ret"
	if findings := check(accept); len(findings) != 0 {
		t.Fatalf("a load and store of a global at its width must pass: %v", findings)
	}
	cases := []struct{ name, body, want string }{
		{"unknown symbol", "  bind w0 = k\n  clobber x9\n  adrp x9, other\n  add x9, x9, :lo12:other\n  ldr w0, [x9]\n  ret", "does not hold that symbol's page"},
		{"lo12 without the page", "  bind w0 = k\n  clobber x9\n  mov x9, #0\n  add x9, x9, :lo12:st\n  ldr w0, [x9]\n  ret", "does not hold that symbol's page"},
		{"lo12 of another global", "  bind w0 = k\n  clobber x9\n  adrp x9, level\n  add x9, x9, :lo12:st\n  ldr w0, [x9]\n  ret", "does not hold that symbol's page"},
		{"offset past the cell", "  bind w0 = k\n  clobber x9\n  adrp x9, st\n  add x9, x9, :lo12:st\n  ldr w0, [x9, #4]\n  ret", "the only access shape"},
		{"indexed", "  bind w0 = k\n  clobber x9\n  adrp x9, st\n  add x9, x9, :lo12:st\n  ldr w0, [x9, w0, uxtw #2]\n  ret", "the only access shape"},
		{"wider than the cell", "  bind w0 = k\n  clobber x9, x10\n  adrp x9, st\n  add x9, x9, :lo12:st\n  ldr x10, [x9]\n  mov w0, w10\n  ret", "8-byte access to the global st, a 4-byte u32"},
		{"narrower than the cell", "  bind w0 = k\n  clobber x9\n  adrp x9, st\n  add x9, x9, :lo12:st\n  ldrb w0, [x9]\n  ret", "1-byte access to the global st, a 4-byte u32"},
		{"pair", "  bind w0 = k\n  clobber x9, x10, x11\n  adrp x9, st\n  add x9, x9, :lo12:st\n  ldp w10, w11, [x9]\n  add w0, w10, w11\n  ret", "one scalar"},
		{"address lost at a call", "  bind w0 = k\n  clobber x9, x29, x30\n  frame 16\n  sub sp, sp, #16\n  stp x29, x30, [sp]\n  adrp x9, st\n  add x9, x9, :lo12:st\n  bl helper\n  ldr w0, [x9]\n  ldp x29, x30, [sp]\n  add sp, sp, #16\n  ret", "memory operands go through the declared sp frame or a bound span base"},
		{"address lost with the register", "  bind w0 = k\n  clobber x9\n  adrp x9, st\n  add x9, x9, :lo12:st\n  add x9, x9, #4\n  ldr w0, [x9]\n  ret", "memory operands go through the declared sp frame or a bound span base"},
	}
	for _, tc := range cases {
		findings := check(tc.body)
		if len(findings) == 0 {
			t.Errorf("%s: must be refused", tc.name)
			continue
		}
		if !strings.Contains(strings.Join(findings, "\n"), tc.want) {
			t.Errorf("%s: want %q, got %v", tc.name, tc.want, findings)
		}
	}
}

// The `add xA, xN, :lo12:sym` form: parsed, spelled back, encoded as ADD
// (immediate) with imm12 left for the linker, and relocated as
// PAGEOFF12 / ADD_ABS_LO12_NC beside the adrp's PAGE21 / ADR_PREL_PG_HI21.
func TestGlobalAddressEncodingAndRelocations(t *testing.T) {
	decl := "read_st: () -> u32"
	unit, errs := ParseUnit("lo12.oakasm", decl+" = {\n  clobber x9\n  adrp x9, st\n  add x9, x9, :lo12:st\n  ldr w0, [x9]\n  ret\n}\n")
	if len(errs) != 0 {
		t.Fatal(errs)
	}
	fn := unit.Functions[0]
	var add Instruction
	for _, item := range fn.Items {
		if instr, isInstr := item.(Instruction); isInstr && instr.Mnemonic == "add" {
			add = instr
		}
	}
	sym, isSym := add.Operands[2].(Symbol)
	if !isSym || !sym.Lo12 || sym.Name != "st" {
		t.Fatalf("the add's third operand must parse as :lo12:st, got %#v", add.Operands[2])
	}
	if text := add.String(); text != "add x9, x9, :lo12:st" {
		t.Fatalf("the form must spell back as :lo12:, got %q", text)
	}
	code, relocs, err := EncodeFunction(fn)
	if err != nil {
		t.Fatal(err)
	}
	// adrp x9, st: 0x90000009 with the page displacement zero; add x9, x9, #0: 0x91000129.
	if len(code) < 8 {
		t.Fatalf("short encoding: %x", code)
	}
	if word := uint32(code[4]) | uint32(code[5])<<8 | uint32(code[6])<<16 | uint32(code[7])<<24; word != 0x91000129 {
		t.Fatalf("add x9, x9, :lo12:st must encode as ADD (immediate) with imm12 zero, got %08x", word)
	}
	kinds := map[string]string{}
	for _, r := range relocs {
		kinds[r.Kind] = r.Symbol
	}
	if kinds["adrp21"] != "st" || kinds["lo12"] != "st" {
		t.Fatalf("want adrp21 and lo12 relocations against st, got %v", relocs)
	}
	encoded := []EncodedFunction{{Symbol: "_read_st", Bytes: code, Relocs: relocs, Align: 4, Arch: ArchArm64}}
	for _, format := range []ObjectFormat{MachO, ELF} {
		if _, err := WriteObject(format, encoded); err != nil {
			t.Fatalf("%v object with a lo12 relocation: %v", format, err)
		}
	}
}

// A top-level record or array (Global.Aggregate) is a writable region of
// its size at its adrp/add address: fields at their offsets and elements
// under a constant guard are admitted, anything past the size or without
// the guard is refused (docs/spec/94-assembler.md §9, the OS pilot's N9).
func TestCheckerGlobalAggregates(t *testing.T) {
	decl := "peek: (i: u32) -> u32"
	// Table { slots: [8]Slot (8 bytes each), count: u32 }: 68 bytes.
	globals := map[string]Global{"table": {Type: "Table", Aggregate: true, Size: 68}}
	check := func(body string) []string {
		unit, errs := ParseUnit("agg.oakasm", decl+" = {\n"+body+"\n}\n")
		if len(errs) != 0 {
			t.Fatal(errs)
		}
		unit.Functions[0].Globals = globals
		sig, _ := parseSignature(decl)
		return Check(unit.Functions[0], sig, nil)
	}
	address := "  adrp x9, table\n  add x9, x9, :lo12:table\n"
	// The element address lands in a fresh register, as the generator
	// emits it: a write to the base register would end its region fact.
	accept := "  bind w0 = i\n  clobber x9, x10, x11\n" + address + "  ldr w10, [x9, #64]\n  cmp w0, #8\n  b.hs trap\n  add x11, x9, w0, uxtw #3\n  ldr w0, [x11]\n  add w0, w0, w10\n  str w0, [x11, #4]\n  ret\ntrap:\n  brk #1"
	if findings := check(accept); len(findings) != 0 {
		t.Fatalf("a field read, a guarded element, and a field store inside the aggregate must pass: %v", findings)
	}
	cases := []struct{ name, body, want string }{
		{"field past the size", "  bind w0 = i\n  clobber x9\n" + address + "  ldr w0, [x9, #68]\n  ret", "outside its 68 bytes"},
		{"element without a guard", "  bind w0 = i\n  clobber x9, x11\n" + address + "  add x11, x9, w0, uxtw #3\n  ldr w0, [x11]\n  ret", "memory operands go through the declared sp frame or a bound span base"},
		{"guard admits too many", "  bind w0 = i\n  clobber x9, x11\n" + address + "  cmp w0, #9\n  b.hs trap\n  add x11, x9, w0, uxtw #3\n  ldr w0, [x11]\n  ret\ntrap:\n  brk #1", "memory operands go through the declared sp frame or a bound span base"},
	}
	for _, tc := range cases {
		findings := check(tc.body)
		if len(findings) == 0 {
			t.Errorf("%s: must be refused", tc.name)
			continue
		}
		if !strings.Contains(strings.Join(findings, "\n"), tc.want) {
			t.Errorf("%s: want %q, got %v", tc.name, tc.want, findings)
		}
	}
}
