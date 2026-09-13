package asm

// Argument placement under AAPCS64 beyond the eight integer registers
// (docs/spec/94-assembler.md §9, twenty-sixth increment). The general
// registers x0–x7 take arguments in order; once an argument does not fit
// the registers left, it and every integer-class argument after it go to
// the stack, at increasing offsets from the caller's sp at the call (the
// callee's sp at entry). Two stack conventions exist: the standard one
// rounds every stack argument to an 8-byte slot; Apple's arm64 ABI packs
// fundamental types at their natural size and alignment (composites stay
// 8-aligned). The compiler and the checker compute the same layout from
// the signature — the checker from its own reading, so a lowering that
// reads the wrong slot is refused, not trusted.

// ArgClass describes one integer-class argument for the layout: the
// registers it takes when it fits, and its size and alignment on the stack
// under the packing convention (the standard one rounds both to 8).
type ArgClass struct {
	Words int   // registers when passed in registers (1 scalar, 2 span, chunks of a small record, 1 for a reference)
	Bytes int64 // natural size on the stack (packed): 1, 2, 4, 8 for scalars; 16 for a span; chunks*8 for a record
	Align int64 // natural alignment on the stack (packed)
}

// ArgPlace is where an argument lands.
type ArgPlace struct {
	Reg     int   // first register, when in registers
	Regs    int   // registers taken
	OnStack bool  // else at Offset from the entry sp
	Offset  int64 // entry-relative byte offset of the argument's first byte
}

// LayoutArguments places integer-class arguments in order; it returns the
// places and the bytes of the stack area they take, rounded to 16.
func LayoutArguments(args []ArgClass, packed bool) ([]ArgPlace, int64) {
	places := make([]ArgPlace, len(args))
	next, off, stack := 0, int64(0), false
	for i, a := range args {
		if !stack && next+a.Words <= 8 {
			places[i] = ArgPlace{Reg: next, Regs: a.Words}
			next += a.Words
			continue
		}
		stack = true
		size, align := int64(a.Words)*8, int64(8)
		if packed {
			size, align = a.Bytes, a.Align
		}
		if align < 1 {
			align = 1
		}
		off = (off + align - 1) / align * align
		places[i] = ArgPlace{OnStack: true, Offset: off}
		off += size
	}
	return places, (off + 15) / 16 * 16
}
