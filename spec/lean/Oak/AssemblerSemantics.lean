/-!
# Assembler semantics: registers, width views, data processing

`docs/spec/94-assembler.md` §8. The symbolic executor of `asm/verify.go`
transliterates this model: the general register file as 32 values of
64 bits (register 31 reads zero), the `wN`/`xN` width views — a 32-bit
write zero-extends into the 64-bit register, a 32-bit read truncates —
and the data-processing instructions as total bitvector operations that
wrap to their width, exactly Oak's fixed-width arithmetic (`20-types.md`
§11.1), which is what makes the Oak fallback body a usable specification.
-/

namespace Oak.AssemblerSemantics

/-- The general register file. -/
def Regs := Fin 32 → BitVec 64

/-- Register 31 is the zero register on read. -/
def readX (r : Regs) (n : Fin 32) : BitVec 64 :=
  if n = 31 then 0 else r n

def readW (r : Regs) (n : Fin 32) : BitVec 32 :=
  (readX r n).truncate 32

def writeX (r : Regs) (n : Fin 32) (v : BitVec 64) : Regs :=
  fun m => if m = n then v else r m

/-- A 32-bit write zero-extends: the upper half is cleared. -/
def writeW (r : Regs) (n : Fin 32) (v : BitVec 32) : Regs :=
  writeX r n (v.zeroExtend 64)

/-- Reading back a 32-bit write at 32 bits returns the value. -/
theorem readW_writeW (r : Regs) (n : Fin 32) (v : BitVec 32) (h : n ≠ 31) :
    readW (writeW r n v) n = v := by
  simp [readW, writeW, writeX, readX, h]

/-- Reading a 32-bit write at 64 bits is the zero-extension: the aliasing
    law of `Oak.Assembler.alias_same_physical` made concrete. -/
theorem readX_writeW (r : Regs) (n : Fin 32) (v : BitVec 32) (h : n ≠ 31) :
    readX (writeW r n v) n = v.zeroExtend 64 := by
  simp [writeW, writeX, readX, h]

/-- Writes to one register leave every other register unchanged. -/
theorem readX_writeX_other (r : Regs) (n m : Fin 32) (v : BitVec 64)
    (hne : m ≠ n) (hz : m ≠ 31) : readX (writeX r n v) m = readX r m := by
  simp [writeX, readX, hne, hz]

/-- Data-processing operations, total and wrapping at the width. -/
inductive Op where
  | add | sub | and | orr | eor | lsl | lsr
  deriving DecidableEq, Repr

def apply {w : Nat} (op : Op) (a b : BitVec w) : BitVec w :=
  match op with
  | .add => a + b
  | .sub => a - b
  | .and => a &&& b
  | .orr => a ||| b
  | .eor => a ^^^ b
  | .lsl => a <<< (b.toNat % w)
  | .lsr => a >>> (b.toNat % w)

/-- A 64-bit data-processing instruction on registers. -/
def execX (op : Op) (r : Regs) (d n m : Fin 32) : Regs :=
  writeX r d (apply op (readX r n) (readX r m))

/-- A 32-bit data-processing instruction: operands read at 32 bits, the
    result written with zero-extension. -/
def execW (op : Op) (r : Regs) (d n m : Fin 32) : Regs :=
  writeW r d (apply op (readW r n) (readW r m))

/-- The 32-bit result of a 32-bit instruction is the 32-bit operation on
    the 32-bit views — the executor's `truncate`/`zeroExtend` discipline. -/
theorem readW_execW (op : Op) (r : Regs) (d n m : Fin 32) (h : d ≠ 31) :
    readW (execW op r d n m) d = apply op (readW r n) (readW r m) := by
  unfold execW
  exact readW_writeW _ _ _ h

/-- Addition commutes: `add w0, w0, w1` and `add w0, w1, w0` are one
    program — the simplest fact the linear normal form relies on. -/
theorem add_comm' {w : Nat} (a b : BitVec w) : apply .add a b = apply .add b a := by
  simp [apply, BitVec.add_comm]

/-- Subtraction is addition of the negation: `sub` normalizes into the
    same linear form as `add` with a negated coefficient. -/
theorem sub_as_add {w : Nat} (a b : BitVec w) : apply .sub a b = apply .add a (-b) := by
  simp [apply, BitVec.sub_eq_add_neg]

/-- The bit-blaster's justification: two bitvectors are equal exactly when
    every bit agrees, so equality of every bit's canonical decision diagram
    is equality of the values (`asm/blast.go`). -/
theorem eq_of_bits {w : Nat} (a b : BitVec w) (h : ∀ i : Nat, a.getLsbD i = b.getLsbD i) : a = b := by
  apply BitVec.eq_of_getLsbD_eq
  intros
  exact h _

/-- The pointwise laws the blaster applies for `and`, `orr`, `eor`. -/
theorem and_bit {w : Nat} (a b : BitVec w) (i : Nat) :
    (a &&& b).getLsbD i = (a.getLsbD i && b.getLsbD i) := BitVec.getLsbD_and

theorem or_bit {w : Nat} (a b : BitVec w) (i : Nat) :
    (a ||| b).getLsbD i = (a.getLsbD i || b.getLsbD i) := BitVec.getLsbD_or

theorem xor_bit {w : Nat} (a b : BitVec w) (i : Nat) :
    (a ^^^ b).getLsbD i = (a.getLsbD i ^^ b.getLsbD i) := BitVec.getLsbD_xor

end Oak.AssemblerSemantics
