import OakSailFramedComposition

/-! Abstract code-byte placement in the concrete Sail byte map, with
preservation under the two actual frame stores. This is not an ELF loader. -/
set_option autoImplicit false
noncomputable section
namespace OakSailFetchedCode
open LeanRV64D
open OakSailBridge.BitwiseDecoded
open Oak.BitwiseFunction (Op)
attribute [local irreducible] store64

/-- Every byte, including padding-free exhaustion of the fixed function body,
is present in the actual sequential Sail RAM. -/
def BytesAt (s : State) (base : Nat) (bytes : List (BitVec 8)) : Prop :=
  ∀ i : Fin bytes.length, s.mem.get? (base + i.val) = some bytes[i.val]

def FrameCodeAt (s : State) (base : BitVec 64) (op : Op) : Prop :=
  BytesAt s base.toNat (Oak.RiscVFramedBitwise.functionBytes op) ∧
  base.toNat % 4 = 0 ∧ base.toNat + 36 ≤ 2^64

/-- Only bytes that the wrapper writes must be disjoint from code. -/
def CodeStackDisjoint (code : BitVec 64) (stackBase : BitVec 64) : Prop :=
  (code.toNat + 36 ≤ stackBase.toNat ∨ stackBase.toNat + 8 ≤ code.toNat) ∧
  (code.toNat + 36 ≤ (stackBase + (8#64)).toNat ∨
    (stackBase + (8#64)).toNat + 8 ≤ code.toNat)

theorem bytesAt_setRegister (s : State) (base : Nat) (bytes : List (BitVec 8))
    (r : Register) (value : RegisterType r) (h : BytesAt s base bytes) :
    BytesAt (setRegister s r value) base bytes := h

theorem bytesAt_store64 (s : State) (base addr : Nat) (bytes : List (BitVec 8))
    (value : BitVec 64) (h : BytesAt s base bytes)
    (hsep : base + bytes.length ≤ addr ∨ addr + 8 ≤ base) :
    BytesAt (store64 s addr value) base bytes := by
  intro i
  rw [lookup_store64_other s addr (base + i.val) value (by have hi := i.isLt; omega)]
  exact h i

theorem frameCodeAt_savedMemory (s : State) (code base saved1 saved2 : BitVec 64) (op : Op)
    (hcode : FrameCodeAt s code op) (hsep : CodeStackDisjoint code base) :
    FrameCodeAt (frameSavedMemory s base saved1 saved2) code op := by
  refine ⟨?_, hcode.2⟩
  have hlen : (Oak.RiscVFramedBitwise.functionBytes op).length = 36 := by cases op <;> rfl
  apply bytesAt_store64
  · apply bytesAt_store64
    · exact hcode.1
    · simpa only [hlen] using hsep.1
  · simpa only [hlen] using hsep.2

theorem frameCodeAt_finalState (s : State) (code base saved1 saved2 result target : BitVec 64)
    (op : Op) (hcode : FrameCodeAt s code op) (hsep : CodeStackDisjoint code base) :
    FrameCodeAt (finalFrameState s base saved1 saved2 result target) code op := by
  have saved := frameCodeAt_savedMemory s code base saved1 saved2 op hcode hsep
  exact ⟨saved.1, saved.2⟩

def frameWord (op : Op) (i : Fin 9) : BitVec 32 :=
  (framedWords (Oak.RiscVBitwiseFunction.bodyWord op))[i.val]'(by simp [framedWords])

theorem frame_byte (op : Op) (i : Fin 9) (j : Fin 4) :
    (Oak.RiscVFramedBitwise.functionBytes op)[4 * i.val + j.val]? =
      some ((frameWord op i).extractLsb' (8 * j.val) 8) := by
  have hi := i.isLt
  have hj := j.isLt
  have ci : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 ∨ i.val = 4 ∨
      i.val = 5 ∨ i.val = 6 ∨ i.val = 7 ∨ i.val = 8 := by omega
  have cj : j.val = 0 ∨ j.val = 1 ∨ j.val = 2 ∨ j.val = 3 := by omega
  rcases ci with hi|hi|hi|hi|hi|hi|hi|hi|hi <;>
    rcases cj with hj|hj|hj|hj <;>
    cases op <;> simp [frameWord, hi, hj] <;> rfl

theorem placed_frame_word (s : State) (code : BitVec 64) (op : Op) (i : Fin 9)
    (h : FrameCodeAt s code op) :
    ∀ j : Fin 4, s.mem.get? (code.toNat + 4 * i.val + j.val) =
      some ((frameWord op i).extractLsb' (8 * j.val) 8) := by
  intro j
  have hlen : (Oak.RiscVFramedBitwise.functionBytes op).length = 36 := by cases op <;> rfl
  have hij : 4 * i.val + j.val < (Oak.RiscVFramedBitwise.functionBytes op).length := by
    rw [hlen]; have hi := i.isLt; have hj := j.isLt; omega
  have hbyte := h.1 ⟨4 * i.val + j.val, hij⟩
  have hv := frame_byte op i j
  rw [List.getElem?_eq_getElem hij] at hv
  simpa only [Nat.add_assoc] using hbyte.trans hv

theorem frame_word_base_bits (op : Op) (i : Fin 9) :
    (frameWord op i).extractLsb' 0 2 = (3#2) := by
  have hi := i.isLt
  have ci : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 ∨ i.val = 4 ∨
      i.val = 5 ∨ i.val = 6 ∨ i.val = 7 ∨ i.val = 8 := by omega
  rcases ci with hi|hi|hi|hi|hi|hi|hi|hi|hi <;>
    cases op <;> simp [frameWord, hi, framedWords] <;> decide +kernel

def codePC (base : BitVec 64) (i : Fin 9) : BitVec 64 := base + BitVec.ofNat 64 (4 * i.val)

theorem codePC_toNat (base : BitVec 64) (i : Fin 9)
    (h : base.toNat + 36 ≤ 2^64) :
    (codePC base i).toNat = base.toNat + 4 * i.val := by
  unfold codePC
  have hi := i.isLt
  have hn : 4 * i.val < 2^64 := by omega
  rw [_root_.BitVec.toNat_add_of_lt]
  · simp [_root_.BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]
  · simp only [_root_.BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]
    omega

theorem codePC_aligned (base : BitVec 64) (i : Fin 9)
    (h : base.toNat + 36 ≤ 2^64) (ha : base.toNat % 4 = 0) :
    (codePC base i).toNat % 4 = 0 := by
  rw [codePC_toNat base i h]
  omega

theorem codePC_bytes (s : State) (base : BitVec 64) (op : Op) (i : Fin 9)
    (h : FrameCodeAt s base op) :
    ∀ j : Fin 4, s.mem.get? ((codePC base i).toNat + j.val) =
      some ((frameWord op i).extractLsb' (8 * j.val) 8) := by
  rw [codePC_toNat base i h.2.2]
  exact placed_frame_word s base op i h

example (code : BitVec 64) : ¬ CodeStackDisjoint code code := by
  intro h
  have hs := h.1
  omega

example (s : State) (op : Op) : ¬ FrameCodeAt s (0xfffffffffffffff0#64) op := by
  intro h
  have hb := h.2.2
  change 18446744073709551600 + 36 ≤ 18446744073709551616 at hb
  omega

end OakSailFetchedCode
