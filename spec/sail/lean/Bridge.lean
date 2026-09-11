import Out
import Oak.ArmASL

/-!
# The Sail bridge: Sail-generated Lean ≡ `Oak.ArmASL`

`docs/spec/94-assembler.md` §8, grounding stage 3. `Out.lean` is what Sail's
Lean backend generates from `spec/sail/arm_primitives.sail`, Arm's own
pseudocode for the primitives the assembler's semantics rest on. This file
proves the hand transliteration `Oak.ArmASL` equal to that generated code,
closing the chain Arm's ASL → Sail → Lean (mechanical) ≡ `Oak.ArmASL` ≡
`Oak.AssemblerSemantics` (proved) ≡ the Go executor (checked on the
silicon).
-/

namespace Oak.SailBridge

open Oak.AssemblerSemantics
open Oak.ArmASL

/-- Our flags record as Arm's `nzcv` bit-vector: N is the top bit. -/
def Flags.toBits (f : Flags) : BitVec 4 :=
  ((BitVec.ofBool f.n ++ BitVec.ofBool f.z) ++ BitVec.ofBool f.c) ++ BitVec.ofBool f.v

/-- Arm's `nzcv` bit-vector as our flags record. -/
def Flags.ofBits (b : BitVec 4) : Flags :=
  { n := b.getLsbD 3, z := b.getLsbD 2, c := b.getLsbD 1, v := b.getLsbD 0 }

theorem Flags.toBits_ofBits (b : BitVec 4) : Flags.toBits (Flags.ofBits b) = b := by
  revert b; decide

theorem Flags.ofBits_toBits (f : Flags) : Flags.ofBits (Flags.toBits f) = f := by
  obtain ⟨n, z, c, v⟩ := f
  cases n <;> cases z <;> cases c <;> cases v <;> rfl

/-- **`ConditionHolds`**: the generated function on the flag bits is ours on
    the flags record, for every condition code and flag pattern. -/
theorem ConditionHolds_bridge (cond nzcv : BitVec 4) :
    Out.Functions.ConditionHolds cond nzcv = Oak.ArmASL.ConditionHolds cond (Flags.ofBits nzcv) := by
  revert cond nzcv; decide

/-- `get_slice_int` of a natural number at offset 0 is `BitVec.ofNat`. -/
theorem get_slice_int_natCast (w m : Nat) :
    Sail.get_slice_int w (m : Int) 0 = BitVec.ofNat w m := by
  apply BitVec.eq_of_toNat_eq
  simp only [Sail.get_slice_int, BitVec.extractLsb'_toNat, BitVec.ofInt_natCast, BitVec.toNat_ofNat, Nat.shiftRight_zero]
  rw [Nat.mod_mod_of_dvd]
  exact Nat.pow_dvd_pow 2 (by omega)

/-- `join1` of one bit is that bit. -/
theorem join1_single (v : BitVec 1) : Sail.BitVec.join1 [v] = v := by
  revert v; decide

/-- Arm's `x[N-1]` read through `access` is the sign bit. -/
theorem access_last {w : Nat} (hw : 0 < w) (x : BitVec w) :
    Sail.BitVec.access x (w - 1) = BitVec.ofBool x.msb := by
  have h : w - 1 < w := by omega
  simp only [Sail.BitVec.access, BitVec.msb_eq_getLsbD_last]
  congr 1
  first
    | rw [getElem!_pos x (w - 1) h, BitVec.getLsbD_eq_getElem h]
    | simp [getElem!_def, getElem?_pos, h, BitVec.getLsbD_eq_getElem h]
    | simp [getElem!, decidableGetElem?, h, BitVec.getLsbD_eq_getElem h]

theorem ite_beq_zero_one {α : Type} [DecidableEq α] (a b : α) :
    (if (a == b) = true then (0#1 : BitVec 1) else 1#1) = BitVec.ofBool (decide (a ≠ b)) := by
  by_cases h : a = b <;> simp [h]

theorem ite_beq_one_zero {α : Type} [DecidableEq α] (a b : α) :
    (if (a == b) = true then (1#1 : BitVec 1) else 0#1) = BitVec.ofBool (decide (a = b)) := by
  by_cases h : a = b <;> simp [h]

/-- **`AddWithCarry`**: the generated function is ours, result and flags. -/
theorem AddWithCarry_bridge {w : Nat} (hw : 0 < w) (x y : BitVec w) (b : Bool) :
    Out.Functions.AddWithCarry x y (BitVec.ofBool b) =
      ((Oak.ArmASL.AddWithCarry x y b).1, Flags.toBits (Oak.ArmASL.AddWithCarry x y b).2) := by
  have hw1 : ((w : Int) - 1).toNat = w - 1 := by omega
  have key : Sail.get_slice_int w ((x.toNat : Int) + y.toNat + b.toNat) 0 = BitVec.ofNat w (x.toNat + y.toNat + b.toNat) := by
    rw [← get_slice_int_natCast]; simp
  simp only [Out.Functions.AddWithCarry, Out.Functions.UInt, Out.Functions.SInt, Out.Functions.__GetSlice_int,
    Out.Functions.IsZero, Out.Functions.Zeros, Sail.BitVec.toNatInt, Sail.BitVec.length,
    Int.ofNat_eq_natCast]
  rw [join1_single]
  simp only [Int.toNat_zero, hw1, BitVec.toNat_ofBool]
  rw [key, access_last hw, ite_beq_one_zero, ite_beq_zero_one, ite_beq_zero_one]
  simp only [Oak.ArmASL.AddWithCarry, Flags.toBits, BitVec.ofNat_eq_ofNat, ← Int.natCast_add, ne_eq, Int.natCast_inj]
  first
    | rfl
    | simp only [BitVec.zero_eq]
    | simp [BitVec.zero_eq]

/-- **Conditional select**: the generated function is ours. -/
theorem conditionalSelect_bridge {w : Nat} (cond nzcv : BitVec 4) (inc inv : Bool) (a b : BitVec w) :
    Out.Functions.integer_conditional_select cond nzcv inc inv a b =
      conditionalSelect cond (Flags.ofBits nzcv) inc inv a b := by
  simp only [Out.Functions.integer_conditional_select, conditionalSelect, ConditionHolds_bridge]
  split
  · rfl
  · simp [Sail.BitVec.addInt]

/-- **Conditional compare**: the generated function is ours, as flag bits. -/
theorem conditionalCompare_bridge {w : Nat} (hw : 0 < w) (cond nzcv flags : BitVec 4) (l r : BitVec w) (sub : Bool) :
    Out.Functions.integer_conditional_compare_register cond nzcv flags l r sub =
      Flags.toBits (conditionalCompare cond (Flags.ofBits nzcv) l r (Flags.ofBits flags) sub) := by
  simp only [Out.Functions.integer_conditional_compare_register, conditionalCompare, ConditionHolds_bridge]
  split
  · cases sub
    · simpa using congrArg Prod.snd (AddWithCarry_bridge hw l r false)
    · simpa using congrArg Prod.snd (AddWithCarry_bridge hw l (~~~r) true)
  · simp [Flags.toBits_ofBits]

end Oak.SailBridge

namespace Oak.SailBridge

/-- `access` at any index is the bit (false beyond the width, as `getLsbD`). -/
theorem access_eq {w : Nat} (x : BitVec w) (n : Nat) :
    Sail.BitVec.access x n = BitVec.ofBool (x.getLsbD n) := by
  by_cases h : n < w
  · simp only [Sail.BitVec.access]
    congr 1
    rw [getElem!_pos x n h, BitVec.getLsbD_eq_getElem h]
  · simp only [Sail.BitVec.access]
    congr 1
    rw [getElem!_neg x n h, BitVec.getLsbD_of_ge x n (by omega)]
    rfl

/-- The range Arm's `foreach (i from 'N - 1 to 0 by 1 in dec)` becomes,
    with the start (`'N - 1`) as a parameter. -/
abbrev hsbRange (s : Int) : IntRange := { start := s, stop := 0, step := -1 }

theorem mem_hsbRange (s i : Int) : i ∈ hsbRange s ↔ 0 ≤ i ∧ i ≤ s := by
  simp only [Membership.mem]
  constructor
  · rintro ⟨h, -⟩
    simpa using h
  · intro h
    refine ⟨by simpa using h, ?_⟩
    simp [Int.emod_neg]

/-- The loop body Sail generated, verbatim. -/
abbrev hsbBody {w : Nat} (x : BitVec w) (s : Int) : (i : Int) → i ∈ hsbRange s → Unit → ExceptT Int Id (ForInStep Unit) :=
  fun a _ _ =>
    if (Sail.BitVec.join1 [Sail.BitVec.access x a.toNat] == 1#1) = true then do
      let v ← throw a
      pure (ForInStep.yield v)
    else pure (ForInStep.yield ())

/-- Running the generated loop from bit `n` finds the highest set bit at or
    below `n`, as our list search does. -/
theorem hsb_loop_spec {w : Nat} (x : BitVec w) (s : Int) (n : Nat) (hn : (n : Int) ≤ s)
    (hs : ((n : Int) - (hsbRange s).start) % (hsbRange s).step = 0) :
    (IntRange.forIn'.loop (hsbRange s) (hsbBody x s) () (n : Int) hs).run =
      match (List.range (n + 1)).reverse.find? (fun j => x.getLsbD j) with
      | some j => Except.error (j : Int)
      | none => Except.ok () := by
  induction n with
  | zero =>
    unfold IntRange.forIn'.loop
    rw [dif_pos ((mem_hsbRange _ _).2 ⟨by omega, by omega⟩)]
    simp only [hsbBody, access_eq, join1_single, Int.toNat_natCast,
      List.range_succ, List.range_zero, List.nil_append, List.reverse_cons, List.reverse_nil, List.find?_cons, List.find?_nil]
    cases hx : x.getLsbD 0
    · split
      · rename_i h; simp only [beq_iff_eq] at h
        first
          | exact absurd h (by simp)
          | exact absurd (congrArg BitVec.toNat h) (by simp)
      simp only [pure_bind]
      unfold IntRange.forIn'.loop
      rw [dif_neg (by rw [mem_hsbRange]; omega)]
      simp [ExceptT.run_pure]
      rfl
    · split
      · simp [ExceptT.run_throw]
        try rfl
      · rename_i h; simp only [beq_iff_eq] at h; exact (h rfl).elim
  | succ m ih =>
    unfold IntRange.forIn'.loop
    rw [dif_pos ((mem_hsbRange _ _).2 ⟨by omega, by omega⟩)]
    have hstep : ((m + 1 : Nat) : Int) + -1 = (m : Int) := by omega
    have hrange : (List.range (m + 1 + 1)).reverse = (m + 1) :: (List.range (m + 1)).reverse := by
      simp [List.range_succ]
    simp only [hsbBody, access_eq, join1_single, Int.toNat_natCast]
    rw [hrange, List.find?_cons]
    cases hx : x.getLsbD (m + 1)
    · split
      · rename_i h; simp only [beq_iff_eq] at h
        first
          | exact absurd h (by simp)
          | exact absurd (congrArg BitVec.toNat h) (by simp)
      simp only [pure_bind]
      simp only [hstep]
      rw [ih (by omega)]
    · split
      · simp [ExceptT.run_throw]
        try rfl
      · rename_i h; simp only [beq_iff_eq] at h; exact (h rfl).elim

/-- The loop specification with the start index as an arbitrary integer. -/
theorem hsb_loop_spec' {w : Nat} (x : BitVec w) (s i : Int) (n : Nat) (hi : i = n) (hn : (n : Int) ≤ s)
    (hs : (i - (hsbRange s).start) % (hsbRange s).step = 0) :
    (IntRange.forIn'.loop (hsbRange s) (hsbBody x s) () i hs).run =
      match (List.range (n + 1)).reverse.find? (fun j => x.getLsbD j) with
      | some j => Except.error (j : Int)
      | none => Except.ok () := by
  subst hi
  exact hsb_loop_spec x s n hn hs

/-- **`HighestSetBit`**: the generated early-return loop is our list search,
    at every width. -/
theorem HighestSetBit_bridge {w : Nat} (x : BitVec w) :
    Out.Functions.HighestSetBit x = Oak.ArmASL.HighestSetBit x := by
  simp only [Out.Functions.HighestSetBit, Sail.BitVec.length, forIn, forIn', IntRange.forIn',
    ExceptM.run, Oak.ArmASL.HighestSetBit]
  cases w with
  | zero =>
    unfold IntRange.forIn'.loop
    rw [dif_neg (by rw [mem_hsbRange]; omega)]
    simp [ExceptT.run_pure]
    try rfl
  | succ k =>
    rw [ExceptT.run_bind, hsb_loop_spec' x (((k + 1 : Nat) : Int) - 1) (((k + 1 : Nat) : Int) - 1) k (by omega) (by omega)]
    cases hfind : (List.range (k + 1)).reverse.find? (fun j => x.getLsbD j) <;> simp [ExceptT.run_pure] <;> try rfl

/-- **`CountLeadingZeroBits`** follows. -/
theorem CountLeadingZeroBits_bridge {w : Nat} (x : BitVec w) :
    Out.Functions.CountLeadingZeroBits x = Oak.ArmASL.CountLeadingZeroBits x := by
  simp [Out.Functions.CountLeadingZeroBits, Oak.ArmASL.CountLeadingZeroBits, HighestSetBit_bridge, Sail.BitVec.length]

end Oak.SailBridge
