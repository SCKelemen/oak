import Std.Tactic.BVDecide

/-!
RV64 AUIPC+JALR/ADDI relocation core. Natural addresses are bounded to u64;
we refuse address wrap and malformed pairs. This is a mathematical model with
production decision pins, not implementation refinement of Go or Oak, and
not a proof of ELF, symbol resolution, loading, or whole-program execution.
-/
namespace Oak.RV64Relocation

def delta (place target : Nat) : Int := (target : Int) - (place : Int)
def high (d : Int) : Int := (d + 2048) / 4096
def low (d : Int) : Int := d - high d * 4096

def fits (call : Bool) (place target : Nat) : Bool :=
  decide (place % 2 = 0 ∧ place + 7 < 2^64 ∧ target < 2^64 ∧
    (call = true → target % 2 = 0) ∧
    -2147485696 ≤ delta place target ∧ delta place target ≤ 2147481599)

def pairMatches (call : Bool) (upper lower : BitVec 32) : Bool :=
  let rd := upper.extractLsb' 7 5
  (upper &&& 0x7f#32) == 0x17#32 && rd != 0#5 &&
    lower.extractLsb' 7 5 == rd && lower.extractLsb' 15 5 == rd &&
    (lower &&& 0x707f#32) == (if call then 0x67#32 else 0x13#32) &&
    (!call || rd == 1#5)

def patchUpper (word : BitVec 32) (hi : BitVec 20) : BitVec 32 :=
  (word &&& 0xfff#32) ||| (hi.zeroExtend 32 <<< 12)
def patchLower (word : BitVec 32) (lo : BitVec 12) : BitVec 32 :=
  (word &&& 0xfffff#32) ||| (lo.zeroExtend 32 <<< 20)

def decode (upper lower : BitVec 32) : Int :=
  (upper.extractLsb' 12 20).toInt * 4096 + (lower.extractLsb' 20 12).toInt

def relocate (call : Bool) (upper lower : BitVec 32) (place target : Nat) :
    Option (BitVec 32 × BitVec 32) :=
  if fits call place target && pairMatches call upper lower then
    some (patchUpper upper (BitVec.ofInt 20 (high (delta place target))),
      patchLower lower (BitVec.ofInt 12 (low (delta place target))))
  else none

theorem patchUpper_fixed (w : BitVec 32) (hi : BitVec 20) :
    patchUpper w hi &&& 0xfff#32 = w &&& 0xfff#32 := by
  unfold patchUpper
  bv_decide

theorem patchLower_fixed (w : BitVec 32) (lo : BitVec 12) :
    patchLower w lo &&& 0xfffff#32 = w &&& 0xfffff#32 := by
  unfold patchLower
  bv_decide

theorem patchUpper_immediate (w : BitVec 32) (hi : BitVec 20) :
    (patchUpper w hi).extractLsb' 12 20 = hi := by
  unfold patchUpper
  bv_decide

theorem patchLower_immediate (w : BitVec 32) (lo : BitVec 12) :
    (patchLower w lo).extractLsb' 20 12 = lo := by
  unfold patchLower
  bv_decide

theorem split_bounds (d : Int) (hlo : -2147485696 ≤ d) (hhi : d ≤ 2147481599) :
    -524288 ≤ high d ∧ high d < 524288 ∧ -2048 ≤ low d ∧ low d < 2048 := by
  unfold low high
  omega

theorem split_exact (d : Int) : high d * 4096 + low d = d := by
  unfold low
  omega

theorem decode_patch (upper lower : BitVec 32) (d : Int)
    (hlo : -2147485696 ≤ d) (hhi : d ≤ 2147481599) :
    decode (patchUpper upper (BitVec.ofInt 20 (high d)))
      (patchLower lower (BitVec.ofInt 12 (low d))) = d := by
  obtain ⟨hhlo, hhhi, hllo, hlhi⟩ := split_bounds d hlo hhi
  unfold decode
  rw [patchUpper_immediate, patchLower_immediate]
  rw [BitVec.toInt_ofInt_eq_self (w := 20) (by decide) hhlo hhhi]
  rw [BitVec.toInt_ofInt_eq_self (w := 12) (by decide) hllo hlhi]
  exact split_exact d

theorem relocate_eq_some_iff (call : Bool) (upper lower : BitVec 32)
    (place target : Nat) (patched : BitVec 32 × BitVec 32) :
    relocate call upper lower place target = some patched ↔
      fits call place target = true ∧ pairMatches call upper lower = true ∧
      patched = (patchUpper upper (BitVec.ofInt 20 (high (delta place target))),
        patchLower lower (BitVec.ofInt 12 (low (delta place target)))) := by
  unfold relocate
  by_cases hf : fits call place target = true <;>
    by_cases hp : pairMatches call upper lower = true <;>
      simp [hf, hp, eq_comm]

theorem relocate_reaches {call : Bool} {upper lower : BitVec 32}
    {place target : Nat} {patched : BitVec 32 × BitVec 32}
    (h : relocate call upper lower place target = some patched) :
    (place : Int) + decode patched.1 patched.2 = (target : Int) := by
  obtain ⟨hf, _, hp⟩ := (relocate_eq_some_iff call upper lower place target patched).mp h
  simp only [fits, decide_eq_true_eq] at hf
  rw [hp]
  rw [decode_patch upper lower (delta place target) hf.2.2.2.2.1 hf.2.2.2.2.2]
  unfold delta
  omega

-- The JALR bit-zero clearing step preserves an admitted call target.
theorem call_target_even {place target : Nat} (h : fits true place target = true) :
    target % 2 = 0 := by
  simp only [fits, decide_eq_true_eq] at h
  exact h.2.2.2.1 True.intro

-- Regression: the old signed-32-bit check admitted this invalid upper half.
example : fits false 0 2147481600 = false := by decide
example : fits false 0 2147481599 = true := by decide
example : fits false 2147485696 0 = true := by decide
example : relocate true 0x00000097#32 0x000080e7#32 65536 65552 =
    some (0x00000097#32, 0x010080e7#32) := by decide

end Oak.RV64Relocation
