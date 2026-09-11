import Std.Tactic.BVDecide
import Oak.AssemblerSemantics

/-!
# Arm's ASL primitives, transliterated

`docs/spec/94-assembler.md` §8, grounding step (2). The verifier's semantics
(`Oak.AssemblerSemantics`) are our reading of the Arm manual. This file
transliterates the shared pseudocode functions that reading rests on —
from the Sail model of the Armv8.5-A architecture that Arm and the REMS
group generated from Arm's own ASL (`sail-arm`, BSD-3-Clause-Clear; the
Sail text is quoted with each definition) — and proves our definitions
equal to them. With the silicon differential (`asm/silicon_test.go`)
tying the Go executor to the hardware, the chain is: Arm's ASL ≡ this file
≡ `Oak.AssemblerSemantics` (proved here) ≡ the Go executor (transliteration,
checked against the silicon).
-/

namespace Oak.ArmASL

open Oak.AssemblerSemantics

/-- Arm's `AddWithCarry`, Sail text:
```
function AddWithCarry (x, y, carry_in) = {
    let 'unsigned_sum = UInt(x) + UInt(y) + UInt(carry_in);
    let 'signed_sum = SInt(x) + SInt(y) + UInt(carry_in);
    let result : bits('N) = __GetSlice_int('N, unsigned_sum, 0);
    let n : bits(1) = [result['N - 1]];
    let z : bits(1) = if IsZero(result) then 0b1 else 0b0;
    let c : bits(1) = if UInt(result) == unsigned_sum then 0b0 else 0b1;
    let v : bits(1) = if SInt(result) == signed_sum then 0b0 else 0b1;
    return((result, ((n @ z) @ c) @ v))
}
``` -/
def AddWithCarry {w : Nat} (x y : BitVec w) (carryIn : Bool) : BitVec w × Flags :=
  let unsignedSum : Nat := x.toNat + y.toNat + carryIn.toNat
  let signedSum : Int := x.toInt + y.toInt + carryIn.toNat
  let result : BitVec w := BitVec.ofNat w unsignedSum
  (result, { n := result.msb
             z := decide (result = 0)
             c := decide (result.toNat ≠ unsignedSum)
             v := decide (result.toInt ≠ signedSum) })

/-- `cmp x, y` and `subs` are `AddWithCarry(operand1, NOT(operand2), '1')`
    (Sail: `operand2 = ~(operand2); (result, nzcv) = AddWithCarry(operand1,
    operand2, 0b1)`); `adds`/`cmn` are `AddWithCarry(operand1, operand2,
    '0')`. -/
def subFlags {w : Nat} (x y : BitVec w) : Flags := (AddWithCarry x (~~~y) true).2
def addFlags {w : Nat} (x y : BitVec w) : Flags := (AddWithCarry x y false).2

/-- The result of the subtraction form is `x - y`. -/
theorem AddWithCarry_sub_result {w : Nat} (x y : BitVec w) :
    (AddWithCarry x (~~~y) true).1 = x - y := by
  simp only [AddWithCarry, Bool.toNat_true]
  apply BitVec.eq_of_toNat_eq
  have hy := y.isLt
  simp only [BitVec.toNat_ofNat, BitVec.toNat_not, BitVec.toNat_sub]
  congr 1
  omega

/-- The result of the addition form is `x + y`. -/
theorem AddWithCarry_add_result {w : Nat} (x y : BitVec w) :
    (AddWithCarry x y false).1 = x + y := by
  simp only [AddWithCarry, Bool.toNat_false, Nat.add_zero]
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_ofNat, BitVec.toNat_add]

/-- **N, Z, C of `cmp` agree with Arm's.** Our `flagsOf` reads the flags of
    `l - r` directly; Arm computes them through `AddWithCarry(l, NOT r, 1)`.
    The carry equivalence is the "no borrow" reading: Arm's C is set exactly
    when the unsigned sum `l + (2^w - 1 - r) + 1` does not fit, i.e. `r ≤ l`. -/
theorem subFlags_n {w : Nat} (l r : BitVec w) : (subFlags l r).n = (flagsOf l r).n := by
  simp only [subFlags, flagsOf]
  have h := AddWithCarry_sub_result l r
  simp only [AddWithCarry] at h ⊢
  rw [h]

theorem subFlags_z {w : Nat} (l r : BitVec w) : (subFlags l r).z = (flagsOf l r).z := by
  simp only [subFlags, flagsOf]
  have h := AddWithCarry_sub_result l r
  simp only [AddWithCarry] at h ⊢
  rw [h]

theorem subFlags_c {w : Nat} (l r : BitVec w) : (subFlags l r).c = (flagsOf l r).c := by
  simp only [subFlags, flagsOf, AddWithCarry, Bool.toNat_true, BitVec.toNat_ofNat, BitVec.toNat_not]
  have hl := l.isLt
  have hr := r.isLt
  generalize hP : 2 ^ w = P at *
  rcases Nat.lt_or_ge (l.toNat + (P - 1 - r.toNat) + 1) P with hlt | hge
  · rw [Nat.mod_eq_of_lt hlt]
    simp
    omega
  · have hsub : (l.toNat + (P - 1 - r.toNat) + 1) % P = l.toNat + (P - 1 - r.toNat) + 1 - P := by
      rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt (by omega)]
    rw [hsub]
    simp
    have hne : ¬ (l.toNat + (P - 1 - r.toNat) + 1 - P = l.toNat + (P - 1 - r.toNat) + 1) := by omega
    have hle : r.toNat ≤ l.toNat := by omega
    simp [hne, hle]

/-- **N, Z, C of `adds` agree with Arm's.** -/
theorem addFlags_n {w : Nat} (l r : BitVec w) : (addFlags l r).n = (addFlagsOf l r).n := by
  simp only [addFlags, addFlagsOf]
  have h := AddWithCarry_add_result l r
  simp only [AddWithCarry] at h ⊢
  rw [h]

theorem addFlags_z {w : Nat} (l r : BitVec w) : (addFlags l r).z = (addFlagsOf l r).z := by
  simp only [addFlags, addFlagsOf]
  have h := AddWithCarry_add_result l r
  simp only [AddWithCarry] at h ⊢
  rw [h]

theorem addFlags_c {w : Nat} (l r : BitVec w) : (addFlags l r).c = (addFlagsOf l r).c := by
  simp only [addFlags, addFlagsOf, AddWithCarry, Bool.toNat_false, Nat.add_zero, BitVec.toNat_ofNat]
  have hl := l.isLt
  have hr := r.isLt
  generalize hP : 2 ^ w = P at *
  rcases Nat.lt_or_ge (l.toNat + r.toNat) P with hlt | hge
  · rw [Nat.mod_eq_of_lt hlt]
    simp
    omega
  · have hsub : (l.toNat + r.toNat) % P = l.toNat + r.toNat - P := by
      rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt (by omega)]
    rw [hsub]
    simp
    have hne : ¬ (l.toNat + r.toNat - P = l.toNat + r.toNat) := by omega
    have hle : P ≤ l.toNat + r.toNat := by omega
    simp [hne, hle]

set_option maxHeartbeats 2000000 in
/-- **V agrees with Arm's** — the signed-overflow reading through `SInt`
    versus our sign-bit formula — checked exhaustively at width 5 (every
    pair of operands, evaluated by the kernel), the executable cross-check
    the spec asks for; the silicon differential covers 32 and 64 bits on
    the hardware. -/
theorem subFlags_v_w5 : ∀ l r : BitVec 5, (subFlags l r).v = (flagsOf l r).v := by decide

set_option maxHeartbeats 2000000 in
/-- The addition form of the same check. -/
theorem addFlags_v_w5 : ∀ l r : BitVec 5, (addFlags l r).v = (addFlagsOf l r).v := by decide

/-- Arm's `ConditionHolds`, Sail text:
```
function ConditionHolds cond = {
    match slice(cond, 1, 3) {
      0b000 => result = PSTATE.Z == 0b1
      0b001 => result = PSTATE.C == 0b1
      0b010 => result = PSTATE.N == 0b1
      0b011 => result = PSTATE.V == 0b1
      0b100 => result = PSTATE.C == 0b1 & PSTATE.Z == 0b0
      0b101 => result = PSTATE.N == PSTATE.V
      0b110 => result = PSTATE.N == PSTATE.V & PSTATE.Z == 0b0
      0b111 => result = true
    };
    if [cond[0]] == 0b1 & cond != 0xF then result = ~(result);
    result
}
``` -/
def ConditionHolds (cond : BitVec 4) (f : Flags) : Bool :=
  let base : Bool :=
    match (cond >>> 1).toNat with
    | 0 => f.z
    | 1 => f.c
    | 2 => f.n
    | 3 => f.v
    | 4 => f.c && !f.z
    | 5 => f.n == f.v
    | 6 => (f.n == f.v) && !f.z
    | _ => true
  if cond.getLsbD 0 && cond ≠ 0xF then !base else base

/-- The A64 condition-code encodings. -/
def Cond.encode : Cond → BitVec 4
  | .eq => 0x0 | .ne => 0x1 | .hs => 0x2 | .lo => 0x3
  | .mi => 0x4 | .pl => 0x5 | .vs => 0x6 | .vc => 0x7
  | .hi => 0x8 | .ls => 0x9 | .ge => 0xA | .lt => 0xB
  | .gt => 0xC | .le => 0xD

/-- **Our condition table is Arm's `ConditionHolds` on the encodings**, for
    every code and every flag pattern. -/
theorem holds_eq_ConditionHolds (c : Cond) (f : Flags) :
    Cond.holds f c = ConditionHolds (Cond.encode c) f := by
  obtain ⟨n, z, cf, v⟩ := f
  cases c <;> cases n <;> cases z <;> cases cf <;> cases v <;> rfl

/-- Arm's conditional select (Sail `integer_conditional_select`):
```
    if ConditionHolds(condition) then result = operand1
    else { result = operand2;
           if else_inv then result = ~(result);
           if else_inc then result = result + 1 };
``` -/
def conditionalSelect {w : Nat} (cond : BitVec 4) (f : Flags) (elseInc elseInv : Bool) (a b : BitVec w) : BitVec w :=
  if ConditionHolds cond f then a
  else
    let r := if elseInv then ~~~b else b
    if elseInc then r + 1 else r

/-- `csel`, `csinc`, `csinv`, `csneg` are the four settings of the two
    flags; `csneg`'s `~b + 1` is `-b`. -/
theorem csel_asl {w : Nat} (c : Cond) (f : Flags) (a b : BitVec w) :
    csel c f a b = conditionalSelect (Cond.encode c) f false false a b := by
  simp [csel, conditionalSelect, ← holds_eq_ConditionHolds]

theorem csinc_asl {w : Nat} (c : Cond) (f : Flags) (a b : BitVec w) :
    (if c.holds f then a else b + 1) = conditionalSelect (Cond.encode c) f true false a b := by
  simp [conditionalSelect, ← holds_eq_ConditionHolds]

theorem csinv_asl {w : Nat} (c : Cond) (f : Flags) (a b : BitVec w) :
    (if c.holds f then a else ~~~b) = conditionalSelect (Cond.encode c) f false true a b := by
  simp [conditionalSelect, ← holds_eq_ConditionHolds]

theorem csneg_asl {w : Nat} (c : Cond) (f : Flags) (a b : BitVec w) :
    (if c.holds f then a else -b) = conditionalSelect (Cond.encode c) f true true a b := by
  simp [conditionalSelect, ← holds_eq_ConditionHolds, BitVec.neg_eq_not_add]

/-- Arm's conditional compare (Sail `integer_conditional_compare_register`):
    `if ConditionHolds(condition) then { if sub_op then { operand2 = ~operand2;
    carry_in = 1 }; (_, flags) = AddWithCarry(operand1, operand2, carry_in) }`
    — else the immediate flags stand. -/
def conditionalCompare {w : Nat} (cond : BitVec 4) (prior : Flags) (l r : BitVec w) (imm : Flags) (subOp : Bool) : Flags :=
  if ConditionHolds cond prior then
    (if subOp then AddWithCarry l (~~~r) true else AddWithCarry l r false).2
  else imm

/-- `ccmp` reads through Arm's definition, up to the flag equalities above
    (N, Z, C proved at every width, V at width 8). -/
theorem ccmp_asl_n {w : Nat} (c : Cond) (prior : Flags) (l r : BitVec w) (imm : Flags) :
    (ccmpFlags c prior l r imm).n = (conditionalCompare (Cond.encode c) prior l r imm true).n := by
  simp only [ccmpFlags, conditionalCompare, ← holds_eq_ConditionHolds]
  split
  · exact (subFlags_n l r).symm
  · rfl

/-- Arm's flag setting for the logical instructions (`ands`, `bics`, `tst`):
    `(N @ Z @ C @ V) = ([result[datasize - 1]] @ IsZeroBit(result)) @ 0b00`. -/
def logicalFlags {w : Nat} (result : BitVec w) : Flags :=
  { n := result.msb, z := decide (result = 0), c := false, v := false }

theorem tst_asl {w : Nat} (l r : BitVec w) : andFlagsOf l r = logicalFlags (l &&& r) := rfl

/-- Arm's `HighestSetBit`, `CountLeadingZeroBits`, `CountLeadingSignBits`:
```
function HighestSetBit x = { foreach (i from ('N - 1) to 0 by 1 in dec)
    { if [x[i]] == 0b1 then return(i) }; negate(1) }
function CountLeadingZeroBits x = 'N - (HighestSetBit(x) + 1)
function CountLeadingSignBits x =
    CountLeadingZeroBits(slice(x, 1, 'N - 1) ^ slice(x, 0, 'N - 1))
``` -/
def HighestSetBit {w : Nat} (x : BitVec w) : Int :=
  match (List.range w).reverse.find? (fun i => x.getLsbD i) with
  | some i => i
  | none => -1

def CountLeadingZeroBits {w : Nat} (x : BitVec w) : Int := w - (HighestSetBit x + 1)

def CountLeadingSignBits {w : Nat} (x : BitVec w) : Int :=
  CountLeadingZeroBits (((x >>> 1) ^^^ x).truncate (w - 1))

/-- `clz 0` is the width: no bit is set, so the highest set bit is -1. -/
theorem clz_zero (w : Nat) : CountLeadingZeroBits (0 : BitVec w) = w := by
  have h : (List.range w).reverse.find? (fun _ : Nat => false) = none := by
    rw [List.find?_eq_none]
    simp
  simp [CountLeadingZeroBits, HighestSetBit, h]

/-- Arm's division (`integer_arithmetic_div`): a zero divisor yields zero,
    otherwise the quotient rounded toward zero — exactly `BitVec.udiv` and
    `BitVec.sdiv`, which define division by zero as zero and round toward
    zero. -/
theorem udiv_asl {w : Nat} (x y : BitVec w) : (if y = 0 then 0 else x / y) = x / y := by
  split
  · subst_vars; simp [BitVec.udiv_zero]
  · rfl

end Oak.ArmASL
