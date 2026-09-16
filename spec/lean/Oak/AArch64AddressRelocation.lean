import Std.Tactic.BVDecide

/-!
# AArch64 ADRP + ADD address relocation

This module specifies the arithmetic and bit-patching core used by the
executable writer's `adrl21` relocation.  It covers an already selected
two-instruction pair and natural-number place/target addresses admitted into
the production 64-bit address space, including the pair's complete eight-byte
footprint. It does not specify symbol resolution, section layout, file-format
relocation records, loading, register execution, or the provenance of the
original words.
-/

namespace Oak.AArch64AddressRelocation

def pageDelta (place target : Nat) : Int :=
  (target / 4096 : Nat) - (place / 4096 : Nat)

def adrlFits (place target : Nat) : Bool :=
  decide (place % 4 = 0 ∧ -(2 ^ 20) ≤ pageDelta place target ∧
    pageDelta place target < 2 ^ 20 ∧ place + 7 < 2 ^ 64 ∧
    target < 2 ^ 64)

def adrpImmediate (place target : Nat) : BitVec 21 :=
  BitVec.ofInt 21 (pageDelta place target)

def low12 (target : Nat) : BitVec 12 := BitVec.ofNat 12 target

def adrpOpcodeMatches (word : BitVec 32) : Bool :=
  (word &&& 0x9f000000#32) == 0x90000000#32

def addOpcodeMatches (word : BitVec 32) : Bool :=
  (word &&& 0xffc00000#32) == 0x91000000#32

def register (word : BitVec 32) : BitVec 5 := word.extractLsb' 0 5
def addBase (word : BitVec 32) : BitVec 5 := word.extractLsb' 5 5

def pairMatches (adrp add : BitVec 32) : Bool :=
  adrpOpcodeMatches adrp && addOpcodeMatches add &&
    register adrp != 31#5 && register adrp == register add &&
    register adrp == addBase add

def patchADRP (word : BitVec 32) (immediate : BitVec 21) : BitVec 32 :=
  (word &&& 0x9f00001f#32) |||
    ((immediate.extractLsb' 0 2).zeroExtend 32 <<< 29) |||
    ((immediate.extractLsb' 2 19).zeroExtend 32 <<< 5)

def patchADD (word : BitVec 32) (lo : BitVec 12) : BitVec 32 :=
  (word &&& 0xffc003ff#32) ||| (lo.zeroExtend 32 <<< 10)

def decodeADRPPageDelta (word : BitVec 32) : Int :=
  ((word.extractLsb' 5 19) ++ (word.extractLsb' 29 2)).toInt

def decodeADRLTarget (adrp add : BitVec 32) (place : Nat) : Int :=
  (place / 4096 : Nat) * 4096 + decodeADRPPageDelta adrp * 4096 +
    (add.extractLsb' 10 12).toNat

def relocateADRL (adrp add : BitVec 32) (place target : Nat) :
    Option (BitVec 32 × BitVec 32) :=
  if adrlFits place target && pairMatches adrp add then
    some (patchADRP adrp (adrpImmediate place target),
      patchADD add (low12 target))
  else
    none

theorem patchADRP_fixed (word : BitVec 32) (immediate : BitVec 21) :
    patchADRP word immediate &&& 0x9f00001f#32 =
      word &&& 0x9f00001f#32 := by
  unfold patchADRP
  bv_decide

theorem patchADRP_immediate (word : BitVec 32) (immediate : BitVec 21) :
    (patchADRP word immediate).extractLsb' 5 19 ++
      (patchADRP word immediate).extractLsb' 29 2 = immediate := by
  unfold patchADRP
  bv_decide

theorem patchADD_fixed (word : BitVec 32) (lo : BitVec 12) :
    patchADD word lo &&& 0xffc003ff#32 = word &&& 0xffc003ff#32 := by
  unfold patchADD
  bv_decide

theorem patchADD_immediate (word : BitVec 32) (lo : BitVec 12) :
    (patchADD word lo).extractLsb' 10 12 = lo := by
  unfold patchADD
  bv_decide

theorem adrpImmediate_toInt (place target : Nat)
    (hfits : adrlFits place target = true) :
    (adrpImmediate place target).toInt = pageDelta place target := by
  simp only [adrlFits, decide_eq_true_eq] at hfits
  unfold adrpImmediate
  exact BitVec.toInt_ofInt_eq_self (by omega) hfits.2.1 hfits.2.2.1

theorem low12_toNat (target : Nat) :
    (low12 target).toNat = target % 4096 := by
  simp [low12, BitVec.toNat_ofNat]

theorem decodeADRP_patch (word : BitVec 32) (place target : Nat)
    (hfits : adrlFits place target = true) :
    decodeADRPPageDelta (patchADRP word (adrpImmediate place target)) =
      pageDelta place target := by
  unfold decodeADRPPageDelta
  rw [patchADRP_immediate]
  exact adrpImmediate_toInt place target hfits

theorem decodeADRL_patch_reaches (adrp add : BitVec 32) (place target : Nat)
    (hfits : adrlFits place target = true) :
    decodeADRLTarget (patchADRP adrp (adrpImmediate place target))
      (patchADD add (low12 target)) place = target := by
  rw [decodeADRLTarget, decodeADRP_patch adrp place target hfits,
    patchADD_immediate, low12_toNat]
  unfold pageDelta
  have hdiv := Nat.div_add_mod target 4096
  omega

theorem relocateADRL_eq_some_iff (adrp add patchedADRP patchedADD : BitVec 32)
    (place target : Nat) :
    relocateADRL adrp add place target = some (patchedADRP, patchedADD) ↔
      adrlFits place target = true ∧ pairMatches adrp add = true ∧
      patchedADRP = patchADRP adrp (adrpImmediate place target) ∧
      patchedADD = patchADD add (low12 target) := by
  unfold relocateADRL
  by_cases hfits : adrlFits place target = true <;>
    by_cases hpair : pairMatches adrp add = true <;>
      simp [hfits, hpair, eq_comm]

theorem relocateADRL_preserves_fields {adrp add patchedADRP patchedADD : BitVec 32}
    {place target : Nat}
    (h : relocateADRL adrp add place target = some (patchedADRP, patchedADD)) :
    patchedADRP &&& 0x9f00001f#32 = adrp &&& 0x9f00001f#32 ∧
      patchedADD &&& 0xffc003ff#32 = add &&& 0xffc003ff#32 := by
  have hs := (relocateADRL_eq_some_iff adrp add patchedADRP patchedADD place target).mp h
  rw [hs.2.2.1, hs.2.2.2]
  exact ⟨patchADRP_fixed _ _, patchADD_fixed _ _⟩

theorem relocateADRL_reaches {adrp add patchedADRP patchedADD : BitVec 32}
    {place target : Nat}
    (h : relocateADRL adrp add place target = some (patchedADRP, patchedADD)) :
    decodeADRLTarget patchedADRP patchedADD place = target := by
  have hs := (relocateADRL_eq_some_iff adrp add patchedADRP patchedADD place target).mp h
  rw [hs.2.2.1, hs.2.2.2]
  exact decodeADRL_patch_reaches adrp add place target hs.1

/-! ## Production correspondence examples -/

example : pairMatches 0x90000009#32 0x91000129#32 = true := by decide
example : pairMatches 0x10000009#32 0x91000129#32 = false := by decide
example : pairMatches 0x90000009#32 0x91400129#32 = false := by decide
example : pairMatches 0x90000009#32 0x91000109#32 = false := by decide
example : pairMatches 0x9000001f#32 0x910003ff#32 = false := by decide

example : adrlFits 0x10004 0x10abc = true := by decide
example : adrlFits 0 (((2 ^ 20) - 1) * 4096 + 4095) = true := by decide
example : adrlFits (2 ^ 20 * 4096) 0xabc = true := by decide
example : adrlFits 0 (2 ^ 20 * 4096) = false := by decide
example : adrlFits ((2 ^ 20 + 1) * 4096) 0 = false := by decide
example : adrlFits (2 ^ 64 - 4) 0 = false := by decide
example : adrlFits (2 ^ 64 - 8) (2 ^ 64 - 1) = true := by decide
example : adrlFits (2 ^ 64 - 4) (2 ^ 64 - 1) = false := by decide
example : adrlFits 0 (2 ^ 64 - 1) = false := by decide

example :
    relocateADRL 0x90000009#32 0x91000129#32 0x10004 0x10abc =
      some (0x90000009#32, 0x912af129#32) := by decide

end Oak.AArch64AddressRelocation
