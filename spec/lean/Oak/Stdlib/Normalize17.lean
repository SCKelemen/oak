import Oak.Normalization
import Oak.Stdlib.KeyTree
import Oak.Stdlib.NormalizeTables

/-!
# Oak.Stdlib.Normalize17 — the Unicode 17.0.0 instance of the normalization model

`Oak.Normalization` proves the NFC laws for any `UCD` that is closed
(`UCD.Closed`: nothing inside a decomposition decomposes further) and whose
primary composites undo their composition (`UCD.Inverse`). This file
instantiates the model with the Unicode 17.0.0 data `stdlib/normalize.oak`
carries — the generated key trees of `NormalizeTables.lean` plus the
algorithmic Hangul syllables (UAX #15 §3.12) — and discharges both
hypotheses: the table part by evaluating every entry in the kernel
(`decompTree_closed`, `pairTree_inverse`), the Hangul part by arithmetic on
the syllable index. `nfc_idem_u17` and `nfd_nfc_u17` are then unconditional.
-/

namespace Oak.Stdlib.Normalize17

open Oak.Normalization Oak.Stdlib.KeyTree

set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

/-! ## Hangul syllables (UAX #15 §3.12) -/

def sBase : Nat := 44032
def lBase : Nat := 4352
def vBase : Nat := 4449
def tBase : Nat := 4519
def lCount : Nat := 19
def vCount : Nat := 21
def tCount : Nat := 28
def nCount : Nat := 588
def sCount : Nat := 11172

def IsSyllable (c : Nat) : Prop := sBase ≤ c ∧ c < sBase + sCount

instance (c : Nat) : Decidable (IsSyllable c) := by unfold IsSyllable; infer_instance

/-- The full decomposition of a syllable: `L V` or `L V T`. -/
def hangulDecomp (c : Nat) : List Nat :=
  if (c - sBase) % tCount = 0 then
    [lBase + (c - sBase) / nCount, vBase + ((c - sBase) % nCount) / tCount]
  else
    [lBase + (c - sBase) / nCount, vBase + ((c - sBase) % nCount) / tCount, tBase + (c - sBase) % tCount]

/-- `L + V` is the `LV` syllable, `LV + T` the `LVT` syllable. -/
def hangulCompose (s c : Nat) : Option Nat :=
  if lBase ≤ s ∧ s < lBase + lCount ∧ vBase ≤ c ∧ c < vBase + vCount then
    some (sBase + ((s - lBase) * vCount + (c - vBase)) * tCount)
  else if IsSyllable s ∧ (s - sBase) % tCount = 0 ∧ tBase < c ∧ c < tBase + tCount then
    some (s + (c - tBase))
  else none

/-! ## The data -/

def ccc17 (c : Nat) : Nat := (lookup cccTree c).getD 0

def decomp17 (c : Nat) : Option (List Nat) :=
  if IsSyllable c then some (hangulDecomp c) else lookup decompTree c

def pairKey (s c : Nat) : Nat := s * 2097152 + c

def compose17 (s c : Nat) : Option Nat :=
  match hangulCompose s c with
  | some p => some p
  | none => if s < 2097152 ∧ c < 2097152 then lookup pairTree (pairKey s c) else none

/-- The Unicode 17.0.0 character data as the model reads it. -/
def u17 : UCD := { ccc := ccc17, decomp := decomp17, compose := compose17 }

theorem u17_decomp (c : Nat) : u17.decomp c = decomp17 c := rfl
theorem u17_compose (s c : Nat) : u17.compose s c = compose17 s c := rfl

/-! ## Facts the kernel decides over the tables -/

/-- The jamo range `1100..11C2` has no table decomposition. -/
theorem jamo_lookup_none : ∀ x : Fin 195, lookup decompTree (4352 + x.val) = none := by
  decide +kernel

/-- Every scalar inside a table decomposition has no decomposition of its own. -/
theorem decompTree_closed :
    (entries decompTree).all (fun e => e.2.all (fun x => (decomp17 x).isNone)) = true := by
  decide +kernel

/-- Every table composite undoes its composition through full decomposition, and
    the algorithm claims neither side. -/
theorem pairTree_inverse :
    (entries pairTree).all (fun e =>
      (hangulCompose (e.1 / 2097152) (e.1 % 2097152)).isNone &&
      (decompose u17 e.2 == decompose u17 (e.1 / 2097152) ++ [e.1 % 2097152])) = true := by
  decide +kernel

/-! ## Closure -/

theorem not_syllable_of_jamo (x : Nat) (h1 : 4352 ≤ x) (h2 : x < 4547) : ¬ IsSyllable x := by
  unfold IsSyllable; simp only [sBase, sCount]; omega

theorem decomp17_jamo (x : Nat) (h1 : 4352 ≤ x) (h2 : x < 4547) : decomp17 x = none := by
  unfold decomp17
  rw [if_neg (not_syllable_of_jamo x h1 h2)]
  have := jamo_lookup_none ⟨x - 4352, by omega⟩
  have hx : 4352 + (x - 4352) = x := by omega
  rw [hx] at this
  exact this

theorem hangulDecomp_mem_jamo (c x : Nat) (hc : IsSyllable c) (hx : x ∈ hangulDecomp c) :
    4352 ≤ x ∧ x < 4547 := by
  unfold IsSyllable sBase sCount at hc
  unfold hangulDecomp at hx
  rw [sBase, tCount, lBase, vBase, tBase, nCount] at hx
  split at hx
  · rw [List.mem_cons, List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with h | h
    · rw [h]; omega
    · rw [h]; omega
  · rw [List.mem_cons, List.mem_cons, List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with h | h | h
    · rw [h]; omega
    · rw [h]; omega
    · rw [h]; constructor <;> omega

theorem u17_closed : UCD.Closed u17 := by
  intro c d hcd x hx
  rw [u17_decomp] at hcd ⊢
  unfold decomp17 at hcd
  split at hcd
  · rename_i hs
    have hd : hangulDecomp c = d := Option.some.inj hcd
    rw [← hd] at hx
    have := hangulDecomp_mem_jamo c x hs hx
    exact decomp17_jamo x this.1 this.2
  · have hp := lookup_prop decompTree (fun _ d => d.all (fun x => (decomp17 x).isNone)) decompTree_closed c d hcd
    simp only [List.all_eq_true] at hp
    have := hp x hx
    cases h : decomp17 x with
    | none => rfl
    | some _ => rw [h] at this; simp at this

/-! ## Inverse -/

theorem decompose_jamo (x : Nat) (h1 : 4352 ≤ x) (h2 : x < 4547) : decompose u17 x = [x] :=
  decompose_of_none u17 (decomp17_jamo x h1 h2)

theorem decompose_syllable (c : Nat) (hc : IsSyllable c) : decompose u17 c = hangulDecomp c := by
  unfold decompose
  rw [u17_decomp]
  unfold decomp17
  rw [if_pos hc]
  exact Option.getD_some

theorem hangul_lv_inverse (s c : Nat)
    (h : lBase ≤ s ∧ s < lBase + lCount ∧ vBase ≤ c ∧ c < vBase + vCount) :
    decompose u17 (sBase + ((s - lBase) * vCount + (c - vBase)) * tCount) = decompose u17 s ++ [c] := by
  rw [lBase, lCount, vBase, vCount] at h
  rw [sBase, lBase, vCount, vBase, tCount]
  rw [decompose_jamo s (by omega) (by omega)]
  have hsyl : IsSyllable (44032 + ((s - 4352) * 21 + (c - 4449)) * 28) := by
    unfold IsSyllable sBase sCount; omega
  rw [decompose_syllable _ hsyl]
  unfold hangulDecomp
  rw [sBase, tCount, lBase, vBase, tBase, nCount]
  have ht : (44032 + ((s - 4352) * 21 + (c - 4449)) * 28 - 44032) % 28 = 0 := by omega
  rw [if_pos ht, List.singleton_append, List.cons.injEq, List.cons.injEq]
  refine ⟨?_, ?_, rfl⟩ <;> omega

theorem hangul_lvt_inverse (s c : Nat) (hs : IsSyllable s) (ht0 : (s - sBase) % tCount = 0)
    (hc : tBase < c ∧ c < tBase + tCount) :
    decompose u17 (s + (c - tBase)) = decompose u17 s ++ [c] := by
  have hs0 := hs
  unfold IsSyllable sBase sCount at hs0
  rw [sBase, tCount] at ht0
  rw [tBase, tCount] at hc
  rw [tBase]
  have hs' : IsSyllable (s + (c - 4519)) := by
    unfold IsSyllable sBase sCount; omega
  rw [decompose_syllable _ hs', decompose_syllable s hs]
  unfold hangulDecomp
  rw [sBase, tCount, lBase, vBase, tBase, nCount]
  rw [if_pos ht0]
  have ht : (s + (c - 4519) - 44032) % 28 ≠ 0 := by omega
  rw [if_neg ht, List.cons_append, List.cons_append, List.nil_append, List.cons.injEq,
    List.cons.injEq, List.cons.injEq]
  refine ⟨?_, ?_, ?_, rfl⟩ <;> omega

theorem u17_inverse : UCD.Inverse u17 := by
  intro s c p hcomp _hnone
  rw [u17_compose] at hcomp
  unfold compose17 at hcomp
  split at hcomp
  · rename_i q hq
    have hpq : q = p := Option.some.inj hcomp
    rw [hpq] at hq
    unfold hangulCompose at hq
    split at hq
    · rename_i h
      rw [← Option.some.inj hq]
      exact hangul_lv_inverse s c h
    · split at hq
      · rename_i h
        rw [← Option.some.inj hq]
        exact hangul_lvt_inverse s c h.1 h.2.1 h.2.2
      · exact absurd hq (by simp)
  · rename_i _hnoh
    split at hcomp
    · rename_i hlt
      have hp := lookup_prop pairTree
        (fun k p => (hangulCompose (k / 2097152) (k % 2097152)).isNone &&
          (decompose u17 p == decompose u17 (k / 2097152) ++ [k % 2097152]))
        pairTree_inverse (pairKey s c) p hcomp
      have hkey_s : pairKey s c / 2097152 = s := by unfold pairKey; omega
      have hkey_c : pairKey s c % 2097152 = c := by unfold pairKey; omega
      rw [hkey_s, hkey_c] at hp
      have hp2 := (Bool.and_eq_true _ _).mp hp
      exact beq_iff_eq.mp hp2.2
    · exact absurd hcomp (by simp)

/-! ## The laws, unconditionally, for Unicode 17.0.0 -/

theorem nfd_idem_u17 (l : List Nat) : nfd u17 (nfd u17 l) = nfd u17 l :=
  nfd_idem u17 u17_closed l

theorem nfd_nfc_u17 (l : List Nat) : nfd u17 (nfc u17 l) = nfd u17 l :=
  nfd_nfc u17 u17_closed u17_inverse l

theorem nfc_idem_u17 (l : List Nat) : nfc u17 (nfc u17 l) = nfc u17 l :=
  nfc_idem u17 u17_closed u17_inverse l

end Oak.Stdlib.Normalize17
