import Oak.Stdlib.HashExtracted
import Oak.Stdlib.HashLaws

/-!
# Oak.Stdlib.Sha256Laws — the streaming law of the extracted SHA-256

A digest computed by feeding the input in pieces equals the digest of the
whole input: `sha256_update` over `a` and then over `b` reaches a state
equivalent to `sha256_update` over `a ++ b`, and `sha256_final` respects that
equivalence, so `sha256 (a ++ b)` is the pieces' digest. The proof does not
open the compression function: it only needs that the compression is total
and fuel-insensitive once the fuel exceeds its round count, and that it reads
the block through the first sixty-four bytes. Everything else is the byte
loop of `sha256_update`, its whole-block fast path, and the padding loops of
`sha256_final`.

The equivalence is needed because the fast path compresses a window of the
input directly and leaves the state's block buffer untouched, while the byte
path copies bytes into the buffer first; the two agree on the hash words, the
fill count, the byte total, and the buffered prefix, which is all the
finalization reads.
-/

namespace Oak.Stdlib.Hash

set_option maxRecDepth 65536
set_option linter.unusedSimpArgs false

/-! ## Fuel does not matter once it covers the rounds -/

theorem rounds_loop1_fuel : ∀ (n : Nat) (w : Array UInt32) (i : UInt32) (f1 f2 : Nat),
    64 - i.toNat ≤ n → n < f1 → n < f2 →
      sha256_rounds.loop1 w i f1 = sha256_rounds.loop1 w i f2 ∧ ∃ r, sha256_rounds.loop1 w i f1 = some r := by
  intro n
  induction n with
  | zero =>
    intro w i f1 f2 hn h1 h2
    cases f1 with
    | zero => omega
    | succ f1 =>
      cases f2 with
      | zero => omega
      | succ f2 =>
        unfold sha256_rounds.loop1
        have hd : decide (i < (64 : UInt32)) = false := by
          apply decide_eq_false; rw [UInt32.lt_iff_toNat_lt]; simp; omega
        simp only [hd, Bool.false_eq_true, ↓reduceIte, Option.pure_def]
        first | exact ⟨trivial, _, rfl⟩ | exact ⟨rfl, _, rfl⟩
  | succ n ih =>
    intro w i f1 f2 hn h1 h2
    cases f1 with
    | zero => omega
    | succ f1 =>
      cases f2 with
      | zero => omega
      | succ f2 =>
        unfold sha256_rounds.loop1
        by_cases hlt : i < (64 : UInt32)
        · have hd : decide (i < (64 : UInt32)) = true := decide_eq_true hlt
          simp only [hd, ↓reduceIte, rotr32, Option.pure_def, Option.bind_eq_bind, Option.bind_some]
          have hi : i.toNat < 64 := by
            have := UInt32.lt_iff_toNat_lt.mp hlt; simpa using this
          have hi1 : (i + 1).toNat = i.toNat + 1 := by
            rw [UInt32.toNat_add, show (1 : UInt32).toNat = 1 by decide]; exact Nat.mod_eq_of_lt (by omega)
          exact ih _ (i + 1) f1 f2 (by omega) (by omega) (by omega)
        · have hd : decide (i < (64 : UInt32)) = false := decide_eq_false hlt
          simp only [hd, Bool.false_eq_true, ↓reduceIte, Option.pure_def]
          first | exact ⟨trivial, _, rfl⟩ | exact ⟨rfl, _, rfl⟩

theorem rounds_loop2_fuel : ∀ (n : Nat) (w : Array UInt32) (i a b c d e f g hh : UInt32) (f1 f2 : Nat),
    64 - i.toNat ≤ n → n < f1 → n < f2 →
      sha256_rounds.loop2 w i a b c d e f g hh f1 = sha256_rounds.loop2 w i a b c d e f g hh f2 ∧
      ∃ r, sha256_rounds.loop2 w i a b c d e f g hh f1 = some r := by
  intro n
  induction n with
  | zero =>
    intro w i a b c d e f g hh f1 f2 hn h1 h2
    cases f1 with
    | zero => omega
    | succ f1 =>
      cases f2 with
      | zero => omega
      | succ f2 =>
        unfold sha256_rounds.loop2
        have hd : decide (i < (64 : UInt32)) = false := by
          apply decide_eq_false; rw [UInt32.lt_iff_toNat_lt]; simp; omega
        simp only [hd, Bool.false_eq_true, ↓reduceIte, Option.pure_def]
        first | exact ⟨trivial, _, rfl⟩ | exact ⟨rfl, _, rfl⟩
  | succ n ih =>
    intro w i a b c d e f g hh f1 f2 hn h1 h2
    cases f1 with
    | zero => omega
    | succ f1 =>
      cases f2 with
      | zero => omega
      | succ f2 =>
        unfold sha256_rounds.loop2
        by_cases hlt : i < (64 : UInt32)
        · have hd : decide (i < (64 : UInt32)) = true := decide_eq_true hlt
          simp only [hd, ↓reduceIte, rotr32, Option.pure_def, Option.bind_eq_bind, Option.bind_some]
          have hi : i.toNat < 64 := by
            have := UInt32.lt_iff_toNat_lt.mp hlt; simpa using this
          have hi1 : (i + 1).toNat = i.toNat + 1 := by
            rw [UInt32.toNat_add, show (1 : UInt32).toNat = 1 by decide]; exact Nat.mod_eq_of_lt (by omega)
          exact ih w (i + 1) _ _ _ _ _ _ _ _ f1 f2 (by omega) (by omega) (by omega)
        · have hd : decide (i < (64 : UInt32)) = false := decide_eq_false hlt
          simp only [hd, Bool.false_eq_true, ↓reduceIte, Option.pure_def]
          first | exact ⟨trivial, _, rfl⟩ | exact ⟨rfl, _, rfl⟩

theorem rounds_fuel (h w : Array UInt32) (f1 f2 : Nat) (h1 : 64 < f1) (h2 : 64 < f2) :
    sha256_rounds h w f1 = sha256_rounds h w f2 ∧ ∃ r, sha256_rounds h w f1 = some r := by
  unfold sha256_rounds
  dsimp only
  obtain ⟨heq1, r1, hr1⟩ := rounds_loop1_fuel 48 w 16 f1 f2 (by simp) (by omega) (by omega)
  rw [← heq1, hr1]
  obtain ⟨w', i'⟩ := r1
  simp only [bind, Option.bind]
  obtain ⟨heq2, r2, hr2⟩ := rounds_loop2_fuel 64 w' 0 (h.getD 0 0) (h.getD 1 0) (h.getD 2 0) (h.getD 3 0)
    (h.getD 4 0) (h.getD 5 0) (h.getD 6 0) (h.getD 7 0) f1 f2 (by simp) (by omega) (by omega)
  rw [← heq2, hr2]
  obtain ⟨_, _, _, _, _, _, _, _, _⟩ := r2
  first | exact ⟨trivial, _, rfl⟩ | exact ⟨rfl, _, rfl⟩

theorem compress_loop1_fuel : ∀ (n : Nat) (block : Array UInt8) (w : Array UInt32) (i : UInt32) (f1 f2 : Nat),
    16 - i.toNat ≤ n → n < f1 → n < f2 →
      sha256_compress.loop1 block w i f1 = sha256_compress.loop1 block w i f2 ∧
      ∃ r, sha256_compress.loop1 block w i f1 = some r := by
  intro n
  induction n with
  | zero =>
    intro block w i f1 f2 hn h1 h2
    cases f1 with
    | zero => omega
    | succ f1 =>
      cases f2 with
      | zero => omega
      | succ f2 =>
        unfold sha256_compress.loop1
        have hd : decide (i < (16 : UInt32)) = false := by
          apply decide_eq_false; rw [UInt32.lt_iff_toNat_lt]; simp; omega
        simp only [hd, Bool.false_eq_true, ↓reduceIte, Option.pure_def]
        first | exact ⟨trivial, _, rfl⟩ | exact ⟨rfl, _, rfl⟩
  | succ n ih =>
    intro block w i f1 f2 hn h1 h2
    cases f1 with
    | zero => omega
    | succ f1 =>
      cases f2 with
      | zero => omega
      | succ f2 =>
        unfold sha256_compress.loop1
        by_cases hlt : i < (16 : UInt32)
        · have hd : decide (i < (16 : UInt32)) = true := decide_eq_true hlt
          simp only [hd, ↓reduceIte]
          have hi : i.toNat < 16 := by
            have := UInt32.lt_iff_toNat_lt.mp hlt; simpa using this
          have hi1 : (i + 1).toNat = i.toNat + 1 := by
            rw [UInt32.toNat_add, show (1 : UInt32).toNat = 1 by decide]; exact Nat.mod_eq_of_lt (by omega)
          exact ih block _ (i + 1) f1 f2 (by omega) (by omega) (by omega)
        · have hd : decide (i < (16 : UInt32)) = false := decide_eq_false hlt
          simp only [hd, Bool.false_eq_true, ↓reduceIte, Option.pure_def]
          first | exact ⟨trivial, _, rfl⟩ | exact ⟨rfl, _, rfl⟩

/-- The fuel any compression needs; `sha256_compress` and `sha256_compress_view`
    agree with their value at this fuel from here on. -/
def compressFuel : Nat := 128

theorem compress_fuel (h : Array UInt32) (block : Array UInt8) (f1 f2 : Nat) (h1 : 64 < f1) (h2 : 64 < f2) :
    sha256_compress h block f1 = sha256_compress h block f2 ∧ ∃ r, sha256_compress h block f1 = some r := by
  unfold sha256_compress
  dsimp only
  obtain ⟨heq1, r1, hr1⟩ := compress_loop1_fuel 16 block (Array.replicate 64 0) 0 f1 f2 (by simp) (by omega) (by omega)
  rw [← heq1, hr1]
  obtain ⟨w', i'⟩ := r1
  simp only [bind, Option.bind]
  obtain ⟨heq2, r2, hr2⟩ := rounds_fuel h w' f1 f2 h1 h2
  rw [← heq2, hr2]
  first | exact ⟨trivial, _, rfl⟩ | exact ⟨rfl, _, rfl⟩

/-- The compression as a function: its value at `compressFuel`. -/
def compressFn (h : Array UInt32) (block : Array UInt8) : Array UInt32 :=
  match sha256_compress h block compressFuel with
  | some r => r
  | none => h

theorem compress_eq (h : Array UInt32) (block : Array UInt8) (fuel : Nat) (hf : 64 < fuel) :
    sha256_compress h block fuel = some (compressFn h block) := by
  obtain ⟨heq, r, hr⟩ := compress_fuel h block fuel compressFuel hf (by decide)
  unfold compressFn
  rw [← heq, hr]

/-! ## The compression reads the block through its first sixty-four bytes -/

theorem compress_loop1_congr (block block' : Array UInt8) (hb : ∀ k, k < 64 → block.getD k 0 = block'.getD k 0)
    (w : Array UInt32) (i : UInt32) (fuel : Nat) :
    sha256_compress.loop1 block w i fuel = sha256_compress.loop1 block' w i fuel := by
  induction fuel generalizing w i with
  | zero => rfl
  | succ fuel ih =>
    unfold sha256_compress.loop1
    by_cases hlt : i < (16 : UInt32)
    · have hd : decide (i < (16 : UInt32)) = true := decide_eq_true hlt
      simp only [hd, ↓reduceIte]
      have hi : i.toNat < 16 := by
        have := UInt32.lt_iff_toNat_lt.mp hlt; simpa using this
      have h4 : (i * 4).toNat = 4 * i.toNat := by
        rw [UInt32.toNat_mul, show (4 : UInt32).toNat = 4 by decide, Nat.mod_eq_of_lt (by omega)]; omega
      have hk : ∀ c : UInt32, c.toNat ≤ 3 → (i * 4 + c).toNat = 4 * i.toNat + c.toNat := by
        intro c hc; rw [UInt32.toNat_add, h4, Nat.mod_eq_of_lt (by omega)]
      have e0 : block.getD (i * 4).toNat 0 = block'.getD (i * 4).toNat 0 := hb _ (by rw [h4]; omega)
      have e1 : block.getD (i * 4 + 1).toNat 0 = block'.getD (i * 4 + 1).toNat 0 :=
        hb _ (by rw [hk 1 (by decide)]; simp; omega)
      have e2 : block.getD (i * 4 + 2).toNat 0 = block'.getD (i * 4 + 2).toNat 0 :=
        hb _ (by rw [hk 2 (by decide)]; simp; omega)
      have e3 : block.getD (i * 4 + 3).toNat 0 = block'.getD (i * 4 + 3).toNat 0 :=
        hb _ (by rw [hk 3 (by decide)]; simp; omega)
      rw [e0, e1, e2, e3]
      exact ih _ _
    · have hd : decide (i < (16 : UInt32)) = false := decide_eq_false hlt
      simp only [hd, Bool.false_eq_true, ↓reduceIte]

theorem compress_congr (h : Array UInt32) (block block' : Array UInt8)
    (hb : ∀ k, k < 64 → block.getD k 0 = block'.getD k 0) (fuel : Nat) :
    sha256_compress h block fuel = sha256_compress h block' fuel := by
  unfold sha256_compress
  dsimp only
  rw [compress_loop1_congr block block' hb]

theorem compressFn_congr (h : Array UInt32) (block block' : Array UInt8)
    (hb : ∀ k, k < 64 → block.getD k 0 = block'.getD k 0) : compressFn h block = compressFn h block' := by
  unfold compressFn; rw [compress_congr h block block' hb]

theorem view_loop1_eq (block : Array UInt8) (w : Array UInt32) (i : UInt32) (fuel : Nat) :
    sha256_compress_view.loop1 block w i fuel = sha256_compress.loop1 block w i fuel := by
  induction fuel generalizing w i with
  | zero => rfl
  | succ fuel ih =>
    unfold sha256_compress_view.loop1 sha256_compress.loop1
    by_cases hlt : i < (16 : UInt32)
    · have hd : decide (i < (16 : UInt32)) = true := decide_eq_true hlt
      simp only [hd, ↓reduceIte]
      exact ih _ _
    · have hd : decide (i < (16 : UInt32)) = false := decide_eq_false hlt
      simp only [hd, Bool.false_eq_true, ↓reduceIte]

theorem compress_view_eq (h : Array UInt32) (block : Array UInt8) (hsize : 64 ≤ block.size) (hsmall : block.size < 2 ^ 32)
    (fuel : Nat) : sha256_compress_view h block fuel = sha256_compress h block fuel := by
  unfold sha256_compress_view sha256_compress
  dsimp only
  have hd : decide (block.size.toUInt32 ≥ (64 : UInt32)) = true := by
    apply decide_eq_true
    show (64 : UInt32) ≤ block.size.toUInt32
    rw [UInt32.le_iff_toNat_le, toUInt32_toNat_of_lt _ hsmall]; simpa using hsize
  simp only [hd, ↓reduceIte, view_loop1_eq]

/-! ## The byte model of `sha256_update` -/

/-- A state whose block buffer has the sixty-four bytes `sha256_init` gives it. -/
def WF (s : Sha256State) : Prop := s.block.size = 64

/-- Two states the finalization cannot tell apart: same hash words, fill
    count, byte total, and buffered prefix. The fast path of `sha256_update`
    leaves bytes it compressed directly out of the buffer, so this is the
    relation the streaming law holds up to. -/
def Equiv (s t : Sha256State) : Prop :=
  s.h = t.h ∧ s.filled = t.filled ∧ s.total = t.total ∧
  ∀ k, k < s.filled.toNat → s.block.getD k 0 = t.block.getD k 0

theorem Equiv.refl (s : Sha256State) : Equiv s s := ⟨rfl, rfl, rfl, fun _ _ => rfl⟩

theorem Equiv.symm {s t : Sha256State} (h : Equiv s t) : Equiv t s := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨h1.symm, h2.symm, h3.symm, fun k hk => (h4 k (by rw [h2]; exact hk)).symm⟩

theorem Equiv.trans {s t u : Sha256State} (h : Equiv s t) (h' : Equiv t u) : Equiv s u := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  obtain ⟨h1', h2', h3', h4'⟩ := h'
  exact ⟨h1.trans h1', h2.trans h2', h3.trans h3', fun k hk => (h4 k hk).trans (h4' k (by rw [← h2]; exact hk))⟩

/-- The state with its byte total replaced. -/
def setTotal (s : Sha256State) (x : UInt64) : Sha256State := { s with total := x }

/-- One byte into the state: buffer it, and compress when the block fills. -/
def absorb (s : Sha256State) (b : UInt8) : Sha256State :=
  let blk := s.block.setIfInBounds s.filled.toNat b
  let f := s.filled + 1
  if f == (64 : UInt32) then { s with h := compressFn s.h blk, block := blk, filled := 0 }
  else { s with block := blk, filled := f }

/-- `n` bytes of `src` from index `i`. -/
def absorbRange (src : Array UInt8) (s : Sha256State) (i : Nat) : Nat → Sha256State
  | 0 => s
  | n + 1 => absorbRange src (absorb s (src.getD i 0)) (i + 1) n

theorem absorbRange_zero (src : Array UInt8) (s : Sha256State) (i : Nat) : absorbRange src s i 0 = s := rfl
theorem absorbRange_succ (src : Array UInt8) (s : Sha256State) (i n : Nat) :
    absorbRange src s i (n + 1) = absorbRange src (absorb s (src.getD i 0)) (i + 1) n := rfl

theorem absorbRange_add (src : Array UInt8) (s : Sha256State) (i m n : Nat) :
    absorbRange src (absorbRange src s i m) (i + m) n = absorbRange src s i (m + n) := by
  induction m generalizing s i with
  | zero => simp [absorbRange_zero]
  | succ m ih =>
    rw [absorbRange_succ, Nat.succ_add, absorbRange_succ]
    have := ih (absorb s (src.getD i 0)) (i + 1)
    rw [show i + 1 + m = i + (m + 1) by omega] at this
    exact this

theorem absorbRange_congr (src src' : Array UInt8) (s : Sha256State) (i i' n : Nat)
    (h : ∀ k, k < n → src.getD (i + k) 0 = src'.getD (i' + k) 0) :
    absorbRange src s i n = absorbRange src' s i' n := by
  induction n generalizing s i i' with
  | zero => rfl
  | succ n ih =>
    rw [absorbRange_succ, absorbRange_succ]
    have h0 := h 0 (by omega)
    simp only [Nat.add_zero] at h0
    rw [h0]
    apply ih
    intro k hk
    have := h (k + 1) (by omega)
    rw [show i + (k + 1) = i + 1 + k by omega, show i' + (k + 1) = i' + 1 + k by omega] at this
    exact this

theorem absorb_wf {s : Sha256State} (hs : WF s) (b : UInt8) : WF (absorb s b) := by
  unfold absorb WF at *
  dsimp only
  split <;> simp [hs]

theorem absorbRange_wf {s : Sha256State} (hs : WF s) (src : Array UInt8) (i n : Nat) : WF (absorbRange src s i n) := by
  induction n generalizing s i with
  | zero => exact hs
  | succ n ih => rw [absorbRange_succ]; exact ih (absorb_wf hs _) _

theorem absorb_total (s : Sha256State) (b : UInt8) : (absorb s b).total = s.total := by
  unfold absorb; dsimp only; split <;> rfl

theorem absorbRange_total (src : Array UInt8) (s : Sha256State) (i n : Nat) : (absorbRange src s i n).total = s.total := by
  induction n generalizing s i with
  | zero => rfl
  | succ n ih => rw [absorbRange_succ, ih, absorb_total]

theorem getD_setIfInBounds_ne (a : Array UInt8) (j k : Nat) (v : UInt8) (h : j ≠ k) :
    (a.setIfInBounds j v).getD k 0 = a.getD k 0 := by
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds, if_neg h]

theorem getD_setIfInBounds_eq (a : Array UInt8) (j : Nat) (v : UInt8) (h : j < a.size) :
    (a.setIfInBounds j v).getD j 0 = v := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds, if_pos rfl, if_pos h]; rfl

theorem filled_lt_of_wf {s : Sha256State} (hf : s.filled.toNat < 64) : (s.filled + 1).toNat = s.filled.toNat + 1 := by
  rw [UInt32.toNat_add, show (1 : UInt32).toNat = 1 by decide]; exact Nat.mod_eq_of_lt (by omega)

/-- Absorbing the same byte into equivalent well-formed states with the
    buffer below sixty-four keeps them equivalent. -/
theorem absorb_equiv {s t : Sha256State} (hs : WF s) (ht : WF t) (hf : s.filled.toNat < 64) (heq : Equiv s t) (b : UInt8) :
    Equiv (absorb s b) (absorb t b) := by
  obtain ⟨h1, h2, h3, h4⟩ := heq
  have hblk : ∀ k, k ≤ s.filled.toNat →
      (s.block.setIfInBounds s.filled.toNat b).getD k 0 = (t.block.setIfInBounds s.filled.toNat b).getD k 0 := by
    intro k hk
    by_cases hkf : k = s.filled.toNat
    · subst hkf
      rw [getD_setIfInBounds_eq _ _ _ (by rw [hs]; exact hf), getD_setIfInBounds_eq _ _ _ (by rw [ht]; exact hf)]
    · rw [getD_setIfInBounds_ne _ _ _ _ (Ne.symm hkf), getD_setIfInBounds_ne _ _ _ _ (Ne.symm hkf)]
      exact h4 k (by omega)
  unfold absorb
  dsimp only
  rw [← h2, ← h1]
  by_cases h64 : (s.filled + 1 == (64 : UInt32)) = true
  · simp only [h64, ↓reduceIte]
    have h64' : s.filled.toNat = 63 := by
      have := congrArg UInt32.toNat (beq_iff_eq.mp h64)
      rw [filled_lt_of_wf hf] at this; simpa using this
    refine ⟨?_, rfl, h3, fun k hk => by simp at hk⟩
    show compressFn s.h _ = compressFn s.h _
    apply compressFn_congr
    intro k hk
    exact hblk k (by omega)
  · simp only [h64, Bool.false_eq_true, ↓reduceIte]
    refine ⟨rfl, rfl, h3, ?_⟩
    intro k hk
    show (s.block.setIfInBounds s.filled.toNat b).getD k 0 = (t.block.setIfInBounds s.filled.toNat b).getD k 0
    have hk' : k < (s.filled + 1).toNat := hk
    rw [filled_lt_of_wf hf] at hk'
    exact hblk k (by omega)

/-- The fill count never reaches sixty-four. -/
theorem absorb_filled_lt {s : Sha256State} (hf : s.filled.toNat < 64) (b : UInt8) : (absorb s b).filled.toNat < 64 := by
  unfold absorb
  dsimp only
  split
  · simp
  · rename_i h64
    show (s.filled + 1).toNat < 64
    rw [filled_lt_of_wf hf]
    have : s.filled.toNat + 1 ≠ 64 := by
      intro h; apply h64; rw [beq_iff_eq]; apply UInt32.toNat.inj; rw [filled_lt_of_wf hf, h]; decide
    omega

theorem absorbRange_filled_lt {s : Sha256State} (hf : s.filled.toNat < 64) (src : Array UInt8) (i n : Nat) :
    (absorbRange src s i n).filled.toNat < 64 := by
  induction n generalizing s i with
  | zero => exact hf
  | succ n ih => rw [absorbRange_succ]; exact ih (absorb_filled_lt hf _) _

theorem absorbRange_equiv {s t : Sha256State} (hs : WF s) (ht : WF t) (hf : s.filled.toNat < 64) (heq : Equiv s t)
    (src : Array UInt8) (i n : Nat) : Equiv (absorbRange src s i n) (absorbRange src t i n) := by
  induction n generalizing s t i with
  | zero => exact heq
  | succ n ih =>
    rw [absorbRange_succ, absorbRange_succ]
    exact ih (absorb_wf hs _) (absorb_wf ht _) (absorb_filled_lt hf _) (absorb_equiv hs ht hf heq _) (i + 1)

/-! ## The byte loop -/

theorem toUInt32_toNat_of_lt' (n : Nat) (h : n < 2 ^ 32) : (n.toUInt32).toNat = n := toUInt32_toNat_of_lt n h

theorem update_loop2 (src : Array UInt8) (hsrc : src.size < 2 ^ 32) :
    ∀ (fuel : Nat) (s : Sha256State) (i : UInt32), i.toNat ≤ src.size → src.size - i.toNat + 65 < fuel →
      sha256_update.loop2 src s i fuel = some (absorbRange src s i.toNat (src.size - i.toNat), src.size.toUInt32) := by
  intro fuel
  induction fuel with
  | zero => intro s i _ hf; omega
  | succ fuel ih =>
    intro s i hi hf
    have hsz : (src.size.toUInt32).toNat = src.size := toUInt32_toNat_of_lt _ hsrc
    unfold sha256_update.loop2
    by_cases hlt : i.toNat < src.size
    · have hd : decide (i < src.size.toUInt32) = true := by
        rw [decide_eq_true_iff, UInt32.lt_iff_toNat_lt, hsz]; exact hlt
      simp only [hd, ↓reduceIte]
      have hi1 : (i + 1).toNat = i.toNat + 1 := by
        rw [UInt32.toNat_add, show (1 : UInt32).toNat = 1 by decide]; exact Nat.mod_eq_of_lt (by omega)
      rw [show src.size - i.toNat = (src.size - (i.toNat + 1)) + 1 by omega, absorbRange_succ]
      -- the body is one `absorb`
      by_cases h64 : (s.filled + 1 == (64 : UInt32)) = true
      · simp only [h64, ↓reduceIte, compress_eq _ _ fuel (by omega)]
        simp only [bind, Option.bind, Option.pure_def]
        rw [ih _ (i + 1) (by omega) (by omega), hi1]
        unfold absorb; dsimp only; rw [if_pos h64]
      · simp only [h64, Bool.false_eq_true, ↓reduceIte]
        simp only [bind, Option.bind, Option.pure_def]
        rw [ih _ (i + 1) (by omega) (by omega), hi1]
        unfold absorb; dsimp only; rw [if_neg h64]
    · have hd : decide (i < src.size.toUInt32) = false := by
        rw [decide_eq_false_iff_not, UInt32.lt_iff_toNat_lt, hsz]; exact hlt
      simp only [hd, Bool.false_eq_true, ↓reduceIte]
      have : src.size - i.toNat = 0 := by omega
      rw [this, absorbRange_zero]
      have hi' : i = src.size.toUInt32 := by apply UInt32.toNat.inj; rw [hsz]; omega
      rw [hi']; rfl

/-! ## The whole-block fast path -/

/-- Below sixty-four bytes from an empty buffer, absorbing only buffers. -/
theorem absorb_prefix (src : Array UInt8) (s : Sha256State) (hs : WF s) (h0 : s.filled = 0) (i : Nat) :
    ∀ m, m ≤ 63 →
      (absorbRange src s i m).h = s.h ∧ (absorbRange src s i m).filled.toNat = m ∧
      (absorbRange src s i m).total = s.total ∧ WF (absorbRange src s i m) ∧
      ∀ k, k < m → (absorbRange src s i m).block.getD k 0 = src.getD (i + k) 0 := by
  intro m
  induction m with
  | zero => intro _; refine ⟨rfl, by rw [absorbRange_zero, h0]; rfl, rfl, hs, fun k hk => by omega⟩
  | succ m ih =>
    intro hm
    obtain ⟨hh, hfill, htot, hwf, hget⟩ := ih (by omega)
    have hstep : absorbRange src s i (m + 1) = absorb (absorbRange src s i m) (src.getD (i + m) 0) := by
      rw [← absorbRange_add src s i m 1, absorbRange_succ, absorbRange_zero]
    rw [hstep]
    have hne : ((absorbRange src s i m).filled + 1 == (64 : UInt32)) = false := by
      rw [beq_eq_false_iff_ne]; intro h
      have := congrArg UInt32.toNat h
      rw [filled_lt_of_wf (by omega), hfill] at this; simp at this; omega
    unfold absorb
    dsimp only
    rw [hne]
    simp only [Bool.false_eq_true, ↓reduceIte]
    refine ⟨hh, ?_, htot, ?_, ?_⟩
    · show ((absorbRange src s i m).filled + 1).toNat = m + 1
      rw [filled_lt_of_wf (by omega), hfill]
    · show ((absorbRange src s i m).block.setIfInBounds _ _).size = 64
      rw [Array.size_setIfInBounds]; exact hwf
    · intro k hk
      show ((absorbRange src s i m).block.setIfInBounds (absorbRange src s i m).filled.toNat _).getD k 0 = _
      rw [hfill]
      by_cases hkm : k = m
      · subst hkm; rw [getD_setIfInBounds_eq _ _ _ (by rw [hwf]; omega)]
      · rw [getD_setIfInBounds_ne _ _ _ _ (Ne.symm hkm)]; exact hget k (by omega)

theorem extract_getD (src : Array UInt8) (i k : Nat) (hk : k < 64) (hi : i + 64 ≤ src.size) :
    (src.extract i (i + 64)).getD k 0 = src.getD (i + k) 0 := by
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_extract]
  rw [if_pos (by omega)]

theorem absorbRange_snoc (src : Array UInt8) (s : Sha256State) (i m : Nat) :
    absorbRange src s i (m + 1) = absorb (absorbRange src s i m) (src.getD (i + m) 0) := by
  rw [← absorbRange_add src s i m 1, absorbRange_succ, absorbRange_zero]

/-- Sixty-four bytes from an empty buffer are one compression of that window. -/
theorem absorb_block (src : Array UInt8) (s : Sha256State) (hs : WF s) (h0 : s.filled = 0) (i : Nat)
    (hi : i + 64 ≤ src.size) :
    Equiv (absorbRange src s i 64) { s with h := compressFn s.h (src.extract i (i + 64)), filled := 0 } := by
  obtain ⟨m, hm⟩ : ∃ m, m = 63 := ⟨_, rfl⟩
  rw [show (64 : Nat) = m + 1 by omega, absorbRange_snoc]
  obtain ⟨hh, hfill, htot, hwf, hget⟩ := absorb_prefix src s hs h0 i m (by omega)
  generalize ht : absorbRange src s i m = t at *
  have h64 : (t.filled + 1 == (64 : UInt32)) = true := by
    rw [beq_iff_eq]; apply UInt32.toNat.inj; rw [filled_lt_of_wf (by omega), hfill, hm]; decide
  unfold absorb
  dsimp only
  rw [h64]
  simp only [↓reduceIte]
  refine ⟨?_, rfl, htot, fun k hk => by simp at hk⟩
  show compressFn t.h _ = compressFn s.h _
  rw [hh]
  apply compressFn_congr
  intro k hk
  rw [show i + (m + 1) = i + 64 by omega, extract_getD src i k hk hi, hfill]
  by_cases hkm : k = m
  · subst hkm; rw [getD_setIfInBounds_eq _ _ _ (by rw [hwf]; omega)]
  · rw [getD_setIfInBounds_ne _ _ _ _ (Ne.symm hkm)]; exact hget k (by omega)

theorem update_loop1 (src : Array UInt8) (hsrc : src.size < 2 ^ 32) :
    ∀ (fuel : Nat) (s : Sha256State) (i : UInt32), WF s → s.filled.toNat < 64 → i.toNat ≤ src.size →
      (src.size - i.toNat) / 64 + 66 < fuel →
      ∃ s' i', sha256_update.loop1 src s i fuel = some (s', i') ∧ WF s' ∧ s'.filled.toNat < 64 ∧
        i.toNat ≤ i'.toNat ∧ i'.toNat ≤ src.size ∧
        Equiv s' (absorbRange src s i.toNat (i'.toNat - i.toNat)) := by
  intro fuel
  induction fuel with
  | zero => intro s i _ _ _ hf; omega
  | succ fuel ih =>
    intro s i hs hf0 hi hf
    have hsz : (src.size.toUInt32).toNat = src.size := toUInt32_toNat_of_lt _ hsrc
    unfold sha256_update.loop1
    by_cases hcond : s.filled = 0 ∧ 64 ≤ src.size ∧ i.toNat + 64 ≤ src.size
    · obtain ⟨hz, h64, hi64⟩ := hcond
      have hc : (((s.filled == (0 : UInt32)) && decide (src.size.toUInt32 ≥ (64 : UInt32))) &&
          decide (i ≤ src.size.toUInt32 - (64 : UInt32))) = true := by
        have h1 : (s.filled == (0 : UInt32)) = true := by rw [beq_iff_eq]; exact hz
        have h2 : decide (src.size.toUInt32 ≥ (64 : UInt32)) = true := by
          apply decide_eq_true; show (64 : UInt32) ≤ _
          rw [UInt32.le_iff_toNat_le, hsz]; simpa using h64
        have h3 : decide (i ≤ src.size.toUInt32 - (64 : UInt32)) = true := by
          apply decide_eq_true
          rw [UInt32.le_iff_toNat_le, UInt32.toNat_sub_of_le, hsz]
          · simp; omega
          · rw [UInt32.le_iff_toNat_le, hsz]; simpa using h64
        rw [h1, h2, h3]; rfl
      simp only [hc, ↓reduceIte]
      have hext : (src.extract i.toNat (i.toNat + (64 : UInt32).toNat)).size = 64 := by
        rw [Array.size_extract]; simp; omega
      rw [compress_view_eq _ _ (by rw [hext]; exact Nat.le_refl _) (by rw [hext]; decide) fuel, compress_eq _ _ fuel (by omega)]
      simp only [bind, Option.bind]
      have hi64' : (i + 64).toNat = i.toNat + 64 := by
        rw [UInt32.toNat_add, show (64 : UInt32).toNat = 64 by decide]; exact Nat.mod_eq_of_lt (by omega)
      obtain ⟨s', i', hloop, hwf', hf', hle, hle', heq⟩ :=
        ih { s with h := compressFn s.h (src.extract i.toNat (i.toNat + (64 : UInt32).toNat)) } (i + 64)
          hs hf0 (by omega) (by rw [hi64']; omega)
      refine ⟨s', i', hloop, hwf', hf', by omega, hle', ?_⟩
      rw [hi64'] at heq hle
      have hblock := absorb_block src s hs hz i.toNat (by omega)
      rw [show i'.toNat - i.toNat = 64 + (i'.toNat - (i.toNat + 64)) by omega, ← absorbRange_add]
      refine heq.trans ?_
      apply absorbRange_equiv
      · exact hs
      · exact absorbRange_wf hs src _ _
      · exact hf0
      · have hrec : ({ s with h := compressFn s.h (src.extract i.toNat (i.toNat + (64 : UInt32).toNat)) } : Sha256State)
            = { s with h := compressFn s.h (src.extract i.toNat (i.toNat + 64)), filled := 0 } := by
          rw [show (64 : UInt32).toNat = 64 by decide]
          cases s; simp only at hz; subst hz; rfl
        rw [hrec]; exact hblock.symm
    · have hc : (((s.filled == (0 : UInt32)) && decide (src.size.toUInt32 ≥ (64 : UInt32))) &&
          decide (i ≤ src.size.toUInt32 - (64 : UInt32))) = false := by
        by_cases hz : s.filled = 0
        · have h1 : (s.filled == (0 : UInt32)) = true := by rw [beq_iff_eq]; exact hz
          by_cases h64 : 64 ≤ src.size
          · have h2 : decide (src.size.toUInt32 ≥ (64 : UInt32)) = true := by
              apply decide_eq_true; show (64 : UInt32) ≤ _
              rw [UInt32.le_iff_toNat_le, hsz]; simpa using h64
            have h3 : decide (i ≤ src.size.toUInt32 - (64 : UInt32)) = false := by
              apply decide_eq_false; intro h
              apply hcond; refine ⟨hz, h64, ?_⟩
              rw [UInt32.le_iff_toNat_le, UInt32.toNat_sub_of_le, hsz] at h
              · simp at h; omega
              · rw [UInt32.le_iff_toNat_le, hsz]; simpa using h64
            rw [h1, h2, h3]; rfl
          · have h2 : decide (src.size.toUInt32 ≥ (64 : UInt32)) = false := by
              apply decide_eq_false; show ¬ (64 : UInt32) ≤ _
              rw [UInt32.le_iff_toNat_le, hsz]; simpa using h64
            rw [h1, h2]; rfl
        · have h1 : (s.filled == (0 : UInt32)) = false := by rw [beq_eq_false_iff_ne]; exact hz
          rw [h1]; rfl
      simp only [hc, Bool.false_eq_true, ↓reduceIte]
      refine ⟨s, i, rfl, hs, hf0, Nat.le_refl _, hi, ?_⟩
      rw [Nat.sub_self, absorbRange_zero]; exact Equiv.refl s

/-! ## `sha256_update` is the byte model, up to the buffer -/

theorem equiv_set_total {s t : Sha256State} (h : Equiv s t) (x : UInt64) :
    Equiv (setTotal s x) (setTotal t x) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨h1, h2, rfl, h4⟩

theorem Equiv.total_eq {s t : Sha256State} (h : Equiv s t) : s.total = t.total := h.2.2.1
theorem Equiv.filled_eq {s t : Sha256State} (h : Equiv s t) : s.filled = t.filled := h.2.1

theorem update_spec (s : Sha256State) (hs : WF s) (hf0 : s.filled.toNat < 64) (src : Array UInt8)
    (hsrc : src.size < 2 ^ 32) (fuel : Nat) (hf : src.size + 70 < fuel) :
    ∃ s', sha256_update s src fuel = some s' ∧ WF s' ∧ s'.filled.toNat < 64 ∧
      Equiv s' (setTotal (absorbRange src s 0 src.size) (s.total + (src.size.toUInt32).toUInt64)) := by
  obtain ⟨s1, i1, hloop1, hwf1, hf1, -, hle1, heq1⟩ :=
    update_loop1 src hsrc fuel s 0 hs hf0 (by simp) (by simp; omega)
  have hloop2 := update_loop2 src hsrc fuel s1 i1 hle1 (by omega)
  unfold sha256_update
  dsimp only
  rw [hloop1]
  simp only [bind, Option.bind]
  rw [hloop2]
  refine ⟨_, rfl, absorbRange_wf hwf1 src _ _, absorbRange_filled_lt hf1 src _ _, ?_⟩
  have h0 : (0 : UInt32).toNat = 0 := rfl
  rw [h0, Nat.sub_zero] at heq1
  have htot1 : s1.total = s.total := by rw [heq1.total_eq, absorbRange_total]
  have hrest : Equiv (absorbRange src s1 i1.toNat (src.size - i1.toNat)) (absorbRange src s 0 src.size) := by
    have hsplit : absorbRange src s 0 src.size = absorbRange src (absorbRange src s 0 i1.toNat) i1.toNat (src.size - i1.toNat) := by
      have := absorbRange_add src s 0 i1.toNat (src.size - i1.toNat)
      rw [Nat.zero_add, Nat.add_sub_cancel' hle1] at this
      exact this.symm
    rw [hsplit]
    exact absorbRange_equiv hwf1 (absorbRange_wf hs src _ _) hf1 heq1 src _ _
  rw [absorbRange_total, htot1]
  exact equiv_set_total hrest _

/-! ## `sha256_final` reads only what `Equiv` compares -/

/-- Agreement on the hash words, fill count, total, and the first `n` buffered bytes. -/
def AgreeTo (s t : Sha256State) (n : Nat) : Prop :=
  s.h = t.h ∧ s.filled = t.filled ∧ s.total = t.total ∧ ∀ k, k < n → s.block.getD k 0 = t.block.getD k 0

theorem agreeTo_of_equiv {s t : Sha256State} (h : Equiv s t) : AgreeTo s t s.filled.toNat := h

theorem agreeTo_mono {s t : Sha256State} {m n : Nat} (h : AgreeTo s t n) (hmn : m ≤ n) : AgreeTo s t m :=
  ⟨h.1, h.2.1, h.2.2.1, fun k hk => h.2.2.2 k (by omega)⟩

/-- Zeroing the buffer from the fill point, `n` bytes. -/
def zeroFill (s : Sha256State) : Nat → Sha256State
  | 0 => s
  | n + 1 => zeroFill { s with block := s.block.setIfInBounds s.filled.toNat 0, filled := s.filled + 1 } n

theorem zeroFill_zero (s : Sha256State) : zeroFill s 0 = s := rfl
theorem zeroFill_succ (s : Sha256State) (n : Nat) :
    zeroFill s (n + 1) = zeroFill { s with block := s.block.setIfInBounds s.filled.toNat 0, filled := s.filled + 1 } n := rfl

theorem zeroFill_props (s : Sha256State) (hs : WF s) :
    ∀ n, s.filled.toNat + n ≤ 64 →
      WF (zeroFill s n) ∧ (zeroFill s n).h = s.h ∧ (zeroFill s n).total = s.total ∧
      (zeroFill s n).filled.toNat = s.filled.toNat + n ∧
      (∀ k, k < s.filled.toNat → (zeroFill s n).block.getD k 0 = s.block.getD k 0) ∧
      (∀ k, s.filled.toNat ≤ k → k < s.filled.toNat + n → (zeroFill s n).block.getD k 0 = 0) := by
  intro n
  induction n generalizing s with
  | zero => intro _; exact ⟨hs, rfl, rfl, by simp [zeroFill_zero], fun _ _ => rfl, fun k h1 h2 => by omega⟩
  | succ n ih =>
    intro hn
    rw [zeroFill_succ]
    have hf : s.filled.toNat < 64 := by omega
    have hf1 : (s.filled + 1).toNat = s.filled.toNat + 1 := filled_lt_of_wf hf
    have hwf' : WF { s with block := s.block.setIfInBounds s.filled.toNat 0, filled := s.filled + 1 } := by
      show (s.block.setIfInBounds _ _).size = 64; rw [Array.size_setIfInBounds]; exact hs
    obtain ⟨hwf, hh, htot, hfill, hkeep, hzero⟩ := ih _ hwf' (by show (s.filled + 1).toNat + n ≤ 64; rw [hf1]; omega)
    refine ⟨hwf, hh, htot, by rw [hfill]; show (s.filled + 1).toNat + n = _; rw [hf1]; omega, ?_, ?_⟩
    · intro k hk
      rw [hkeep k (by show k < (s.filled + 1).toNat; rw [hf1]; omega)]
      exact getD_setIfInBounds_ne _ _ _ _ (by omega)
    · intro k hk1 hk2
      by_cases hkf : k = s.filled.toNat
      · subst hkf
        rw [hkeep _ (by show _ < (s.filled + 1).toNat; rw [hf1]; omega)]
        exact getD_setIfInBounds_eq _ _ _ (by rw [hs]; exact hf)
      · exact hzero k (by show (s.filled + 1).toNat ≤ k; rw [hf1]; omega) (by show k < (s.filled + 1).toNat + n; rw [hf1]; omega)

theorem zeroFill_congr (s t : Sha256State) (hs : WF s) (ht : WF t) (n : Nat) (hn : s.filled.toNat + n ≤ 64)
    (h : AgreeTo s t s.filled.toNat) : AgreeTo (zeroFill s n) (zeroFill t n) (s.filled.toNat + n) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  obtain ⟨_, hh, htot, hfill, hkeep, hzero⟩ := zeroFill_props s hs n hn
  obtain ⟨_, hh', htot', hfill', hkeep', hzero'⟩ := zeroFill_props t ht n (by rw [← h2]; exact hn)
  refine ⟨by rw [hh, hh', h1], ?_, by rw [htot, htot', h3], ?_⟩
  · apply UInt32.toNat.inj; rw [hfill, hfill', h2]
  · intro k hk
    by_cases hkf : k < s.filled.toNat
    · rw [hkeep k hkf, hkeep' k (by rw [← h2]; exact hkf)]; exact h4 k hkf
    · rw [hzero k (by omega) hk, hzero' k (by rw [← h2]; omega) (by rw [← h2]; exact hk)]

theorem final_loop1_spec : ∀ (n : Nat) (s : Sha256State) (fuel : Nat), s.filled.toNat ≤ 64 → 64 - s.filled.toNat ≤ n → n < fuel →
    sha256_final.loop1 s fuel = some (zeroFill s (64 - s.filled.toNat)) := by
  intro n
  induction n with
  | zero =>
    intro s fuel hle hn hf
    cases fuel with
    | zero => omega
    | succ fuel =>
      unfold sha256_final.loop1
      have hd : decide (s.filled < (64 : UInt32)) = false := by
        apply decide_eq_false; rw [UInt32.lt_iff_toNat_lt]; simp; omega
      simp only [hd, Bool.false_eq_true, ↓reduceIte, Option.pure_def]
      rw [show 64 - s.filled.toNat = 0 by omega, zeroFill_zero]
  | succ n ih =>
    intro s fuel hle hn hf
    cases fuel with
    | zero => omega
    | succ fuel =>
      unfold sha256_final.loop1
      by_cases hlt : s.filled.toNat < 64
      · have hd : decide (s.filled < (64 : UInt32)) = true := by
          apply decide_eq_true; rw [UInt32.lt_iff_toNat_lt]; simpa using hlt
        simp only [hd, ↓reduceIte]
        have hf1 : (s.filled + 1).toNat = s.filled.toNat + 1 := filled_lt_of_wf hlt
        rw [ih _ fuel (by show (s.filled + 1).toNat ≤ 64; rw [hf1]; omega) (by show 64 - (s.filled + 1).toNat ≤ n; rw [hf1]; omega) (by omega)]
        rw [show 64 - s.filled.toNat = (64 - (s.filled + 1).toNat) + 1 by rw [hf1]; omega, zeroFill_succ]
      · have hd : decide (s.filled < (64 : UInt32)) = false := by
          apply decide_eq_false; rw [UInt32.lt_iff_toNat_lt]; simpa using hlt
        simp only [hd, Bool.false_eq_true, ↓reduceIte, Option.pure_def]
        rw [show 64 - s.filled.toNat = 0 by omega, zeroFill_zero]

theorem final_loop2_spec : ∀ (n : Nat) (s : Sha256State) (fuel : Nat), s.filled.toNat ≤ 56 → 56 - s.filled.toNat ≤ n → n < fuel →
    sha256_final.loop2 s fuel = some (zeroFill s (56 - s.filled.toNat)) := by
  intro n
  induction n with
  | zero =>
    intro s fuel hle hn hf
    cases fuel with
    | zero => omega
    | succ fuel =>
      unfold sha256_final.loop2
      have hd : decide (s.filled < (56 : UInt32)) = false := by
        apply decide_eq_false; rw [UInt32.lt_iff_toNat_lt]; simp; omega
      simp only [hd, Bool.false_eq_true, ↓reduceIte, Option.pure_def]
      rw [show 56 - s.filled.toNat = 0 by omega, zeroFill_zero]
  | succ n ih =>
    intro s fuel hle hn hf
    cases fuel with
    | zero => omega
    | succ fuel =>
      unfold sha256_final.loop2
      by_cases hlt : s.filled.toNat < 56
      · have hd : decide (s.filled < (56 : UInt32)) = true := by
          apply decide_eq_true; rw [UInt32.lt_iff_toNat_lt]; simpa using hlt
        simp only [hd, ↓reduceIte]
        have hf1 : (s.filled + 1).toNat = s.filled.toNat + 1 := filled_lt_of_wf (by omega)
        rw [ih _ fuel (by show (s.filled + 1).toNat ≤ 56; rw [hf1]; omega) (by show 56 - (s.filled + 1).toNat ≤ n; rw [hf1]; omega) (by omega)]
        rw [show 56 - s.filled.toNat = (56 - (s.filled + 1).toNat) + 1 by rw [hf1]; omega, zeroFill_succ]
      · have hd : decide (s.filled < (56 : UInt32)) = false := by
          apply decide_eq_false; rw [UInt32.lt_iff_toNat_lt]; simpa using hlt
        simp only [hd, Bool.false_eq_true, ↓reduceIte, Option.pure_def]
        rw [show 56 - s.filled.toNat = 0 by omega, zeroFill_zero]

/-- The length bytes, positions `56 + k` for `k` below eight. -/
def lenByte (bits : UInt64) (k : UInt32) : UInt8 := (bits >>> ((56 : UInt64) - ((8 : UInt64) * k.toUInt64))).toUInt8

def lenFill (s : Sha256State) (bits : UInt64) (k : UInt32) : Nat → Sha256State
  | 0 => s
  | n + 1 => lenFill { s with block := s.block.setIfInBounds ((56 : UInt32) + k).toNat (lenByte bits k) } bits (k + 1) n

theorem lenFill_succ (s : Sha256State) (bits : UInt64) (k : UInt32) (n : Nat) :
    lenFill s bits k (n + 1) = lenFill { s with block := s.block.setIfInBounds ((56 : UInt32) + k).toNat (lenByte bits k) } bits (k + 1) n := rfl

theorem lenFill_props (s : Sha256State) (hs : WF s) (bits : UInt64) :
    ∀ (n : Nat) (k : UInt32), k.toNat + n ≤ 8 →
      WF (lenFill s bits k n) ∧ (lenFill s bits k n).h = s.h ∧ (lenFill s bits k n).filled = s.filled ∧
      (lenFill s bits k n).total = s.total ∧
      (∀ j, j < 56 + k.toNat → (lenFill s bits k n).block.getD j 0 = s.block.getD j 0) ∧
      (∀ j, 56 + k.toNat ≤ j → j < 56 + k.toNat + n → (lenFill s bits k n).block.getD j 0 = lenByte bits (j - 56).toUInt32) := by
  intro n
  induction n generalizing s with
  | zero => intro k _; exact ⟨hs, rfl, rfl, rfl, fun _ _ => rfl, fun j h1 h2 => by omega⟩
  | succ n ih =>
    intro k hk
    rw [lenFill_succ]
    have hk1 : (k + 1).toNat = k.toNat + 1 := by
      rw [UInt32.toNat_add, show (1 : UInt32).toNat = 1 by decide]; exact Nat.mod_eq_of_lt (by omega)
    have h56 : ((56 : UInt32) + k).toNat = 56 + k.toNat := by
      rw [UInt32.toNat_add, show (56 : UInt32).toNat = 56 by decide]; exact Nat.mod_eq_of_lt (by omega)
    have hwf' : WF { s with block := s.block.setIfInBounds ((56 : UInt32) + k).toNat (lenByte bits k) } := by
      show (s.block.setIfInBounds _ _).size = 64; rw [Array.size_setIfInBounds]; exact hs
    obtain ⟨hwf, hh, hfill, htot, hkeep, hset⟩ := ih _ hwf' (k + 1) (by rw [hk1]; omega)
    refine ⟨hwf, hh, hfill, htot, ?_, ?_⟩
    · intro j hj
      rw [hkeep j (by rw [hk1]; omega), h56]
      exact getD_setIfInBounds_ne _ _ _ _ (by omega)
    · intro j hj1 hj2
      by_cases hjk : j = 56 + k.toNat
      · rw [hkeep j (by rw [hk1]; omega), h56, hjk, getD_setIfInBounds_eq _ _ _ (by rw [hs]; omega)]
        congr 1; apply UInt32.toNat.inj
        rw [toUInt32_toNat_of_lt _ (by omega)]; omega
      · exact hset j (by rw [hk1]; omega) (by rw [hk1]; omega)

theorem final_loop3_spec (bits : UInt64) : ∀ (n : Nat) (s : Sha256State) (k : UInt32) (fuel : Nat),
    k.toNat ≤ 8 → 8 - k.toNat ≤ n → n < fuel →
    sha256_final.loop3 s bits k fuel = some (lenFill s bits k (8 - k.toNat), (8 : UInt32)) := by
  intro n
  induction n with
  | zero =>
    intro s k fuel hle hn hf
    cases fuel with
    | zero => omega
    | succ fuel =>
      unfold sha256_final.loop3
      have hd : decide (k < (8 : UInt32)) = false := by
        apply decide_eq_false; rw [UInt32.lt_iff_toNat_lt]; simp; omega
      simp only [hd, Bool.false_eq_true, ↓reduceIte, Option.pure_def]
      rw [show 8 - k.toNat = 0 by omega]
      have : k = 8 := by apply UInt32.toNat.inj; simp; omega
      rw [this]; rfl
  | succ n ih =>
    intro s k fuel hle hn hf
    cases fuel with
    | zero => omega
    | succ fuel =>
      unfold sha256_final.loop3
      by_cases hlt : k.toNat < 8
      · have hd : decide (k < (8 : UInt32)) = true := by
          apply decide_eq_true; rw [UInt32.lt_iff_toNat_lt]; simpa using hlt
        simp only [hd, ↓reduceIte]
        have hk1 : (k + 1).toNat = k.toNat + 1 := by
          rw [UInt32.toNat_add, show (1 : UInt32).toNat = 1 by decide]; exact Nat.mod_eq_of_lt (by omega)
        rw [ih _ (k + 1) fuel (by rw [hk1]; omega) (by rw [hk1]; omega) (by omega)]
        rw [show 8 - k.toNat = (8 - (k + 1).toNat) + 1 by rw [hk1]; omega]
        rfl
      · have hd : decide (k < (8 : UInt32)) = false := by
          apply decide_eq_false; rw [UInt32.lt_iff_toNat_lt]; simpa using hlt
        simp only [hd, Bool.false_eq_true, ↓reduceIte, Option.pure_def]
        rw [show 8 - k.toNat = 0 by omega]
        have : k = 8 := by apply UInt32.toNat.inj; simp; omega
        rw [this]; rfl

theorem lenFill_congr (s t : Sha256State) (hs : WF s) (ht : WF t) (bits : UInt64) (h : AgreeTo s t 56) :
    AgreeTo (lenFill s bits 0 8) (lenFill t bits 0 8) 64 := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  obtain ⟨_, hh, hfill, htot, hkeep, hset⟩ := lenFill_props s hs bits 8 0 (by simp)
  obtain ⟨_, hh', hfill', htot', hkeep', hset'⟩ := lenFill_props t ht bits 8 0 (by simp)
  refine ⟨by rw [hh, hh', h1], by rw [hfill, hfill', h2], by rw [htot, htot', h3], ?_⟩
  intro j hj
  by_cases hj56 : j < 56
  · rw [hkeep j (by simpa using hj56), hkeep' j (by simpa using hj56)]; exact h4 j hj56
  · rw [hset j (by simp; omega) (by simp; omega), hset' j (by simp; omega) (by simp; omega)]

/-- The output bytes written from the hash words. -/
def outFill (out : Array UInt8) (h : Array UInt32) (j : UInt32) : Nat → Array UInt8
  | 0 => out
  | n + 1 =>
    let word := h.getD j.toNat 0
    let at_ := j * 4
    outFill ((((out.setIfInBounds at_.toNat (word >>> 24).toUInt8).setIfInBounds (at_ + 1).toNat (word >>> 16).toUInt8).setIfInBounds
      (at_ + 2).toNat (word >>> 8).toUInt8).setIfInBounds (at_ + 3).toNat word.toUInt8) h (j + 1) n

theorem final_loop4_spec (h : Array UInt32) : ∀ (n : Nat) (out : Array UInt8) (tail : Sha256State) (j : UInt32) (fuel : Nat),
    tail.h = h → j.toNat ≤ 8 → 8 - j.toNat ≤ n → n < fuel →
    sha256_final.loop4 out tail j fuel = some (outFill out h j (8 - j.toNat), (8 : UInt32)) := by
  intro n
  induction n with
  | zero =>
    intro out tail j fuel hh hle hn hf
    cases fuel with
    | zero => omega
    | succ fuel =>
      unfold sha256_final.loop4
      have hd : decide (j < (8 : UInt32)) = false := by
        apply decide_eq_false; rw [UInt32.lt_iff_toNat_lt]; simp; omega
      simp only [hd, Bool.false_eq_true, ↓reduceIte, Option.pure_def]
      rw [show 8 - j.toNat = 0 by omega]
      have : j = 8 := by apply UInt32.toNat.inj; simp; omega
      rw [this]; rfl
  | succ n ih =>
    intro out tail j fuel hh hle hn hf
    cases fuel with
    | zero => omega
    | succ fuel =>
      unfold sha256_final.loop4
      by_cases hlt : j.toNat < 8
      · have hd : decide (j < (8 : UInt32)) = true := by
          apply decide_eq_true; rw [UInt32.lt_iff_toNat_lt]; simpa using hlt
        simp only [hd, ↓reduceIte]
        have hj1 : (j + 1).toNat = j.toNat + 1 := by
          rw [UInt32.toNat_add, show (1 : UInt32).toNat = 1 by decide]; exact Nat.mod_eq_of_lt (by omega)
        rw [ih _ tail (j + 1) fuel hh (by rw [hj1]; omega) (by rw [hj1]; omega) (by omega)]
        rw [show 8 - j.toNat = (8 - (j + 1).toNat) + 1 by rw [hj1]; omega, hh]
        rfl
      · have hd : decide (j < (8 : UInt32)) = false := by
          apply decide_eq_false; rw [UInt32.lt_iff_toNat_lt]; simpa using hlt
        simp only [hd, Bool.false_eq_true, ↓reduceIte, Option.pure_def]
        rw [show 8 - j.toNat = 0 by omega]
        have : j = 8 := by apply UInt32.toNat.inj; simp; omega
        rw [this]; rfl


/-! ## The finalization loops, unconditionally -/

theorem final_loop1_all (s : Sha256State) (fuel : Nat) (hf : 64 < fuel) :
    sha256_final.loop1 s fuel = some (zeroFill s (64 - s.filled.toNat)) := by
  by_cases hle : s.filled.toNat ≤ 64
  · exact final_loop1_spec 64 s fuel hle (by omega) hf
  · cases fuel with
    | zero => omega
    | succ fuel =>
      unfold sha256_final.loop1
      have hd : decide (s.filled < (64 : UInt32)) = false := by
        apply decide_eq_false; rw [UInt32.lt_iff_toNat_lt]; simp; omega
      simp only [hd, Bool.false_eq_true, ↓reduceIte, Option.pure_def]
      rw [show 64 - s.filled.toNat = 0 by omega, zeroFill_zero]

theorem final_loop2_all (s : Sha256State) (fuel : Nat) (hf : 56 < fuel) :
    sha256_final.loop2 s fuel = some (zeroFill s (56 - s.filled.toNat)) := by
  by_cases hle : s.filled.toNat ≤ 56
  · exact final_loop2_spec 56 s fuel hle (by omega) hf
  · cases fuel with
    | zero => omega
    | succ fuel =>
      unfold sha256_final.loop2
      have hd : decide (s.filled < (56 : UInt32)) = false := by
        apply decide_eq_false; rw [UInt32.lt_iff_toNat_lt]; simp; omega
      simp only [hd, Bool.false_eq_true, ↓reduceIte, Option.pure_def]
      rw [show 56 - s.filled.toNat = 0 by omega, zeroFill_zero]

theorem final_loop3_all (s : Sha256State) (bits : UInt64) (fuel : Nat) (hf : 8 < fuel) :
    sha256_final.loop3 s bits 0 fuel = some (lenFill s bits 0 8, (8 : UInt32)) :=
  final_loop3_spec bits 8 s 0 fuel (by simp) (by simp) hf

theorem final_loop4_all (out : Array UInt8) (tail : Sha256State) (fuel : Nat) (hf : 8 < fuel) :
    sha256_final.loop4 out tail 0 fuel = some (outFill out tail.h 0 8, (8 : UInt32)) :=
  final_loop4_spec tail.h 8 out tail 0 fuel rfl (by simp) (by simp) hf

/-! ## The finalization as a function of the state -/

/-- The padding byte. -/
def stage1 (s : Sha256State) : Sha256State :=
  { s with block := s.block.setIfInBounds s.filled.toNat 128, filled := s.filled + 1 }

/-- The extra block when the length does not fit. -/
def stage2 (s : Sha256State) : Sha256State :=
  if (56 : UInt32) < (stage1 s).filled then
    { zeroFill (stage1 s) (64 - (stage1 s).filled.toNat) with
      h := compressFn (zeroFill (stage1 s) (64 - (stage1 s).filled.toNat)).h (zeroFill (stage1 s) (64 - (stage1 s).filled.toNat)).block,
      filled := 0 }
  else stage1 s

/-- Zeros up to the length field. -/
def stage3 (s : Sha256State) : Sha256State := zeroFill (stage2 s) (56 - (stage2 s).filled.toNat)

/-- The length field. -/
def stage4 (s : Sha256State) : Sha256State := lenFill (stage3 s) (s.total * 8) 0 8

/-- The bytes `sha256_final` writes for a destination of at least thirty-two bytes. -/
def finalModel (s : Sha256State) (out : Array UInt8) : Array UInt8 :=
  outFill out (compressFn (stage4 s).h (stage4 s).block) 0 8

theorem final_spec (s : Sha256State) (out : Array UInt8) (hout : 32 ≤ out.size) (hsmall : out.size < 2 ^ 32)
    (fuel : Nat) (hf : 70 < fuel) :
    sha256_final s out fuel = some (true, finalModel s out) := by
  have hd : decide (out.size.toUInt32 < (32 : UInt32)) = false := by
    apply decide_eq_false; rw [UInt32.lt_iff_toNat_lt, toUInt32_toNat_of_lt _ hsmall]; simp; omega
  cases s with
  | mk h block filled total =>
    unfold sha256_final
    dsimp only
    simp only [hd, Bool.false_eq_true, ↓reduceIte]
    unfold finalModel stage4 stage3 stage2 stage1
    dsimp only
    by_cases h56 : (56 : UInt32) < filled + 1
    · have hd56 : decide (filled + 1 > (56 : UInt32)) = true := decide_eq_true h56
      simp only [hd56, ↓reduceIte, if_pos h56]
      rw [final_loop1_all _ fuel (by omega)]
      simp only [bind, Option.bind, Option.pure_def]
      rw [compress_eq _ _ fuel (by omega)]
      simp only [bind, Option.bind, Option.pure_def]
      rw [final_loop2_all _ fuel (by omega)]
      simp only [bind, Option.bind, Option.pure_def]
      rw [final_loop3_all _ _ fuel (by omega)]
      simp only [bind, Option.bind, Option.pure_def]
      rw [compress_eq _ _ fuel (by omega)]
      simp only [bind, Option.bind, Option.pure_def]
      rw [final_loop4_all out _ fuel (by omega)]
      try rfl
    · have hd56 : decide (filled + 1 > (56 : UInt32)) = false := decide_eq_false h56
      simp only [hd56, Bool.false_eq_true, ↓reduceIte, if_neg h56]
      simp only [bind, Option.bind, Option.pure_def]
      rw [final_loop2_all _ fuel (by omega)]
      simp only [bind, Option.bind, Option.pure_def]
      rw [final_loop3_all _ _ fuel (by omega)]
      simp only [bind, Option.bind, Option.pure_def]
      rw [compress_eq _ _ fuel (by omega)]
      simp only [bind, Option.bind, Option.pure_def]
      rw [final_loop4_all out _ fuel (by omega)]
      try rfl

theorem final_short (s : Sha256State) (out : Array UInt8) (hout : out.size < 32) (hsmall : out.size < 2 ^ 32) (fuel : Nat) :
    sha256_final s out fuel = some (false, out) := by
  have hd : decide (out.size.toUInt32 < (32 : UInt32)) = true := by
    apply decide_eq_true; rw [UInt32.lt_iff_toNat_lt, toUInt32_toNat_of_lt _ hsmall]; simpa using hout
  unfold sha256_final
  dsimp only
  simp only [hd, ↓reduceIte]
  rfl

/-! ## Equivalent states finalize alike -/

theorem le56_of_not_lt (x : UInt32) (h : ¬ (56 : UInt32) < x) : x.toNat ≤ 56 :=
  Nat.le_of_not_lt (fun hc => h (by rw [UInt32.lt_iff_toNat_lt]; simpa using hc))

theorem stage1_wf {s : Sha256State} (hs : WF s) : WF (stage1 s) := by
  show (s.block.setIfInBounds _ _).size = 64; rw [Array.size_setIfInBounds]; exact hs

theorem stage1_filled {s : Sha256State} (hf : s.filled.toNat < 64) : (stage1 s).filled.toNat = s.filled.toNat + 1 :=
  filled_lt_of_wf hf

theorem stage1_agree (s t : Sha256State) (hs : WF s) (ht : WF t) (hf : s.filled.toNat < 64) (heq : Equiv s t) :
    AgreeTo (stage1 s) (stage1 t) (stage1 s).filled.toNat := by
  obtain ⟨h1, h2, h3, h4⟩ := heq
  rw [stage1_filled hf]
  refine ⟨h1, by show s.filled + 1 = t.filled + 1; rw [h2], h3, ?_⟩
  intro k hk
  show (s.block.setIfInBounds s.filled.toNat 128).getD k 0 = (t.block.setIfInBounds t.filled.toNat 128).getD k 0
  rw [← h2]
  by_cases hkf : k = s.filled.toNat
  · subst hkf
    rw [getD_setIfInBounds_eq _ _ _ (by rw [hs]; exact hf), getD_setIfInBounds_eq _ _ _ (by rw [ht]; exact hf)]
  · rw [getD_setIfInBounds_ne _ _ _ _ (Ne.symm hkf), getD_setIfInBounds_ne _ _ _ _ (Ne.symm hkf)]
    exact h4 k (by omega)

theorem compressFn_agree {s t : Sha256State} (h : AgreeTo s t 64) : compressFn s.h s.block = compressFn t.h t.block := by
  rw [h.1]; exact compressFn_congr _ _ _ h.2.2.2

theorem stage2_props (s : Sha256State) (hs : WF s) (hf : s.filled.toNat < 64) :
    WF (stage2 s) ∧ (stage2 s).filled.toNat ≤ 56 := by
  have h1wf := stage1_wf hs
  have h1f := stage1_filled hf
  unfold stage2
  split
  · rename_i h56
    obtain ⟨zwf, -, -, -, -, -⟩ := zeroFill_props (stage1 s) h1wf (64 - (stage1 s).filled.toNat) (by omega)
    exact ⟨zwf, by simp⟩
  · rename_i h56
    exact ⟨h1wf, le56_of_not_lt _ h56⟩

theorem stage2_agree (s t : Sha256State) (hs : WF s) (ht : WF t) (hf : s.filled.toNat < 64) (heq : Equiv s t) :
    AgreeTo (stage2 s) (stage2 t) (stage2 s).filled.toNat := by
  have hag := stage1_agree s t hs ht hf heq
  have h1wf := stage1_wf hs
  have h1wf' := stage1_wf ht
  have h1f := stage1_filled hf
  have hfill : (stage1 s).filled = (stage1 t).filled := hag.2.1
  unfold stage2
  rw [← hfill]
  by_cases h56 : (56 : UInt32) < (stage1 s).filled
  · rw [if_pos h56, if_pos h56]
    have hz := zeroFill_congr (stage1 s) (stage1 t) h1wf h1wf' (64 - (stage1 s).filled.toNat) (by omega) hag
    rw [Nat.add_sub_cancel' (by omega)] at hz
    exact ⟨compressFn_agree hz, rfl, hz.2.2.1, fun k hk => by simp at hk⟩
  · rw [if_neg h56, if_neg h56]
    exact hag

theorem stage3_agree (s t : Sha256State) (hs : WF s) (ht : WF t) (hf : s.filled.toNat < 64) (heq : Equiv s t) :
    AgreeTo (stage3 s) (stage3 t) 56 ∧ WF (stage3 s) ∧ WF (stage3 t) := by
  have hag := stage2_agree s t hs ht hf heq
  obtain ⟨h2wf, h2le⟩ := stage2_props s hs hf
  have hf' : t.filled.toNat < 64 := by rw [← heq.filled_eq]; exact hf
  obtain ⟨h2wf', -⟩ := stage2_props t ht hf'
  have hfill : (stage2 s).filled = (stage2 t).filled := hag.2.1
  unfold stage3
  have hz := zeroFill_congr (stage2 s) (stage2 t) h2wf h2wf' (56 - (stage2 s).filled.toNat) (by omega) hag
  rw [Nat.add_sub_cancel' h2le] at hz
  rw [← hfill]
  obtain ⟨z3wf, -, -, -, -, -⟩ := zeroFill_props (stage2 s) h2wf (56 - (stage2 s).filled.toNat) (by omega)
  obtain ⟨z3wf', -, -, -, -, -⟩ := zeroFill_props (stage2 t) h2wf' (56 - (stage2 s).filled.toNat) (by rw [← hfill]; omega)
  exact ⟨hz, z3wf, z3wf'⟩

theorem stage4_agree (s t : Sha256State) (hs : WF s) (ht : WF t) (hf : s.filled.toNat < 64) (heq : Equiv s t) :
    AgreeTo (stage4 s) (stage4 t) 64 := by
  obtain ⟨hag, z3wf, z3wf'⟩ := stage3_agree s t hs ht hf heq
  unfold stage4
  rw [heq.total_eq]
  exact lenFill_congr _ _ z3wf z3wf' _ hag

/-- Equivalent states finalize to the same bytes. -/
theorem finalModel_congr (s t : Sha256State) (hs : WF s) (ht : WF t) (hf : s.filled.toNat < 64) (heq : Equiv s t)
    (out : Array UInt8) : finalModel s out = finalModel t out := by
  unfold finalModel
  rw [compressFn_agree (stage4_agree s t hs ht hf heq)]

/-- `sha256_final` cannot tell equivalent states apart. -/
theorem final_congr (s t : Sha256State) (hs : WF s) (ht : WF t) (hf : s.filled.toNat < 64) (heq : Equiv s t)
    (out : Array UInt8) (hsmall : out.size < 2 ^ 32) (fuel : Nat) (hfuel : 70 < fuel) :
    sha256_final s out fuel = sha256_final t out fuel := by
  by_cases hout : out.size < 32
  · rw [final_short s out hout hsmall, final_short t out hout hsmall]
  · rw [final_spec s out (by omega) hsmall fuel hfuel, final_spec t out (by omega) hsmall fuel hfuel,
      finalModel_congr s t hs ht hf heq out]

/-! ## Streaming -/

theorem setTotal_setTotal (s : Sha256State) (x y : UInt64) : setTotal (setTotal s x) y = setTotal s y := rfl

theorem absorb_set_total (s : Sha256State) (x : UInt64) (b : UInt8) :
    absorb (setTotal s x) b = setTotal (absorb s b) x := by
  unfold absorb setTotal
  dsimp only
  split <;> rfl

theorem absorbRange_set_total (src : Array UInt8) (s : Sha256State) (x : UInt64) (i n : Nat) :
    absorbRange src (setTotal s x) i n = setTotal (absorbRange src s i n) x := by
  induction n generalizing s i with
  | zero => rfl
  | succ n ih => rw [absorbRange_succ, absorbRange_succ, absorb_set_total, ih]

theorem absorbRange_append (a b : Array UInt8) (s : Sha256State) :
    absorbRange (a ++ b) s 0 (a.size + b.size) = absorbRange b (absorbRange a s 0 a.size) 0 b.size := by
  rw [← absorbRange_add (a ++ b) s 0 a.size b.size]
  rw [absorbRange_congr (a ++ b) a s 0 0 a.size (fun k hk => by rw [Nat.zero_add, getD_append_left a b k hk])]
  rw [Nat.zero_add]
  apply absorbRange_congr
  intro k hk
  rw [getD_append_right a b (a.size + k) (by omega)]
  simp

theorem size_total (a b : Array UInt8) (hsize : a.size + b.size < 2 ^ 32) :
    (a.size.toUInt32).toUInt64 + (b.size.toUInt32).toUInt64 = ((a.size + b.size).toUInt32).toUInt64 := by
  apply UInt64.toNat.inj
  rw [UInt64.toNat_add, UInt32.toNat_toUInt64, UInt32.toNat_toUInt64, UInt32.toNat_toUInt64,
    toUInt32_toNat_of_lt _ (by omega), toUInt32_toNat_of_lt _ (by omega), toUInt32_toNat_of_lt _ hsize]
  exact Nat.mod_eq_of_lt (by omega)

/-- Feeding `a` then `b` reaches a state equivalent to feeding `a ++ b`. -/
theorem sha256_update_append (s : Sha256State) (hs : WF s) (hf0 : s.filled.toNat < 64) (a b : Array UInt8)
    (hsize : a.size + b.size < 2 ^ 32) (fuel : Nat) (hf : a.size + b.size + 70 < fuel) :
    ∃ s1 s2 s3, sha256_update s a fuel = some s1 ∧ sha256_update s1 b fuel = some s2 ∧
      sha256_update s (a ++ b) fuel = some s3 ∧ Equiv s2 s3 ∧ WF s2 ∧ s2.filled.toNat < 64 ∧ WF s3 := by
  obtain ⟨s1, h1, hwf1, hfill1, heq1⟩ := update_spec s hs hf0 a (by omega) fuel (by omega)
  obtain ⟨s2, h2, hwf2, hfill2, heq2⟩ := update_spec s1 hwf1 hfill1 b (by omega) fuel (by omega)
  obtain ⟨s3, h3, hwf3, -, heq3⟩ := update_spec s hs hf0 (a ++ b) (by simp; omega) fuel (by simp; omega)
  refine ⟨s1, s2, s3, h1, h2, h3, ?_, hwf2, hfill2, hwf3⟩
  refine heq2.trans (Equiv.trans ?_ heq3.symm)
  -- the middle: absorbing `b` after `a` is absorbing `a ++ b`, with the totals summed
  have hA : Equiv (absorbRange b s1 0 b.size) (absorbRange b (setTotal (absorbRange a s 0 a.size) (s.total + (a.size.toUInt32).toUInt64)) 0 b.size) :=
    @absorbRange_equiv s1 (setTotal (absorbRange a s 0 a.size) (s.total + (a.size.toUInt32).toUInt64)) hwf1 (absorbRange_wf hs a 0 a.size) hfill1 heq1 b 0 b.size
  rw [absorbRange_set_total, ← absorbRange_append] at hA
  have htot1 : s1.total = s.total + (a.size.toUInt32).toUInt64 := by rw [heq1.total_eq]; rfl
  have hsum : s.total + (a.size.toUInt32).toUInt64 + (b.size.toUInt32).toUInt64 = s.total + ((a.size + b.size).toUInt32).toUInt64 := by
    rw [UInt64.add_assoc, size_total a b hsize]
  have this := equiv_set_total hA (s1.total + (b.size.toUInt32).toUInt64)
  rw [setTotal_setTotal, htot1, hsum] at this
  rw [Array.size_append, htot1, hsum]
  exact this

/-- The state `sha256_init` returns. -/
def initState : Sha256State :=
  { h := #[(1779033703 : UInt32), (3144134277 : UInt32), (1013904242 : UInt32), (2773480762 : UInt32),
           (1359893119 : UInt32), (2600822924 : UInt32), (528734635 : UInt32), (1541459225 : UInt32)],
    block := Array.replicate 64 (0 : UInt8), filled := (0 : UInt32), total := (0 : UInt64) }

/-- One-shot `sha256` of a concatenation is the streamed digest: init, `a`, `b`, final. -/
theorem sha256_append (a b out : Array UInt8) (hsize : a.size + b.size < 2 ^ 32) (hout : out.size < 2 ^ 32)
    (fuel : Nat) (hf : a.size + b.size + 70 < fuel) :
    ∃ s0 s1 s2, sha256_init fuel = some s0 ∧ sha256_update s0 a fuel = some s1 ∧ sha256_update s1 b fuel = some s2 ∧
      sha256 (a ++ b) out fuel = sha256_final s2 out fuel := by
  have hinit : sha256_init fuel = some initState := rfl
  have hs0wf : WF initState := by
    show (Array.replicate 64 (0 : UInt8)).size = 64; simp
  obtain ⟨s1, s2, s3, h1, h2, h3, heq, hwf2, hfill2, hwf3⟩ :=
    sha256_update_append initState hs0wf (by show (0 : UInt32).toNat < 64; decide) a b hsize fuel hf
  refine ⟨_, s1, s2, hinit, h1, h2, ?_⟩
  unfold sha256
  rw [hinit]
  simp only [bind, Option.bind]
  rw [h3]
  simp only [bind, Option.bind]
  rw [final_congr s3 s2 hwf3 hwf2 (by rw [← heq.filled_eq]; exact hfill2) heq.symm out hout fuel (by omega)]
  cases sha256_final s2 out fuel <;> rfl

end Oak.Stdlib.Hash
