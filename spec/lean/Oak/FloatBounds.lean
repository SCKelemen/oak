import Oak.Floats
import Oak.Reduce

/-!
# Oak.FloatBounds — what a regrouped floating-point reduction computes

`docs/spec/55-parallelism.md` section 4 says that under `order any` a
reduction over an `f32` add declared associative computes *some grouping's*
value, a bounded quantity, while `order tree`, `order left`, and the default
compute the exact named grouping bit for bit. This file states the bound,
over the rounding model of `Oak.Floats` (an integer rounded to `p`
significant bits after every operation):

* `round_error`: one rounding moves a value by at most `|x| / 2^p` — the
  unit roundoff `u = 2^-p`, stated over the integers as
  `2^p · |round p x − x| ≤ |x|`.
* `Grouping`: any nesting of additions over a list of leaves; `depth`,
  `exact` (the mathematical sum), `mass` (the sum of magnitudes),
  `rounded p` (the sum computed with a rounding after each addition).
* `rounded_error`: for every grouping,
  `2^(p·depth) · |rounded − exact| ≤ B p depth · mass`, where
  `B p d + 2^(p·d) = (2^p + 1)^d` (`bound_closed`). Read over the
  rationals with `u = 2^-p`: `|rounded − exact| ≤ ((1 + u)^depth − 1) · Σ|xᵢ|`,
  the classical bound, with no first-order approximation.
* `chain_error`: `reduce.chain` — the left fold from the first element,
  what `order any` lowers a declared-associative reduction to — is the
  grouping of depth `n − 1` over `n` leaves, so its error is within
  `((1 + u)^(n−1) − 1) · Σ|xᵢ|` of the exact sum.
* `tree_depth_log`, `tree_error_log`: `reduce.tree` is a grouping of depth
  at most `bitlen n` (`⌊log₂ n⌋ + 1`), so its error is within
  `((1 + u)^(⌊log₂ n⌋ + 1) − 1) · Σ|xᵢ|`.

Two groupings of the same leaves therefore differ by at most the sum of
their bounds: that is the whole content of "bounded" in the chapter, and
it is why the claim `laws { associative }` on a floating-point add is a
permission with a stated cost rather than a lie about the format.
-/

namespace Oak.Floats

/-! ## The unit roundoff -/

theorem bitlenFuel_bounds : ∀ (fuel n : Nat), n ≤ fuel →
    n < 2 ^ bitlenFuel fuel n ∧ (n ≠ 0 → 2 ^ (bitlenFuel fuel n - 1) ≤ n) := by
  intro fuel
  induction fuel with
  | zero =>
    intro n hn
    have : n = 0 := Nat.le_zero.mp hn
    subst this
    exact ⟨by simp [bitlenFuel], fun h => absurd rfl h⟩
  | succ fuel ih =>
    intro n hn
    by_cases h0 : n = 0
    · subst h0
      exact ⟨by simp [bitlenFuel], fun h => absurd rfl h⟩
    · have hhalf : n / 2 ≤ fuel := by omega
      obtain ⟨hlt, hge⟩ := ih (n / 2) hhalf
      simp only [bitlenFuel, h0, if_false]
      constructor
      · rw [Nat.pow_succ]
        omega
      · intro _
        by_cases hsmall : n / 2 = 0
        · have hz : bitlenFuel fuel (n / 2) = 0 := by
            rw [hsmall]; cases fuel <;> simp [bitlenFuel]
          rw [hz]
          simp
          omega
        · have hlow := hge hsmall
          have hpos : 0 < bitlenFuel fuel (n / 2) := by
            apply Nat.pos_of_ne_zero
            intro hz
            rw [hz] at hlt
            simp at hlt
            omega
          have hsplit : bitlenFuel fuel (n / 2) + 1 - 1 = (bitlenFuel fuel (n / 2) - 1) + 1 := by omega
          rw [hsplit, Nat.pow_succ]
          omega

theorem bitlen_upper (n : Nat) : n < 2 ^ bitlen n := (bitlenFuel_bounds n n (Nat.le_refl n)).1

theorem bitlen_lower {n : Nat} (h : n ≠ 0) : 2 ^ (bitlen n - 1) ≤ n := (bitlenFuel_bounds n n (Nat.le_refl n)).2 h

/-- The distance between two naturals. -/
def dist (a b : Nat) : Nat := if a ≤ b then b - a else a - b

theorem dist_comm (a b : Nat) : dist a b = dist b a := by
  unfold dist; split <;> split <;> omega

/-- One rounding of a magnitude moves it by at most `a / 2^p`: the unit
roundoff, stated over the naturals. -/
theorem roundNat_error (p a : Nat) : 2 ^ p * dist (roundNat p a) a ≤ a := by
  unfold roundNat
  split
  · rename_i hsmall
    simp [dist]
  · rename_i hbig
    have hge : 2 ^ p ≤ a := Nat.not_lt.mp hbig
    have hne : a ≠ 0 := by
      intro h; subst h
      have := Nat.two_pow_pos p
      omega
    have hbit : p < bitlen a := by
      have hup := bitlen_upper a
      apply Nat.lt_of_not_le
      intro hle'
      have : 2 ^ bitlen a ≤ 2 ^ p := Nat.pow_le_pow_right (by decide) hle'
      omega
    -- unit = 2^(bitlen a - p), half = unit / 2 = 2^(bitlen a - p - 1)
    have hshift : bitlen a - p = (bitlen a - p - 1) + 1 := by omega
    have hunit : 2 ^ (bitlen a - p) = 2 * 2 ^ (bitlen a - p - 1) := by
      rw [← Nat.pow_succ']
      congr 1
    have hhalf : 2 ^ (bitlen a - p) / 2 = 2 ^ (bitlen a - p - 1) := by
      rw [hunit]; simp
    -- 2^p * half = 2^(bitlen a - 1) ≤ a
    have hscaled : 2 ^ p * 2 ^ (bitlen a - p - 1) ≤ a := by
      rw [← Nat.pow_add, show p + (bitlen a - p - 1) = bitlen a - 1 by omega]
      exact bitlen_lower hne
    dsimp only
    generalize hu : 2 ^ (bitlen a - p) = unit at *
    have hpos : 0 < unit := by rw [← hu]; exact Nat.two_pow_pos _
    have hdiv := Nat.div_add_mod a unit
    have hmod := Nat.mod_lt a hpos
    rw [hhalf]
    generalize hq : a / unit = q at *
    generalize hr : a % unit = r at *
    generalize hh : 2 ^ (bitlen a - p - 1) = half at *
    have hunit' : unit = 2 * half := hunit
    have hqu : q * unit = unit * q := Nat.mul_comm _ _
    have hqu1 : (q + 1) * unit = unit * q + unit := by rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm]
    -- a = unit * q + r, r < unit; the rounded value is q*unit or (q+1)*unit.
    split
    · -- r < half: down; distance r
      rename_i hlt
      have : dist (q * unit) a = r := by unfold dist; split <;> omega
      rw [this]
      calc 2 ^ p * r ≤ 2 ^ p * half := Nat.mul_le_mul_left _ (Nat.le_of_lt hlt)
        _ ≤ a := hscaled
    · split
      · -- half < r: up; distance unit - r < half
        rename_i _ hgt
        have : dist ((q + 1) * unit) a = unit - r := by unfold dist; split <;> omega
        rw [this]
        calc 2 ^ p * (unit - r) ≤ 2 ^ p * half := Nat.mul_le_mul_left _ (by omega)
          _ ≤ a := hscaled
      · -- a tie: distance exactly half either way
        rename_i _ _
        have hr : r = half := by omega
        split
        · have : dist (q * unit) a = half := by unfold dist; split <;> omega
          rw [this]; exact hscaled
        · have : dist ((q + 1) * unit) a = half := by unfold dist; split <;> omega
          rw [this]; exact hscaled

/-- The magnitude of a difference of naturals, as integers, is their distance. -/
theorem natAbs_ofNat_sub (r a : Nat) : ((r : Int) - (a : Int)).natAbs = dist r a := by
  unfold dist
  split
  · rename_i h
    have hk : ((r : Int) - (a : Int)) = -(((a - r : Nat) : Int)) := by omega
    rw [hk, Int.natAbs_neg, Int.natAbs_natCast]
  · rename_i h
    have hk : ((r : Int) - (a : Int)) = (((r - a : Nat) : Int)) := by omega
    rw [hk, Int.natAbs_natCast]

/-- The rounded integer is the rounded magnitude with the sign restored, so
its distance from `x` is the magnitudes' distance. -/
theorem round_natAbs_dist (p : Nat) (x : Int) : (round p x - x).natAbs = dist (roundNat p x.natAbs) x.natAbs := by
  unfold round
  split
  · rename_i hneg
    have habs := Int.ofNat_natAbs_of_nonpos (Int.le_of_lt hneg)
    simp only [Int.ofNat_eq_natCast] at habs ⊢
    have hk : -((roundNat p x.natAbs : Nat) : Int) - x = ((x.natAbs : Nat) : Int) - ((roundNat p x.natAbs : Nat) : Int) := by omega
    rw [hk, natAbs_ofNat_sub, dist_comm]
  · rename_i hnn
    have habs := Int.natAbs_of_nonneg (Int.not_lt.mp hnn)
    simp only [Int.ofNat_eq_natCast] at habs ⊢
    have hk : ((roundNat p x.natAbs : Nat) : Int) - x = ((roundNat p x.natAbs : Nat) : Int) - ((x.natAbs : Nat) : Int) := by omega
    rw [hk, natAbs_ofNat_sub]

/-- **The unit roundoff.** `2^p · |round p x − x| ≤ |x|`: one rounding moves
a value by at most `|x| / 2^p`, which is `u · |x|` with `u = 2^-p`. -/
theorem round_error (p : Nat) (x : Int) : 2 ^ p * (round p x - x).natAbs ≤ x.natAbs := by
  rw [round_natAbs_dist]
  exact roundNat_error p x.natAbs

/-! ## Any grouping of additions -/

/-- A nesting of additions over integer leaves — the leaves already
representable values, as a reduction's inputs are. -/
inductive Grouping where
  | leaf : Int → Grouping
  | node : Grouping → Grouping → Grouping

namespace Grouping

def depth : Grouping → Nat
  | leaf _ => 0
  | node l r => max (depth l) (depth r) + 1

/-- The mathematical sum of the leaves. -/
def exact : Grouping → Int
  | leaf x => x
  | node l r => exact l + exact r

/-- The sum of the leaves' magnitudes, `Σ|xᵢ|`. -/
def mass : Grouping → Nat
  | leaf x => x.natAbs
  | node l r => mass l + mass r

/-- The sum as the format computes it: every addition rounded once. -/
def rounded (p : Nat) : Grouping → Int
  | leaf x => x
  | node l r => round p (rounded p l + rounded p r)

/-- The error of a grouping: the distance between its rounded and exact sums. -/
def err (p : Nat) (g : Grouping) : Nat := (rounded p g - exact g).natAbs

end Grouping

/-- The bound's numerator at depth `d`, scaled by `2^(p·d)`:
`B p 0 = 0`, `B p (d+1) = (2^p + 1) · B p d + 2^(p·d)`; in closed form
`B p d = (2^p + 1)^d − 2^(p·d)` (`bound_closed`). -/
def B (p : Nat) : Nat → Nat
  | 0 => 0
  | d + 1 => (2 ^ p + 1) * B p d + 2 ^ (p * d)

theorem bound_closed (p d : Nat) : B p d + 2 ^ (p * d) = (2 ^ p + 1) ^ d := by
  induction d with
  | zero => simp [B]
  | succ d ih =>
    simp only [B]
    rw [Nat.pow_succ, ← ih, Nat.mul_succ, Nat.pow_add]
    have alg : ∀ a b c : Nat, (c + 1) * a + b + b * c = (a + b) * (c + 1) := by
      intro a b c
      rw [Nat.succ_mul, Nat.add_mul, Nat.mul_succ, Nat.mul_succ, Nat.mul_comm c a]
      omega
    exact alg (B p d) (2 ^ (p * d)) (2 ^ p)

/-- Scaling the bound up a level never loses: `2^(p·k) · B p m ≤ B p (m + k)`. -/
theorem bound_mono (p m : Nat) : ∀ k, 2 ^ (p * k) * B p m ≤ B p (m + k) := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    have h1 : 2 ^ p * (2 ^ (p * k) * B p m) ≤ 2 ^ p * B p (m + k) := Nat.mul_le_mul_left _ ih
    have h2 : 2 ^ p * B p (m + k) ≤ (2 ^ p + 1) * B p (m + k) := Nat.mul_le_mul_right _ (Nat.le_succ _)
    have h3 : (2 ^ p + 1) * B p (m + k) ≤ B p (m + k + 1) := by
      simp only [B]; exact Nat.le_add_right _ _
    have h4 : 2 ^ (p * (k + 1)) * B p m = 2 ^ p * (2 ^ (p * k) * B p m) := by
      rw [Nat.mul_succ, Nat.pow_add, Nat.mul_comm (2 ^ (p * k)) (2 ^ p), Nat.mul_assoc]
    rw [h4, Nat.add_succ]
    exact Nat.le_trans h1 (Nat.le_trans h2 h3)

/-- The exact sum of a grouping is within its mass. -/
theorem exact_le_mass : ∀ g : Grouping, (Grouping.exact g).natAbs ≤ Grouping.mass g
  | .leaf x => Nat.le_refl _
  | .node l r => by
    simp only [Grouping.exact, Grouping.mass]
    have := Int.natAbs_add_le (Grouping.exact l) (Grouping.exact r)
    have hl := exact_le_mass l
    have hr := exact_le_mass r
    omega

/-- **Any grouping's error is bounded by its depth.**
`2^(p·depth g) · |rounded − exact| ≤ B p (depth g) · mass g`; over the
rationals with `u = 2^-p`, `|rounded − exact| ≤ ((1 + u)^depth − 1) · Σ|xᵢ|`. -/
theorem rounded_error (p : Nat) : ∀ g : Grouping,
    2 ^ (p * Grouping.depth g) * Grouping.err p g ≤ B p (Grouping.depth g) * Grouping.mass g := by
  intro g
  induction g with
  | leaf x => simp [Grouping.depth, Grouping.err, Grouping.rounded, Grouping.exact, B]
  | node l r ihl ihr =>
    have hl : 2 ^ (p * max (Grouping.depth l) (Grouping.depth r)) * Grouping.err p l ≤ B p (max (Grouping.depth l) (Grouping.depth r)) * Grouping.mass l :=
      lift_bound_of p l _ (Nat.le_max_left _ _) ihl
    have hr : 2 ^ (p * max (Grouping.depth l) (Grouping.depth r)) * Grouping.err p r ≤ B p (max (Grouping.depth l) (Grouping.depth r)) * Grouping.mass r :=
      lift_bound_of p r _ (Nat.le_max_right _ _) ihr
    have hmassl := exact_le_mass l
    have hmassr := exact_le_mass r
    simp only [Grouping.depth, Grouping.err, Grouping.rounded, Grouping.exact, Grouping.mass] at *
    generalize hd : max (Grouping.depth l) (Grouping.depth r) = d at *
    generalize hlh : Grouping.rounded p l = lh at *
    generalize hrh : Grouping.rounded p r = rh at *
    generalize hle : Grouping.exact l = le at *
    generalize hre : Grouping.exact r = re at *
    generalize hSl : Grouping.mass l = Sl at *
    generalize hSr : Grouping.mass r = Sr at *
    -- the error splits into the rounding of this addition and the subtrees' errors
    have hsplit : (round p (lh + rh) - (le + re)).natAbs ≤ (round p (lh + rh) - (lh + rh)).natAbs + ((lh - le).natAbs + (rh - re).natAbs) := by
      have h1 : round p (lh + rh) - (le + re) = (round p (lh + rh) - (lh + rh)) + ((lh - le) + (rh - re)) := by omega
      rw [h1]
      have a1 := Int.natAbs_add_le (round p (lh + rh) - (lh + rh)) ((lh - le) + (rh - re))
      have a2 := Int.natAbs_add_le (lh - le) (rh - re)
      exact Nat.le_trans a1 (Nat.add_le_add_left a2 _)
    have hround := round_error p (lh + rh)
    have hsum : (lh + rh).natAbs ≤ (le.natAbs + re.natAbs) + ((lh - le).natAbs + (rh - re).natAbs) := by
      have h1 : lh + rh = (le + re) + ((lh - le) + (rh - re)) := by omega
      rw [h1]
      have a1 := Int.natAbs_add_le (le + re) ((lh - le) + (rh - re))
      have a2 := Int.natAbs_add_le le re
      have a3 := Int.natAbs_add_le (lh - le) (rh - re)
      exact Nat.le_trans a1 (Nat.add_le_add a2 a3)
    -- name the magnitudes
    generalize herr : (round p (lh + rh) - (le + re)).natAbs = err at *
    generalize he0 : (round p (lh + rh) - (lh + rh)).natAbs = e0 at *
    generalize heL : (lh - le).natAbs = eL at *
    generalize heR : (rh - re).natAbs = eR at *
    generalize hM : (lh + rh).natAbs = M at *
    generalize hal : le.natAbs = al at *
    generalize har : re.natAbs = ar at *
    -- 2^p · err ≤ (Sl + Sr) + (2^p + 1) · (eL + eR)
    have hE : 2 ^ p * err ≤ (Sl + Sr) + (2 ^ p + 1) * (eL + eR) := by
      have h1 := Nat.mul_le_mul_left (2 ^ p) hsplit
      rw [Nat.mul_add] at h1
      have h3 : (2 ^ p + 1) * (eL + eR) = 2 ^ p * (eL + eR) + (eL + eR) := by
        rw [Nat.add_mul, Nat.one_mul]
      omega
    -- scale by 2^(p·d) and use the subtree bounds
    have hscale := Nat.mul_le_mul_left (2 ^ (p * d)) hE
    have hexp : 2 ^ (p * d) * ((Sl + Sr) + (2 ^ p + 1) * (eL + eR))
        = 2 ^ (p * d) * (Sl + Sr) + (2 ^ p + 1) * (2 ^ (p * d) * eL + 2 ^ (p * d) * eR) := by
      rw [Nat.mul_add, Nat.mul_left_comm (2 ^ (p * d)) (2 ^ p + 1), Nat.mul_add (2 ^ (p * d)) eL eR]
    rw [hexp] at hscale
    have hsub : (2 ^ p + 1) * (2 ^ (p * d) * eL + 2 ^ (p * d) * eR)
        ≤ (2 ^ p + 1) * (B p d * Sl + B p d * Sr) := Nat.mul_le_mul_left _ (Nat.add_le_add hl hr)
    have hpow : 2 ^ (p * (d + 1)) = 2 ^ (p * d) * 2 ^ p := by rw [Nat.mul_succ, Nat.pow_add]
    have htarget : ((2 ^ p + 1) * B p d + 2 ^ (p * d)) * (Sl + Sr)
        = 2 ^ (p * d) * (Sl + Sr) + (2 ^ p + 1) * (B p d * Sl + B p d * Sr) := by
      rw [Nat.add_mul, Nat.mul_assoc, Nat.mul_add (B p d)]
      omega
    simp only [B]
    rw [hpow, Nat.mul_assoc, htarget]
    exact Nat.le_trans hscale (Nat.add_le_add_left hsub _)
where
  lift_bound_of (p : Nat) (k : Grouping) (d : Nat) (hk : Grouping.depth k ≤ d)
      (base : 2 ^ (p * Grouping.depth k) * Grouping.err p k ≤ B p (Grouping.depth k) * Grouping.mass k) :
      2 ^ (p * d) * Grouping.err p k ≤ B p d * Grouping.mass k := by
    have hkk : d = Grouping.depth k + (d - Grouping.depth k) := by omega
    have step := bound_mono p (Grouping.depth k) (d - Grouping.depth k)
    rw [← hkk] at step
    calc 2 ^ (p * d) * Grouping.err p k
        = 2 ^ (p * (d - Grouping.depth k)) * (2 ^ (p * Grouping.depth k) * Grouping.err p k) := by
          rw [← Nat.mul_assoc, ← Nat.pow_add, ← Nat.mul_add, Nat.add_comm, ← hkk]
      _ ≤ 2 ^ (p * (d - Grouping.depth k)) * (B p (Grouping.depth k) * Grouping.mass k) := Nat.mul_le_mul_left _ base
      _ = (2 ^ (p * (d - Grouping.depth k)) * B p (Grouping.depth k)) * Grouping.mass k := by rw [Nat.mul_assoc]
      _ ≤ B p d * Grouping.mass k := Nat.mul_le_mul_right _ step

/-- The bound of a subtree lifted to a larger depth. -/
theorem lift_bound (p : Nat) (k : Grouping) (d : Nat) (hk : Grouping.depth k ≤ d) :
    2 ^ (p * d) * Grouping.err p k ≤ B p d * Grouping.mass k := by
  have hkk : d = Grouping.depth k + (d - Grouping.depth k) := by omega
  have step := bound_mono p (Grouping.depth k) (d - Grouping.depth k)
  rw [← hkk] at step
  have base : 2 ^ (p * Grouping.depth k) * Grouping.err p k ≤ B p (Grouping.depth k) * Grouping.mass k := rounded_error p k
  calc 2 ^ (p * d) * Grouping.err p k
      = 2 ^ (p * (d - Grouping.depth k)) * (2 ^ (p * Grouping.depth k) * Grouping.err p k) := by
        rw [← Nat.mul_assoc, ← Nat.pow_add, ← Nat.mul_add, Nat.add_comm, ← hkk]
    _ ≤ 2 ^ (p * (d - Grouping.depth k)) * (B p (Grouping.depth k) * Grouping.mass k) := Nat.mul_le_mul_left _ base
    _ = (2 ^ (p * (d - Grouping.depth k)) * B p (Grouping.depth k)) * Grouping.mass k := by rw [Nat.mul_assoc]
    _ ≤ B p d * Grouping.mass k := Nat.mul_le_mul_right _ step

/-! ## The chain: what `order any` computes -/

/-- The left comb over `x :: xs`: `((x + x₁) + x₂) + ⋯`, the grouping of
`reduce.chain` (`Oak.Reduce.chainFold`). -/
def leftComb (x : Int) : List Int → Grouping
  | [] => .leaf x
  | y :: ys => leftCombFrom (.node (.leaf x) (.leaf y)) ys
where
  leftCombFrom (acc : Grouping) : List Int → Grouping
    | [] => acc
    | y :: ys => leftCombFrom (.node acc (.leaf y)) ys

/-- The format's addition: exact, then one rounding. -/
def fadd (p : Nat) (a b : Int) : Int := round p (a + b)

theorem leftCombFrom_rounded (p : Nat) : ∀ (ys : List Int) (acc : Grouping),
    Grouping.rounded p (leftComb.leftCombFrom acc ys) = ys.foldl (fadd p) (Grouping.rounded p acc) := by
  intro ys
  induction ys with
  | nil => intro acc; rfl
  | cons y ys ih => intro acc; simp only [leftComb.leftCombFrom, List.foldl]; rw [ih]; rfl

theorem leftCombFrom_exact : ∀ (ys : List Int) (acc : Grouping),
    Grouping.exact (leftComb.leftCombFrom acc ys) = Grouping.exact acc + ys.sum := by
  intro ys
  induction ys with
  | nil => intro acc; simp [leftComb.leftCombFrom]
  | cons y ys ih => intro acc; simp only [leftComb.leftCombFrom, List.sum_cons]; rw [ih]; simp [Grouping.exact]; omega

theorem leftCombFrom_mass : ∀ (ys : List Int) (acc : Grouping),
    Grouping.mass (leftComb.leftCombFrom acc ys) = Grouping.mass acc + (ys.map Int.natAbs).sum := by
  intro ys
  induction ys with
  | nil => intro acc; simp [leftComb.leftCombFrom]
  | cons y ys ih => intro acc; simp only [leftComb.leftCombFrom, List.map, List.sum_cons]; rw [ih]; simp [Grouping.mass]; omega

theorem leftCombFrom_depth : ∀ (ys : List Int) (acc : Grouping),
    Grouping.depth (leftComb.leftCombFrom acc ys) = Grouping.depth acc + ys.length := by
  intro ys
  induction ys with
  | nil => intro acc; simp [leftComb.leftCombFrom]
  | cons y ys ih =>
    intro acc
    simp only [leftComb.leftCombFrom, List.length_cons]
    rw [ih]
    simp [Grouping.depth]
    omega

/-- `reduce.chain` over `x :: xs` is the left comb's rounded sum. -/
theorem chain_is_leftComb (p : Nat) (z x : Int) (xs : List Int) :
    Oak.Reduce.chainFold (fadd p) z (x :: xs) = Grouping.rounded p (leftComb x xs) := by
  cases xs with
  | nil => rfl
  | cons y ys =>
    simp only [Oak.Reduce.chainFold, leftComb, List.foldl]
    rw [leftCombFrom_rounded]
    rfl

theorem leftComb_depth (x : Int) (xs : List Int) : Grouping.depth (leftComb x xs) = xs.length := by
  cases xs with
  | nil => rfl
  | cons y ys => simp only [leftComb, List.length_cons]; rw [leftCombFrom_depth]; simp [Grouping.depth]; omega

theorem leftComb_exact (x : Int) (xs : List Int) : Grouping.exact (leftComb x xs) = (x :: xs).sum := by
  cases xs with
  | nil => simp [leftComb, Grouping.exact]
  | cons y ys => simp only [leftComb, List.sum_cons]; rw [leftCombFrom_exact]; simp [Grouping.exact]; omega

theorem leftComb_mass (x : Int) (xs : List Int) : Grouping.mass (leftComb x xs) = ((x :: xs).map Int.natAbs).sum := by
  cases xs with
  | nil => simp [leftComb, Grouping.mass]
  | cons y ys => simp only [leftComb, List.map, List.sum_cons]; rw [leftCombFrom_mass]; simp [Grouping.mass]; omega

/-- **The bound for `order any`.** `reduce.chain` over `n + 1` values —
what a declared-associative reduction lowers to — is within
`((1 + u)^n − 1) · Σ|xᵢ|` of the exact sum, stated over the integers as
`2^(p·n) · |chain − Σxᵢ| ≤ B p n · Σ|xᵢ|`. -/
theorem chain_error (p : Nat) (z x : Int) (xs : List Int) :
    2 ^ (p * xs.length) * (Oak.Reduce.chainFold (fadd p) z (x :: xs) - (x :: xs).sum).natAbs
      ≤ B p xs.length * ((x :: xs).map Int.natAbs).sum := by
  rw [chain_is_leftComb, ← leftComb_exact x xs, ← leftComb_mass x xs, ← leftComb_depth x xs]
  exact rounded_error p (leftComb x xs)

/-- Two groupings of the same leaves differ by at most the sum of their
bounds — the distance between any two orders a program might name. -/
theorem groupings_differ (p : Nat) (g h : Grouping) (hexact : Grouping.exact g = Grouping.exact h) :
    2 ^ (p * (max (Grouping.depth g) (Grouping.depth h))) * (Grouping.rounded p g - Grouping.rounded p h).natAbs
      ≤ B p (max (Grouping.depth g) (Grouping.depth h)) * (Grouping.mass g + Grouping.mass h) := by
  generalize hd : max (Grouping.depth g) (Grouping.depth h) = d
  have split : (Grouping.rounded p g - Grouping.rounded p h).natAbs ≤ Grouping.err p g + Grouping.err p h := by
    unfold Grouping.err
    have h1 : Grouping.rounded p g - Grouping.rounded p h = (Grouping.rounded p g - Grouping.exact g) - (Grouping.rounded p h - Grouping.exact h) := by rw [hexact]; omega
    rw [h1]
    have := Int.natAbs_sub_le (Grouping.rounded p g - Grouping.exact g) (Grouping.rounded p h - Grouping.exact h)
    omega
  have hg := lift_bound p g d (by rw [← hd]; exact Nat.le_max_left _ _)
  have hh := lift_bound p h d (by rw [← hd]; exact Nat.le_max_right _ _)
  have := Nat.mul_le_mul_left (2 ^ (p * d)) split
  rw [Nat.mul_add] at this
  rw [Nat.mul_add]
  omega

/-! ## The tree is a grouping too -/

open Oak.Reduce in
/-- A stack of partials whose values are the rounded sums of groupings,
entry by entry. -/
def StackOf (p : Nat) : List (Partial Int) → List Grouping → Prop
  | [], [] => True
  | q :: s, g :: gs => q.value = Grouping.rounded p g ∧ StackOf p s gs
  | _, _ => False

/-- The exact and absolute sums a list of groupings accounts for. -/
def exactSum (gs : List Grouping) : Int := (gs.map Grouping.exact).sum
def massSum (gs : List Grouping) : Nat := (gs.map Grouping.mass).sum

open Oak.Reduce in
theorem collapse_stack (p : Nat) : ∀ (s : List (Partial Int)) (gs : List Grouping), StackOf p s gs →
    ∃ gs', StackOf p (collapse (fadd p) s) gs' ∧ exactSum gs' = exactSum gs ∧ massSum gs' = massSum gs := by
  intro s
  induction s using collapse.induct (fadd p) with
  | case1 top next rest heq ih =>
    intro gs hs
    match gs, hs with
    | gt :: gn :: grest, ⟨htop, hnext, hrest⟩ =>
      rw [collapse, if_pos heq]
      have hmerged : StackOf p ({ value := fadd p next.value top.value, level := next.level + 1 } :: rest) (Grouping.node gn gt :: grest) := by
        refine ⟨?_, hrest⟩
        simp only [Grouping.rounded, fadd]
        rw [htop, hnext]
      obtain ⟨gs', hgs', hex, hmass⟩ := ih _ hmerged
      refine ⟨gs', hgs', ?_, ?_⟩
      · rw [hex]; simp [exactSum, Grouping.exact]; omega
      · rw [hmass]; simp [massSum, Grouping.mass]; omega
  | case2 top next rest hne =>
    intro gs hs
    rw [collapse, if_neg hne]
    exact ⟨gs, hs, rfl, rfl⟩
  | case3 s hs =>
    intro gs hgs
    have : collapse (fadd p) s = s := by
      cases s with
      | nil => rw [collapse]; exact hs
      | cons q rest =>
        cases rest with
        | nil => exact collapse_single _ q
        | cons q2 rest2 => exact (hs q q2 rest2 rfl).elim
    rw [this]
    exact ⟨gs, hgs, rfl, rfl⟩

open Oak.Reduce in
theorem push_stack (p : Nat) (s : List (Partial Int)) (gs : List Grouping) (x : Int) (hs : StackOf p s gs) :
    ∃ gs', StackOf p (push (fadd p) s x) gs' ∧ exactSum gs' = x + exactSum gs ∧ massSum gs' = x.natAbs + massSum gs := by
  have hleaf : StackOf p ({ value := x, level := 0 } :: s) (Grouping.leaf x :: gs) := ⟨rfl, hs⟩
  obtain ⟨gs', hgs', hex, hmass⟩ := collapse_stack p _ _ hleaf
  refine ⟨gs', hgs', ?_, ?_⟩
  · rw [hex]; simp [exactSum, Grouping.exact]
  · rw [hmass]; simp [massSum, Grouping.mass]

open Oak.Reduce in
theorem fold_stack (p : Nat) : ∀ (xs : List Int) (s : List (Partial Int)) (gs : List Grouping), StackOf p s gs →
    ∃ gs', StackOf p (xs.foldl (push (fadd p)) s) gs' ∧ exactSum gs' = xs.sum + exactSum gs ∧ massSum gs' = (xs.map Int.natAbs).sum + massSum gs := by
  intro xs
  induction xs with
  | nil => intro s gs hs; exact ⟨gs, hs, by simp, by simp⟩
  | cons x xs ih =>
    intro s gs hs
    obtain ⟨gs1, h1, hex1, hmass1⟩ := push_stack p s gs x hs
    obtain ⟨gs2, h2, hex2, hmass2⟩ := ih _ _ h1
    refine ⟨gs2, by simpa [List.foldl] using h2, ?_, ?_⟩
    · rw [hex2, hex1]; simp [List.sum_cons]; omega
    · rw [hmass2, hmass1]; simp [List.map, List.sum_cons]; omega

open Oak.Reduce in
theorem finish_stack (p : Nat) : ∀ (s : List (Partial Int)) (gs : List Grouping), s ≠ [] → StackOf p s gs →
    ∃ g, finish (fadd p) s = some (Grouping.rounded p g) ∧ Grouping.exact g = exactSum gs ∧ Grouping.mass g = massSum gs := by
  intro s
  induction s using finish.induct (fadd p) with
  | case1 => intro gs h; exact absurd rfl h
  | case2 q =>
    intro gs _ hs
    match gs, hs with
    | [g], ⟨hq, _⟩ =>
      refine ⟨g, ?_, ?_, ?_⟩
      · simp [finish, hq]
      · simp [exactSum]
      · simp [massSum]
  | case3 top next rest ih =>
    intro gs _ hs
    match gs, hs with
    | gt :: gn :: grest, ⟨htop, hnext, hrest⟩ =>
      have hmerged : StackOf p ({ value := fadd p next.value top.value, level := next.level } :: rest) (Grouping.node gn gt :: grest) := by
        refine ⟨?_, hrest⟩
        simp only [Grouping.rounded, fadd]
        rw [htop, hnext]
      obtain ⟨g, hg, hex, hmass⟩ := ih _ (List.cons_ne_nil _ _) hmerged
      refine ⟨g, ?_, ?_, ?_⟩
      · rw [finish]; exact hg
      · rw [hex]; simp [exactSum, Grouping.exact]; omega
      · rw [hmass]; simp [massSum, Grouping.mass]; omega

/-- **`reduce.tree` computes a grouping's value.** Over a non-empty list the
binary-counter tree is the rounded sum of some grouping of exactly those
leaves — so `rounded_error` bounds it by that grouping's depth, and
`groupings_differ` bounds its distance from the chain. -/
theorem tree_is_grouping (p : Nat) (z : Int) (xs : List Int) (h : xs ≠ []) :
    ∃ g : Grouping, Oak.Reduce.tree (fadd p) z xs = Grouping.rounded p g ∧
      Grouping.exact g = xs.sum ∧ Grouping.mass g = (xs.map Int.natAbs).sum := by
  obtain ⟨gs, hgs, hex, hmass⟩ := fold_stack p xs [] [] trivial
  have hne : xs.foldl (Oak.Reduce.push (fadd p)) [] ≠ [] := by
    match xs, h with
    | x :: rest, _ =>
      simp only [List.foldl]
      -- every push leaves a non-empty stack, and the fold starts from a push
      have : ∀ (ys : List Int) (s : List (Oak.Reduce.Partial Int)), s ≠ [] → ys.foldl (Oak.Reduce.push (fadd p)) s ≠ [] := by
        intro ys
        induction ys with
        | nil => intro s hs; simpa using hs
        | cons y ys ih => intro s hs; simp only [List.foldl]; exact ih _ (Oak.Reduce.collapse_ne_nil _ _ (List.cons_ne_nil _ _))
      exact this rest _ (Oak.Reduce.collapse_ne_nil _ _ (List.cons_ne_nil _ _))
  obtain ⟨g, hg, hgex, hgmass⟩ := finish_stack p _ gs hne hgs
  refine ⟨g, ?_, ?_, ?_⟩
  · simp only [Oak.Reduce.tree]
    rw [hg]
  · rw [hgex, hex]; simp [exactSum]
  · rw [hgmass, hmass]; simp [massSum]

/-! ## The tree's depth is logarithmic

`reduce.tree` is a binary counter: a partial at level `k` is a grouping of
depth at most `k` over exactly `2^k` leaves, the stack's levels strictly
increase from the head down, and `finish` merges the leftovers so that the
result is at most one deeper than the bottom's level. Every level is below
`bitlen n` because `2^level ≤ n < 2^(bitlen n)`, so the tree's depth is at
most `bitlen n` — `⌊log₂ n⌋ + 1` — against the chain's `n − 1`. -/

namespace Grouping
/-- The number of leaves. -/
def leaves : Grouping → Nat
  | leaf _ => 1
  | node l r => leaves l + leaves r
end Grouping

def leavesSum (gs : List Grouping) : Nat := (gs.map Grouping.leaves).sum

open Oak.Reduce in
/-- The binary counter's invariant beside `StackOf`: a partial at level `k`
holds a grouping of depth at most `k` over exactly `2^k` leaves. -/
def Levels : List (Partial Int) → List Grouping → Prop
  | [], [] => True
  | q :: s, g :: gs => Grouping.depth g ≤ q.level ∧ Grouping.leaves g = 2 ^ q.level ∧ Levels s gs
  | _, _ => False

open Oak.Reduce in
/-- Levels strictly increase from the head down. -/
def Ascending : List (Partial Int) → Prop
  | top :: next :: rest => top.level < next.level ∧ Ascending (next :: rest)
  | _ => True

open Oak.Reduce in
/-- A stack about to collapse: the head is at most its neighbour's level and
the rest ascends — the state after a push or a merge. -/
def Counter : List (Partial Int) → Prop
  | top :: next :: rest => top.level ≤ next.level ∧ Ascending (next :: rest)
  | _ => True

open Oak.Reduce in
/-- Every level is below `L`. -/
def AllBelow (L : Nat) : List (Partial Int) → Prop
  | [] => True
  | q :: s => q.level < L ∧ AllBelow L s

open Oak.Reduce in
/-- `collapse` keeps the counter invariant and leaves the stack ascending;
the leaves, the exact sum and the mass are conserved. -/
theorem collapse_counter (p : Nat) : ∀ (s : List (Partial Int)) (gs : List Grouping),
    StackOf p s gs → Levels s gs → Counter s →
    ∃ gs', StackOf p (collapse (fadd p) s) gs' ∧ Levels (collapse (fadd p) s) gs' ∧
      Ascending (collapse (fadd p) s) ∧
      exactSum gs' = exactSum gs ∧ massSum gs' = massSum gs ∧ leavesSum gs' = leavesSum gs := by
  intro s
  induction s using collapse.induct (fadd p) with
  | case1 top next rest heq ih =>
    intro gs hs hl hc
    match gs, hs, hl with
    | gt :: gn :: grest, ⟨htop, hnext, hrest⟩, ⟨hdt, hlt, hdn, hln, hlrest⟩ =>
      rw [collapse, if_pos heq]
      have hmerged : StackOf p ({ value := fadd p next.value top.value, level := next.level + 1 } :: rest) (Grouping.node gn gt :: grest) := by
        refine ⟨?_, hrest⟩
        simp only [Grouping.rounded, fadd]
        rw [htop, hnext]
      have hlevels : Levels ({ value := fadd p next.value top.value, level := next.level + 1 } :: rest) (Grouping.node gn gt :: grest) := by
        refine ⟨?_, ?_, hlrest⟩
        · simp only [Grouping.depth]; omega
        · simp only [Grouping.leaves]; rw [hlt, hln, heq, Nat.pow_succ]; omega
      have hcounter : Counter ({ value := fadd p next.value top.value, level := next.level + 1 } :: rest) := by
        obtain ⟨_, hasc⟩ := hc
        cases rest with
        | nil => trivial
        | cons r rest' =>
          obtain ⟨hlt', hasc'⟩ := hasc
          exact ⟨Nat.succ_le_of_lt hlt', hasc'⟩
      obtain ⟨gs', hgs', hl', hasc', hex, hmass, hleaves⟩ := ih _ hmerged hlevels hcounter
      refine ⟨gs', hgs', hl', hasc', ?_, ?_, ?_⟩
      · rw [hex]; simp [exactSum, Grouping.exact]; omega
      · rw [hmass]; simp [massSum, Grouping.mass]; omega
      · rw [hleaves]; simp [leavesSum, Grouping.leaves]; omega
  | case2 top next rest hne =>
    intro gs hs hl hc
    rw [collapse, if_neg hne]
    obtain ⟨hle, hasc⟩ := hc
    exact ⟨gs, hs, hl, ⟨Nat.lt_of_le_of_ne hle hne, hasc⟩, rfl, rfl, rfl⟩
  | case3 s hs =>
    intro gs hgs hl _
    have hasc : Ascending s := by
      cases s with
      | nil => trivial
      | cons q rest =>
        cases rest with
        | nil => trivial
        | cons q2 rest2 => exact (hs q q2 rest2 rfl).elim
    have : collapse (fadd p) s = s := by
      cases s with
      | nil => rw [collapse]; exact hs
      | cons q rest =>
        cases rest with
        | nil => exact collapse_single _ q
        | cons q2 rest2 => exact (hs q q2 rest2 rfl).elim
    rw [this]
    exact ⟨gs, hgs, hl, hasc, rfl, rfl, rfl⟩

open Oak.Reduce in
theorem push_counter (p : Nat) (s : List (Partial Int)) (gs : List Grouping) (x : Int)
    (hs : StackOf p s gs) (hl : Levels s gs) (hasc : Ascending s) :
    ∃ gs', StackOf p (push (fadd p) s x) gs' ∧ Levels (push (fadd p) s x) gs' ∧
      Ascending (push (fadd p) s x) ∧
      exactSum gs' = x + exactSum gs ∧ massSum gs' = x.natAbs + massSum gs ∧
      leavesSum gs' = 1 + leavesSum gs := by
  have hleaf : StackOf p ({ value := x, level := 0 } :: s) (Grouping.leaf x :: gs) := ⟨rfl, hs⟩
  have hlleaf : Levels ({ value := x, level := 0 } :: s) (Grouping.leaf x :: gs) := ⟨Nat.le_refl _, rfl, hl⟩
  have hc : Counter ({ value := x, level := 0 } :: s) := by
    cases s with
    | nil => trivial
    | cons q rest => exact ⟨Nat.zero_le _, hasc⟩
  obtain ⟨gs', hgs', hl', hasc', hex, hmass, hleaves⟩ := collapse_counter p _ _ hleaf hlleaf hc
  refine ⟨gs', hgs', hl', hasc', ?_, ?_, ?_⟩
  · rw [hex]; simp [exactSum, Grouping.exact]
  · rw [hmass]; simp [massSum, Grouping.mass]
  · rw [hleaves]; simp [leavesSum, Grouping.leaves]

open Oak.Reduce in
theorem fold_counter (p : Nat) : ∀ (xs : List Int) (s : List (Partial Int)) (gs : List Grouping),
    StackOf p s gs → Levels s gs → Ascending s →
    ∃ gs', StackOf p (xs.foldl (push (fadd p)) s) gs' ∧ Levels (xs.foldl (push (fadd p)) s) gs' ∧
      Ascending (xs.foldl (push (fadd p)) s) ∧
      exactSum gs' = xs.sum + exactSum gs ∧ massSum gs' = (xs.map Int.natAbs).sum + massSum gs ∧
      leavesSum gs' = xs.length + leavesSum gs := by
  intro xs
  induction xs with
  | nil => intro s gs hs hl hasc; exact ⟨gs, hs, hl, hasc, by simp, by simp, by simp⟩
  | cons x xs ih =>
    intro s gs hs hl hasc
    obtain ⟨gs1, h1, hl1, hasc1, hex1, hmass1, hleaves1⟩ := push_counter p s gs x hs hl hasc
    obtain ⟨gs2, h2, hl2, hasc2, hex2, hmass2, hleaves2⟩ := ih _ _ h1 hl1 hasc1
    refine ⟨gs2, by simpa [List.foldl] using h2, by simpa [List.foldl] using hl2, by simpa [List.foldl] using hasc2, ?_, ?_, ?_⟩
    · rw [hex2, hex1]; simp [List.sum_cons]; omega
    · rw [hmass2, hmass1]; simp [List.map, List.sum_cons]; omega
    · rw [hleaves2, hleaves1]; simp [List.length]; omega

open Oak.Reduce in
/-- `2^level` leaves each, `n` leaves in all: every level is below `bitlen n`. -/
theorem levels_below (L n : Nat) (hn : n < 2 ^ L) : ∀ (s : List (Partial Int)) (gs : List Grouping),
    Levels s gs → leavesSum gs ≤ n → AllBelow L s
  | [], [], _, _ => trivial
  | q :: s, g :: gs, ⟨_, hleaves, hrest⟩, hsum => by
    have hsplit : leavesSum (g :: gs) = Grouping.leaves g + leavesSum gs := by
      simp [leavesSum, List.map, List.sum_cons]
    rw [hsplit] at hsum
    refine ⟨?_, levels_below L n hn s gs hrest (by omega)⟩
    apply Nat.lt_of_not_le
    intro hL
    have hpow : 2 ^ L ≤ 2 ^ q.level := Nat.pow_le_pow_right (by decide) hL
    omega
  | [], _ :: _, h, _ => h.elim
  | _ :: _, [], h, _ => h.elim

open Oak.Reduce in
/-- The leftover merges: the head may be one deeper than its level, the rest
within theirs. -/
def Finishing : List (Partial Int) → List Grouping → Prop
  | [], [] => True
  | q :: s, g :: gs => Grouping.depth g ≤ q.level + 1 ∧ Levels s gs
  | _, _ => False

theorem levels_finishing : ∀ (s : List (Oak.Reduce.Partial Int)) (gs : List Grouping),
    Levels s gs → Finishing s gs
  | [], [], _ => trivial
  | _ :: s, _ :: gs, ⟨hd, _, hl⟩ => ⟨Nat.le_succ_of_le hd, hl⟩
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

open Oak.Reduce in
/-- Ascent depends on the head's level only. -/
theorem ascending_relevel (q q' : Partial Int) (rest : List (Partial Int)) (h : q.level = q'.level)
    (ha : Ascending (q :: rest)) : Ascending (q' :: rest) := by
  cases rest with
  | nil => trivial
  | cons r rest' =>
    obtain ⟨hlt, hrest⟩ := ha
    refine ⟨?_, hrest⟩
    rw [← h]; exact hlt

open Oak.Reduce in
/-- `finish` over an ascending stack whose levels are below `L` yields a
grouping of depth at most `L`: each merge is at most one deeper than the
surviving level, and the bottom's level survives to the end. -/
theorem finish_depth (p L : Nat) : ∀ (s : List (Partial Int)) (gs : List Grouping), s ≠ [] →
    StackOf p s gs → Finishing s gs → Ascending s → AllBelow L s →
    ∃ g, finish (fadd p) s = some (Grouping.rounded p g) ∧ Grouping.exact g = exactSum gs ∧
      Grouping.mass g = massSum gs ∧ Grouping.depth g ≤ L := by
  intro s
  induction s using finish.induct (fadd p) with
  | case1 => intro gs h; exact absurd rfl h
  | case2 q =>
    intro gs _ hs hf _ hb
    match gs, hs, hf, hb with
    | [g], ⟨hq, _⟩, ⟨hd, _⟩, ⟨hqL, _⟩ =>
      refine ⟨g, ?_, ?_, ?_, ?_⟩
      · simp [finish, hq]
      · simp [exactSum]
      · simp [massSum]
      · omega
  | case3 top next rest ih =>
    intro gs _ hs hf hasc hb
    match gs, hs, hf, hasc, hb with
    | gt :: gn :: grest, ⟨htop, hnext, hrest⟩, ⟨hdt, hdn, _, hlrest⟩, ⟨hlt, hasc'⟩, ⟨_, hnL, hbrest⟩ =>
      have hmerged : StackOf p ({ value := fadd p next.value top.value, level := next.level } :: rest) (Grouping.node gn gt :: grest) := by
        refine ⟨?_, hrest⟩
        simp only [Grouping.rounded, fadd]
        rw [htop, hnext]
      have hfin : Finishing ({ value := fadd p next.value top.value, level := next.level } :: rest) (Grouping.node gn gt :: grest) := by
        refine ⟨?_, hlrest⟩
        simp only [Grouping.depth]; omega
      obtain ⟨g, hg, hex, hmass, hdepth⟩ :=
        ih _ (List.cons_ne_nil _ _) hmerged hfin (ascending_relevel next _ rest rfl hasc') ⟨hnL, hbrest⟩
      refine ⟨g, ?_, ?_, ?_, hdepth⟩
      · rw [finish]; exact hg
      · rw [hex]; simp [exactSum, Grouping.exact]; omega
      · rw [hmass]; simp [massSum, Grouping.mass]; omega

/-- **`reduce.tree` is a grouping of logarithmic depth.** Over a non-empty
list the binary-counter tree is the rounded sum of a grouping of exactly
those leaves whose depth is at most `bitlen n` — `⌊log₂ n⌋ + 1` — where the
chain's is `n − 1` (`leftComb_depth`). -/
theorem tree_depth_log (p : Nat) (z : Int) (xs : List Int) (h : xs ≠ []) :
    ∃ g : Grouping, Oak.Reduce.tree (fadd p) z xs = Grouping.rounded p g ∧
      Grouping.exact g = xs.sum ∧ Grouping.mass g = (xs.map Int.natAbs).sum ∧
      Grouping.depth g ≤ bitlen xs.length := by
  obtain ⟨gs, hgs, hl, hasc, hex, hmass, hleaves⟩ := fold_counter p xs [] [] trivial trivial trivial
  have hne : xs.foldl (Oak.Reduce.push (fadd p)) [] ≠ [] := by
    match xs, h with
    | x :: rest, _ =>
      simp only [List.foldl]
      have : ∀ (ys : List Int) (s : List (Oak.Reduce.Partial Int)), s ≠ [] → ys.foldl (Oak.Reduce.push (fadd p)) s ≠ [] := by
        intro ys
        induction ys with
        | nil => intro s hs; simpa using hs
        | cons y ys ih => intro s hs; simp only [List.foldl]; exact ih _ (Oak.Reduce.collapse_ne_nil _ _ (List.cons_ne_nil _ _))
      exact this rest _ (Oak.Reduce.collapse_ne_nil _ _ (List.cons_ne_nil _ _))
  have hbelow : AllBelow (bitlen xs.length) (xs.foldl (Oak.Reduce.push (fadd p)) []) :=
    levels_below (bitlen xs.length) xs.length (bitlen_upper _) _ _ hl (by rw [hleaves]; simp [leavesSum])
  obtain ⟨g, hg, hgex, hgmass, hdepth⟩ :=
    finish_depth p (bitlen xs.length) _ gs hne hgs (levels_finishing _ _ hl) hasc hbelow
  refine ⟨g, ?_, ?_, ?_, hdepth⟩
  · simp only [Oak.Reduce.tree]
    rw [hg]
  · rw [hgex, hex]; simp [exactSum]
  · rw [hgmass, hmass]; simp [massSum]

/-- **The tree's error bound at logarithmic depth.** Where `chain_error`
bounds the chain over `n + 1` leaves at depth `n`, the tree over `n` leaves
is bounded at depth `bitlen n`:
`2^(p·bitlen n) · |tree − Σxᵢ| ≤ B p (bitlen n) · Σ|xᵢ|`, that is
`|tree − Σxᵢ| ≤ ((1 + u)^(⌊log₂ n⌋ + 1) − 1) · Σ|xᵢ|`. -/
theorem tree_error_log (p : Nat) (z : Int) (xs : List Int) (h : xs ≠ []) :
    2 ^ (p * bitlen xs.length) * (Oak.Reduce.tree (fadd p) z xs - xs.sum).natAbs
      ≤ B p (bitlen xs.length) * (xs.map Int.natAbs).sum := by
  obtain ⟨g, hg, hex, hmass, hdepth⟩ := tree_depth_log p z xs h
  rw [hg, ← hex, ← hmass]
  exact lift_bound p g _ hdepth

end Oak.Floats
