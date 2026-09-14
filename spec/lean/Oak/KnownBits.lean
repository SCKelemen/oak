/-!
# Known bits in the bit-level decider

Model for `asm/floats_ops.go` (`knownBits`, `floatTerm`) and its twin in the
theorem lowering written in Oak (`prove/solver/lower.oak`, `kb_of_new`,
`t_float`). A floating-point operation over operands whose every bit is
fixed by the term's structure folds, at construction, to the IEEE value of
the constants — the fold both lowerings must make on the same terms, so
the solver written in Oak and the Go decider blast the same applications.

A *known-bits* pair `(value, known)` approximates a bit vector: on every
position `known` marks, the vector's bit is `value`'s. The transfer
functions below are the ones the analysis runs — a constant; `and`, `or`,
`xor`; a shift by a constant count; the width adapters; a conditional under
a known selector bit, else the bits its arms agree on; a comparison's zero
upper bits — and each is proved sound: if the operands are approximated,
so is the result. A vector approximated with every bit known *is* the
value (`exact`), so the fold evaluates the operation on the value the
diagram would have found on every path (`fold_app`).
-/

namespace Oak.KnownBits

/-- `x` agrees with `value` on every bit `known` marks. -/
def Approx {w : Nat} (value known : BitVec w) (x : BitVec w) : Prop :=
  ∀ i, known.getLsbD i = true → x.getLsbD i = value.getLsbD i

/-- A constant knows every bit. -/
theorem const_sound {w : Nat} (c : BitVec w) : Approx c (BitVec.allOnes w) c := by
  intro i _; rfl

/-- Every bit known pins the vector down: the fold's value is the vector. -/
theorem exact {w : Nat} (value x : BitVec w) (h : Approx value (BitVec.allOnes w) x) : x = value := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hiw
  exact h i (by simp [hiw])

/-! ### The transfer functions -/

/-- `and`: a bit is known where both are, or where either is a known zero. -/
def andKnown {w : Nat} (va ka vb kb : BitVec w) : BitVec w :=
  (ka &&& kb) ||| (ka &&& ~~~va) ||| (kb &&& ~~~vb)

theorem and_sound {w : Nat} (va ka vb kb x y : BitVec w)
    (hx : Approx va ka x) (hy : Approx vb kb y) :
    Approx (va &&& vb &&& andKnown va ka vb kb) (andKnown va ka vb kb) (x &&& y) := by
  intro i hi
  simp only [andKnown, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not] at hi ⊢
  have hx' := hx i; have hy' := hy i
  revert hi hx' hy'
  cases x.getLsbD i <;> cases y.getLsbD i <;> cases va.getLsbD i <;> cases vb.getLsbD i <;>
    cases ka.getLsbD i <;> cases kb.getLsbD i <;> simp

/-- `or`: a bit is known where both are, or where either is a known one. -/
def orKnown {w : Nat} (va ka vb kb : BitVec w) : BitVec w :=
  (ka &&& kb) ||| (ka &&& va) ||| (kb &&& vb)

theorem or_sound {w : Nat} (va ka vb kb x y : BitVec w)
    (hx : Approx va ka x) (hy : Approx vb kb y) :
    Approx ((va ||| vb) &&& orKnown va ka vb kb) (orKnown va ka vb kb) (x ||| y) := by
  intro i hi
  simp only [orKnown, BitVec.getLsbD_or, BitVec.getLsbD_and] at hi ⊢
  have hx' := hx i; have hy' := hy i
  revert hi hx' hy'
  cases x.getLsbD i <;> cases y.getLsbD i <;> cases va.getLsbD i <;> cases vb.getLsbD i <;>
    cases ka.getLsbD i <;> cases kb.getLsbD i <;> simp

/-- `xor`: a bit is known where both are. -/
theorem xor_sound {w : Nat} (va ka vb kb x y : BitVec w)
    (hx : Approx va ka x) (hy : Approx vb kb y) :
    Approx ((va ^^^ vb) &&& (ka &&& kb)) (ka &&& kb) (x ^^^ y) := by
  intro i hi
  simp only [BitVec.getLsbD_xor, BitVec.getLsbD_and] at hi ⊢
  have hx' := hx i; have hy' := hy i
  revert hi hx' hy'
  cases x.getLsbD i <;> cases y.getLsbD i <;> cases va.getLsbD i <;> cases vb.getLsbD i <;>
    cases ka.getLsbD i <;> cases kb.getLsbD i <;> simp

/-- The low `n` bits, ones: what a left shift by `n` shifts in. -/
def lowOnes (w n : Nat) : BitVec w := ~~~(BitVec.allOnes w <<< n)

/-- The high `n` bits, ones: what a right shift by `n` shifts in. -/
def highOnes (w n : Nat) : BitVec w := ~~~(BitVec.allOnes w >>> n)

/-- A left shift by a constant: the bits shifted in are known zero. -/
theorem shl_sound {w : Nat} (va ka x : BitVec w) (n : Nat) (hx : Approx va ka x) :
    Approx (va <<< n) ((ka <<< n) ||| lowOnes w n) (x <<< n) := by
  intro i hi
  simp only [lowOnes, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_not,
    BitVec.getLsbD_allOnes] at hi ⊢
  by_cases hiw : i < w
  · by_cases hin : i < n
    · simp [hiw, hin]
    · have hlow : i - n < w := by omega
      simp only [hiw, hin, hlow, decide_true, decide_false, Bool.not_false, Bool.not_true, Bool.true_and,
        Bool.and_true, Bool.and_false, Bool.or_false] at hi ⊢
      exact hx (i - n) hi
  · simp [hiw]

/-- A logical right shift by a constant: the bits shifted in are known zero. -/
theorem shr_sound {w : Nat} (va ka x : BitVec w) (n : Nat) (hx : Approx va ka x) :
    Approx (va >>> n) ((ka >>> n) ||| highOnes w n) (x >>> n) := by
  intro i hi
  simp only [highOnes, BitVec.getLsbD_or, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_not,
    BitVec.getLsbD_allOnes] at hi ⊢
  by_cases hin : n + i < w
  · have hiw : i < w := by omega
    simp only [hiw, hin, decide_true, Bool.not_true, Bool.and_false, Bool.or_false] at hi
    exact hx (n + i) hi
  · rw [BitVec.getLsbD_of_ge x (n + i) (by omega), BitVec.getLsbD_of_ge va (n + i) (by omega)]

/-- An arithmetic right shift by a constant: the bits shifted in are the
sign, known when the sign is. -/
theorem sar_sound {w : Nat} (va ka x : BitVec w) (n : Nat) (hx : Approx va ka x) :
    Approx ((va >>> n) ||| (if ka.getLsbD (w - 1) && va.getLsbD (w - 1) then highOnes w n else 0#w))
      ((ka >>> n) ||| (if ka.getLsbD (w - 1) then highOnes w n else 0#w))
      (x.sshiftRight n) := by
  intro i hi
  by_cases hiw : w ≤ i
  · -- Past the width every bit is zero.
    have h1 := BitVec.getLsbD_of_ge (x.sshiftRight n) i hiw
    have h2 := BitVec.getLsbD_of_ge ((va >>> n) ||| (if ka.getLsbD (w - 1) && va.getLsbD (w - 1) then highOnes w n else 0#w)) i hiw
    rw [h1, h2]
  · have hiw' : i < w := by omega
    by_cases hin : n + i < w
    · -- Inside the shifted bits: the operand's bit.
      have hk : ka.getLsbD (n + i) = true := by
        simp only [highOnes, BitVec.getLsbD_or, BitVec.getLsbD_ushiftRight] at hi
        cases hka : ka.getLsbD (n + i)
        · rw [hka] at hi
          simp only [Bool.false_or] at hi
          split at hi
          · simp only [BitVec.getLsbD_not, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_allOnes, hin,
              decide_true, Bool.not_true, Bool.and_false] at hi
            exact absurd hi Bool.false_ne_true
          · simp only [BitVec.getLsbD_zero] at hi
            exact absurd hi Bool.false_ne_true
        · rfl
      rw [BitVec.getLsbD_sshiftRight, BitVec.getLsbD_or, BitVec.getLsbD_ushiftRight]
      simp only [hiw, decide_false, Bool.not_false, Bool.true_and, hin, if_true]
      rw [hx (n + i) hk]
      have hva : va.getLsbD (n + i) = va.getLsbD (n + i) := rfl
      cases hv : va.getLsbD (n + i)
      · simp only [Bool.false_or]
        split
        · simp only [highOnes, BitVec.getLsbD_not, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_allOnes, hin,
            decide_true, Bool.not_true, Bool.and_false]
        · simp only [BitVec.getLsbD_zero]
      · simp only [Bool.true_or]
    · -- The fill: the sign bit, known when the sign is.
      have hva : va.getLsbD (n + i) = false := BitVec.getLsbD_of_ge va (n + i) (by omega)
      have hka : ka.getLsbD (n + i) = false := BitVec.getLsbD_of_ge ka (n + i) (by omega)
      have hsign : ka.getLsbD (w - 1) = true := by
        simp only [highOnes, BitVec.getLsbD_or, BitVec.getLsbD_ushiftRight, hka, Bool.false_or] at hi
        split at hi
        · assumption
        · simp only [BitVec.getLsbD_zero] at hi
          exact absurd hi Bool.false_ne_true
      have hm : x.msb = va.getLsbD (w - 1) := by
        rw [BitVec.msb_eq_getLsbD_last]
        exact hx (w - 1) hsign
      rw [BitVec.getLsbD_sshiftRight, BitVec.getLsbD_or, BitVec.getLsbD_ushiftRight, hva]
      simp only [hiw, decide_false, Bool.not_false, Bool.true_and, hin, if_false, Bool.false_or, hm, hsign,
        Bool.true_and]
      cases va.getLsbD (w - 1)
      · simp
      · simp [highOnes, hin, hiw']

/-- A conditional under a known selector bit is its arm. -/
theorem ite_known_sound {w v : Nat} (va ka vb kb : BitVec w) (vc kc : BitVec v) (x y : BitVec w) (c : BitVec v)
    (hx : Approx va ka x) (hy : Approx vb kb y) (hc : Approx vc kc c) (hk : kc.getLsbD 0 = true) :
    Approx (if vc.getLsbD 0 then va else vb) (if vc.getLsbD 0 then ka else kb)
      (if c.getLsbD 0 then x else y) := by
  rw [hc 0 hk]
  cases vc.getLsbD 0 <;> simp_all

/-- A conditional under an unknown selector knows the bits its arms agree on. -/
theorem ite_agree_sound {w : Nat} (va ka vb kb x y : BitVec w) (c : Bool)
    (hx : Approx va ka x) (hy : Approx vb kb y) :
    Approx (va &&& (ka &&& kb &&& ~~~(va ^^^ vb))) (ka &&& kb &&& ~~~(va ^^^ vb)) (if c then x else y) := by
  intro i hi
  have hsel : (if c then x else y).getLsbD i = if c then x.getLsbD i else y.getLsbD i := by
    cases c <;> simp
  rw [hsel]
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_xor] at hi ⊢
  have hx' := hx i; have hy' := hy i
  revert hi hx' hy'
  cases c <;> cases x.getLsbD i <;> cases y.getLsbD i <;> cases va.getLsbD i <;> cases vb.getLsbD i <;>
    cases ka.getLsbD i <;> cases kb.getLsbD i <;> simp

/-- A comparison's bits above the first are zero (the blaster sets them so). -/
theorem cmp_sound {w : Nat} (x : BitVec w) (h : ∀ i, 1 ≤ i → x.getLsbD i = false) :
    Approx 0#w (~~~(1#w)) x := by
  intro i hi
  simp only [BitVec.getLsbD_not, BitVec.getLsbD_one, BitVec.getLsbD_zero] at hi ⊢
  by_cases hi0 : i = 0
  · simp_all
  · exact h i (by omega)

/-- The width adapters: a zero-extension knows its upper bits zero, a
truncation keeps what it keeps (`setWidth` is both). -/
theorem setWidth_sound {w v : Nat} (va ka x : BitVec w) (hx : Approx va ka x) :
    Approx (va.setWidth v) (ka.setWidth v ||| ~~~((BitVec.allOnes w).setWidth v)) (x.setWidth v) := by
  intro i hi
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_setWidth, BitVec.getLsbD_not, BitVec.getLsbD_allOnes] at hi ⊢
  by_cases hiv : i < v
  · by_cases hiw : i < w
    · simp only [hiv, hiw, decide_true, Bool.true_and, Bool.and_true, Bool.not_true, Bool.and_false,
        Bool.or_false] at hi
      rw [hx i hi]
    · rw [BitVec.getLsbD_of_ge x i (by omega), BitVec.getLsbD_of_ge va i (by omega)]
  · simp_all

/-! ### The fold -/

/-- An operation over operands whose every bit is known is the operation on
the values — under any interpretation, the IEEE one included: what
`floatTerm` and `t_float` substitute for the application. -/

theorem fold_app1 {w : Nat} {α : Type} (op : BitVec w → α) (v x : BitVec w)
    (h : Approx v (BitVec.allOnes w) x) : op x = op v := by
  rw [exact v x h]

theorem fold_app2 {w u : Nat} {α : Type} (op : BitVec w → BitVec u → α) (v x : BitVec w) (v' y : BitVec u)
    (h : Approx v (BitVec.allOnes w) x) (h' : Approx v' (BitVec.allOnes u) y) : op x y = op v v' := by
  rw [exact v x h, exact v' y h']

theorem fold_app3 {w u t : Nat} {α : Type} (op : BitVec w → BitVec u → BitVec t → α)
    (v x : BitVec w) (v' y : BitVec u) (v'' z : BitVec t)
    (h : Approx v (BitVec.allOnes w) x) (h' : Approx v' (BitVec.allOnes u) y) (h'' : Approx v'' (BitVec.allOnes t) z) :
    op x y z = op v v' v'' := by
  rw [exact v x h, exact v' y h', exact v'' z h'']

end Oak.KnownBits
