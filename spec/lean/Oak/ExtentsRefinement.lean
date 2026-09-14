import Oak.Extents

/-! # Compiler correspondence for the extent-fact discharge

`typechecker/extents.go` decides whether an element access is in range from
the live extent facts (`indexUnder`, called by `recordIndexProof`), and
`Oak.Extents` states the laws each rule cites. This module transliterates
`indexUnder` — the fact kinds it consults, the index shapes the
recognizers read, and the decision itself — and proves it sound: whenever
the transliterated decision says `true`, the index value is below the
container's length in every environment where the live facts hold.

The correspondence is scoped to the discharge: the extraction of facts from
conditions, declarations, and loops (`factsFromCondition`,
`declarationFacts`, `loopConditionFacts`) and the flow-sensitive kills stay
transliterations whose laws `Oak.Extents` states individually
(`guard_without_wrap`, `bound_through_upper`, `kill_is_conservative`, …).
The Go decision is maintained as a line-for-line transliteration of
`indexUnder` below; `docs/spec/50-borrowing.md` names both. Go's `int64`
bounds and offsets are the non-negative values the recognizers admit
(`constantIndex` refuses negatives), modeled as `Nat`; dead facts are
filtered before the decision, as every Go loop skips them. -/

namespace Oak.ExtentsRefinement

/-- The live facts `indexUnder` consults, as the checker stores them
    (`extentFact`): the container, the other binding, the literal bound,
    and the offset of an index bound. -/
inductive Fact where
  /-- `factMinLen`: `bound ≤ len container`. -/
  | minLen (container : String) (bound : Nat)
  /-- `factIndexBound`: `other + offset < len container`. -/
  | indexBound (container other : String) (offset : Nat)
  /-- `factSameLen`: `len container = len other`. -/
  | sameLen (container other : String)
  /-- `factIndexLit`: `other < bound`. -/
  | indexLit (other : String) (bound : Nat)
  /-- `factLowerLit`: `bound ≤ other`. -/
  | lowerLit (other : String) (bound : Nat)
  /-- `factDivIndex`: `other < len container / bound`. -/
  | divIndex (container other : String) (bound : Nat)
  deriving DecidableEq, Repr

/-- An environment: the bindings' values and the containers' lengths at the
    access. -/
structure Env where
  value : String → Nat
  len : String → Nat

/-- What a fact claims of an environment. -/
def Fact.holds (env : Env) : Fact → Prop
  | .minLen c k => k ≤ env.len c
  | .indexBound c o off => env.value o + off < env.len c
  | .sameLen c o => env.len c = env.len o
  | .indexLit o k => env.value o < k
  | .lowerLit o k => k ≤ env.value o
  | .divIndex c o k => env.value o < env.len c / k

/-- The index shapes the recognizers read, in the order `indexUnder` tries
    them: a refinement construction (`refinedBelow`: its value `v` is
    below the predicate's bound, or the construction trapped), a masked
    expression (`maskedIndex`), `i * k + j` (`scaledIndex`),
    `i * k + j * m + c` (`scaledIndex2`), `i - k` (`minusIndex`), a
    constant (`constantIndex`), and `i + j` (`offsetIndex`). -/
inductive Shape where
  | refined (v bound : Nat)
  | masked (x mask : Nat)
  | scaled (i : String) (k j : Nat)
  | scaled2 (i : String) (k : Nat) (j : String) (m c : Nat)
  | minus (i : String) (k : Nat)
  | const (c : Nat)
  | offset (i : String) (j : Nat)

/-- The index's value. -/
def Shape.value (env : Env) : Shape → Nat
  | .refined v _ => v
  | .masked x m => x &&& m
  | .scaled i k j => env.value i * k + j
  | .scaled2 i k j m c => env.value i * k + env.value j * m + c
  | .minus i k => env.value i - k
  | .const c => c
  | .offset i j => env.value i + j

/-- What the shape's own construction guarantees: a refinement's value is
    below its bound (the guard trapped otherwise). -/
def Shape.assumption : Shape → Prop
  | .refined v b => v < b
  | _ => True

/-- Transliteration of `lengthAtLeast`: the container's declared static
    extent (an owned array `[N]T`), or a live min-length fact, is at least
    `n`. -/
def lengthAtLeast (facts : List Fact) (name : String) (static : Option Nat) (n : Nat) : Bool :=
  (match static with | some N => decide (n ≤ N) | none => false) ||
    facts.any fun f => match f with
      | .minLen c k => decide (c = name ∧ n ≤ k)
      | _ => false

/-- Transliteration of `literalUpper`: the smallest live literal bound on a
    binding. -/
def literalUpper (facts : List Fact) (binding : String) : Option Nat :=
  facts.foldl (fun acc f => match f with
    | .indexLit o k => if o = binding then (match acc with | some b => some (min b k) | none => some k) else acc
    | _ => acc) none

/-- Transliteration of `literalLower`: the largest live literal lower bound. -/
def literalLower (facts : List Fact) (binding : String) : Option Nat :=
  facts.foldl (fun acc f => match f with
    | .lowerLit o k => if o = binding then (match acc with | some b => some (max b k) | none => some k) else acc
    | _ => acc) none

/-- Transliteration of `indexUnder`. -/
def indexUnder (facts : List Fact) (name : String) (static : Option Nat) : Shape → Bool
  | .refined _ bound => lengthAtLeast facts name static bound
  | .masked _ mask => lengthAtLeast facts name static (mask + 1)
  | .scaled i k j =>
    (match literalUpper facts i with
      | some u => decide (1 ≤ u) && lengthAtLeast facts name static ((u - 1) * k + j + 1)
      | none => false) ||
    facts.any fun f => match f with
      | .divIndex c o b => decide (o = i ∧ c = name ∧ b = k ∧ j < k)
      | _ => false
  | .scaled2 i k j m c =>
    match literalUpper facts i, literalUpper facts j with
    | some u₁, some u₂ =>
      decide (1 ≤ u₁) && decide (1 ≤ u₂) && lengthAtLeast facts name static ((u₁ - 1) * k + (u₂ - 1) * m + c + 1)
    | _, _ => false
  | .minus i k =>
    match literalLower facts i with
    | some l =>
      decide (k ≤ l) &&
        ((match literalUpper facts i with
          | some u => decide (k ≤ u) && lengthAtLeast facts name static (u - k)
          | none => false) ||
         facts.any fun f => match f with
          | .indexBound c o off => decide (o = i ∧ off = 0 ∧ c = name)
          | _ => false)
    | none => false
  | .const c =>
    (match static with | some N => decide (c < N) | none => false) ||
    facts.any fun f => match f with
      | .minLen cont k => decide (cont = name ∧ c < k)
      | _ => false
  | .offset i j =>
    (match literalUpper facts i with
      | some u => lengthAtLeast facts name static (u + j)
      | none => false) ||
    (facts.any fun f => match f with
      | .divIndex c o k => decide (o = i ∧ c = name ∧ j < k)
      | _ => false) ||
    facts.any fun f => match f with
      | .indexBound c o off =>
        decide (o = i ∧ j ≤ off) &&
          (decide (c = name) || facts.any fun g => match g with
            | .sameLen a b => decide ((a = c ∧ b = name) ∨ (a = name ∧ b = c))
            | _ => false)
      | _ => false

/-! ## Soundness -/

/-- Every fact in a list holds. -/
def Holds (env : Env) (facts : List Fact) : Prop := ∀ f ∈ facts, f.holds env

theorem lengthAtLeast_sound {facts : List Fact} {name : String} {static : Option Nat} {n : Nat}
    {env : Env} (hfacts : Holds env facts) (hstatic : ∀ N, static = some N → env.len name = N)
    (h : lengthAtLeast facts name static n = true) : n ≤ env.len name := by
  unfold lengthAtLeast at h
  rw [Bool.or_eq_true] at h
  rcases h with h | h
  · cases static with
    | none => simp at h
    | some N =>
      simp at h
      rw [hstatic N rfl]
      exact h
  · rw [List.any_eq_true] at h
    obtain ⟨f, hf, hmatch⟩ := h
    cases f with
    | minLen c k =>
      simp at hmatch
      obtain ⟨rfl, hk⟩ := hmatch
      have := hfacts _ hf
      simp [Fact.holds] at this
      omega
    | indexBound => simp at hmatch
    | sameLen => simp at hmatch
    | indexLit => simp at hmatch
    | lowerLit => simp at hmatch
    | divIndex => simp at hmatch

/-- A bound `literalUpper` returns is a live `indexLit` fact's bound (or the
    minimum of several), so the binding is below it. -/
theorem literalUpper_sound {facts : List Fact} {binding : String} {u : Nat} {env : Env}
    (hfacts : Holds env facts) (h : literalUpper facts binding = some u) : env.value binding < u := by
  unfold literalUpper at h
  -- Generalize the accumulator: an accumulator that is `some b` with the
  -- binding below `b` stays so, and every fold step only lowers it.
  suffices key : ∀ (fs : List Fact) (acc : Option Nat),
      (∀ f ∈ fs, f.holds env) → (∀ b, acc = some b → env.value binding < b) →
      ∀ r, fs.foldl (fun acc f => match f with
        | .indexLit o k => if o = binding then (match acc with | some b => some (min b k) | none => some k) else acc
        | _ => acc) acc = some r → env.value binding < r by
    exact key facts none hfacts (by intro b hb; cases hb) u h
  intro fs
  induction fs with
  | nil => intro acc _ hacc r hr; exact hacc r hr
  | cons f rest ih =>
    intro acc hfs hacc r hr
    simp only [List.foldl_cons] at hr
    have hf := hfs f (List.mem_cons_self ..)
    have hrest : ∀ g ∈ rest, g.holds env := fun g hg => hfs g (List.mem_cons_of_mem _ hg)
    refine ih _ hrest ?_ r hr
    intro b hb
    cases f with
    | indexLit o k =>
      simp only at hb
      by_cases ho : o = binding
      · subst ho
        simp [Fact.holds] at hf
        simp only [ite_true] at hb
        cases acc with
        | none => simp at hb; omega
        | some b' =>
          simp at hb
          have := hacc b' rfl
          omega
      · simp [ho] at hb; exact hacc b hb
    | minLen => exact hacc b hb
    | indexBound => exact hacc b hb
    | sameLen => exact hacc b hb
    | lowerLit => exact hacc b hb
    | divIndex => exact hacc b hb

/-- A bound `literalLower` returns is a live `lowerLit` fact's bound (or the
    maximum of several), so it is at most the binding. -/
theorem literalLower_sound {facts : List Fact} {binding : String} {l : Nat} {env : Env}
    (hfacts : Holds env facts) (h : literalLower facts binding = some l) : l ≤ env.value binding := by
  unfold literalLower at h
  suffices key : ∀ (fs : List Fact) (acc : Option Nat),
      (∀ f ∈ fs, f.holds env) → (∀ b, acc = some b → b ≤ env.value binding) →
      ∀ r, fs.foldl (fun acc f => match f with
        | .lowerLit o k => if o = binding then (match acc with | some b => some (max b k) | none => some k) else acc
        | _ => acc) acc = some r → r ≤ env.value binding by
    exact key facts none hfacts (by intro b hb; cases hb) l h
  intro fs
  induction fs with
  | nil => intro acc _ hacc r hr; exact hacc r hr
  | cons f rest ih =>
    intro acc hfs hacc r hr
    simp only [List.foldl_cons] at hr
    have hf := hfs f (List.mem_cons_self ..)
    have hrest : ∀ g ∈ rest, g.holds env := fun g hg => hfs g (List.mem_cons_of_mem _ hg)
    refine ih _ hrest ?_ r hr
    intro b hb
    cases f with
    | lowerLit o k =>
      simp only at hb
      by_cases ho : o = binding
      · subst ho
        simp [Fact.holds] at hf
        simp only [ite_true] at hb
        cases acc with
        | none => simp at hb; omega
        | some b' =>
          simp at hb
          have := hacc b' rfl
          omega
      · simp [ho] at hb; exact hacc b hb
    | minLen => exact hacc b hb
    | indexBound => exact hacc b hb
    | sameLen => exact hacc b hb
    | indexLit => exact hacc b hb
    | divIndex => exact hacc b hb

/-- **The discharge is sound.** When the transliterated `indexUnder` accepts
    an access, its index is below the container's length in every
    environment where the live facts hold and the static extent is the
    length — each shape by the law its Go rule cites. -/
theorem indexUnder_sound (facts : List Fact) (name : String) (static : Option Nat) (s : Shape)
    (env : Env) (hfacts : Holds env facts) (hstatic : ∀ N, static = some N → env.len name = N)
    (hshape : s.assumption) (h : indexUnder facts name static s = true) :
    s.value env < env.len name := by
  cases s with
  | refined v bound =>
    simp only [Shape.assumption] at hshape
    simp only [indexUnder] at h
    have := lengthAtLeast_sound hfacts hstatic h
    simp only [Shape.value]; omega
  | masked x mask =>
    simp only [indexUnder] at h
    have := lengthAtLeast_sound hfacts hstatic h
    simp only [Shape.value]
    exact Oak.Extents.masked_under_length x mask _ (by omega)
  | scaled i k j =>
    simp only [indexUnder, Shape.value] at h ⊢
    rw [Bool.or_eq_true] at h
    rcases h with h | h
    · cases hu : literalUpper facts i with
      | none => simp [hu] at h
      | some u =>
        simp only [hu, Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨_, hlen⟩ := h
        have hi := literalUpper_sound hfacts hu
        have hl := lengthAtLeast_sound hfacts hstatic hlen
        exact Oak.Extents.scaled_under_bound _ k j u _ hi (by omega)
    · rw [List.any_eq_true] at h
      obtain ⟨f, hf, hmatch⟩ := h
      cases f with
      | divIndex c o b =>
        simp at hmatch
        obtain ⟨rfl, rfl, rfl, hj⟩ := hmatch
        have := hfacts _ hf
        simp [Fact.holds] at this
        exact Oak.Extents.div_bound_scaled _ j _ _ this hj
      | minLen => simp at hmatch
      | indexBound => simp at hmatch
      | sameLen => simp at hmatch
      | indexLit => simp at hmatch
      | lowerLit => simp at hmatch
  | scaled2 i k j m c =>
    simp only [indexUnder, Shape.value] at h ⊢
    cases hu₁ : literalUpper facts i with
    | none => simp [hu₁] at h
    | some u₁ =>
      cases hu₂ : literalUpper facts j with
      | none => simp [hu₁, hu₂] at h
      | some u₂ =>
        simp only [hu₁, hu₂, Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨⟨_, _⟩, hlen⟩ := h
        have hi := literalUpper_sound hfacts hu₁
        have hj := literalUpper_sound hfacts hu₂
        have hl := lengthAtLeast_sound hfacts hstatic hlen
        exact Oak.Extents.scaled2_under_bound _ _ k m c u₁ u₂ _ hi hj (by omega)
  | minus i k =>
    simp only [indexUnder, Shape.value] at h ⊢
    cases hl : literalLower facts i with
    | none => simp [hl] at h
    | some l =>
      simp only [hl, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨hkl, h⟩ := h
      have hlow := literalLower_sound hfacts hl
      rw [Bool.or_eq_true] at h
      rcases h with h | h
      · cases hu : literalUpper facts i with
        | none => simp [hu] at h
        | some u =>
          simp only [hu, Bool.and_eq_true, decide_eq_true_eq] at h
          obtain ⟨hku, hlen⟩ := h
          have hi := literalUpper_sound hfacts hu
          have hlen' := lengthAtLeast_sound hfacts hstatic hlen
          exact Oak.Extents.subtraction_under_bounds _ k l u _ hlow hkl hi hlen'
      · rw [List.any_eq_true] at h
        obtain ⟨f, hf, hmatch⟩ := h
        cases f with
        | indexBound cont o off =>
          simp at hmatch
          obtain ⟨rfl, rfl, rfl⟩ := hmatch
          have := hfacts _ hf
          simp [Fact.holds] at this
          exact Oak.Extents.subtraction_under_length _ k _ (by omega) this
        | minLen => simp at hmatch
        | sameLen => simp at hmatch
        | indexLit => simp at hmatch
        | lowerLit => simp at hmatch
        | divIndex => simp at hmatch
  | const c =>
    simp only [indexUnder, Shape.value] at h ⊢
    rw [Bool.or_eq_true] at h
    rcases h with h | h
    · cases static with
      | none => simp at h
      | some N =>
        simp at h
        rw [hstatic N rfl]
        exact h
    · rw [List.any_eq_true] at h
      obtain ⟨f, hf, hmatch⟩ := h
      cases f with
      | minLen cont k =>
        simp at hmatch
        obtain ⟨rfl, hk⟩ := hmatch
        have := hfacts _ hf
        simp [Fact.holds] at this
        exact Oak.Extents.constant_under_min_length c k _ this hk
      | indexBound => simp at hmatch
      | sameLen => simp at hmatch
      | indexLit => simp at hmatch
      | lowerLit => simp at hmatch
      | divIndex => simp at hmatch
  | offset i j =>
    simp only [indexUnder, Shape.value] at h ⊢
    rw [Bool.or_eq_true, Bool.or_eq_true] at h
    rcases h with (h | h) | h
    · cases hu : literalUpper facts i with
      | none => simp [hu] at h
      | some u =>
        simp only [hu] at h
        have hi := literalUpper_sound hfacts hu
        have hl := lengthAtLeast_sound hfacts hstatic h
        exact Oak.Extents.literal_bound_under_length _ u j _ hi hl
    · rw [List.any_eq_true] at h
      obtain ⟨f, hf, hmatch⟩ := h
      cases f with
      | divIndex cont o k =>
        simp at hmatch
        obtain ⟨rfl, rfl, hj⟩ := hmatch
        have := hfacts _ hf
        simp [Fact.holds] at this
        exact Oak.Extents.div_bound_under_length _ j _ k this hj
      | minLen => simp at hmatch
      | indexBound => simp at hmatch
      | sameLen => simp at hmatch
      | indexLit => simp at hmatch
      | lowerLit => simp at hmatch
    · rw [List.any_eq_true] at h
      obtain ⟨f, hf, hmatch⟩ := h
      cases f with
      | indexBound cont o off =>
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hmatch
        obtain ⟨⟨rfl, hoff⟩, hcont⟩ := hmatch
        have hb := hfacts _ hf
        simp [Fact.holds] at hb
        rw [Bool.or_eq_true] at hcont
        rcases hcont with hcont | hcont
        · simp at hcont
          subst hcont
          exact Oak.Extents.offset_under_bound _ off j _ hb hoff
        · rw [List.any_eq_true] at hcont
          obtain ⟨g, hg, gmatch⟩ := hcont
          cases g with
          | sameLen a b =>
            simp at gmatch
            have hs := hfacts _ hg
            simp [Fact.holds] at hs
            rcases gmatch with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · have := Oak.Extents.offset_under_bound _ off j _ hb hoff
              exact Oak.Extents.bound_transfers _ _ _ this hs
            · have := Oak.Extents.offset_under_bound _ off j _ hb hoff
              exact Oak.Extents.bound_transfers _ _ _ this hs.symm
          | minLen => simp at gmatch
          | indexBound => simp at gmatch
          | indexLit => simp at gmatch
          | lowerLit => simp at gmatch
          | divIndex => simp at gmatch
      | minLen => simp at hmatch
      | sameLen => simp at hmatch
      | indexLit => simp at hmatch
      | lowerLit => simp at hmatch
      | divIndex => simp at hmatch


/-! ## The decisions rendered by the Go checker

Each line is one index site of `typechecker/extents_refinement_test.go`:
the live facts, the container's static extent, and the shape the
recognizers read, rendered by the Go checker with its decision and checked
here by `decide`. The test fails when a rendering is missing, `lake build`
when a rendering is wrong. -/

example : indexUnder [] "v" (some 8) (Shape.const 3) = true := by decide
example : indexUnder [] "v" (some 8) (Shape.masked 0 7) = true := by decide
example : indexUnder [Fact.indexLit "i" 6] "v" (some 8) (Shape.offset "i" 2) = true := by decide
example : indexUnder [Fact.indexLit "i" 4] "v" (some 8) (Shape.scaled "i" 2 1) = true := by decide
example : indexUnder [Fact.minLen "v" 4, Fact.indexLit "i" 4] "v" none (Shape.offset "i" 0) = true := by decide
example : indexUnder [Fact.indexLit "i" 9] "v" (some 8) (Shape.offset "i" 0) = false := by decide

end Oak.ExtentsRefinement
