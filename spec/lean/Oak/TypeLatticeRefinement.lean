import Oak.TypeLattice

namespace Oak.TypeLatticeRefinement

open Oak.TypeLattice

/-! # Compiler correspondence for the type lattice

`typechecker/lattice.go` decides `IsSubtype` by normalizing both sides to
disjunctive normal form over opaque nominal atoms and checking that every
left clause is implied by some right clause. This module transliterates that
decision procedure (`clauseImplies`, `decide` = `IsSubtype`, `dnfOf` =
`latticeDNFOf`) and proves it is exactly semantic containment in the free
distributive lattice of `Oak.TypeLattice`:

* **sound** — an accepted pair is contained under every valuation of the
  atoms as semantic sets;
* **complete** — a rejected pair has a concrete countermodel;
* **normalization-faithful** — DNF conversion preserves denotation, so the
  type-level procedure decides the type-level ordering.

The Go implementation folds n-ary unions/intersections; the model uses their
binary form, which agrees by associativity of join/meet. -/

variable {α : Type} [DecidableEq α]

/-- A clause is a conjunction of atoms; a DNF is a disjunction of clauses
    (mirrors `latticeClause` / `latticeDNF`). -/
abbrev Clause (α : Type) := List α
abbrev DNF (α : Type) := List (Clause α)

/-- Transliteration of `clauseImplies`: conjunction `left` implies `right`
    exactly when every atom `right` requires is required by `left`. -/
def clauseImplies (left right : Clause α) : Bool :=
  right.all fun a => left.contains a

/-- Transliteration of `IsSubtype`'s core loop: every left clause must be
    implied by some right clause. -/
def decide (d1 d2 : DNF α) : Bool :=
  d1.all fun c1 => d2.any fun c2 => clauseImplies c1 c2

/-- A clause denotes the meet of its atoms under a valuation. -/
def ClauseDenote (V : α → Ty X) (c : Clause α) : Ty X :=
  fun x => ∀ a ∈ c, V a x

/-- A DNF denotes the join of its clauses. -/
def DNFDenote (V : α → Ty X) (d : DNF α) : Ty X :=
  fun x => ∃ c ∈ d, ClauseDenote V c x

/-- **Soundness**: an accepted pair is semantically contained under every
    valuation. -/
theorem decide_sound {d1 d2 : DNF α} (h : decide d1 d2 = true)
    {X : Type} (V : α → Ty X) : DNFDenote V d1 ≤ₜ DNFDenote V d2 := by
  intro x hx
  obtain ⟨c1, hc1, hsat⟩ := hx
  have hany := List.all_eq_true.mp h c1 hc1
  obtain ⟨c2, hc2, himp⟩ := List.any_eq_true.mp hany
  refine ⟨c2, hc2, ?_⟩
  intro a ha
  have hcontains := List.all_eq_true.mp himp a ha
  exact hsat a (List.mem_of_elem_eq_true hcontains)

theorem exists_false_of_all_false {β : Type} {l : List β} {p : β → Bool}
    (h : l.all p = false) : ∃ x ∈ l, p x = false := by
  induction l with
  | nil => simp [List.all] at h
  | cons b rest ih =>
    cases hb : p b with
    | false => exact ⟨b, by simp, hb⟩
    | true =>
      have hrest : rest.all p = false := by
        simp only [List.all_cons, hb, Bool.true_and] at h
        exact h
      obtain ⟨x, hx, hpx⟩ := ih hrest
      exact ⟨x, by simp [hx], hpx⟩

/-- **Completeness**: a rejected pair has a countermodel — value the atoms by
    membership in the failing clause. -/
theorem decide_complete {d1 d2 : DNF α} (h : decide d1 d2 = false) :
    ∃ V : α → Ty Unit, ¬ (DNFDenote V d1 ≤ₜ DNFDenote V d2) := by
  unfold decide at h
  obtain ⟨c1, hc1, hfail⟩ := exists_false_of_all_false h
  refine ⟨fun a => fun _ => a ∈ c1, ?_⟩
  intro hle
  have hd1 : DNFDenote (fun a => fun _ => a ∈ c1) d1 () :=
    ⟨c1, hc1, fun a ha => ha⟩
  obtain ⟨c2, hc2, hsat⟩ := hle () hd1
  have himp : clauseImplies c1 c2 = true := by
    apply List.all_eq_true.mpr
    intro a ha
    exact List.elem_eq_true_of_mem (hsat a ha)
  have hany := List.any_eq_true.mpr ⟨c2, hc2, himp⟩
  rw [hfail] at hany
  exact Bool.noConfusion hany

/-- The lattice type syntax the procedure normalizes (binary form of the
    compiler's n-ary `UnionType`/`IntersectionType`). -/
inductive LatticeTy (α : Type) where
  | never
  | any
  | atom (a : α)
  | union (l r : LatticeTy α)
  | inter (l r : LatticeTy α)

/-- Denotation into the semantic lattice of `Oak.TypeLattice`. -/
def denote (V : α → Ty X) : LatticeTy α → Ty X
  | .never => bottom
  | .any => top
  | .atom a => V a
  | .union l r => join (denote V l) (denote V r)
  | .inter l r => meet (denote V l) (denote V r)

/-- Transliteration of `mergeClauses` (deduplicating conjunction merge). -/
def mergeClauses (left right : Clause α) : Clause α :=
  left ++ right.filter (fun a => !left.contains a)

/-- Transliteration of the intersection case of `latticeDNFOf`: the cartesian
    product of clause sets. -/
def productDNF (d1 d2 : DNF α) : DNF α :=
  d1.flatMap fun c1 => d2.map fun c2 => mergeClauses c1 c2

/-- Transliteration of `latticeDNFOf`. -/
def dnfOf : LatticeTy α → DNF α
  | .never => []
  | .any => [[]]
  | .atom a => [[a]]
  | .union l r => dnfOf l ++ dnfOf r
  | .inter l r => productDNF (dnfOf l) (dnfOf r)

theorem mem_mergeClauses {left right : Clause α} {a : α} :
    a ∈ mergeClauses left right ↔ a ∈ left ∨ a ∈ right := by
  simp only [mergeClauses, List.mem_append, List.mem_filter]
  constructor
  · rintro (h | ⟨h, _⟩)
    · exact Or.inl h
    · exact Or.inr h
  · rintro (h | h)
    · exact Or.inl h
    · by_cases hleft : a ∈ left
      · exact Or.inl hleft
      · refine Or.inr ⟨h, ?_⟩
        simp [List.contains_eq_mem, hleft]

theorem clauseDenote_merge {V : α → Ty X} {c1 c2 : Clause α} {x : X} :
    ClauseDenote V (mergeClauses c1 c2) x ↔
      ClauseDenote V c1 x ∧ ClauseDenote V c2 x := by
  constructor
  · intro h
    exact ⟨fun a ha => h a (mem_mergeClauses.mpr (Or.inl ha)),
           fun a ha => h a (mem_mergeClauses.mpr (Or.inr ha))⟩
  · intro ⟨h1, h2⟩ a ha
    cases mem_mergeClauses.mp ha with
    | inl h => exact h1 a h
    | inr h => exact h2 a h

theorem dnfDenote_product {V : α → Ty X} {d1 d2 : DNF α} {x : X} :
    DNFDenote V (productDNF d1 d2) x ↔
      DNFDenote V d1 x ∧ DNFDenote V d2 x := by
  constructor
  · intro ⟨c, hc, hsat⟩
    simp only [productDNF, List.mem_flatMap, List.mem_map] at hc
    obtain ⟨c1, hc1, c2, hc2, rfl⟩ := hc
    have := clauseDenote_merge.mp hsat
    exact ⟨⟨c1, hc1, this.1⟩, ⟨c2, hc2, this.2⟩⟩
  · intro ⟨⟨c1, hc1, h1⟩, ⟨c2, hc2, h2⟩⟩
    refine ⟨mergeClauses c1 c2, ?_, clauseDenote_merge.mpr ⟨h1, h2⟩⟩
    simp only [productDNF, List.mem_flatMap, List.mem_map]
    exact ⟨c1, hc1, c2, hc2, rfl⟩

/-- **Normalization preserves denotation**: the DNF the compiler computes
    denotes exactly the type it normalized. -/
theorem dnfOf_denotes (V : α → Ty X) (t : LatticeTy α) (x : X) :
    DNFDenote V (dnfOf t) x ↔ denote V t x := by
  induction t with
  | never => simp [dnfOf, DNFDenote, denote, bottom]
  | any =>
    simp [dnfOf, DNFDenote, denote, top]
    exact fun a ha => absurd ha (List.not_mem_nil)
  | atom a => simp [dnfOf, DNFDenote, ClauseDenote, denote]
  | union l r ihl ihr =>
    simp only [dnfOf, DNFDenote, denote, join, List.mem_append]
    constructor
    · rintro ⟨c, (hc | hc), hsat⟩
      · exact Or.inl (ihl.mp ⟨c, hc, hsat⟩)
      · exact Or.inr (ihr.mp ⟨c, hc, hsat⟩)
    · rintro (h | h)
      · obtain ⟨c, hc, hsat⟩ := ihl.mpr h
        exact ⟨c, Or.inl hc, hsat⟩
      · obtain ⟨c, hc, hsat⟩ := ihr.mpr h
        exact ⟨c, Or.inr hc, hsat⟩
  | inter l r ihl ihr =>
    simp only [dnfOf, denote, meet]
    rw [show DNFDenote V (productDNF (dnfOf l) (dnfOf r)) x ↔ _ from dnfDenote_product]
    exact and_congr ihl ihr

/-- **The type-level procedure decides the type-level ordering**: accepted
    exactly when denotations are contained under every valuation (soundness),
    with a countermodel on rejection (completeness). -/
theorem isSubtype_sound {t1 t2 : LatticeTy α}
    (h : decide (dnfOf t1) (dnfOf t2) = true)
    {X : Type} (V : α → Ty X) : denote V t1 ≤ₜ denote V t2 := by
  intro x hx
  have := decide_sound h V x ((dnfOf_denotes V t1 x).mpr hx)
  exact (dnfOf_denotes V t2 x).mp this

theorem isSubtype_complete {t1 t2 : LatticeTy α}
    (h : decide (dnfOf t1) (dnfOf t2) = false) :
    ∃ V : α → Ty Unit, ¬ (denote V t1 ≤ₜ denote V t2) := by
  obtain ⟨V, hV⟩ := decide_complete h
  refine ⟨V, ?_⟩
  intro hle
  apply hV
  intro x hx
  have := hle x ((dnfOf_denotes V t1 x).mp hx)
  exact (dnfOf_denotes V t2 x).mpr this

end Oak.TypeLatticeRefinement
