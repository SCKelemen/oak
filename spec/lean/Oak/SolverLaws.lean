import Oak.RupCheck

/-!
# The solver's laws

`prove/solver/sat.oak` is the conflict-driven solver behind the
certificate rung (docs/spec/125-verification.md §3 "By certificate"). It
is untrusted: whatever it records, the checkers (`internal/lrat/lrat.go`,
`prove/solver/lrat.oak`) decide, and `Oak.RupCheck` is why an accepted
record refutes the formula. This module states the other half, the laws
the solver relies on so that what it records is accepted — a completeness
statement about the recording, over the same relation the checkers
decide:

- **Resolution** (`resolvent_sound`, `resolvent_propagates`): the resolvent
  of two clauses is implied by both, and the step bounded variable
  elimination records — the resolvent with its two parents as hints, the
  clause holding the pivot first — is a hint chain the checkers accept.
- **The replayed chain** (`replay_propagates`, `learned_entails`): conflict
  analysis records the reasons of the replayed trail literals in trail
  order, then the conflict clause. When each reason is unit under the
  learned clause's negation and the literals replayed before it, the
  hints are a `Propagate` chain and the learned clause is entailed by
  the database.
- **The mark discipline** (`trail_replays`): over a propagation trail —
  every implied literal's reason unit under the trail before it — the
  chain condition follows from the analysis's marks: every antecedent of
  a replayed reason is either kept in the learned clause or is itself a
  replayed literal (seen marks 1 and 2/3 in `sat_analyze`). Decisions are
  never replayed, so a decision antecedent must be kept — the first-UIP
  frontier.
- **Reconstruction** (`reconstruct_models`, `elimination_step_models`):
  after eliminating a variable, walking its clauses with their pivot
  literals and flipping the pivot of an unsatisfied clause (`sat_extend`)
  yields a model of those clauses whenever the assignment satisfies every
  resolvent; the rest of the formula, which no longer mentions the
  variable, is untouched.

The solver's code is checked against these laws by its fixtures and the
corpus (`sat_oak_test.go`, `prove_sat_test.go`), not proved; the record it
writes is checked by the checkers on every run.
-/

set_option autoImplicit false

namespace Oak.SolverLaws

open Oak.RupCheck

theorem negate_negate (l : Literal) : negate (negate l) = l := by
  cases l with
  | mk index positive => cases positive <;> rfl

theorem negate_injective {l m : Literal} (h : negate l = negate m) : l = m := by
  have := congrArg negate h
  simpa [negate_negate] using this

/-! ## Resolution -/

/-- The resolvent of `c` (holding `p`) and `d` (holding `negate p`) on the
pivot `p`: every other literal of both. `sat_resolve` writes exactly this,
literals made distinct and a tautology dropped, neither of which changes
what the clause says. -/
def resolvent (c d : Clause) (p : Literal) : Clause :=
  c.filter (· ≠ p) ++ d.filter (· ≠ negate p)

theorem mem_resolvent_left {c d : Clause} {p l : Literal} (hl : l ∈ c) (ne : l ≠ p) :
    l ∈ resolvent c d p := by
  unfold resolvent
  exact List.mem_append_left _ (List.mem_filter.mpr ⟨hl, by simpa using ne⟩)

theorem mem_resolvent_right {c d : Clause} {p l : Literal} (hl : l ∈ d) (ne : l ≠ negate p) :
    l ∈ resolvent c d p := by
  unfold resolvent
  exact List.mem_append_right _ (List.mem_filter.mpr ⟨hl, by simpa using ne⟩)

/-- A resolvent is implied by its parents. -/
theorem resolvent_sound {a : Assignment} {c d : Clause} {p : Literal}
    (hc : SatisfiesClause a c) (hd : SatisfiesClause a d) :
    SatisfiesClause a (resolvent c d p) := by
  obtain ⟨l, hl, hv⟩ := hc
  by_cases eq : l = p
  · subst eq
    obtain ⟨m, hm, hmv⟩ := hd
    refine ⟨m, mem_resolvent_right hm ?_, hmv⟩
    intro bad
    subst bad
    exact holds_not_negate hv hmv
  · exact ⟨l, mem_resolvent_left hl eq, hv⟩

/-- The step elimination records: the resolvent, its parents as hints
with the clause holding the pivot first. Under the resolvent's negation
that clause is unit on the pivot and the other parent then conflicts. -/
theorem resolvent_propagates {db : Database} {i j : Nat} {c d : Clause} {p : Literal}
    (hi : db i = some c) (hj : db j = some d) (hp : p ∈ c) (_hnp : negate p ∈ d) :
    Propagate db ((resolvent c d p).map negate) [i, j] := by
  apply Propagate.unit hi (u := p)
  · refine ⟨hp, ?_⟩
    intro l hl
    by_cases eq : l = p
    · exact Or.inl eq
    · exact Or.inr (List.mem_map.mpr ⟨l, mem_resolvent_left hl eq, rfl⟩)
  · apply Propagate.conflict hj
    intro l hl
    by_cases eq : l = negate p
    · subst eq
      exact List.mem_cons.mpr (Or.inl (negate_negate p))
    · exact List.mem_cons.mpr (Or.inr (List.mem_map.mpr ⟨l, mem_resolvent_right hl eq, rfl⟩))

/-- The recorded resolvent is entailed, by the checker's own reasoning. -/
theorem resolvent_entails {db : Database} {i j : Nat} {c d : Clause} {p : Literal}
    (hi : db i = some c) (hj : db j = some d) (hp : p ∈ c) (hnp : negate p ∈ d)
    (a : Assignment) (hm : Models a db) : SatisfiesClause a (resolvent c d p) :=
  rup_entails (resolvent_propagates hi hj hp hnp) a hm

/-! ## The replayed chain -/

/-- The replayed stretch of the trail: each literal with the id of its
reason, in trail order. -/
abbrev Replay := List (Literal × Nat)

/-- The chain condition, accumulating the replayed literals in `earlier`:
each reason is a live clause holding its literal, unit under the earlier
replayed literals and the learned clause's negation. -/
def Replays (db : Database) (learned : Clause) : List Literal → Replay → Prop
  | _, [] => True
  | earlier, (u, r) :: rest =>
      (∃ c, db r = some c ∧ UnitUnder (earlier ++ learned.map negate) c u) ∧
        Replays db learned (u :: earlier) rest

/-- The literals assumed once the replay is walked. -/
def assumed : List Literal → Replay → List Literal
  | earlier, [] => earlier
  | earlier, (u, _) :: rest => assumed (u :: earlier) rest

/-- The hints as recorded: the replayed reasons in trail order, then the
conflict clause. -/
def hintsOf (replay : Replay) (conflict : Nat) : List Nat :=
  replay.map Prod.snd ++ [conflict]

theorem replay_propagates {db : Database} {learned : Clause} {conflict : Nat} :
    ∀ (earlier : List Literal) (replay : Replay),
      Replays db learned earlier replay →
      (∃ c, db conflict = some c ∧ Falsified (assumed earlier replay ++ learned.map negate) c) →
      Propagate db (earlier ++ learned.map negate) (hintsOf replay conflict) := by
  intro earlier replay
  induction replay generalizing earlier with
  | nil =>
    intro _ ⟨c, hc, hf⟩
    exact Propagate.conflict hc hf
  | cons step rest ih =>
    obtain ⟨u, r⟩ := step
    intro ⟨⟨c, hr, hu⟩, more⟩ final
    exact Propagate.unit hr hu (ih (u :: earlier) more final)

/-- The learned clause is entailed by the database: the chain the solver
records from an empty `earlier` is a `Propagate` from the clause's
negation, and `rup_entails` closes. -/
theorem learned_entails {db : Database} {learned : Clause} {replay : Replay} {conflict : Nat}
    (chain : Replays db learned [] replay)
    (final : ∃ c, db conflict = some c ∧ Falsified (assumed [] replay ++ learned.map negate) c)
    (a : Assignment) (hm : Models a db) : SatisfiesClause a learned :=
  rup_entails (by simpa using replay_propagates [] replay chain final) a hm

/-! ## The mark discipline over a propagation trail -/

/-- A trail entry: the literal and, for an implied literal, its reason. A
decision carries none. -/
abbrev Trail := List (Literal × Option Nat)

/-- The propagation invariant: an implied literal's reason is a live clause
holding it that was unit under the literals before it on the trail. The
list is in trail order; `before` is the trail so far, as literals. -/
def Propagated (db : Database) : List Literal → Trail → Prop
  | _, [] => True
  | before, (u, reason) :: rest =>
      (∀ r, reason = some r → ∃ c, db r = some c ∧ UnitUnder before c u) ∧
        Propagated db (u :: before) rest

/-- The replayed entries of a trail: implied literals the analysis marked. -/
def replayed (marked : Literal → Bool) : Trail → Replay
  | [] => []
  | (u, some r) :: rest => if marked u then (u, r) :: replayed marked rest else replayed marked rest
  | (_, none) :: rest => replayed marked rest

/-- The frontier the marks describe: every literal of a replayed reason
other than the implied one is kept (in the learned clause, seen mark 1)
or is the negation of a marked implied literal (seen marks 2 and 3),
which the trail order then places earlier. -/
def Frontier (db : Database) (learned : Clause) (marked : Literal → Bool) (trail : Trail) : Prop :=
  ∀ u r, (u, some r) ∈ trail → marked u = true →
    ∀ c, db r = some c → ∀ l, l ∈ c → l ≠ u →
      l ∈ learned ∨ (marked (negate l) = true ∧ ∃ r', (negate l, some r') ∈ trail)

/-- A literal is on the trail once. -/
def Distinct (trail : Trail) : Prop :=
  ∀ l o o', (l, o) ∈ trail → (l, o') ∈ trail → o = o'

theorem mem_replayed {marked : Literal → Bool} {l : Literal} {r : Nat} :
    ∀ trail : Trail, (l, r) ∈ replayed marked trail → (l, some r) ∈ trail ∧ marked l = true := by
  intro trail
  induction trail with
  | nil => intro h; simp [replayed] at h
  | cons entry rest ih =>
    obtain ⟨u, reason⟩ := entry
    intro h
    cases reason with
    | none =>
      simp only [replayed] at h
      obtain ⟨mem, mk⟩ := ih h
      exact ⟨List.mem_cons_of_mem _ mem, mk⟩
    | some r' =>
      simp only [replayed] at h
      by_cases mk : marked u = true
      · rw [if_pos mk] at h
        rcases List.mem_cons.mp h with eq | tail
        · cases eq
          exact ⟨List.mem_cons_self, mk⟩
        · obtain ⟨mem, mk'⟩ := ih tail
          exact ⟨List.mem_cons_of_mem _ mem, mk'⟩
      · rw [if_neg mk] at h
        obtain ⟨mem, mk'⟩ := ih h
        exact ⟨List.mem_cons_of_mem _ mem, mk'⟩

theorem mem_replayed_of {marked : Literal → Bool} {l : Literal} {r : Nat} :
    ∀ trail : Trail, (l, some r) ∈ trail → marked l = true → (l, r) ∈ replayed marked trail := by
  intro trail
  induction trail with
  | nil => intro h; simp at h
  | cons entry rest ih =>
    obtain ⟨u, reason⟩ := entry
    intro h mk
    rcases List.mem_cons.mp h with eq | tail
    · cases eq
      simp only [replayed, mk, if_true]
      exact List.mem_cons_self
    · cases reason with
      | none => simpa [replayed] using ih tail mk
      | some r' =>
        simp only [replayed]
        by_cases mku : marked u = true
        · rw [if_pos mku]; exact List.mem_cons_of_mem _ (ih tail mk)
        · rw [if_neg mku]; exact ih tail mk

theorem mem_assumed {l : Literal} :
    ∀ (earlier : List Literal) (replay : Replay),
      l ∈ assumed earlier replay ↔ l ∈ earlier ∨ ∃ r, (l, r) ∈ replay := by
  intro earlier replay
  induction replay generalizing earlier with
  | nil => simp [assumed]
  | cons step rest ih =>
    obtain ⟨u, r⟩ := step
    simp only [assumed]
    rw [ih (u :: earlier)]
    constructor
    · intro h
      rcases h with h | ⟨r', h⟩
      · rcases List.mem_cons.mp h with eq | tail
        · subst eq; exact Or.inr ⟨r, List.mem_cons_self⟩
        · exact Or.inl tail
      · exact Or.inr ⟨r', List.mem_cons_of_mem _ h⟩
    · intro h
      rcases h with h | ⟨r', h⟩
      · exact Or.inl (List.mem_cons_of_mem _ h)
      · rcases List.mem_cons.mp h with eq | tail
        · cases eq; exact Or.inl (List.mem_cons_self)
        · exact Or.inr ⟨r', tail⟩

/-- Walking a propagation trail from a split point: `done` is the trail
walked so far, `before` its literals, `earlier` its marked implied
literals; the marked implied literals of `rest` satisfy the chain
condition from `earlier`. -/
theorem trail_replays_from {db : Database} {learned : Clause} {marked : Literal → Bool}
    {trail : Trail} (frontier : Frontier db learned marked trail) (distinct : Distinct trail) :
    ∀ (rest done : Trail) (before earlier : List Literal),
      done ++ rest = trail →
      (∀ l, l ∈ before → ∃ o, (l, o) ∈ done) →
      (∀ l r, (l, some r) ∈ done → marked l = true → l ∈ earlier) →
      Propagated db before rest →
      Replays db learned earlier (replayed marked rest) := by
  intro rest
  induction rest with
  | nil => intros; simp [replayed, Replays]
  | cons entry rest ih =>
    obtain ⟨u, reason⟩ := entry
    intro done before earlier split hbefore hearlier prop
    obtain ⟨hreason, more⟩ := prop
    have split' : (done ++ [(u, reason)]) ++ rest = trail := by
      simpa [List.append_assoc] using split
    have hbefore' : ∀ l, l ∈ u :: before → ∃ o, (l, o) ∈ done ++ [(u, reason)] := by
      intro l h
      rcases List.mem_cons.mp h with eq | tail
      · subst eq; exact ⟨reason, by simp⟩
      · obtain ⟨o, ho⟩ := hbefore l tail
        exact ⟨o, List.mem_append_left _ ho⟩
    have inTrail : (u, reason) ∈ trail := by
      rw [← split]; exact List.mem_append_right _ (List.mem_cons_self)
    cases reason with
    | none =>
      simp only [replayed]
      refine ih (done ++ [(u, none)]) (u :: before) earlier split' hbefore' ?_ more
      intro l r h mk
      rcases List.mem_append.mp h with h | h
      · exact hearlier l r h mk
      · simp at h
    | some r =>
      simp only [replayed]
      by_cases mk : marked u = true
      · rw [if_pos mk]
        refine ⟨?_, ?_⟩
        · obtain ⟨c, hc, unit⟩ := hreason r rfl
          refine ⟨c, hc, unit.1, ?_⟩
          intro l hl
          by_cases ne : l = u
          · exact Or.inl ne
          · right
            have neg : negate l ∈ before := by
              rcases unit.2 l hl with eq | neg
              · exact absurd eq ne
              · exact neg
            rcases frontier u r inTrail mk c hc l hl ne with kept | ⟨mkn, r', hr'⟩
            · exact List.mem_append_right _ (List.mem_map.mpr ⟨l, kept, rfl⟩)
            · obtain ⟨o, ho⟩ := hbefore _ neg
              have inTrail' : (negate l, o) ∈ trail := by
                rw [← split]; exact List.mem_append_left _ ho
              have eq := distinct _ _ _ inTrail' hr'
              subst eq
              exact List.mem_append_left _ (hearlier _ _ ho mkn)
        · refine ih (done ++ [(u, some r)]) (u :: before) (u :: earlier) split' hbefore' ?_ more
          intro l r' h mk'
          rcases List.mem_append.mp h with h | h
          · exact List.mem_cons_of_mem _ (hearlier l r' h mk')
          · simp at h; obtain ⟨rfl, _⟩ := h; exact List.mem_cons_self
      · rw [if_neg mk]
        refine ih (done ++ [(u, some r)]) (u :: before) earlier split' hbefore' ?_ more
        intro l r' h mk'
        rcases List.mem_append.mp h with h | h
        · exact hearlier l r' h mk'
        · simp at h; obtain ⟨rfl, _⟩ := h; exact absurd mk' mk

/-- Over a whole propagation trail, the analysis's marks give the chain
condition from nothing assumed. -/
theorem trail_replays {db : Database} {learned : Clause} {marked : Literal → Bool}
    {trail : Trail} (frontier : Frontier db learned marked trail) (distinct : Distinct trail)
    (prop : Propagated db [] trail) :
    Replays db learned [] (replayed marked trail) :=
  trail_replays_from frontier distinct trail [] [] [] rfl (by simp) (by simp) prop

/-- The conflict clause under the marks: each of its literals is kept or
is the negation of a marked implied literal. -/
def ConflictFrontier (learned : Clause) (marked : Literal → Bool) (trail : Trail) (c : Clause) : Prop :=
  ∀ l, l ∈ c → l ∈ learned ∨ (marked (negate l) = true ∧ ∃ r, (negate l, some r) ∈ trail)

/-- What `sat_analyze` records — the marked reasons in trail order, then
the conflict — is accepted, and the learned clause is entailed. -/
theorem analysis_entails {db : Database} {learned : Clause} {marked : Literal → Bool}
    {trail : Trail} {conflict : Nat} {c : Clause}
    (frontier : Frontier db learned marked trail) (distinct : Distinct trail)
    (prop : Propagated db [] trail) (hc : db conflict = some c)
    (final : ConflictFrontier learned marked trail c)
    (a : Assignment) (hm : Models a db) : SatisfiesClause a learned := by
  apply learned_entails (trail_replays frontier distinct prop) ⟨c, hc, ?_⟩ a hm
  intro l hl
  rcases final l hl with kept | ⟨mk, r, hr⟩
  · exact List.mem_append_right _ (List.mem_map.mpr ⟨l, kept, rfl⟩)
  · apply List.mem_append_left
    rw [mem_assumed]
    right
    exact ⟨r, mem_replayed_of trail hr mk⟩

/-! ## Reconstruction after elimination -/

/-- `a` with the literal `p` made true. -/
def flip (a : Assignment) (p : Literal) : Assignment :=
  fun i => if i = p.index then p.positive else a i

theorem flip_holds (a : Assignment) (p : Literal) : Holds (flip a p) p := by
  simp [Holds, flip]

theorem flip_other {a : Assignment} {p l : Literal} (ne : l.index ≠ p.index) :
    Holds (flip a p) l ↔ Holds a l := by
  simp [Holds, flip, ne]

/-- Two assignments that agree away from the variable `x`. -/
def AgreeOff (x : Nat) (a b : Assignment) : Prop := ∀ i, i ≠ x → a i = b i

theorem agreeOff_refl (x : Nat) (a : Assignment) : AgreeOff x a a := fun _ _ => rfl

theorem agreeOff_flip {x : Nat} {a b : Assignment} {p : Literal} (h : AgreeOff x a b)
    (hp : p.index = x) : AgreeOff x a (flip b p) := by
  intro i ne
  have : i ≠ p.index := by rw [hp]; exact ne
  simp [flip, this, h i ne]

/-- A clause not mentioning `x` is satisfied alike by assignments agreeing
off `x`. -/
def Avoids (x : Nat) (c : Clause) : Prop := ∀ l, l ∈ c → l.index ≠ x

theorem satisfies_of_agreeOff {x : Nat} {a b : Assignment} {c : Clause}
    (h : AgreeOff x a b) (avoid : Avoids x c) (hc : SatisfiesClause a c) : SatisfiesClause b c := by
  obtain ⟨l, hl, hv⟩ := hc
  refine ⟨l, hl, ?_⟩
  unfold Holds at *
  rw [← h l.index (avoid l hl)]
  exact hv

/-- An eliminated clause with its pivot: the literal of the eliminated
variable it holds. `sat_eliminate` pushes each clause of the variable so,
`sat_extend` walks the stack backward. -/
abbrev Stack := List (Clause × Literal)

open Classical in
/-- The walk `sat_extend` performs over the entries of one variable: an
unsatisfied clause flips its pivot true. -/
noncomputable def reconstruct : Assignment → Stack → Assignment
  | a, [] => a
  | a, (c, p) :: rest => reconstruct (if SatisfiesClause a c then a else flip a p) rest

/-- The stack of one variable `x`: every pivot is a literal of `x` held by
its clause, and no other literal of the clause is of `x`. -/
def OnVariable (x : Nat) (stack : Stack) : Prop :=
  ∀ c p, (c, p) ∈ stack → p.index = x ∧ p ∈ c ∧ ∀ l, l ∈ c → l ≠ p → l.index ≠ x

/-- The assignment satisfies every resolvent across the stack: the
clauses the elimination left in the formula (a tautological resolvent is
satisfied by anything). -/
def ResolventsHold (a : Assignment) (stack : Stack) : Prop :=
  ∀ c p d q, (c, p) ∈ stack → (d, q) ∈ stack → q = negate p → SatisfiesClause a (resolvent c d p)

theorem reconstruct_agreeOff {x : Nat} (stack : Stack) (onx : OnVariable x stack) :
    ∀ a, AgreeOff x a (reconstruct a stack) := by
  induction stack with
  | nil => intro a; exact agreeOff_refl x a
  | cons entry rest ih =>
    obtain ⟨c, p⟩ := entry
    intro a
    have onrest : OnVariable x rest := fun c' p' h => onx c' p' (List.mem_cons_of_mem _ h)
    have hp : p.index = x := (onx c p (List.mem_cons_self)).1
    simp only [reconstruct]
    by_cases sat : SatisfiesClause a c
    · simp only [sat, if_true]; exact ih onrest a
    · simp only [sat, if_false]
      intro i ne
      have := ih onrest (flip a p) i ne
      rw [← this]
      exact agreeOff_flip (agreeOff_refl x a) hp i ne

/-- Reconstruction over one variable yields a model of its clauses. The
invariant carried along the walk: the current assignment agrees with the
original off `x` (so it still satisfies every resolvent) and satisfies
every entry walked so far; a flip keeps the walked entries satisfied,
because a walked entry that held only through the flipped literal is
satisfied on its other literals by the resolvent with the flipping
clause. -/
theorem reconstruct_models {x : Nat} {a : Assignment} (whole : Stack) (onx : OnVariable x whole)
    (res : ResolventsHold a whole) :
    ∀ (walked rest : Stack) (b : Assignment),
      (∀ e, e ∈ walked → e ∈ whole) → (∀ e, e ∈ rest → e ∈ whole) →
      AgreeOff x a b →
      (∀ c p, (c, p) ∈ walked → SatisfiesClause b c) →
      ∀ c p, (c, p) ∈ walked ++ rest → SatisfiesClause (reconstruct b rest) c := by
  intro walked rest
  induction rest generalizing walked with
  | nil =>
    intro b _ _ _ hwalked c p hmem
    simpa [reconstruct] using hwalked c p (by simpa using hmem)
  | cons entry rest ih =>
    obtain ⟨c₀, p₀⟩ := entry
    intro b hw hr agree hwalked c p hmem
    have inwhole : (c₀, p₀) ∈ whole := hr _ (List.mem_cons_self)
    have hr' : ∀ e, e ∈ rest → e ∈ whole := fun e h => hr e (List.mem_cons_of_mem _ h)
    have hw' : ∀ e, e ∈ walked ++ [(c₀, p₀)] → e ∈ whole := by
      intro e h
      rcases List.mem_append.mp h with h | h
      · exact hw e h
      · simp at h; subst h; exact inwhole
    have reorder : (c, p) ∈ (walked ++ [(c₀, p₀)]) ++ rest := by
      simpa [List.append_assoc] using hmem
    simp only [reconstruct]
    by_cases sat : SatisfiesClause b c₀
    · simp only [sat, if_true]
      refine ih (walked ++ [(c₀, p₀)]) b hw' hr' agree ?_ c p reorder
      intro c' p' h
      rcases List.mem_append.mp h with h | h
      · exact hwalked c' p' h
      · simp at h; obtain ⟨rfl, _⟩ := h; exact sat
    · simp only [sat, if_false]
      obtain ⟨hp₀x, hp₀c, hothers⟩ := onx c₀ p₀ inwhole
      have agree' : AgreeOff x a (flip b p₀) := agreeOff_flip agree hp₀x
      refine ih (walked ++ [(c₀, p₀)]) (flip b p₀) hw' hr' agree' ?_ c p reorder
      intro c' p' h
      rcases List.mem_append.mp h with h | h
      · -- A walked entry stays satisfied after the flip.
        have satb := hwalked c' p' h
        obtain ⟨hp'x, hp'c, hothers'⟩ := onx c' p' (hw _ h)
        obtain ⟨l, hl, hv⟩ := satb
        by_cases lx : l.index = x
        · -- Its satisfying literal is of x. It is p' (the only literal of
          -- x in c'); it was true under b and p₀ was false, so p' is the
          -- negation of p₀ and the resolvent supplies another literal.
          have lp : l = p' := Classical.byContradiction fun ne => hothers' l hl ne lx
          subst lp
          have p₀false : ¬ Holds b p₀ := by
            intro hp₀
            exact sat ⟨p₀, hp₀c, hp₀⟩
          have opposite : l = negate p₀ := by
            cases l with
            | mk li lpos =>
              cases p₀ with
              | mk pi ppos =>
                simp [Holds, negate] at *
                subst lx
                subst hp₀x
                cases lpos <;> cases ppos <;> simp_all
          have resolved := res c₀ p₀ c' l inwhole (hw _ h) opposite
          obtain ⟨m, hm, hmv⟩ := resolved
          unfold resolvent at hm
          rcases List.mem_append.mp hm with hm | hm
          · -- A literal of c₀ other than p₀: false under b, since c₀ is unsatisfied.
            obtain ⟨hmc, hne⟩ := List.mem_filter.mp hm
            exfalso
            have : ¬ Holds b m := fun hb => sat ⟨m, hmc, hb⟩
            have mx : m.index ≠ x := hothers m hmc (by simpa using hne)
            apply this
            unfold Holds at *
            rw [← agree m.index mx]
            exact hmv
          · obtain ⟨hmd, hne⟩ := List.mem_filter.mp hm
            have hne' : m ≠ negate p₀ := by simpa using hne
            have mx : m.index ≠ x := by
              intro mx
              apply hne'
              have : m = l := Classical.byContradiction fun ne => hothers' m hmd ne mx
              rw [this, opposite]
            refine ⟨m, hmd, ?_⟩
            rw [flip_other (by rw [hp₀x]; exact mx)]
            unfold Holds at *
            rw [← agree m.index mx]
            exact hmv
        · refine ⟨l, hl, ?_⟩
          rw [flip_other (by rw [hp₀x]; exact lx)]
          exact hv
      · simp at h
        obtain ⟨hc', hp'⟩ := h
        subst hc'
        subst hp'
        exact ⟨_, hp₀c, flip_holds _ _⟩

/-- The elimination step, as `sat_extend` undoes it: a model of the
resolvents and of the clauses that avoid `x` extends to a model of the
eliminated clauses and those clauses alike. -/
theorem elimination_step_models {x : Nat} {a : Assignment} (stack : Stack) (rest : List Clause)
    (onx : OnVariable x stack) (res : ResolventsHold a stack)
    (avoid : ∀ c, c ∈ rest → Avoids x c) (hrest : ∀ c, c ∈ rest → SatisfiesClause a c) :
    (∀ c p, (c, p) ∈ stack → SatisfiesClause (reconstruct a stack) c) ∧
      ∀ c, c ∈ rest → SatisfiesClause (reconstruct a stack) c := by
  refine ⟨?_, ?_⟩
  · intro c p h
    exact reconstruct_models stack onx res [] stack a (by simp) (fun _ h => h)
      (agreeOff_refl x a) (by simp) c p (by simpa using h)
  · intro c h
    exact satisfies_of_agreeOff (reconstruct_agreeOff stack onx a) (avoid c h) (hrest c h)

end Oak.SolverLaws
