import Oak.CNFFolds

set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace Oak.CNFObligation
open Oak.CNFEmission

theorem fits_iff (used roots capacity : UInt32) (fuel : Nat) :
    cnf_obligation_fits used roots capacity fuel = some true ↔
      8 + used.toNat + 1 + roots.toNat ≤ capacity.toNat := by
  have raw : cnf_obligation_fits used roots capacity fuel = some true ↔
      (Oak.LRATBounds.lrat_fits 8 used capacity fuel = some true ∧
       Oak.LRATBounds.lrat_fits (8 + used) 1 capacity fuel = some true) ∧
       Oak.LRATBounds.lrat_fits (8 + used + 1) roots capacity fuel = some true := by
    change some (((decide ((8 : UInt32) ≤ capacity) && decide (used ≤ capacity-8)) &&
      (decide (8+used ≤ capacity) && decide (1 ≤ capacity-(8+used)))) &&
      (decide (8+used+1 ≤ capacity) && decide (roots ≤ capacity-(8+used+1)))) = some true ↔ _
    simp [Oak.LRATBounds.lrat_fits]
  rw [raw]
  constructor
  · rintro ⟨⟨a,b⟩,c⟩
    have x := Oak.LRATBounds.fits_no_wrap 8 used capacity fuel a
    have y := Oak.LRATBounds.fits_no_wrap (8+used) 1 capacity fuel b
    have z := (Oak.LRATBounds.fits_iff _ _ _ _).mp c
    rw [y, x] at z
    exact z
  · intro h
    have a : Oak.LRATBounds.lrat_fits 8 used capacity fuel = some true :=
      (Oak.LRATBounds.fits_iff _ _ _ _).mpr (by change 8 + used.toNat ≤ capacity.toNat; omega)
    have x := Oak.LRATBounds.fits_no_wrap 8 used capacity fuel a
    have b : Oak.LRATBounds.lrat_fits (8+used) 1 capacity fuel = some true :=
      (Oak.LRATBounds.fits_iff _ _ _ _).mpr (by rw [x]; change 8 + used.toNat + 1 ≤ capacity.toNat; omega)
    have y := Oak.LRATBounds.fits_no_wrap (8+used) 1 capacity fuel b
    exact ⟨⟨a,b⟩, (Oak.LRATBounds.fits_iff _ _ _ _).mpr (by rw [y,x]; exact h)⟩

theorem append_no_wrap (used roots capacity n : UInt32) (fuel : Nat)
    (fits : cnf_obligation_fits used roots capacity fuel = some true)
    (count : n.toNat ≤ roots.toNat) :
    (used + n + 1).toNat = used.toNat + n.toNat + 1 ∧
      8 + (used + n + 1).toNat ≤ capacity.toNat := by
  have h := (fits_iff used roots capacity fuel).mp fits
  have := capacity.toNat_lt
  have sum : (used+n).toNat = used.toNat+n.toNat := by
    rw [UInt32.toNat_add, Nat.mod_eq_of_lt (by omega)]
  have next : (used+n+1).toNat = used.toNat+n.toNat+1 := by
    rw [UInt32.toNat_add, sum]
    change (used.toNat+n.toNat+1) % 4294967296 = _
    omega
  exact ⟨next, by rw [next]; omega⟩

theorem finish_refused (l : Layout) (mem : Array UInt32) (at_ used n : UInt32)
    (always : Bool) (fuel : Nat) :
    cnf_obligation_finish l mem at_ used n always false fuel =
      some (NONE, mem.setIfInBounds (l.state_at + STATE_EXCEEDED).toNat 1) := by
  rfl

theorem finish_true (l : Layout) (mem : Array UInt32) (at_ used n : UInt32) (fuel : Nat) :
    cnf_obligation_finish l mem at_ used n true true fuel = some (CNF_REFUTED, mem) := by rfl

theorem finish_empty (l : Layout) (mem : Array UInt32) (at_ used : UInt32) (fuel : Nat) :
    cnf_obligation_finish l mem at_ used 0 false true fuel = some (CNF_PROVEN, mem) := by rfl

def commit (l : Layout) (mem : Array UInt32) (at_ used n : UInt32) : Array UInt32 :=
  let mem := mem.setIfInBounds at_.toNat n
  let mem := mem.setIfInBounds (l.state_at + STATE_CLAUSES_USED).toNat (used+n+1)
  mem.setIfInBounds (l.state_at + STATE_CLAUSE_COUNT).toNat
    (mem.getD (l.state_at + STATE_CLAUSE_COUNT).toNat 0 + 1)

theorem finish_clause (l : Layout) (mem : Array UInt32) (at_ used n : UInt32)
    (fuel : Nat) (nonempty : n ≠ 0) :
    cnf_obligation_finish l mem at_ used n false true fuel =
      some (CNF_CLAUSE, commit l mem at_ used n) := by
  simp only [cnf_obligation_finish, Bool.false_eq_true, if_true,
    if_false, beq_iff_eq, nonempty, Option.pure_def, Bind.bind, Option.bind, commit]

theorem refused (l : Layout) (mem p : Array UInt32) (fuel : Nat)
    (noRoom : cnf_obligation_fits
      (mem.getD (l.state_at + STATE_CLAUSES_USED).toNat 0) (p.getD 2 0)
      l.clauses_cap (fuel+1) = some false) :
    cnf_obligation l mem p (fuel+1) =
      some (NONE, mem.setIfInBounds (l.state_at + STATE_EXCEEDED).toNat 1) := by
  simp only [cnf_obligation, problem_roots, Option.pure_def, Bind.bind, Option.bind]
  change (do
    let fits ← cnf_obligation_fits (mem.getD (l.state_at+STATE_CLAUSES_USED).toNat 0)
      (p.getD 2 0) l.clauses_cap (fuel+1)
    let (out,n,always,_) ← cnf_obligation.loop1 l mem p (p.getD 2 0)
      (l.clauses_at+LRAT_HEADER_WORDS+mem.getD (l.state_at+STATE_CLAUSES_USED).toNat 0)
      0 false fits 0 (fuel+1)
    let (result,out) ← cnf_obligation_finish l out
      (l.clauses_at+LRAT_HEADER_WORDS+mem.getD (l.state_at+STATE_CLAUSES_USED).toNat 0)
      (mem.getD (l.state_at+STATE_CLAUSES_USED).toNat 0) n always fits (fuel+1)
    pure (result,out)) = _
  rw [noRoom]
  simp only [Bind.bind, Option.bind, cnf_obligation.loop1, Bool.and_false,
    Bool.false_eq_true, if_false, Option.pure_def, finish_refused]

-- A root means a trap except at the final position, where it is the claim.
def rootLiteral (bit r roots : UInt32) : UInt32 := if r+1 == roots then bit ^^^ 1 else bit

theorem root_meaning (assignment : Oak.RupCheck.Assignment) (bit r roots : UInt32) :
    Oak.CNFFolds.value assignment (rootLiteral bit r roots) =
      (if r+1 == roots then !Oak.CNFFolds.value assignment bit else Oak.CNFFolds.value assignment bit) := by
  unfold rootLiteral
  split <;> simp [Oak.CNFFolds.value_flip]

def rootStart (p : Array UInt32) : UInt32 :=
  HEADER_WORDS + p.getD 1 0 * LEAF_WORDS + p.getD 0 0 * TERM_WORDS

theorem root_start (p : Array UInt32) (fuel : Nat) :
    roots_at p fuel = some (rootStart p) := by rfl

def readLiteral (l : Layout) (mem p : Array UInt32) (r roots : UInt32) : UInt32 :=
  rootLiteral (mem.getD (l.bits_at + p.getD (rootStart p + r).toNat 0 * 64).toNat 0) r roots

def step (mem : Array UInt32) (at_ n : UInt32) (always : Bool) (lit : UInt32) :
    Array UInt32 × UInt32 × Bool :=
  if lit == 1 then (mem,n,true)
  else if lit == 0 then (mem,n,always)
  else (mem.setIfInBounds (at_+1+n).toNat (Oak.CNFLiteral.encode lit),n+1,always)

theorem loop_step (l : Layout) (mem p : Array UInt32) (roots at_ n r : UInt32)
    (always : Bool) (fuel : Nat) (inside : r < roots) :
    cnf_obligation.loop1 l mem p roots at_ n always true r (fuel+1) =
      let next := step mem at_ n always (readLiteral l mem p r roots)
      cnf_obligation.loop1 l next.1 p roots at_ next.2.1 next.2.2 true (r+1) fuel := by
  simp only [cnf_obligation.loop1, inside, decide_true, Bool.true_and, if_true,
    root_start, Bind.bind, Option.bind, Option.pure_def]
  change Option.bind (if readLiteral l mem p r roots == 1 then some (mem,n,true)
    else Option.bind (if readLiteral l mem p r roots == 0 then some (mem,n)
      else some (mem.setIfInBounds (at_+1+n).toNat
        (Oak.CNFLiteral.encode (readLiteral l mem p r roots)),n+1))
      (fun pair => some (pair.1,pair.2,always)))
    (fun next => cnf_obligation.loop1 l next.1 p roots at_ next.2.1 next.2.2 true (r+1) fuel) = _
  by_cases h1 : readLiteral l mem p r roots = 1
  · simp only [step, h1, beq_self_eq_true, if_true, Bind.bind, Option.bind]
  · by_cases h0 : readLiteral l mem p r roots = 0
    all_goals simp only [step, beq_iff_eq, h1, h0, show (0 : UInt32) ≠ 1 by decide, if_true, if_false, Bind.bind, Option.bind]

theorem loop_done (l : Layout) (mem p : Array UInt32) (roots at_ n r : UInt32)
    (always : Bool) (fuel : Nat) (done : ¬ r < roots) :
    cnf_obligation.loop1 l mem p roots at_ n always true r (fuel+1) =
      some (mem,n,always,r) := by
  simp only [cnf_obligation.loop1, done, decide_false, Bool.false_and,
    Bool.false_eq_true, if_false, Option.pure_def]

def consume (mem : Array UInt32) (at_ n : UInt32) (always : Bool) :
    List UInt32 → Array UInt32 × UInt32 × Bool
  | [] => (mem,n,always)
  | lit::rest =>
    let next := step mem at_ n always lit
    consume next.1 at_ next.2.1 next.2.2 rest

-- Records the actual root reads as memory evolves. Deriving those reads from
-- the original blasted roots requires a non-aliasing layout invariant.
inductive Trace (l : Layout) (p : Array UInt32) (roots at_ : UInt32) :
    Array UInt32 → UInt32 → Bool → UInt32 → List UInt32 → Prop
  | done (mem : Array UInt32) (n r : UInt32) (always : Bool) (end_ : ¬ r < roots) :
      Trace l p roots at_ mem n always r []
  | next (mem : Array UInt32) (n r lit : UInt32) (always : Bool) (rest : List UInt32)
      (inside : r < roots) (read : readLiteral l mem p r roots = lit)
      (tail : let s := step mem at_ n always lit
        Trace l p roots at_ s.1 s.2.1 s.2.2 (r+1) rest) :
      Trace l p roots at_ mem n always r (lit::rest)

theorem loop_trace (l : Layout) (mem p : Array UInt32) (roots at_ n r : UInt32)
    (always : Bool) (lits : List UInt32) (fuel : Nat)
    (trace : Trace l p roots at_ mem n always r lits) :
    ∃ finish, cnf_obligation.loop1 l mem p roots at_ n always true r (fuel+lits.length+1) =
      some ((consume mem at_ n always lits).1, (consume mem at_ n always lits).2.1,
        (consume mem at_ n always lits).2.2, finish) := by
  induction trace with
  | done mem n r always end_ =>
    exact ⟨r, loop_done l mem p roots at_ n r always fuel end_⟩
  | next mem n r lit always rest inside read tail ih =>
    simp only [List.length_cons]
    rw [loop_step l mem p roots at_ n r always _ inside, read]
    exact ih


theorem production_trace (l : Layout) (mem p : Array UInt32) (initialUsed : UInt32)
    (lits : List UInt32) (fuel : Nat)
    (used : mem.getD (l.state_at+STATE_CLAUSES_USED).toNat 0 = initialUsed)
    (admit : cnf_obligation_fits initialUsed (p.getD 2 0) l.clauses_cap
      (fuel+lits.length+1) = some true)
    (trace : Trace l p (p.getD 2 0) (l.clauses_at+LRAT_HEADER_WORDS+initialUsed)
      mem 0 false 0 lits) :
    cnf_obligation l mem p (fuel+lits.length+1) =
      let s := consume mem (l.clauses_at+LRAT_HEADER_WORDS+initialUsed) 0 false lits
      cnf_obligation_finish l s.1 (l.clauses_at+LRAT_HEADER_WORDS+initialUsed)
        initialUsed s.2.1 s.2.2 true (fuel+lits.length+1) := by
  obtain ⟨finish,run⟩ := loop_trace l mem p _ _ 0 0 false lits fuel trace
  simp only [cnf_obligation, problem_roots, Option.pure_def, Bind.bind, Option.bind]
  change _ = _
  simp only [show (2 : UInt32).toNat = 2 from rfl, used, admit, run, Option.pure_def, Bind.bind, Option.bind]
  cases cnf_obligation_finish l (consume mem (l.clauses_at+LRAT_HEADER_WORDS+initialUsed) 0 false lits).1
    (l.clauses_at+LRAT_HEADER_WORDS+initialUsed) initialUsed
    (consume mem (l.clauses_at+LRAT_HEADER_WORDS+initialUsed) 0 false lits).2.1
    (consume mem (l.clauses_at+LRAT_HEADER_WORDS+initialUsed) 0 false lits).2.2 true (fuel+lits.length+1)
    <;> rfl

theorem consume_always (mem : Array UInt32) (at_ n : UInt32) (always : Bool) (es : List UInt32) :
    (consume mem at_ n always es).2.2 = (always || es.any (· == 1)) := by
  induction es generalizing mem n always with
  | nil => simp [consume]
  | cons e es ih =>
    by_cases h1 : e = 1
    · subst e; simp [consume, step, ih]
    · by_cases h0 : e = 0
      · subst e; simp [consume, step, ih]
      · have he : (e == (1 : UInt32)) = false := by simpa using h1
        simp [consume, step, h1, h0, ih, he]


def literals (es : List UInt32) : List UInt32 := es.filter (fun e => e != 0 && e != 1)

theorem consume_count (mem : Array UInt32) (at_ n : UInt32) (always : Bool) (es : List UInt32)
    (bound : n.toNat + (literals es).length < 4294967296) :
    (consume mem at_ n always es).2.1.toNat = n.toNat + (literals es).length := by
  induction es generalizing mem n always with
  | nil => simp [consume, literals]
  | cons e es ih =>
    by_cases h1 : e = 1
    · subst e
      simpa only [consume, step, beq_self_eq_true, if_true, literals, List.filter_cons,
        bne_self_eq_false, Bool.and_false, Bool.false_eq_true, if_false] using ih mem n true (by simpa [literals] using bound)
    · by_cases h0 : e = 0
      · subst e
        simpa [consume, step, literals] using ih mem n always (by simpa [literals] using bound)
      · have eh0 : (e != (0 : UInt32)) = true := by simpa using h0
        have eh1 : (e != (1 : UInt32)) = true := by simpa using h1
        have len : (literals (e::es)).length = (literals es).length + 1 := by
          simp only [literals, List.filter_cons, eh0, eh1, Bool.true_and, if_true, List.length_cons]
        rw [len] at bound
        have inc : (n+1).toNat = n.toNat+1 := by
          change (n.toNat+1) % 4294967296 = n.toNat+1
          omega
        have tail := ih (mem.setIfInBounds (at_+1+n).toNat (Oak.CNFLiteral.encode e)) (n+1) always
          (by rw [inc]; omega)
        simp only [consume, step, beq_iff_eq, h1, h0, if_false, len]
        rw [tail, inc]
        omega

theorem reduction_semantics (assignment : Oak.RupCheck.Assignment) (es : List UInt32) :
    es.any (Oak.CNFFolds.value assignment) =
      (es.any (· == 1) || (literals es).any (Oak.CNFLiteral.edgeValue assignment)) := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    by_cases h0 : e = 0
    · subst e; simpa [literals, Oak.CNFFolds.value] using ih
    by_cases h1 : e = 1
    · subst e; simp [literals, Oak.CNFFolds.value]
    · simp only [List.any_cons, literals, List.filter_cons, bne_iff_ne, h0, h1,
        Bool.true_and, if_true, Oak.CNFFolds.value, beq_iff_eq, if_false]
      simp only [literals] at ih
      rw [ih]
      have eh : (e == (1 : UInt32)) = false := by simpa using h1
      cases hv : Oak.CNFLiteral.edgeValue assignment e <;> simp [h0, h1, hv, eh]

-- Constant outcomes are sound for the observed literal sequence. The trace
-- theorem above relates that reducer to production; source-root preservation
-- is still a separate layout/bitblasting obligation.
theorem proven_meaning (assignment : Oak.RupCheck.Assignment) (mem : Array UInt32)
    (at_ : UInt32) (es : List UInt32) (bound : (literals es).length < 4294967296)
    (empty : (consume mem at_ 0 false es).2.1 = 0)
    (never : (consume mem at_ 0 false es).2.2 = false) :
    es.any (Oak.CNFFolds.value assignment) = false := by
  have count := consume_count mem at_ 0 false es (by simpa using bound)
  rw [empty] at count
  have len : (literals es).length = 0 := by simpa using count.symm
  have noLits : literals es = [] := List.length_eq_zero_iff.mp len
  have noTrue := consume_always mem at_ 0 false es
  rw [never] at noTrue
  rw [reduction_semantics, noLits]
  simpa using noTrue.symm

theorem refuted_meaning (assignment : Oak.RupCheck.Assignment) (mem : Array UInt32)
    (at_ : UInt32) (es : List UInt32)
    (always : (consume mem at_ 0 false es).2.2 = true) :
    es.any (Oak.CNFFolds.value assignment) = true := by
  have yes := consume_always mem at_ 0 false es
  rw [always] at yes
  have hit : es.any (· == 1) = true := by simpa using yes.symm
  rw [reduction_semantics, hit]
  rfl

theorem clause_meaning (assignment : Oak.RupCheck.Assignment) (es : List UInt32)
    (noTrue : es.any (· == 1) = false) :
    Oak.RupCheck.SatisfiesClause assignment
      ((literals es).map (fun e => Oak.LRATRUP.decodeWord (Oak.CNFLiteral.encode e))) ↔
      es.any (Oak.CNFFolds.value assignment) = true := by
  have valid : ∀ e ∈ literals es, (2 : UInt32) ≤ e := by
    intro e member
    simp only [literals, List.mem_filter, Bool.and_eq_true, bne_iff_ne] at member
    have zero := member.2.1
    have one := member.2.2
    simp only [UInt32.le_iff_toNat_le]
    have z : e.toNat ≠ 0 := by intro h; apply zero; exact UInt32.toNat_inj.mp h
    have o : e.toNat ≠ 1 := by intro h; apply one; exact UInt32.toNat_inj.mp h
    change 2 ≤ e.toNat
    omega
  rw [Oak.CNFLiteral.clause_semantics assignment (literals es) valid,
    reduction_semantics, noTrue]
  simp only [Bool.false_or, List.any_eq_true]

end Oak.CNFObligation
