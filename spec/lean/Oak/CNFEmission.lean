import Oak.CNFEmissionExtracted
import Oak.CNFLiteral
import Oak.LRATBounds
import Oak.LRATStore

/-!
Production clause-emitter admission and writes. Array bounds and separation of
state from the clause region are explicit layout premises. This does not prove
layout construction, extraction, gate generation, or compiled execution.
-/
set_option autoImplicit false
namespace Oak.CNFEmission

/-- Exact mathematical capacity contract for the production guard. -/
theorem fits_iff (used n capacity : UInt32) (fuel : Nat) :
    cnf_clause_fits used n capacity fuel = some true ↔
      1 ≤ n.toNat ∧ n.toNat ≤ 3 ∧ 8 + used.toNat + n.toNat + 1 ≤ capacity.toNat := by
  change some (((decide (n ≥ 1) && decide (n ≤ 3)) &&
    (decide ((8 : UInt32) ≤ capacity) && decide (used ≤ capacity - 8))) &&
    (decide ((8 : UInt32) + used ≤ capacity) && decide (n + 1 ≤ capacity - (8 + used)))) = some true ↔ _
  simp only [Option.some.injEq, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨⟨hn, hn3⟩, ⟨hc, hu⟩⟩, ⟨ha, he⟩⟩
    have first : Oak.LRATBounds.lrat_fits 8 used capacity fuel = some true := by
      simp [Oak.LRATBounds.lrat_fits, hc, hu]
    have bound := (Oak.LRATBounds.fits_iff 8 used capacity fuel).mp first
    have exactStart := Oak.LRATBounds.fits_no_wrap 8 used capacity fuel first
    have next : (n + 1).toNat = n.toNat + 1 := by
      rw [UInt32.toNat_add, Nat.mod_eq_of_lt]
      · rfl
      rw [UInt32.le_iff_toNat_le] at hn3
      change n.toNat + 1 < 4294967296
      change n.toNat ≤ 3 at hn3
      omega
    have second : Oak.LRATBounds.lrat_fits (8 + used) (n + 1) capacity fuel = some true := by
      simp [Oak.LRATBounds.lrat_fits, ha, he]
    have endBound := (Oak.LRATBounds.fits_iff (8 + used) (n + 1) capacity fuel).mp second
    rw [exactStart, next] at endBound
    exact ⟨(UInt32.le_iff_toNat_le.mp hn), (UInt32.le_iff_toNat_le.mp hn3), endBound⟩
  · rintro ⟨hn, hn3, bound⟩
    have first := (Oak.LRATBounds.fits_iff 8 used capacity fuel).mpr (by simpa using (show 8 + used.toNat ≤ capacity.toNat by omega))
    have exactStart := Oak.LRATBounds.fits_no_wrap 8 used capacity fuel first
    have next : (n + 1).toNat = n.toNat + 1 := by
      rw [UInt32.toNat_add, Nat.mod_eq_of_lt (by change n.toNat + 1 < 4294967296; omega)]
      rfl
    have second := (Oak.LRATBounds.fits_iff (8 + used) (n + 1) capacity fuel).mpr (by rw [exactStart, next]; exact bound)
    simp only [Oak.LRATBounds.lrat_fits, Option.pure_def, Option.some.injEq,
      Bool.and_eq_true, decide_eq_true_eq] at first second
    exact ⟨⟨⟨UInt32.le_iff_toNat_le.mpr hn, UInt32.le_iff_toNat_le.mpr hn3⟩, first⟩, second⟩

def arity (b c : UInt32) : UInt32 :=
  if c == NONE then if b == NONE then 1 else 2 else 3

def used (l : Layout) (mem : Array UInt32) : UInt32 :=
  mem.getD (l.state_at + STATE_CLAUSES_USED).toNat 0

/-- A refused append changes only the exceeded flag. -/
theorem refused (l : Layout) (mem : Array UInt32) (a b c : UInt32) (fuel : Nat)
    (h : cnf_clause_fits (used l mem) (arity b c) l.clauses_cap fuel = some false) :
    cnf_emit l mem a b c fuel =
      some ((), mem.setIfInBounds (l.state_at + STATE_EXCEEDED).toNat 1) := by
  unfold used arity at h
  unfold cnf_emit
  dsimp only
  rw [h]
  rfl

def edges (a b c : UInt32) : List UInt32 :=
  if c == NONE then if b == NONE then [a] else [a, b] else [a, b, c]

def writeWords (mem : Array UInt32) (at_ : Nat) : List UInt32 → Array UInt32
  | [] => mem
  | word :: rest => writeWords (mem.setIfInBounds at_ word) (at_ + 1) rest

def emitted (l : Layout) (mem : Array UInt32) (a b c : UInt32) : Array UInt32 :=
  let at_ := (l.clauses_at + 8 + used l mem).toNat
  let words := arity b c :: (edges a b c).map Oak.CNFLiteral.encode
  let body := writeWords mem at_ words
  let advanced := body.setIfInBounds (l.state_at + STATE_CLAUSES_USED).toNat
    (used l mem + arity b c + 1)
  advanced.setIfInBounds (l.state_at + STATE_CLAUSE_COUNT).toNat
    (advanced.getD (l.state_at + STATE_CLAUSE_COUNT).toNat 0 + 1)

/-- Successful execution writes the independent list of length-prefixed
encoded literals, then advances the two counters. Addresses must not wrap. -/
theorem emitted_exact (l : Layout) (mem : Array UInt32) (a b c : UInt32) (fuel : Nat)
    (h : cnf_clause_fits (used l mem) (arity b c) l.clauses_cap fuel = some true)
    (addresses : ∀ k : UInt32, k ≤ arity b c →
      (l.clauses_at + 8 + used l mem + k).toNat =
        (l.clauses_at + 8 + used l mem).toNat + k.toNat) :
    cnf_emit l mem a b c fuel = some ((), emitted l mem a b c) := by
  unfold used arity at h
  unfold cnf_emit
  dsimp only
  rw [h]
  have lit (e : UInt32) : cnf_lit e fuel = some (Oak.CNFLiteral.encode e) := rfl
  by_cases hc : c = NONE
  · by_cases hb : b = NONE
    · have a1 := addresses 1 (by simp [arity, hc, hb])
      simp [used, Nat.add_assoc] at a1
      simp [emitted, edges, arity, hc, hb, used, lit, writeWords, a1,
        LRAT_HEADER_WORDS, Nat.add_assoc]
    · have a1 := addresses 1 (by simp [arity, hc, hb])
      have a2 := addresses 2 (by simp [arity, hc, hb])
      simp [used, Nat.add_assoc] at a1 a2
      simp [emitted, edges, arity, hc, hb, used, lit, writeWords, a1, a2,
        LRAT_HEADER_WORDS, Nat.add_assoc]
  · have a1 := addresses 1 (by simp [arity, hc])
    have a2 := addresses 2 (by simp [arity, hc])
    have a3 := addresses 3 (by simp [arity, hc])
    simp [used, Nat.add_assoc] at a1 a2 a3
    simp [emitted, edges, arity, hc, used, lit, writeWords, a1, a2, a3,
      LRAT_HEADER_WORDS, Nat.add_assoc]

theorem writeWords_size (mem : Array UInt32) (at_ : Nat) (words : List UInt32) :
    (writeWords mem at_ words).size = mem.size := by
  induction words generalizing mem at_ with
  | nil => rfl
  | cons word rest ih => simpa [writeWords] using ih (mem.setIfInBounds at_ word) (at_ + 1)

theorem writeWords_outside (mem : Array UInt32) (at_ k : Nat) (words : List UInt32)
    (outside : k < at_ ∨ at_ + words.length ≤ k) :
    (writeWords mem at_ words).getD k 0 = mem.getD k 0 := by
  induction words generalizing mem at_ with
  | nil => rfl
  | cons word rest ih =>
    rw [writeWords, ih _ (at_ + 1) (by simp only [List.length_cons] at outside; omega)]
    exact Oak.LRATChecker.array_getD_set_ne _ _ _ _ _ (by simp only [List.length_cons] at outside; omega)

theorem writeWords_read (mem : Array UInt32) (at_ j : Nat) (words : List UInt32)
    (room : at_ + words.length ≤ mem.size) (inside : j < words.length) :
    (writeWords mem at_ words).getD (at_ + j) 0 = words[j] := by
  induction words generalizing mem at_ j with
  | nil => simp at inside
  | cons word rest ih =>
    cases j with
    | zero =>
      simp only [Nat.add_zero, List.getElem_cons_zero]
      rw [writeWords, writeWords_outside _ (at_ + 1) at_ rest (Or.inl (by omega))]
      exact Oak.LRATChecker.array_getD_set_self _ _ _ _ (by simp only [List.length_cons] at room; omega)
    | succ j =>
      have room' : at_ + 1 + rest.length ≤ (mem.setIfInBounds at_ word).size := by
        simp only [Array.size_setIfInBounds, List.length_cons] at *
        omega
      have inside' : j < rest.length := by simpa using inside
      simpa [writeWords, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (mem.setIfInBounds at_ word) (at_ + 1) j room' inside'

/-- Admission bounds every emitted cell, relative to a nonwrapping region. -/
theorem addresses_exact (base used n capacity : UInt32) (fuel : Nat)
    (accepted : cnf_clause_fits used n capacity fuel = some true)
    (region : base.toNat + capacity.toNat < 4294967296) :
    ∀ k : UInt32, k ≤ n →
      (base + 8 + used + k).toNat = base.toNat + 8 + used.toNat + k.toNat := by
  have bound := (fits_iff used n capacity fuel).mp accepted
  intro k hk
  rw [UInt32.le_iff_toNat_le] at hk
  have first := Oak.LRATChecker.add_exact base 8 (by change base.toNat + 8 < 4294967296; omega)
  have second := Oak.LRATChecker.add_exact (base + 8) used (by rw [first]; change base.toNat + 8 + used.toNat < 4294967296; omega)
  rw [Oak.LRATChecker.add_exact (base + 8 + used) k (by rw [second, first]; change base.toNat + 8 + used.toNat + k.toNat < 4294967296; omega), second, first]
  rfl

/-- The record body has exactly the arity stated in its header. -/
theorem edges_length (a b c : UInt32) : (edges a b c).length = (arity b c).toNat := by
  unfold edges arity
  split <;> simp_all
  split <;> rfl

/-- The actual successful emitter stores the expected record at every offset.
The state cells are assumed to lie before the clause region. -/
theorem production_record (l : Layout) (mem out : Array UInt32)
    (a b c : UInt32) (fuel : Nat)
    (accepted : cnf_clause_fits (used l mem) (arity b c) l.clauses_cap fuel = some true)
    (region : l.clauses_at.toNat + l.clauses_cap.toNat < 4294967296)
    (capacity : l.clauses_at.toNat + l.clauses_cap.toNat ≤ mem.size)
    (separate : l.state_at.toNat + 6 ≤ l.clauses_at.toNat)
    (run : cnf_emit l mem a b c fuel = some ((), out)) :
    ∀ (j : Nat) (hj : j < 1 + (edges a b c).length),
      out.getD (l.clauses_at.toNat + 8 + (used l mem).toNat + j) 0 =
        (arity b c :: (edges a b c).map Oak.CNFLiteral.encode)[j]'(by simpa [Nat.add_comm] using hj) := by
  have bound := (fits_iff _ _ _ fuel).mp accepted
  have addr := addresses_exact l.clauses_at (used l mem) (arity b c) l.clauses_cap fuel accepted region
  have start := addr 0 (by simp)
  simp only [UInt32.add_zero, UInt32.toNat_zero, Nat.add_zero] at start
  have exact := emitted_exact l mem a b c fuel accepted (by intro k hk; rw [addr k hk, start])
  rw [exact, Option.some.injEq, Prod.mk.injEq] at run
  have outEq : out = emitted l mem a b c := run.2.symm
  intro j hj
  rw [outEq]
  have index4 : (l.state_at + STATE_CLAUSES_USED).toNat = l.state_at.toNat + 4 := by
    apply Oak.LRATChecker.add_exact
    change l.state_at.toNat + 4 < 4294967296
    omega
  have index5 : (l.state_at + STATE_CLAUSE_COUNT).toNat = l.state_at.toNat + 5 := by
    apply Oak.LRATChecker.add_exact
    change l.state_at.toNat + 5 < 4294967296
    omega
  unfold emitted
  dsimp only
  rw [Oak.LRATChecker.array_getD_set_ne _ _ _ _ _ (by rw [index5]; omega)]
  rw [Oak.LRATChecker.array_getD_set_ne _ _ _ _ _ (by rw [index4]; omega)]
  rw [start]
  apply writeWords_read
  · simp only [List.length_cons, List.length_map, edges_length]
    omega

/-- Read the payload from the stored record, excluding its length word. -/
def readPayload (out : Array UInt32) (start count : Nat) : List UInt32 :=
  (List.range count).map (fun j => out.getD (start + 1 + j) 0)

/-- The actual emitted payload, decoded by LRAT, has the source edge-clause
meaning. Constants must have been folded by the caller. -/
theorem production_clause (l : Layout) (mem out : Array UInt32)
    (a b c : UInt32) (fuel : Nat)
    (accepted : cnf_clause_fits (used l mem) (arity b c) l.clauses_cap fuel = some true)
    (region : l.clauses_at.toNat + l.clauses_cap.toNat < 4294967296)
    (capacity : l.clauses_at.toNat + l.clauses_cap.toNat ≤ mem.size)
    (separate : l.state_at.toNat + 6 ≤ l.clauses_at.toNat)
    (run : cnf_emit l mem a b c fuel = some ((), out))
    (valid : ∀ e ∈ edges a b c, 2 ≤ e) (assignment : Oak.RupCheck.Assignment) :
    Oak.RupCheck.SatisfiesClause assignment
      ((readPayload out (l.clauses_at.toNat + 8 + (used l mem).toNat)
        (edges a b c).length).map Oak.LRATRUP.decodeWord) ↔
      ∃ e ∈ edges a b c, Oak.CNFLiteral.edgeValue assignment e = true := by
  have words : readPayload out (l.clauses_at.toNat + 8 + (used l mem).toNat)
      (edges a b c).length = (edges a b c).map Oak.CNFLiteral.encode := by
    apply List.ext_getElem
    · simp [readPayload]
    · intro i hi hj
      have inside : i < (edges a b c).length := by simpa using hj
      have cell := production_record l mem out a b c fuel accepted region capacity separate run
        (i + 1) (by omega)
      simpa [readPayload, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using cell
  rw [words, List.map_map]
  exact Oak.CNFLiteral.clause_semantics assignment (edges a b c) valid

/-- Accepted append counters cannot wrap if the prior clause count is no
larger than the used payload, the invariant of length-prefixed records. -/
theorem counters_no_wrap (used n capacity count : UInt32) (fuel : Nat)
    (accepted : cnf_clause_fits used n capacity fuel = some true)
    (countBound : count ≤ used) :
    (used + n + 1).toNat = used.toNat + n.toNat + 1 ∧
      (count + 1).toNat = count.toNat + 1 := by
  have bound := (fits_iff used n capacity fuel).mp accepted
  have max := capacity.toNat_lt
  rw [UInt32.le_iff_toNat_le] at countBound
  have sum := Oak.LRATChecker.add_exact used n (by omega)
  constructor
  · rw [Oak.LRATChecker.add_exact (used + n) 1 (by rw [sum]; change used.toNat + n.toNat + 1 < 4294967296; omega), sum]
    rfl
  · exact Oak.LRATChecker.add_exact count 1 (by change count.toNat + 1 < 4294967296; omega)

/-- No other cell is changed by the successful emitter. -/
theorem production_frame (l : Layout) (mem out : Array UInt32)
    (a b c : UInt32) (fuel k : Nat)
    (accepted : cnf_clause_fits (used l mem) (arity b c) l.clauses_cap fuel = some true)
    (region : l.clauses_at.toNat + l.clauses_cap.toNat < 4294967296)
    (run : cnf_emit l mem a b c fuel = some ((), out))
    (outside : k < l.clauses_at.toNat + 8 + (used l mem).toNat ∨
      l.clauses_at.toNat + 8 + (used l mem).toNat + 1 + (edges a b c).length ≤ k)
    (notUsed : (l.state_at + STATE_CLAUSES_USED).toNat ≠ k)
    (notCount : (l.state_at + STATE_CLAUSE_COUNT).toNat ≠ k) :
    out.getD k 0 = mem.getD k 0 := by
  have addr := addresses_exact l.clauses_at (used l mem) (arity b c) l.clauses_cap fuel accepted region
  have start := addr 0 (by simp)
  simp only [UInt32.add_zero, UInt32.toNat_zero, Nat.add_zero] at start
  have exact := emitted_exact l mem a b c fuel accepted (by intro i hi; rw [addr i hi, start])
  rw [exact, Option.some.injEq, Prod.mk.injEq] at run
  rw [← run.2]
  unfold emitted
  dsimp only
  rw [Oak.LRATChecker.array_getD_set_ne _ _ _ _ _ notCount,
    Oak.LRATChecker.array_getD_set_ne _ _ _ _ _ notUsed]
  apply writeWords_outside
  simpa only [start, List.length_cons, List.length_map, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using outside

end Oak.CNFEmission
