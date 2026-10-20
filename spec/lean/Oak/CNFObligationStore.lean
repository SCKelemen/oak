import Oak.CNFObligation

set_option autoImplicit false
namespace Oak.CNFObligationStore
open Oak.CNFEmission Oak.CNFObligation

def words (es : List UInt32) : List UInt32 := (literals es).map Oak.CNFLiteral.encode

-- Admission plus a nonwrapping physical region derives the address bound.
theorem layout_bounds (base used roots capacity : UInt32) (fuel : Nat)
    (admit : cnf_obligation_fits used roots capacity fuel = some true)
    (region : base.toNat+capacity.toNat < 4294967296) :
    (base+LRAT_HEADER_WORDS+used).toNat = base.toNat+8+used.toNat ∧
      (base+LRAT_HEADER_WORDS+used).toNat+1+roots.toNat ≤ base.toNat+capacity.toNat := by
  have fits := (Oak.CNFObligation.fits_iff used roots capacity fuel).mp admit
  have first : (base+LRAT_HEADER_WORDS).toNat = base.toNat+8 := by
    change (base.toNat+8) % 4294967296 = base.toNat+8
    omega
  have addr : (base+LRAT_HEADER_WORDS+used).toNat = base.toNat+8+used.toNat := by
    rw [UInt32.toNat_add, first, Nat.mod_eq_of_lt (by omega)]
  exact ⟨addr, by rw [addr]; omega⟩

theorem state_separation (l : Layout) (used roots : UInt32) (fuel : Nat)
    (admit : cnf_obligation_fits used roots l.clauses_cap fuel = some true)
    (region : l.clauses_at.toNat+l.clauses_cap.toNat < 4294967296)
    (stateBefore : l.state_at.toNat+5 < l.clauses_at.toNat) :
    ∀ j : Nat,
      (l.state_at+STATE_CLAUSES_USED).toNat ≠ (l.clauses_at+LRAT_HEADER_WORDS+used).toNat+j ∧
      (l.state_at+STATE_CLAUSE_COUNT).toNat ≠ (l.clauses_at+LRAT_HEADER_WORDS+used).toNat+j := by
  intro j
  have addr := (layout_bounds l.clauses_at used roots l.clauses_cap fuel admit region).1
  rw [addr]
  change (l.state_at.toNat+4) % 4294967296 ≠ l.clauses_at.toNat+8+used.toNat+j ∧
    (l.state_at.toNat+5) % 4294967296 ≠ l.clauses_at.toNat+8+used.toNat+j
  have := l.clauses_at.toNat_lt
  omega

-- This is equality of the actual reducer's memory, not an assumed readback.
theorem consume_words (mem : Array UInt32) (at_ n : UInt32) (always : Bool) (es : List UInt32)
    (bound : at_.toNat + 1 + n.toNat + (literals es).length < 4294967296) :
    (consume mem at_ n always es).1 =
      writeWords mem (at_.toNat + 1 + n.toNat) (words es) := by
  induction es generalizing mem n always with
  | nil => rfl
  | cons e es ih =>
    by_cases h1 : e = 1
    · subst e
      simpa [consume, step, words, literals] using ih mem n true (by simpa [literals] using bound)
    · by_cases h0 : e = 0
      · subst e
        simpa [consume, step, words, literals] using ih mem n always (by simpa [literals] using bound)
      · have eh0 : (e != (0 : UInt32)) = true := by simpa using h0
        have eh1 : (e != (1 : UInt32)) = true := by simpa using h1
        have ls : literals (e::es) = e :: literals es := by
          simp only [literals, List.filter_cons, eh0, eh1, Bool.true_and, if_true]
        rw [ls, List.length_cons] at bound
        have inc : (n+1).toNat = n.toNat+1 := by
          change (n.toNat+1) % 4294967296 = n.toNat+1
          omega
        have first : (at_+1).toNat = at_.toNat+1 := by
          change (at_.toNat+1) % 4294967296 = at_.toNat+1
          omega
        have addr : (at_+1+n).toNat = at_.toNat+1+n.toNat := by
          rw [UInt32.toNat_add, first, Nat.mod_eq_of_lt (by omega)]
        simp only [consume, step, beq_iff_eq, h1, h0, if_false, words, ls, List.map_cons, writeWords]
        rw [ih _ (n+1) always (by rw [inc]; omega), addr, inc]
        rfl

theorem consume_read (mem : Array UInt32) (at_ n : UInt32) (always : Bool) (es : List UInt32)
    (bound : at_.toNat+1+n.toNat+(literals es).length < 4294967296)
    (room : at_.toNat+1+n.toNat+(literals es).length ≤ mem.size)
    (j : Nat) (inside : j < (words es).length) :
    (consume mem at_ n always es).1.getD (at_.toNat+1+n.toNat+j) 0 = (words es)[j] := by
  rw [consume_words mem at_ n always es bound]
  exact writeWords_read _ _ _ _ (by simpa [words] using room) inside

theorem consume_frame (mem : Array UInt32) (at_ n : UInt32) (always : Bool) (es : List UInt32)
    (bound : at_.toNat+1+n.toNat+(literals es).length < 4294967296)
    (i : Nat) (outside : i < at_.toNat+1+n.toNat ∨
      at_.toNat+1+n.toNat+(literals es).length ≤ i) :
    (consume mem at_ n always es).1.getD i 0 = mem.getD i 0 := by
  rw [consume_words mem at_ n always es bound]
  exact writeWords_outside _ _ _ _ (by simpa [words] using outside)

-- Keeping root cells outside the append interval preserves every such read.
-- The UInt32 root-address expression is explicit; validity of the source root
-- indices and construction of the layout are separate obligations.
theorem root_read_preserved (l : Layout) (mem p : Array UInt32) (at_ n r roots : UInt32)
    (always : Bool) (es : List UInt32)
    (bound : at_.toNat+1+n.toNat+(literals es).length < 4294967296)
    (outside : (l.bits_at+p.getD (rootStart p+r).toNat 0*64).toNat < at_.toNat+1+n.toNat ∨
      at_.toNat+1+n.toNat+(literals es).length ≤
        (l.bits_at+p.getD (rootStart p+r).toNat 0*64).toNat) :
    readLiteral l (consume mem at_ n always es).1 p r roots = readLiteral l mem p r roots := by
  unfold readLiteral
  rw [consume_frame mem at_ n always es bound _ outside]

-- Finalization writes the length and two counters. Keeping the counter cells
-- outside the payload preserves all the literal words through publication.
theorem commit_payload (l : Layout) (mem : Array UInt32) (at_ used n : UInt32) (j : Nat)
    (notHeader : at_.toNat ≠ j)
    (notUsed : (l.state_at+STATE_CLAUSES_USED).toNat ≠ j)
    (notCount : (l.state_at+STATE_CLAUSE_COUNT).toNat ≠ j) :
    (commit l mem at_ used n).getD j 0 = mem.getD j 0 := by
  unfold commit
  rw [Oak.LRATChecker.array_getD_set_ne _ _ _ _ _ notCount,
    Oak.LRATChecker.array_getD_set_ne _ _ _ _ _ notUsed,
    Oak.LRATChecker.array_getD_set_ne _ _ _ _ _ notHeader]

theorem commit_header (l : Layout) (mem : Array UInt32) (at_ used n : UInt32)
    (room : at_.toNat < mem.size)
    (notUsed : (l.state_at+STATE_CLAUSES_USED).toNat ≠ at_.toNat)
    (notCount : (l.state_at+STATE_CLAUSE_COUNT).toNat ≠ at_.toNat) :
    (commit l mem at_ used n).getD at_.toNat 0 = n := by
  unfold commit
  rw [Oak.LRATChecker.array_getD_set_ne _ _ _ _ _ notCount,
    Oak.LRATChecker.array_getD_set_ne _ _ _ _ _ notUsed,
    Oak.LRATChecker.array_getD_set_self _ _ _ _ room]

theorem published_payload (l : Layout) (mem : Array UInt32) (at_ used : UInt32) (es : List UInt32)
    (bound : at_.toNat+1+(literals es).length < 4294967296)
    (room : at_.toNat+1+(literals es).length ≤ mem.size)
    (j : Nat) (inside : j < (words es).length)
    (notUsed : (l.state_at+STATE_CLAUSES_USED).toNat ≠ at_.toNat+1+j)
    (notCount : (l.state_at+STATE_CLAUSE_COUNT).toNat ≠ at_.toNat+1+j) :
    let s := consume mem at_ 0 false es
    (commit l s.1 at_ used s.2.1).getD (at_.toNat+1+j) 0 = (words es)[j] := by
  dsimp only
  rw [commit_payload l _ at_ used _ _ (by omega) notUsed notCount]
  simpa using consume_read mem at_ 0 false es (by simpa using bound) (by simpa using room) j inside

theorem published_header (l : Layout) (mem : Array UInt32) (at_ used : UInt32) (es : List UInt32)
    (bound : at_.toNat+1+(literals es).length < 4294967296)
    (room : at_.toNat+1+(literals es).length ≤ mem.size)
    (notUsed : (l.state_at+STATE_CLAUSES_USED).toNat ≠ at_.toNat)
    (notCount : (l.state_at+STATE_CLAUSE_COUNT).toNat ≠ at_.toNat) :
    let s := consume mem at_ 0 false es
    ((commit l s.1 at_ used s.2.1).getD at_.toNat 0).toNat = (literals es).length := by
  dsimp only
  rw [commit_header l _ at_ used _ (by
    rw [consume_words mem at_ 0 false es (by simpa using bound), writeWords_size]; omega) notUsed notCount]
  simpa using consume_count mem at_ 0 false es (by change 0 + (literals es).length < 4294967296; omega)

-- Exact endpoint contract for the production function. Layout premises refer
-- to physical addresses; no global layout validity is inferred from them.
theorem production_record (l : Layout) (mem p : Array UInt32) (used : UInt32)
    (es : List UInt32) (fuel : Nat)
    (counter : mem.getD (l.state_at+STATE_CLAUSES_USED).toNat 0 = used)
    (admit : cnf_obligation_fits used (p.getD 2 0) l.clauses_cap (fuel+es.length+1) = some true)
    (trace : Trace l p (p.getD 2 0) (l.clauses_at+LRAT_HEADER_WORDS+used) mem 0 false 0 es)
    (bound : (l.clauses_at+LRAT_HEADER_WORDS+used).toNat+1+(literals es).length < 4294967296)
    (room : (l.clauses_at+LRAT_HEADER_WORDS+used).toNat+1+(literals es).length ≤ mem.size)
    (separate : ∀ j, j ≤ (literals es).length →
      (l.state_at+STATE_CLAUSES_USED).toNat ≠ (l.clauses_at+LRAT_HEADER_WORDS+used).toNat+j ∧
      (l.state_at+STATE_CLAUSE_COUNT).toNat ≠ (l.clauses_at+LRAT_HEADER_WORDS+used).toNat+j)
    (nonempty : 0 < (literals es).length) (noTrue : es.any (· == 1) = false) :
    ∃ out, cnf_obligation l mem p (fuel+es.length+1) = some (CNF_CLAUSE,out) ∧
      (out.getD (l.clauses_at+LRAT_HEADER_WORDS+used).toNat 0).toNat = (literals es).length ∧
      ∀ j (inside : j < (words es).length),
        out.getD ((l.clauses_at+LRAT_HEADER_WORDS+used).toNat+1+j) 0 = (words es)[j] := by
  let at_ := l.clauses_at+LRAT_HEADER_WORDS+used
  let s := consume mem at_ 0 false es
  have count : s.2.1.toNat = (literals es).length := by
    simpa [s] using (consume_count mem at_ 0 false es (by change 0+(literals es).length < 4294967296; omega))
  have positive : s.2.1 ≠ 0 := by intro h; rw [h] at count; change 0 = _ at count; omega
  have never : s.2.2 = false := by
    change (consume mem at_ 0 false es).2.2 = false
    rw [consume_always, noTrue]; rfl
  refine ⟨commit l s.1 at_ used s.2.1, ?_, ?_, ?_⟩
  · rw [production_trace l mem p used es fuel counter admit trace]
    change cnf_obligation_finish l s.1 at_ used s.2.1 s.2.2 true _ = _
    rw [never, finish_clause l s.1 at_ used s.2.1 _ positive]
  · exact published_header l mem at_ used es bound room
      (by simpa [at_] using (separate 0 (by omega)).1) (by simpa [at_] using (separate 0 (by omega)).2)
  · intro j inside
    have within : j+1 ≤ (literals es).length := by simp only [words, List.length_map] at inside; omega
    exact published_payload l mem at_ used es bound room j inside
      (by simpa [at_, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using (separate (j+1) within).1)
      (by simpa [at_, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using (separate (j+1) within).2)

theorem readPayload_exact (out : Array UInt32) (at_ : Nat) (es : List UInt32)
    (cells : ∀ j (inside : j < (words es).length), out.getD (at_+1+j) 0 = (words es)[j]) :
    readPayload out at_ (words es).length = words es := by
  apply List.ext_getElem
  · simp [readPayload]
  · intro i h1 h2
    simpa [readPayload] using cells i h2

theorem stored_semantics (assignment : Oak.RupCheck.Assignment) (out : Array UInt32)
    (at_ : Nat) (es : List UInt32)
    (header : (out.getD at_ 0).toNat = (literals es).length)
    (cells : ∀ j (inside : j < (words es).length), out.getD (at_+1+j) 0 = (words es)[j])
    (noTrue : es.any (· == 1) = false) :
    Oak.RupCheck.SatisfiesClause assignment
      ((readPayload out at_ (out.getD at_ 0).toNat).map Oak.LRATRUP.decodeWord) ↔
      es.any (Oak.CNFFolds.value assignment) = true := by
  have len : (words es).length = (literals es).length := by simp [words]
  rw [header, ← len, readPayload_exact out at_ es cells]
  simpa [words, List.map_map, Function.comp_def] using clause_meaning assignment es noTrue

end Oak.CNFObligationStore
