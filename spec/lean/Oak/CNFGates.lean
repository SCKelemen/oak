import Oak.CNFEmission
import Oak.Tseitin

/-!
Production Tseitin clause sequences. The helpers extracted from cnf.oak execute
exactly these cnf_emit calls, and their decoded clauses define the intended gate.
Allocation, folding, the final obligation, and source lowering are separate.
-/
set_option autoImplicit false
namespace Oak.CNFGates
open Oak.CNFEmission

abbrev Clause := UInt32 × UInt32 × UInt32

def binary (op g x y : UInt32) : List Clause :=
  if op == OP_AND then
    [(g ^^^ 1, x, NONE), (g ^^^ 1, y, NONE), (g, x ^^^ 1, y ^^^ 1)]
  else if op == OP_OR then
    [(g, x ^^^ 1, NONE), (g, y ^^^ 1, NONE), (g ^^^ 1, x, y)]
  else
    [(g ^^^ 1, x, y), (g ^^^ 1, x ^^^ 1, y ^^^ 1),
      (g, x ^^^ 1, y), (g, x, y ^^^ 1)]

def mux (g c t e : UInt32) : List Clause :=
  [(g ^^^ 1, c ^^^ 1, t), (g ^^^ 1, c, e),
    (g, c ^^^ 1, t ^^^ 1), (g, c, e ^^^ 1),
    (g ^^^ 1, t, e), (g, t ^^^ 1, e ^^^ 1)]

def run (l : Layout) (fuel : Nat) (mem : Array UInt32) : List Clause → Option (Unit × Array UInt32)
  | [] => some ((), mem)
  | (a, b, c) :: rest => do
      let (_, next) ← cnf_emit l mem a b c fuel
      run l fuel next rest

theorem binary_execution (l : Layout) (mem : Array UInt32) (op g x y : UInt32) (fuel : Nat) :
    cnf_emit_binary l mem op g x y fuel = run l fuel mem (binary op g x y) := by
  simp only [cnf_emit_binary, binary]
  split <;> (try split) <;> simp [run, Option.bind_assoc]

theorem mux_execution (l : Layout) (mem : Array UInt32) (g c t e : UInt32) (fuel : Nat) :
    cnf_emit_mux l mem g c t e fuel = run l fuel mem (mux g c t e) := by
  simp [cnf_emit_mux, mux, run]

/-- Exclude constants and the sentinel node (both polarities). -/
def Regular (e : UInt32) : Prop := 2 ≤ e ∧ e < 4294967294

theorem regular_flip (e : UInt32) (h : Regular e) : Regular (e ^^^ 1) := by
  have index : ((e ^^^ 1) >>> (1 : UInt32)) = e >>> 1 := by
    rw [UInt32.shiftRight_xor]
    change _ ^^^ (0 : UInt32) = _
    simp
  have natIndex := congrArg UInt32.toNat index
  simp only [UInt32.toNat_shiftRight] at natIndex
  simp only [Regular, UInt32.le_iff_toNat_le, UInt32.lt_iff_toNat_lt] at *
  change 2 ≤ e.toNat ∧ e.toNat < 4294967294 at h
  change 2 ≤ (e ^^^ 1).toNat ∧ (e ^^^ 1).toNat < 4294967294
  change (e ^^^ 1).toNat >>> 1 = e.toNat >>> 1 at natIndex
  rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow] at natIndex
  omega

theorem regular_not_none (e : UInt32) (h : Regular e) : e ≠ NONE := by
  intro he
  subst e
  have hn := h.2
  exact (by decide : ¬ ((NONE : UInt32) < 4294967294)) hn

theorem flip_value (a : Oak.RupCheck.Assignment) (e : UInt32) :
    Oak.CNFLiteral.edgeValue a (e ^^^ 1) = !Oak.CNFLiteral.edgeValue a e := by
  have index : ((e ^^^ 1) >>> (1 : UInt32)) = e >>> 1 := by
    rw [UInt32.shiftRight_xor]
    change _ ^^^ (0 : UInt32) = _
    simp
  have polarity : ((e ^^^ 1) &&& 1 == 0) = !(e &&& 1 == 0) := by
    apply Bool.eq_iff_iff.mpr
    simp [← UInt32.toNat_inj, ← Nat.mod_two_not_eq_one, Nat.xor_mod_two_eq_one]
  simp only [Oak.CNFLiteral.edgeValue, index, polarity]
  cases (e &&& 1 == 0) <;> simp

def decoded (q : Clause) : List Oak.RupCheck.Literal :=
  (edges q.1 q.2.1 q.2.2).map (fun e => Oak.LRATRUP.decodeWord (Oak.CNFLiteral.encode e))

def Satisfies (a : Oak.RupCheck.Assignment) (qs : List Clause) : Prop :=
  ∀ q ∈ qs, Oak.RupCheck.SatisfiesClause a (decoded q)

theorem clause_meaning (a : Oak.RupCheck.Assignment) (q : Clause)
    (valid : ∀ e ∈ edges q.1 q.2.1 q.2.2, 2 ≤ e) :
    Oak.RupCheck.SatisfiesClause a (decoded q) ↔
      ∃ e ∈ edges q.1 q.2.1 q.2.2, Oak.CNFLiteral.edgeValue a e = true :=
  Oak.CNFLiteral.clause_semantics a _ valid

def binaryValue (op : UInt32) (x y : Bool) : Bool :=
  if op == OP_AND then x && y else if op == OP_OR then x || y else xor x y

theorem binary_semantics (a : Oak.RupCheck.Assignment) (op g x y : UInt32)
    (hg : Regular g) (hx : Regular x) (hy : Regular y) :
    Satisfies a (binary op g x y) ↔
      Oak.CNFLiteral.edgeValue a g = binaryValue op
        (Oak.CNFLiteral.edgeValue a x) (Oak.CNFLiteral.edgeValue a y) := by
  have gn := regular_not_none g hg
  have xn := regular_not_none x hx
  have yn := regular_not_none y hy
  have gf := regular_flip g hg
  have xf := regular_flip x hx
  have yf := regular_flip y hy
  have xfn := regular_not_none _ xf
  have yfn := regular_not_none _ yf
  simp only [Satisfies, binary, binaryValue]
  split <;> (try split) <;>
    simp [decoded, edges, xn, yn, xfn, yfn, Oak.RupCheck.SatisfiesClause, Oak.CNFLiteral.literal_semantics,
      hg.1, hx.1, hy.1, gf.1, xf.1, yf.1, flip_value] <;>
    cases Oak.CNFLiteral.edgeValue a g <;>
    cases Oak.CNFLiteral.edgeValue a x <;>
    cases Oak.CNFLiteral.edgeValue a y <;> simp_all

theorem mux_semantics (a : Oak.RupCheck.Assignment) (g c t e : UInt32)
    (hg : Regular g) (hc : Regular c) (ht : Regular t) (he : Regular e) :
    Satisfies a (mux g c t e) ↔
      Oak.CNFLiteral.edgeValue a g =
        (if Oak.CNFLiteral.edgeValue a c then Oak.CNFLiteral.edgeValue a t
         else Oak.CNFLiteral.edgeValue a e) := by
  have tn := regular_not_none t ht
  have en := regular_not_none e he
  have gf := regular_flip g hg
  have cf := regular_flip c hc
  have tf := regular_flip t ht
  have ef := regular_flip e he
  have tfn := regular_not_none _ tf
  have efn := regular_not_none _ ef
  simp [Satisfies, mux, decoded, edges, tn, en, tfn, efn,
    Oak.RupCheck.SatisfiesClause, Oak.CNFLiteral.literal_semantics, hg.1, hc.1, ht.1, he.1,
    gf.1, cf.1, tf.1, ef.1, flip_value]
  cases Oak.CNFLiteral.edgeValue a g <;>
    cases Oak.CNFLiteral.edgeValue a c <;>
    cases Oak.CNFLiteral.edgeValue a t <;>
    cases Oak.CNFLiteral.edgeValue a e <;> simp_all

/-- A sequence in which every append is admitted. A normal return alone is
insufficient: cnf_emit also returns normally after setting STATE_EXCEEDED. -/
inductive Admitted (l : Layout) (fuel : Nat) :
    Array UInt32 → List Clause → Array UInt32 → Prop
  | nil (mem) : Admitted l fuel mem [] mem
  | cons {mem next out : Array UInt32} {q : Clause} {qs : List Clause}
      (room : l.clauses_at.toNat + l.clauses_cap.toNat ≤ mem.size)
      (fits : cnf_clause_fits (used l mem) (arity q.2.1 q.2.2) l.clauses_cap fuel = some true)
      (step : cnf_emit l mem q.1 q.2.1 q.2.2 fuel = some ((), next))
      (rest : Admitted l fuel next qs out) : Admitted l fuel mem (q :: qs) out

theorem admitted_run (l : Layout) (fuel : Nat) (mem out : Array UInt32) (qs : List Clause)
    (h : Admitted l fuel mem qs out) : run l fuel mem qs = some ((), out) := by
  induction h with
  | nil => rfl
  | cons room fits step rest ih => simp [run, step, ih]

def record (q : Clause) : List UInt32 :=
  arity q.2.1 q.2.2 :: (edges q.1 q.2.1 q.2.2).map Oak.CNFLiteral.encode

def words (qs : List Clause) : List UInt32 := qs.flatMap record

theorem step_used (l : Layout) (fuel : Nat) (mem next : Array UInt32) (q : Clause)
    (region : l.clauses_at.toNat + l.clauses_cap.toNat < 4294967296)
    (separate : l.state_at.toNat + 6 ≤ l.clauses_at.toNat)
    (room : l.clauses_at.toNat + l.clauses_cap.toNat ≤ mem.size)
    (fits : cnf_clause_fits (used l mem) (arity q.2.1 q.2.2) l.clauses_cap fuel = some true)
    (step : cnf_emit l mem q.1 q.2.1 q.2.2 fuel = some ((), next)) :
    (used l next).toNat = (used l mem).toNat + (record q).length := by
  have addr := addresses_exact l.clauses_at (used l mem) (arity q.2.1 q.2.2) l.clauses_cap fuel fits region
  have start := addr 0 (by simp)
  simp only [UInt32.add_zero, UInt32.toNat_zero, Nat.add_zero] at start
  have exact := emitted_exact l mem q.1 q.2.1 q.2.2 fuel fits (by intro k hk; rw [addr k hk, start])
  rw [exact, Option.some.injEq, Prod.mk.injEq] at step
  have i4 : (l.state_at + STATE_CLAUSES_USED).toNat = l.state_at.toNat + 4 := by
    apply Oak.LRATChecker.add_exact
    change l.state_at.toNat + 4 < 4294967296
    omega
  have i5 : (l.state_at + STATE_CLAUSE_COUNT).toNat = l.state_at.toNat + 5 := by
    apply Oak.LRATChecker.add_exact
    change l.state_at.toNat + 5 < 4294967296
    omega
  rw [← step.2]
  unfold used emitted
  dsimp only
  rw [Oak.LRATChecker.array_getD_set_ne _ _ _ _ _ (by rw [i4, i5]; omega)]
  rw [Oak.LRATChecker.array_getD_set_self _ _ _ _ (by rw [writeWords_size, i4]; omega)]
  have advance := (counters_no_wrap (used l mem) (arity q.2.1 q.2.2) l.clauses_cap 0 fuel fits (by simp)).1
  simpa only [used, record, List.length_cons, List.length_map, edges_length, Nat.add_assoc] using advance

/-- Later admitted clauses cannot overwrite any earlier payload word. -/
theorem admitted_prefix (l : Layout) (fuel : Nat) (mem out : Array UInt32) (qs : List Clause)
    (region : l.clauses_at.toNat + l.clauses_cap.toNat < 4294967296)
    (separate : l.state_at.toNat + 6 ≤ l.clauses_at.toNat)
    (h : Admitted l fuel mem qs out) (k : Nat)
    (lo : l.clauses_at.toNat + 8 ≤ k)
    (hi : k < l.clauses_at.toNat + 8 + (used l mem).toNat) :
    out.getD k 0 = mem.getD k 0 := by
  induction h with
  | nil => rfl
  | @cons mem next out q qs room fits step rest ih =>
    have advance := step_used l fuel mem next q region separate room fits step
    rw [ih (by omega)]
    apply production_frame l mem next q.1 q.2.1 q.2.2 fuel k fits region step (Or.inl hi)
    · have addr := Oak.LRATChecker.add_exact l.state_at STATE_CLAUSES_USED (by change l.state_at.toNat + 4 < 4294967296; omega)
      rw [addr]; change l.state_at.toNat + 4 ≠ k; omega
    · have addr := Oak.LRATChecker.add_exact l.state_at STATE_CLAUSE_COUNT (by change l.state_at.toNat + 5 < 4294967296; omega)
      rw [addr]; change l.state_at.toNat + 5 ≠ k; omega

/-- Every length and literal word survives in the final buffer, in order. -/
theorem admitted_words (l : Layout) (fuel : Nat) (mem out : Array UInt32) (qs : List Clause)
    (region : l.clauses_at.toNat + l.clauses_cap.toNat < 4294967296)
    (separate : l.state_at.toNat + 6 ≤ l.clauses_at.toNat)
    (h : Admitted l fuel mem qs out) :
    ∀ j (hj : j < (words qs).length),
      out.getD (l.clauses_at.toNat + 8 + (used l mem).toNat + j) 0 = (words qs)[j] := by
  induction h with
  | nil => simp [words]
  | @cons mem next out q qs room fits step rest ih =>
    intro j hj
    have advance := step_used l fuel mem next q region separate room fits step
    have ws : words (q :: qs) = record q ++ words qs := by simp [words]
    simp only [ws] at hj ⊢
    by_cases before : j < (record q).length
    · rw [List.getElem_append_left before]
      rw [admitted_prefix l fuel next out qs region separate rest _ (by omega) (by omega)]
      exact production_record l mem next q.1 q.2.1 q.2.2 fuel fits region room separate step j
        (by simpa [record, Nat.add_comm] using before)
    · rw [List.getElem_append_right (by omega)]
      have tail := ih (j - (record q).length) (by simp only [List.length_append] at hj; omega)
      have pos : l.clauses_at.toNat + 8 + (used l next).toNat + (j - (record q).length) =
          l.clauses_at.toNat + 8 + (used l mem).toNat + j := by omega
      simpa only [pos] using tail

/-- Read the payloads at the proved record boundaries in the final buffer.
The length headers at these boundaries are separately covered by admitted_words. -/
def readRecords (out : Array UInt32) (start : Nat) : List Clause → List (List Oak.RupCheck.Literal)
  | [] => []
  | q :: qs =>
      (readPayload out start (edges q.1 q.2.1 q.2.2).length).map Oak.LRATRUP.decodeWord ::
        readRecords out (start + (record q).length) qs

theorem read_records_of_words (out : Array UInt32) (start : Nat) (qs : List Clause)
    (h : ∀ j (hj : j < (words qs).length), out.getD (start + j) 0 = (words qs)[j]) :
    readRecords out start qs = qs.map decoded := by
  induction qs generalizing start with
  | nil => rfl
  | cons q qs ih =>
    have ws : words (q :: qs) = record q ++ words qs := by simp [words]
    have head : readPayload out start (edges q.1 q.2.1 q.2.2).length =
        (edges q.1 q.2.1 q.2.2).map Oak.CNFLiteral.encode := by
      apply List.ext_getElem
      · simp [readPayload]
      · intro i hi hj
        have inside : i < (edges q.1 q.2.1 q.2.2).length := by simpa using hj
        have cell := h (i + 1) (by simp [ws, record]; omega)
        simp only [ws] at cell
        rw [List.getElem_append_left (by simp [record]; omega)] at cell
        simpa [readPayload, record, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using cell
    have tail : ∀ j (hj : j < (words qs).length),
        out.getD (start + (record q).length + j) 0 = (words qs)[j] := by
      intro j hj
      have cell := h ((record q).length + j) (by simp only [ws, List.length_append]; omega)
      simp only [ws] at cell
      rw [List.getElem_append_right (by omega)] at cell
      simpa [Nat.add_assoc] using cell
    simp only [readRecords, List.map_cons, head, List.map_map, decoded, ih _ tail]
    rfl

def BufferSatisfies (a : Oak.RupCheck.Assignment) (out : Array UInt32)
    (start : Nat) (qs : List Clause) : Prop :=
  ∀ cl ∈ readRecords out start qs, Oak.RupCheck.SatisfiesClause a cl

theorem admitted_semantics (l : Layout) (fuel : Nat) (mem out : Array UInt32) (qs : List Clause)
    (region : l.clauses_at.toNat + l.clauses_cap.toNat < 4294967296)
    (separate : l.state_at.toNat + 6 ≤ l.clauses_at.toNat)
    (h : Admitted l fuel mem qs out) (a : Oak.RupCheck.Assignment) :
    BufferSatisfies a out (l.clauses_at.toNat + 8 + (used l mem).toNat) qs ↔ Satisfies a qs := by
  unfold BufferSatisfies
  rw [read_records_of_words _ _ _ (admitted_words l fuel mem out qs region separate h)]
  constructor
  · intro sat q member
    exact sat (decoded q) (List.mem_map.mpr ⟨q, member, rfl⟩)
  · intro sat cl member
    obtain ⟨q, hq, heq⟩ := List.mem_map.mp member
    rw [← heq]
    exact sat q hq

/-- The actual binary helper and the meaning of its final stored clauses. -/
theorem binary_production (l : Layout) (fuel : Nat) (mem out : Array UInt32)
    (op g x y : UInt32) (a : Oak.RupCheck.Assignment)
    (region : l.clauses_at.toNat + l.clauses_cap.toNat < 4294967296)
    (separate : l.state_at.toNat + 6 ≤ l.clauses_at.toNat)
    (h : Admitted l fuel mem (binary op g x y) out)
    (hg : Regular g) (hx : Regular x) (hy : Regular y) :
    cnf_emit_binary l mem op g x y fuel = some ((), out) ∧
      (BufferSatisfies a out (l.clauses_at.toNat + 8 + (used l mem).toNat) (binary op g x y) ↔
        Oak.CNFLiteral.edgeValue a g = binaryValue op
          (Oak.CNFLiteral.edgeValue a x) (Oak.CNFLiteral.edgeValue a y)) := by
  constructor
  · rw [binary_execution]; exact admitted_run l fuel mem out _ h
  · exact (admitted_semantics l fuel mem out _ region separate h a).trans
      (binary_semantics a op g x y hg hx hy)

/-- The actual mux helper and the meaning of its final stored clauses. -/
theorem mux_production (l : Layout) (fuel : Nat) (mem out : Array UInt32)
    (g c t e : UInt32) (a : Oak.RupCheck.Assignment)
    (region : l.clauses_at.toNat + l.clauses_cap.toNat < 4294967296)
    (separate : l.state_at.toNat + 6 ≤ l.clauses_at.toNat)
    (h : Admitted l fuel mem (mux g c t e) out)
    (hg : Regular g) (hc : Regular c) (ht : Regular t) (he : Regular e) :
    cnf_emit_mux l mem g c t e fuel = some ((), out) ∧
      (BufferSatisfies a out (l.clauses_at.toNat + 8 + (used l mem).toNat) (mux g c t e) ↔
        Oak.CNFLiteral.edgeValue a g =
          (if Oak.CNFLiteral.edgeValue a c then Oak.CNFLiteral.edgeValue a t
           else Oak.CNFLiteral.edgeValue a e)) := by
  constructor
  · rw [mux_execution]; exact admitted_run l fuel mem out _ h
  · exact (admitted_semantics l fuel mem out _ region separate h a).trans
      (mux_semantics a g c t e hg hc ht he)

end Oak.CNFGates
