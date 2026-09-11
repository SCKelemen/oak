namespace Oak.GraphemeBreak

/-! # Extended grapheme cluster boundaries (UAX #29)

Model for `stdlib/grapheme.oak`: the Grapheme_Cluster_Boundary_Rules of
Unicode Standard Annex #29 (section 3.1.1, rules GB1–GB13 and GB999, in the
Unicode 15.1+ form with GB9c) and the state machine the library runs.

Two definitions, one theorem:

* `ruleBreak history cur` is the **specification**: the rules exactly as the
  annex words them, tried in order, each rule reading the text before the
  candidate position through a scan (`history` is that text most recent
  first). GB9c scans back over the InCB Extend/Linker run to the consonant,
  GB11 back over the Extend run to the pictographic base, GB12/GB13 count the
  Regional_Indicator run.
* `machineBreak history cur` is the **implementation**: `grapheme_breaks`
  applied to `grapheme_advance` folded over the text, i.e. a bounded state
  (`prev`, `riRun`, `pict`, `conjunct`) instead of scans. The Oak functions
  are line-for-line transliterations of `breaks` and `advance`
  (`GraphemeState` has the same four fields with the same meaning, and the
  class constants match the `GCB` constructors in order).
* `machine_agrees` proves the two decide every position identically, for
  every history of well-formed symbols. Well-formedness (`Sym.WF`) is the
  shape the Unicode Character Database guarantees and the library's table
  is checked against in `compiler/e2e_stdlib_grapheme_laws_test.go`: an
  Extended_Pictographic or InCB=Consonant scalar has class Other, an
  InCB=Linker scalar has class Extend, an InCB=Extend scalar has class
  Extend or ZWJ.

The same Go test enumerates every symbol sequence up to length five, runs
the compiled Oak machine, and compares each decision with an independent
transliteration of `ruleBreak`, so the proof, the Go oracle, and the
executable agree on the same law. -/

/-- Grapheme_Cluster_Break values (UAX #29 Table 2). The constructor order is
    the numbering of `GB_OTHER .. GB_LVT` in `grapheme.oak`. -/
inductive GCB
  | other | cr | lf | control | extend | zwj | ri | prepend | spacingMark
  | l | v | t | lv | lvt
  deriving DecidableEq, Repr

/-- Indic_Conjunct_Break values (`INCB_NONE .. INCB_LINKER`). -/
inductive InCB
  | none | consonant | extend | linker
  deriving DecidableEq, Repr

/-- The properties of one scalar that the rules read. -/
structure Sym where
  gcb : GCB
  incb : InCB
  pict : Bool
  deriving DecidableEq, Repr

/-- The shape of the Unicode data: pictographic and consonant scalars are
    class Other, linkers are Extend, InCB=Extend scalars are Extend or ZWJ. -/
def Sym.WF (s : Sym) : Prop :=
  (s.pict = true → s.gcb = .other) ∧
  (s.incb = .consonant → s.gcb = .other) ∧
  (s.incb = .linker → s.gcb = .extend) ∧
  (s.incb = .extend → s.gcb = .extend ∨ s.gcb = .zwj)

def isControl (g : GCB) : Bool := g == .control || g == .cr || g == .lf

/-! ## The specification: scans over the history -/

/-- The Regional_Indicator run ending the history (GB12, GB13). -/
def riRun : List Sym → Nat
  | [] => 0
  | s :: rest => if s.gcb == .ri then riRun rest + 1 else 0

/-- Drop the Extend run at the head of the history. -/
def dropExtend : List Sym → List Sym
  | s :: rest => if s.gcb == .extend then dropExtend rest else s :: rest
  | [] => []

/-- `\p{Extended_Pictographic} Extend*` ends the history (the GB11 base). -/
def pictBase (history : List Sym) : Bool :=
  match dropExtend history with
  | p :: _ => p.pict
  | [] => false

/-- `\p{Extended_Pictographic} Extend* ZWJ` ends the history (GB11's left side). -/
def pictZwj : List Sym → Bool
  | s :: rest => s.gcb == .zwj && pictBase rest
  | [] => false

/-- Scan back over the InCB Extend/Linker run: `some seen` when the run ends
    at an InCB=Consonant (`seen` records whether the run held a Linker),
    `none` otherwise. -/
def conjScan : List Sym → Bool → Option Bool
  | [], _ => none
  | s :: rest, seen =>
    if s.incb == .linker then conjScan rest true
    else if s.incb == .extend then conjScan rest seen
    else if s.incb == .consonant then some seen
    else none

/-- `\p{InCB=Consonant} [\p{InCB=Extend} \p{InCB=Linker}]* \p{InCB=Linker}
    [\p{InCB=Extend} \p{InCB=Linker}]*` ends the history (GB9c's left side). -/
def conjLinked (history : List Sym) : Bool :=
  conjScan history false == some true

/-- The Grapheme_Cluster_Boundary_Rules, in the annex's order, deciding
    whether a boundary falls between `history` (most recent first) and `cur`.
    https://www.unicode.org/reports/tr29/#Grapheme_Cluster_Boundary_Rules -/
def ruleBreak (history : List Sym) (cur : Sym) : Bool :=
  match history with
  | [] => true                                                        -- GB1: sot ÷
  | prev :: _ =>
    if prev.gcb == .cr && cur.gcb == .lf then false                    -- GB3
    else if isControl prev.gcb then true                               -- GB4
    else if isControl cur.gcb then true                                -- GB5
    else if prev.gcb == .l &&
        (cur.gcb == .l || cur.gcb == .v || cur.gcb == .lv || cur.gcb == .lvt) then false -- GB6
    else if (prev.gcb == .lv || prev.gcb == .v) && (cur.gcb == .v || cur.gcb == .t) then false -- GB7
    else if (prev.gcb == .lvt || prev.gcb == .t) && cur.gcb == .t then false -- GB8
    else if cur.gcb == .extend || cur.gcb == .zwj then false           -- GB9
    else if cur.gcb == .spacingMark then false                         -- GB9a
    else if prev.gcb == .prepend then false                            -- GB9b
    else if conjLinked history && cur.incb == .consonant then false    -- GB9c
    else if pictZwj history && cur.pict then false                     -- GB11
    else if prev.gcb == .ri && cur.gcb == .ri && riRun history % 2 == 1 then false -- GB12, GB13
    else true                                                          -- GB999

/-! ## The implementation: a bounded state -/

/-- `GraphemeState` in `grapheme.oak`. -/
structure State where
  prev : GCB
  riRun : Nat
  pict : Nat
  conjunct : Nat
  deriving DecidableEq, Repr

/-- `grapheme_initial`. -/
def initial : State := ⟨.other, 0, 0, 0⟩

/-- `grapheme_breaks`. -/
def breaks (st : State) (cur : Sym) : Bool :=
  if st.prev == .cr && cur.gcb == .lf then false
  else if isControl st.prev then true
  else if isControl cur.gcb then true
  else if st.prev == .l &&
      (cur.gcb == .l || cur.gcb == .v || cur.gcb == .lv || cur.gcb == .lvt) then false
  else if (st.prev == .lv || st.prev == .v) && (cur.gcb == .v || cur.gcb == .t) then false
  else if (st.prev == .lvt || st.prev == .t) && cur.gcb == .t then false
  else if cur.gcb == .extend || cur.gcb == .zwj then false
  else if cur.gcb == .spacingMark then false
  else if st.prev == .prepend then false
  else if st.conjunct == 2 && cur.incb == .consonant then false
  else if st.pict == 2 && cur.pict then false
  else if st.prev == .ri && cur.gcb == .ri && st.riRun % 2 == 1 then false
  else true

/-- `grapheme_advance`. -/
def advance (st : State) (cur : Sym) : State :=
  { prev := cur.gcb
    riRun := if cur.gcb == .ri then st.riRun + 1 else 0
    pict := if cur.pict then 1
      else if st.pict == 1 && cur.gcb == .extend then 1
      else if st.pict == 1 && cur.gcb == .zwj then 2
      else 0
    conjunct := if cur.incb == .consonant then 1
      else if cur.incb == .linker && st.conjunct ≥ 1 then 2
      else if cur.incb == .extend && st.conjunct ≥ 1 then st.conjunct
      else 0 }

/-- The state after the history: the oldest scalar is consumed first, which
    is the order `grapheme_next` folds `grapheme_advance` over the text. -/
def run : List Sym → State
  | [] => initial
  | s :: rest => advance (run rest) s

/-- The library's decision: GB1 at the start, otherwise `breaks` on the state. -/
def machineBreak (history : List Sym) (cur : Sym) : Bool :=
  match history with
  | [] => true
  | _ :: _ => breaks (run history) cur

/-! ## Correspondence: each state field is the scan it stands for -/

theorem run_prev (s : Sym) (rest : List Sym) : (run (s :: rest)).prev = s.gcb := by
  simp [run, advance]

theorem run_riRun : ∀ history : List Sym, (run history).riRun = riRun history
  | [] => rfl
  | s :: rest => by
    simp only [run, advance, riRun]
    rw [run_riRun rest]

/-- The pictographic state as a scan: 2 for `Pict Extend* ZWJ`, 1 for
    `Pict Extend*`, 0 otherwise. -/
def pictState (history : List Sym) : Nat :=
  if pictZwj history then 2 else if pictBase history then 1 else 0

theorem pictBase_cons_of_ne {s : Sym} (rest : List Sym) (h : s.gcb ≠ .extend) :
    pictBase (s :: rest) = s.pict := by
  have hb : (s.gcb == .extend) = false := by
    cases hg : s.gcb <;> simp_all
  simp [pictBase, dropExtend, hb]

theorem pictBase_cons_extend {s : Sym} (rest : List Sym) (h : s.gcb = .extend) :
    pictBase (s :: rest) = pictBase rest := by
  simp [pictBase, dropExtend, h]

/-- Under a ZWJ head the base scan fails: a ZWJ is not pictographic (WF). -/
theorem pictBase_of_pictZwj (history : List Sym) (wf : ∀ s ∈ history, s.WF)
    (h : pictZwj history = true) : pictBase history = false := by
  cases history with
  | nil => simp [pictZwj] at h
  | cons z rest =>
    have hz : z.gcb = .zwj := by
      simp only [pictZwj, Bool.and_eq_true, beq_iff_eq] at h
      exact h.1
    have hne : z.gcb ≠ .extend := by rw [hz]; decide
    rw [pictBase_cons_of_ne rest hne]
    have hwf := wf z (List.mem_cons_self ..)
    cases hp : z.pict with
    | false => rfl
    | true =>
      have := hwf.1 hp
      rw [hz] at this
      cases this

theorem pictState_eq_one (history : List Sym) (wf : ∀ s ∈ history, s.WF) :
    (pictState history == 1) = pictBase history := by
  unfold pictState
  cases hz : pictZwj history with
  | true =>
    rw [pictBase_of_pictZwj history wf hz]
    rfl
  | false =>
    cases pictBase history <;> rfl

theorem run_pict : ∀ history : List Sym, (∀ s ∈ history, s.WF) →
    (run history).pict = pictState history
  | [], _ => rfl
  | s :: rest, wf => by
    have wfRest : ∀ x ∈ rest, x.WF := fun x hx => wf x (List.mem_cons_of_mem s hx)
    have ih := run_pict rest wfRest
    have hwf := wf s (List.mem_cons_self ..)
    have key := pictState_eq_one rest wfRest
    simp only [run, advance]
    rw [ih, key]
    cases hp : s.pict with
    | true =>
      have ho : s.gcb = .other := hwf.1 hp
      have hne : s.gcb ≠ .extend := by rw [ho]; decide
      simp [pictState, pictZwj, pictBase_cons_of_ne rest hne, ho, hp]
    | false =>
      cases hg : s.gcb with
      | extend =>
        simp only [pictState, pictZwj, pictBase_cons_extend rest hg, hg]
        cases pictBase rest <;> simp
      | zwj =>
        have hne : s.gcb ≠ .extend := by rw [hg]; decide
        simp only [pictState, pictZwj, pictBase_cons_of_ne rest hne, hg, hp]
        cases pictBase rest <;> simp
      | _ =>
        have hne : s.gcb ≠ .extend := by rw [hg]; decide
        simp [pictState, pictZwj, pictBase_cons_of_ne rest hne, hg, hp]

/-- The conjunct state as a scan: 2 once the run back to a consonant held a
    linker, 1 when it reached a consonant without one, 0 otherwise. -/
def conjState (history : List Sym) : Nat :=
  match conjScan history false with
  | some true => 2
  | some false => 1
  | none => 0

/-- The `seen` flag only ever joins in: scanning with it set is scanning
    without it and forcing the answer. -/
theorem conjScan_seen : ∀ (history : List Sym) (seen : Bool),
    conjScan history seen = (conjScan history false).map (fun b => b || seen)
  | [], _ => rfl
  | s :: rest, seen => by
    simp only [conjScan]
    cases hi : s.incb with
    | linker =>
      simp only [BEq.rfl, if_true]
      rw [conjScan_seen rest true]
      cases conjScan rest false with
      | none => rfl
      | some b => simp
    | extend =>
      simp
      exact conjScan_seen rest seen
    | consonant => simp
    | none => simp

theorem run_conjunct : ∀ history : List Sym, (run history).conjunct = conjState history
  | [] => rfl
  | s :: rest => by
    have ih := run_conjunct rest
    simp only [run, advance]
    rw [ih]
    cases hi : s.incb with
    | none => simp [conjState, conjScan, hi]
    | consonant => simp [conjState, conjScan, hi]
    | extend =>
      simp only [conjState, conjScan, hi]
      simp
      cases conjScan rest false with
      | none => simp
      | some b => cases b <;> simp
    | linker =>
      simp only [conjState, conjScan, hi]
      simp
      rw [conjScan_seen rest true]
      cases conjScan rest false with
      | none => simp
      | some b => cases b <;> simp

theorem conjState_eq_two (history : List Sym) : (conjState history == 2) = conjLinked history := by
  unfold conjState conjLinked
  cases conjScan history false with
  | none => rfl
  | some b => cases b <;> rfl

theorem pictState_eq_two (history : List Sym) : (pictState history == 2) = pictZwj history := by
  unfold pictState
  cases pictZwj history with
  | true => rfl
  | false => cases pictBase history <;> rfl

/-- The library decides every position exactly as the rules do. -/
theorem machine_agrees (history : List Sym) (cur : Sym) (wf : ∀ s ∈ history, s.WF) :
    machineBreak history cur = ruleBreak history cur := by
  cases history with
  | nil => rfl
  | cons prev rest =>
    simp only [machineBreak, breaks, ruleBreak]
    rw [run_prev, run_riRun, run_conjunct, run_pict (prev :: rest) wf, conjState_eq_two,
      pictState_eq_two]

end Oak.GraphemeBreak
