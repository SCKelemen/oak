/-! # Compiler correspondence for the RV64 checker's register moves

The RV64 seam checker (`asm/rv64_check.go`) keeps facts about integer
registers: the span a register bases (`rvSpan`, naming the raw length
register it was bound with), a normalized copy of a span's length
(`lenNorm`: the register holds the length zero-extended, mapped to the raw
register it names), a parked copy of a raw length register (`lenAlias`),
a constant (`consts`), the region a register addresses (`regions`), and
the raw length registers that have been written since binding (`rawDead`).
On every write `forgetRegister` drops what the register's old value
supported; a raw length register written marks itself dead and the proven
minimum of the spans it measured lapses, while the copies that name it
stay, the length of a span never changing. `deriveShift`'s `addi rd, rs,
0` (mv) then copies what the source held, read from the snapshot taken
before the write: a normalized length, a constant, a span base, a raw
length (canonicalized through an alias), a region.

This module transliterates both — the Go is maintained line for line with
them — and proves them sound (`mv_sound`): whatever the facts said of the
registers before the move, the maintained facts say after it, against a
fixed world of spans and regions in memory with one length per raw name.
`asm/rv64_span_alias_refinement_test.go` renders the Go's maintenance of
the states below as the examples stated at the end.

Registers are numbered as the Go numbers them (`x0` = 0, hard-wired zero);
a 32-bit read is the low 32 bits. The index, scaled, remaining-count, and
difference facts the write also forgets are outside this model: `mv`
copies none of them. -/

namespace Oak.RiscVSpanAlias

abbrev Reg := Nat

/-- `asm.rvRegion`, as the alias rule copies it. -/
structure Region where
  size : Int
  writable : Bool
  deriving Repr, DecidableEq

/-- `asm.rvSpan`: the raw length register the span was bound with, its
    element size, writability, and proven minimum length. -/
structure Span where
  rawLen : Reg
  elem : Int
  writable : Bool
  hasMin : Bool
  minLen : Int
  deriving Repr, DecidableEq

/-- The checker's register facts the move rule maintains. -/
structure Facts where
  spans : List (Reg × Span)
  lenNorm : List (Reg × Reg)
  lenAlias : List (Reg × Reg)
  consts : List (Reg × Int)
  regions : List (Reg × Region)
  rawDead : List Reg
  deriving Repr, DecidableEq

def lookupReg {α : Type} (l : List (Reg × α)) (r : Reg) : Option α :=
  (l.find? (fun p => p.1 == r)).map Prod.snd

def insertReg {α : Type} (l : List (Reg × α)) (r : Reg) (v : α) : List (Reg × α) :=
  (r, v) :: l.filter (fun p => p.1 != r)

def deleteReg {α : Type} (l : List (Reg × α)) (r : Reg) : List (Reg × α) :=
  l.filter (fun p => p.1 != r)

/-- `forgetRegister`, over these facts: the register's own facts go; a span
    measured by it loses its proven minimum and the register is dead as a
    raw length. -/
def forget (st : Facts) (d : Reg) : Facts :=
  let spans := (deleteReg st.spans d).map (fun p =>
    (p.1, if p.2.rawLen == d then { p.2 with hasMin := false } else p.2))
  { spans := spans,
    lenNorm := deleteReg st.lenNorm d,
    lenAlias := deleteReg st.lenAlias d,
    consts := deleteReg st.consts d,
    regions := deleteReg st.regions d,
    rawDead := if spans.any (fun p => p.2.rawLen == d) then d :: st.rawDead else st.rawDead }

/-- `rvSnapshot.rawLen`: the register holds a span's raw length — a parked
    copy, or the bound register itself while it is not dead. -/
def rawLen (pre : Facts) (n : Reg) : Bool :=
  (lookupReg pre.lenAlias n).isSome ||
    (!pre.rawDead.contains n && pre.spans.any (fun p => p.2.rawLen == n))

/-- `rvSnapshot.canonicalRaw`: the bound raw register a copy names. -/
def canonicalRaw (pre : Facts) (n : Reg) : Reg :=
  match lookupReg pre.lenAlias n with
  | some raw => raw
  | none => n

/-- `deriveShift`'s `addi rd, rs, 0`, reading the snapshot `pre` and
    writing the forgotten state `st`, in the Go's order: a normalized
    length, a constant, a span base, a raw length, a region. -/
def aliasNorm (st pre : Facts) (d s : Reg) : Facts :=
  match lookupReg pre.lenNorm s with
  | some raw => { st with lenNorm := insertReg st.lenNorm d raw }
  | none => st

def aliasConst (st pre : Facts) (d s : Reg) : Facts :=
  match lookupReg pre.consts s with
  | some k => { st with consts := insertReg st.consts d k }
  | none => st

def aliasSpan (st pre : Facts) (d s : Reg) : Facts :=
  match lookupReg pre.spans s with
  | some sp => if d ≠ s then { st with spans := insertReg st.spans d sp } else st
  | none => st

def aliasRaw (st pre : Facts) (d s : Reg) : Facts :=
  if rawLen pre s && d != s then { st with lenAlias := insertReg st.lenAlias d (canonicalRaw pre s) } else st

def aliasRegion (st pre : Facts) (d s : Reg) : Facts :=
  match lookupReg pre.regions s with
  | some e => if d ≠ s then { st with regions := insertReg st.regions d e } else st
  | none => st

/-- The whole `addi rd, rs, 0` case: from `x0` it is `li rd, 0`. -/
def alias (st pre : Facts) (d s : Reg) : Facts :=
  if s = 0 then { st with consts := insertReg st.consts d 0 } else
  aliasRegion (aliasRaw (aliasSpan (aliasConst (aliasNorm st pre d s) pre d s) pre d s) pre d s) pre d s

/-- The checker at `mv xD, xS`: nothing for `x0`; otherwise the write
    forgets and the move aliases from the snapshot before it. -/
def mv (st : Facts) (d s : Reg) : Facts :=
  if d = 0 then st else alias (forget st d) st d s

/-! ## Meaning -/

abbrev RegFile := Reg → Int

/-- The low 32 bits: a raw length register is the psABI-widened `u32`. -/
def w (σ : RegFile) (r : Reg) : Int := σ r % 4294967296

/-- What memory says, fixed across a move: `span addr len elem writable`
    and `region addr e`; and `len n`, the length of the span bound with
    raw register `n` — a name, since the length never changes. -/
structure World where
  span : Int → Int → Int → Bool → Prop
  region : Int → Region → Prop
  len : Reg → Int

def SpanMeans (W : World) (σ : RegFile) (b : Reg) (sp : Span) : Prop :=
  W.span (σ b) (W.len sp.rawLen) sp.elem sp.writable ∧
    (sp.hasMin = true → sp.minLen ≤ W.len sp.rawLen)

/-- Every fact holds of the register file: bases address their spans;
    a normalized copy holds the length; a parked raw copy holds it in its
    low 32 bits; constants and regions as stated; and a bound raw length
    register not yet dead still holds its length. -/
def Means (W : World) (σ : RegFile) (st : Facts) : Prop :=
  (∀ p ∈ st.spans, SpanMeans W σ p.1 p.2) ∧
  (∀ p ∈ st.lenNorm, σ p.1 = W.len p.2) ∧
  (∀ p ∈ st.lenAlias, w σ p.1 = W.len p.2) ∧
  (∀ p ∈ st.consts, σ p.1 = p.2) ∧
  (∀ p ∈ st.regions, W.region (σ p.1) p.2) ∧
  (∀ p ∈ st.spans, ¬ p.2.rawLen ∈ st.rawDead → w σ p.2.rawLen = W.len p.2.rawLen)

def WritesOnly (σ σ' : RegFile) (d : Reg) : Prop := ∀ r, r ≠ d → σ' r = σ r

/-! ## Lemmas on the maps -/

theorem mem_deleteReg {α : Type} {l : List (Reg × α)} {d : Reg} {p : Reg × α}
    (h : p ∈ deleteReg l d) : p ∈ l ∧ p.1 ≠ d := by
  unfold deleteReg at h
  rw [List.mem_filter] at h
  exact ⟨h.1, bne_iff_ne.mp h.2⟩

theorem mem_insertReg {α : Type} {l : List (Reg × α)} {d : Reg} {v : α} {p : Reg × α}
    (h : p ∈ insertReg l d v) : p = (d, v) ∨ (p ∈ l ∧ p.1 ≠ d) := by
  unfold insertReg at h
  rw [List.mem_cons, List.mem_filter] at h
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr ⟨h.1, bne_iff_ne.mp h.2⟩

theorem lookupReg_mem {α : Type} {l : List (Reg × α)} {s : Reg} {v : α}
    (h : lookupReg l s = some v) : (s, v) ∈ l := by
  unfold lookupReg at h
  rw [Option.map_eq_some_iff] at h
  obtain ⟨p, hfind, hv⟩ := h
  have hmem := List.mem_of_find?_eq_some hfind
  have hp := List.find?_some hfind
  have h1 : p.1 = s := by simpa using hp
  have : p = (s, v) := Prod.ext h1 hv
  rw [← this]; exact hmem

theorem w_eq_of_eq {σ σ' : RegFile} {r : Reg} (h : σ' r = σ r) : w σ' r = w σ r := by
  unfold w; rw [h]

/-- A span after `forget`: it was there, its base is not `d`, and it is
    the old span with the minimum dropped when `d` measured it. -/
theorem mem_forget_spans {st : Facts} {d : Reg} {p : Reg × Span} (h : p ∈ (forget st d).spans) :
    ∃ q ∈ st.spans, q.1 ≠ d ∧ p.1 = q.1 ∧ p.2.rawLen = q.2.rawLen ∧ p.2.elem = q.2.elem ∧
      p.2.writable = q.2.writable ∧ p.2.minLen = q.2.minLen ∧
      (p.2.hasMin = true → q.2.hasMin = true) ∧ (q.2.rawLen = d → p.2.hasMin = false) := by
  unfold forget at h
  simp only [List.mem_map] at h
  obtain ⟨q, hq, rfl⟩ := h
  obtain ⟨hq, hne⟩ := mem_deleteReg hq
  refine ⟨q, hq, hne, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only
  · split <;> rfl
  · split <;> rfl
  · split <;> rfl
  · split <;> rfl
  · split <;> simp
  · intro hd; simp [hd]

/-- After `forget`, `d` is dead as a raw length whenever a remaining span
    names it. -/
theorem forget_rawDead_self {st : Facts} {d : Reg} {p : Reg × Span}
    (hp : p ∈ (forget st d).spans) (hd : p.2.rawLen = d) : d ∈ (forget st d).rawDead := by
  unfold forget
  simp only
  have hany : ((deleteReg st.spans d).map (fun p => (p.1, if p.2.rawLen == d then { p.2 with hasMin := false } else p.2))).any (fun p => p.2.rawLen == d) = true := by
    rw [List.any_eq_true]
    refine ⟨p, ?_, by simp [hd]⟩
    unfold forget at hp; simpa using hp
  rw [if_pos hany]
  exact List.mem_cons_self

theorem forget_rawDead_mono {st : Facts} {d n : Reg} (h : n ∈ st.rawDead) : n ∈ (forget st d).rawDead := by
  unfold forget; simp only
  split
  · exact List.mem_cons_of_mem _ h
  · exact h

/-! ## Soundness -/

theorem forget_sound {W : World} {σ σ' : RegFile} {st : Facts} {d : Reg}
    (hw : WritesOnly σ σ' d) (h : Means W σ st) : Means W σ' (forget st d) := by
  obtain ⟨hs, hn, ha, hc, hr, hl⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p hp
    obtain ⟨q, hq, hne, h1, hraw, helem, hwr, hmin, hhas, _⟩ := mem_forget_spans hp
    obtain ⟨hspan, hminq⟩ := hs q hq
    refine ⟨?_, ?_⟩
    · rw [h1, hw q.1 hne, hraw, helem, hwr]; exact hspan
    · intro hm; rw [hmin, hraw]; exact hminq (hhas hm)
  · intro p hp; obtain ⟨hp, hne⟩ := mem_deleteReg hp; rw [hw p.1 hne]; exact hn p hp
  · intro p hp; obtain ⟨hp, hne⟩ := mem_deleteReg hp; rw [w_eq_of_eq (hw p.1 hne)]; exact ha p hp
  · intro p hp; obtain ⟨hp, hne⟩ := mem_deleteReg hp; rw [hw p.1 hne]; exact hc p hp
  · intro p hp; obtain ⟨hp, hne⟩ := mem_deleteReg hp; rw [hw p.1 hne]; exact hr p hp
  · intro p hp hdead
    obtain ⟨q, hq, _, _, hraw, _, _, _, _, _⟩ := mem_forget_spans hp
    have hnd : p.2.rawLen ≠ d := fun hd => hdead (by rw [hd]; exact forget_rawDead_self hp hd)
    have hqdead : ¬ q.2.rawLen ∈ st.rawDead := fun hm => hdead (by rw [hraw]; exact forget_rawDead_mono hm)
    rw [w_eq_of_eq (hw _ hnd), hraw]; exact hl q hq hqdead

theorem aliasNorm_rawDead (st pre : Facts) (d s : Reg) : (aliasNorm st pre d s).rawDead = st.rawDead := by
  unfold aliasNorm; split <;> rfl
theorem aliasConst_rawDead (st pre : Facts) (d s : Reg) : (aliasConst st pre d s).rawDead = st.rawDead := by
  unfold aliasConst; split <;> rfl

/-- The copies hold of `d` because they held of `s` and `σ' d = σ s`. -/
theorem aliasNorm_sound {W : World} {σ σ' : RegFile} {st pre : Facts} {d s : Reg}
    (hd : σ' d = σ s) (hpre : ∀ p ∈ pre.lenNorm, σ p.1 = W.len p.2) (h : Means W σ' st) :
    Means W σ' (aliasNorm st pre d s) := by
  unfold aliasNorm
  split
  · rename_i raw hraw
    obtain ⟨a, b, c, e, f, g⟩ := h
    refine ⟨a, ?_, c, e, f, g⟩
    intro p hp
    rcases mem_insertReg hp with rfl | ⟨hp, _⟩
    · show σ' d = W.len raw; rw [hd]; exact hpre (s, raw) (lookupReg_mem hraw)
    · exact b p hp
  · exact h

theorem aliasConst_sound {W : World} {σ σ' : RegFile} {st pre : Facts} {d s : Reg}
    (hd : σ' d = σ s) (hpre : ∀ p ∈ pre.consts, σ p.1 = p.2) (h : Means W σ' st) :
    Means W σ' (aliasConst st pre d s) := by
  unfold aliasConst
  split
  · rename_i k hk
    obtain ⟨a, b, c, e, f, g⟩ := h
    refine ⟨a, b, c, ?_, f, g⟩
    intro p hp
    rcases mem_insertReg hp with rfl | ⟨hp, _⟩
    · show σ' d = k; rw [hd]; exact hpre (s, k) (lookupReg_mem hk)
    · exact e p hp
  · exact h

theorem aliasRegion_sound {W : World} {σ σ' : RegFile} {st pre : Facts} {d s : Reg}
    (hd : σ' d = σ s) (hpre : ∀ p ∈ pre.regions, W.region (σ p.1) p.2) (h : Means W σ' st) :
    Means W σ' (aliasRegion st pre d s) := by
  unfold aliasRegion
  split
  · rename_i e he
    split
    · obtain ⟨a, b, c, e', f, g⟩ := h
      refine ⟨a, b, c, e', ?_, g⟩
      intro p hp
      rcases mem_insertReg hp with rfl | ⟨hp, _⟩
      · show W.region (σ' d) e; rw [hd]; exact hpre (s, e) (lookupReg_mem he)
      · exact f p hp
    · exact h
  · exact h

/-- A copied raw length: through an alias, the alias's raw; else the
    bound register itself, live in `pre`. -/
theorem aliasRaw_sound {W : World} {σ σ' : RegFile} {st pre : Facts} {d s : Reg}
    (hd : σ' d = σ s) (hpre : Means W σ pre) (h : Means W σ' st) :
    Means W σ' (aliasRaw st pre d s) := by
  obtain ⟨hs, hn, ha, hc, hr, hl⟩ := hpre
  unfold aliasRaw
  split
  · rename_i hcond
    simp only [Bool.and_eq_true, bne_iff_ne] at hcond
    obtain ⟨hraw, hne⟩ := hcond
    obtain ⟨a, b, c, e, f, g⟩ := h
    refine ⟨a, b, ?_, e, f, g⟩
    intro p hp
    rcases mem_insertReg hp with rfl | ⟨hp, _⟩
    · show w σ' d = W.len (canonicalRaw pre s)
      have hws : w σ' d = w σ s := by unfold w; rw [hd]
      rw [hws]
      unfold canonicalRaw
      unfold rawLen at hraw
      split
      · rename_i raw hal
        exact ha (s, raw) (lookupReg_mem hal)
      · rename_i hal
        rw [hal] at hraw
        simp only [Option.isSome_none, Bool.false_or, Bool.and_eq_true, Bool.not_eq_true', List.any_eq_true] at hraw
        obtain ⟨hdead, q, hq, hqs⟩ := hraw
        have hqs' : q.2.rawLen = s := by simpa using hqs
        have hnd : ¬ q.2.rawLen ∈ pre.rawDead := by
          rw [hqs']; intro hm
          have := List.contains_iff_mem.mpr hm
          rw [this] at hdead; exact absurd hdead (by decide)
        have := hl q hq hnd
        rw [hqs'] at this; exact this
    · exact c p hp
  · exact h

/-- A copied span base; its raw length register, if it is `d`, is dead
    after the forget, so the live-raw obligation is vacuous. -/
theorem aliasSpan_sound {W : World} {σ σ' : RegFile} {st pre : Facts} {d s : Reg}
    (hd : σ' d = σ s) (hw : WritesOnly σ σ' d) (hpre : Means W σ pre)
    (hdead : st.rawDead = (forget pre d).rawDead) (h : Means W σ' st) :
    Means W σ' (aliasSpan st pre d s) := by
  obtain ⟨hs, hn, ha, hc, hr, hl⟩ := hpre
  unfold aliasSpan
  split
  · rename_i sp hsp
    split
    · rename_i hne
      have hmem := lookupReg_mem hsp
      obtain ⟨a, b, c, e, f, g⟩ := h
      refine ⟨?_, b, c, e, f, ?_⟩
      · intro p hp
        rcases mem_insertReg hp with rfl | ⟨hp, _⟩
        · obtain ⟨hspan, hmin⟩ := hs (s, sp) hmem
          exact ⟨by show W.span (σ' d) _ _ _; rw [hd]; exact hspan, hmin⟩
        · exact a p hp
      · intro p hp hpd
        rcases mem_insertReg hp with rfl | ⟨hp, _⟩
        · simp only at hpd ⊢
          rw [hdead] at hpd
          have hnd : sp.rawLen ≠ d := by
            intro hd'
            apply hpd
            have hin : (s, if sp.rawLen == d then { sp with hasMin := false } else sp) ∈ (forget pre d).spans := by
              unfold forget; simp only [List.mem_map]
              refine ⟨(s, sp), ?_, rfl⟩
              unfold deleteReg; rw [List.mem_filter]
              exact ⟨hmem, by show (s != d) = true; exact bne_iff_ne.mpr (Ne.symm hne)⟩
            have := forget_rawDead_self hin (by simp only; split <;> exact hd')
            rw [hd']; exact this
          have hqdead : ¬ sp.rawLen ∈ pre.rawDead := fun hm => hpd (forget_rawDead_mono hm)
          rw [w_eq_of_eq (hw _ hnd)]; exact hl (s, sp) hmem hqdead
        · exact g p hp hpd
    · exact h
  · exact h

/-- `mv xD, xS` with `d ≠ 0`: with `σ' d = σ s` and `x0` zero, the
    maintained facts hold. -/
theorem mv_sound {W : World} {σ σ' : RegFile} {st : Facts} {d s : Reg}
    (hz : σ 0 = 0) (hd0 : d ≠ 0) (hw : WritesOnly σ σ' d) (hd : σ' d = σ s) (h : Means W σ st) :
    Means W σ' (mv st d s) := by
  have h1 := forget_sound hw h
  unfold mv
  rw [if_neg hd0]
  unfold alias
  split
  · rename_i hs0
    subst hs0
    obtain ⟨a, b, c, e, f, g⟩ := h1
    refine ⟨a, b, c, ?_, f, g⟩
    intro p hp
    rcases mem_insertReg hp with rfl | ⟨hp, _⟩
    · show σ' d = 0; rw [hd]; exact hz
    · exact e p hp
  · obtain ⟨hs, hn, ha, hc, hr, hl⟩ := h
    have m1 := aliasNorm_sound (pre := st) hd hn h1
    have m2 := aliasConst_sound (pre := st) hd hc m1
    have r2 : (aliasConst (aliasNorm (forget st d) st d s) st d s).rawDead = (forget st d).rawDead := by
      rw [aliasConst_rawDead, aliasNorm_rawDead]
    have m3 := aliasSpan_sound hd hw ⟨hs, hn, ha, hc, hr, hl⟩ r2 m2
    have m4 := aliasRaw_sound hd ⟨hs, hn, ha, hc, hr, hl⟩ m3
    exact aliasRegion_sound hd hr m4

/-! ## The Go maintenance, as Lean checks it

Rendered by `TestRV64SpanAliasMatchesLeanTransliteration`
(`asm/rv64_span_alias_refinement_test.go`): each state is the checker's
fact maps before a `mv`, each example what a register holds after. -/

def rv0 : Facts := ⟨[(10, ⟨11, 8, true, true, 4⟩)], [(12, 11)], [(18, 11)], [(13, 7)], [(14, ⟨24, false⟩)], []⟩
def rv1 : Facts := ⟨[(10, ⟨11, 1, false, false, 0⟩)], [(12, 11)], [], [], [], [11]⟩

example : lookupReg (mv rv0 19 10).spans 10 = some ⟨11, 8, true, true, 4⟩ := by decide
example : lookupReg (mv rv0 19 10).lenNorm 10 = none := by decide
example : lookupReg (mv rv0 19 10).lenAlias 10 = none := by decide
example : lookupReg (mv rv0 19 10).consts 10 = none := by decide
example : lookupReg (mv rv0 19 10).regions 10 = none := by decide
example : (mv rv0 19 10).rawDead.contains 10 = false := by decide
example : lookupReg (mv rv0 19 10).lenNorm 12 = some 11 := by decide
example : lookupReg (mv rv0 19 10).consts 13 = some 7 := by decide
example : lookupReg (mv rv0 19 10).regions 14 = some ⟨24, false⟩ := by decide
example : lookupReg (mv rv0 19 10).lenAlias 18 = some 11 := by decide
example : lookupReg (mv rv0 19 10).spans 19 = some ⟨11, 8, true, true, 4⟩ := by decide
example : lookupReg (mv rv0 19 10).lenNorm 19 = none := by decide
example : lookupReg (mv rv0 19 10).lenAlias 19 = none := by decide
example : lookupReg (mv rv0 19 10).consts 19 = none := by decide
example : lookupReg (mv rv0 19 10).regions 19 = none := by decide
example : (mv rv0 19 10).rawDead.contains 19 = false := by decide
example : lookupReg (mv rv0 20 11).spans 10 = some ⟨11, 8, true, true, 4⟩ := by decide
example : lookupReg (mv rv0 20 11).spans 11 = none := by decide
example : lookupReg (mv rv0 20 11).lenNorm 11 = none := by decide
example : lookupReg (mv rv0 20 11).lenAlias 11 = none := by decide
example : lookupReg (mv rv0 20 11).consts 11 = none := by decide
example : lookupReg (mv rv0 20 11).regions 11 = none := by decide
example : (mv rv0 20 11).rawDead.contains 11 = false := by decide
example : lookupReg (mv rv0 20 11).lenNorm 12 = some 11 := by decide
example : lookupReg (mv rv0 20 11).consts 13 = some 7 := by decide
example : lookupReg (mv rv0 20 11).regions 14 = some ⟨24, false⟩ := by decide
example : lookupReg (mv rv0 20 11).lenAlias 18 = some 11 := by decide
example : lookupReg (mv rv0 20 11).spans 20 = none := by decide
example : lookupReg (mv rv0 20 11).lenNorm 20 = none := by decide
example : lookupReg (mv rv0 20 11).lenAlias 20 = some 11 := by decide
example : lookupReg (mv rv0 20 11).consts 20 = none := by decide
example : lookupReg (mv rv0 20 11).regions 20 = none := by decide
example : (mv rv0 20 11).rawDead.contains 20 = false := by decide
example : lookupReg (mv rv0 21 18).spans 10 = some ⟨11, 8, true, true, 4⟩ := by decide
example : lookupReg (mv rv0 21 18).lenNorm 12 = some 11 := by decide
example : lookupReg (mv rv0 21 18).consts 13 = some 7 := by decide
example : lookupReg (mv rv0 21 18).regions 14 = some ⟨24, false⟩ := by decide
example : lookupReg (mv rv0 21 18).spans 18 = none := by decide
example : lookupReg (mv rv0 21 18).lenNorm 18 = none := by decide
example : lookupReg (mv rv0 21 18).lenAlias 18 = some 11 := by decide
example : lookupReg (mv rv0 21 18).consts 18 = none := by decide
example : lookupReg (mv rv0 21 18).regions 18 = none := by decide
example : (mv rv0 21 18).rawDead.contains 18 = false := by decide
example : lookupReg (mv rv0 21 18).spans 21 = none := by decide
example : lookupReg (mv rv0 21 18).lenNorm 21 = none := by decide
example : lookupReg (mv rv0 21 18).lenAlias 21 = some 11 := by decide
example : lookupReg (mv rv0 21 18).consts 21 = none := by decide
example : lookupReg (mv rv0 21 18).regions 21 = none := by decide
example : (mv rv0 21 18).rawDead.contains 21 = false := by decide
example : lookupReg (mv rv0 22 12).spans 10 = some ⟨11, 8, true, true, 4⟩ := by decide
example : lookupReg (mv rv0 22 12).spans 12 = none := by decide
example : lookupReg (mv rv0 22 12).lenNorm 12 = some 11 := by decide
example : lookupReg (mv rv0 22 12).lenAlias 12 = none := by decide
example : lookupReg (mv rv0 22 12).consts 12 = none := by decide
example : lookupReg (mv rv0 22 12).regions 12 = none := by decide
example : (mv rv0 22 12).rawDead.contains 12 = false := by decide
example : lookupReg (mv rv0 22 12).consts 13 = some 7 := by decide
example : lookupReg (mv rv0 22 12).regions 14 = some ⟨24, false⟩ := by decide
example : lookupReg (mv rv0 22 12).lenAlias 18 = some 11 := by decide
example : lookupReg (mv rv0 22 12).spans 22 = none := by decide
example : lookupReg (mv rv0 22 12).lenNorm 22 = some 11 := by decide
example : lookupReg (mv rv0 22 12).lenAlias 22 = none := by decide
example : lookupReg (mv rv0 22 12).consts 22 = none := by decide
example : lookupReg (mv rv0 22 12).regions 22 = none := by decide
example : (mv rv0 22 12).rawDead.contains 22 = false := by decide
example : lookupReg (mv rv0 23 13).spans 10 = some ⟨11, 8, true, true, 4⟩ := by decide
example : lookupReg (mv rv0 23 13).lenNorm 12 = some 11 := by decide
example : lookupReg (mv rv0 23 13).spans 13 = none := by decide
example : lookupReg (mv rv0 23 13).lenNorm 13 = none := by decide
example : lookupReg (mv rv0 23 13).lenAlias 13 = none := by decide
example : lookupReg (mv rv0 23 13).consts 13 = some 7 := by decide
example : lookupReg (mv rv0 23 13).regions 13 = none := by decide
example : (mv rv0 23 13).rawDead.contains 13 = false := by decide
example : lookupReg (mv rv0 23 13).regions 14 = some ⟨24, false⟩ := by decide
example : lookupReg (mv rv0 23 13).lenAlias 18 = some 11 := by decide
example : lookupReg (mv rv0 23 13).spans 23 = none := by decide
example : lookupReg (mv rv0 23 13).lenNorm 23 = none := by decide
example : lookupReg (mv rv0 23 13).lenAlias 23 = none := by decide
example : lookupReg (mv rv0 23 13).consts 23 = some 7 := by decide
example : lookupReg (mv rv0 23 13).regions 23 = none := by decide
example : (mv rv0 23 13).rawDead.contains 23 = false := by decide
example : lookupReg (mv rv0 24 14).spans 10 = some ⟨11, 8, true, true, 4⟩ := by decide
example : lookupReg (mv rv0 24 14).lenNorm 12 = some 11 := by decide
example : lookupReg (mv rv0 24 14).consts 13 = some 7 := by decide
example : lookupReg (mv rv0 24 14).spans 14 = none := by decide
example : lookupReg (mv rv0 24 14).lenNorm 14 = none := by decide
example : lookupReg (mv rv0 24 14).lenAlias 14 = none := by decide
example : lookupReg (mv rv0 24 14).consts 14 = none := by decide
example : lookupReg (mv rv0 24 14).regions 14 = some ⟨24, false⟩ := by decide
example : (mv rv0 24 14).rawDead.contains 14 = false := by decide
example : lookupReg (mv rv0 24 14).lenAlias 18 = some 11 := by decide
example : lookupReg (mv rv0 24 14).spans 24 = none := by decide
example : lookupReg (mv rv0 24 14).lenNorm 24 = none := by decide
example : lookupReg (mv rv0 24 14).lenAlias 24 = none := by decide
example : lookupReg (mv rv0 24 14).consts 24 = none := by decide
example : lookupReg (mv rv0 24 14).regions 24 = some ⟨24, false⟩ := by decide
example : (mv rv0 24 14).rawDead.contains 24 = false := by decide
example : lookupReg (mv rv0 11 10).spans 10 = some ⟨11, 8, true, false, 4⟩ := by decide
example : lookupReg (mv rv0 11 10).lenNorm 10 = none := by decide
example : lookupReg (mv rv0 11 10).lenAlias 10 = none := by decide
example : lookupReg (mv rv0 11 10).consts 10 = none := by decide
example : lookupReg (mv rv0 11 10).regions 10 = none := by decide
example : (mv rv0 11 10).rawDead.contains 10 = false := by decide
example : lookupReg (mv rv0 11 10).spans 11 = some ⟨11, 8, true, true, 4⟩ := by decide
example : lookupReg (mv rv0 11 10).lenNorm 11 = none := by decide
example : lookupReg (mv rv0 11 10).lenAlias 11 = none := by decide
example : lookupReg (mv rv0 11 10).consts 11 = none := by decide
example : lookupReg (mv rv0 11 10).regions 11 = none := by decide
example : (mv rv0 11 10).rawDead.contains 11 = true := by decide
example : lookupReg (mv rv0 11 10).lenNorm 12 = some 11 := by decide
example : lookupReg (mv rv0 11 10).consts 13 = some 7 := by decide
example : lookupReg (mv rv0 11 10).regions 14 = some ⟨24, false⟩ := by decide
example : lookupReg (mv rv0 11 10).lenAlias 18 = some 11 := by decide
example : lookupReg (mv rv0 25 0).spans 0 = none := by decide
example : lookupReg (mv rv0 25 0).lenNorm 0 = none := by decide
example : lookupReg (mv rv0 25 0).lenAlias 0 = none := by decide
example : lookupReg (mv rv0 25 0).consts 0 = none := by decide
example : lookupReg (mv rv0 25 0).regions 0 = none := by decide
example : (mv rv0 25 0).rawDead.contains 0 = false := by decide
example : lookupReg (mv rv0 25 0).spans 10 = some ⟨11, 8, true, true, 4⟩ := by decide
example : lookupReg (mv rv0 25 0).lenNorm 12 = some 11 := by decide
example : lookupReg (mv rv0 25 0).consts 13 = some 7 := by decide
example : lookupReg (mv rv0 25 0).regions 14 = some ⟨24, false⟩ := by decide
example : lookupReg (mv rv0 25 0).lenAlias 18 = some 11 := by decide
example : lookupReg (mv rv0 25 0).spans 25 = none := by decide
example : lookupReg (mv rv0 25 0).lenNorm 25 = none := by decide
example : lookupReg (mv rv0 25 0).lenAlias 25 = none := by decide
example : lookupReg (mv rv0 25 0).consts 25 = some 0 := by decide
example : lookupReg (mv rv0 25 0).regions 25 = none := by decide
example : (mv rv0 25 0).rawDead.contains 25 = false := by decide
example : lookupReg (mv rv0 10 10).spans 10 = none := by decide
example : lookupReg (mv rv0 10 10).lenNorm 10 = none := by decide
example : lookupReg (mv rv0 10 10).lenAlias 10 = none := by decide
example : lookupReg (mv rv0 10 10).consts 10 = none := by decide
example : lookupReg (mv rv0 10 10).regions 10 = none := by decide
example : (mv rv0 10 10).rawDead.contains 10 = false := by decide
example : lookupReg (mv rv0 10 10).lenNorm 12 = some 11 := by decide
example : lookupReg (mv rv0 10 10).consts 13 = some 7 := by decide
example : lookupReg (mv rv0 10 10).regions 14 = some ⟨24, false⟩ := by decide
example : lookupReg (mv rv0 10 10).lenAlias 18 = some 11 := by decide
example : lookupReg (mv rv1 26 11).spans 10 = some ⟨11, 1, false, false, 0⟩ := by decide
example : lookupReg (mv rv1 26 11).spans 11 = none := by decide
example : lookupReg (mv rv1 26 11).lenNorm 11 = none := by decide
example : lookupReg (mv rv1 26 11).lenAlias 11 = none := by decide
example : lookupReg (mv rv1 26 11).consts 11 = none := by decide
example : lookupReg (mv rv1 26 11).regions 11 = none := by decide
example : (mv rv1 26 11).rawDead.contains 11 = true := by decide
example : lookupReg (mv rv1 26 11).lenNorm 12 = some 11 := by decide
example : lookupReg (mv rv1 26 11).spans 26 = none := by decide
example : lookupReg (mv rv1 26 11).lenNorm 26 = none := by decide
example : lookupReg (mv rv1 26 11).lenAlias 26 = none := by decide
example : lookupReg (mv rv1 26 11).consts 26 = none := by decide
example : lookupReg (mv rv1 26 11).regions 26 = none := by decide
example : (mv rv1 26 11).rawDead.contains 26 = false := by decide
example : lookupReg (mv rv1 27 12).spans 10 = some ⟨11, 1, false, false, 0⟩ := by decide
example : (mv rv1 27 12).rawDead.contains 11 = true := by decide
example : lookupReg (mv rv1 27 12).spans 12 = none := by decide
example : lookupReg (mv rv1 27 12).lenNorm 12 = some 11 := by decide
example : lookupReg (mv rv1 27 12).lenAlias 12 = none := by decide
example : lookupReg (mv rv1 27 12).consts 12 = none := by decide
example : lookupReg (mv rv1 27 12).regions 12 = none := by decide
example : (mv rv1 27 12).rawDead.contains 12 = false := by decide
example : lookupReg (mv rv1 27 12).spans 27 = none := by decide
example : lookupReg (mv rv1 27 12).lenNorm 27 = some 11 := by decide
example : lookupReg (mv rv1 27 12).lenAlias 27 = none := by decide
example : lookupReg (mv rv1 27 12).consts 27 = none := by decide
example : lookupReg (mv rv1 27 12).regions 27 = none := by decide
example : (mv rv1 27 12).rawDead.contains 27 = false := by decide

end Oak.RiscVSpanAlias
