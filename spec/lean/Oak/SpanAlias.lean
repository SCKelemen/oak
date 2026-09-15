/-! # Compiler correspondence for span aliases

The AArch64 seam checker (`asm/check.go`) keeps facts about general
registers: a span whose base a register holds and the `w` registers holding
its length (`spanFact`), a memory region a register addresses (`region`),
and the guard on an index register (`idxFact`). Two functions maintain them
across a register move. `forgetRegisterFacts` runs at every write and drops
what the register's old value supported: the span it based, its place among
every span's length registers (a proven minimum lapses with the last one),
an index fact on it or bounded by it, a region in it. `aliasSpan` then reads
a `mov`: `mov xD, xB` makes xD a base of xB's span and an address of xB's
region; `mov wD, wL` makes wD a length register of every span wL measures
and gives it wL's guard.

This module transliterates both — the Go is maintained line for line with
them — and proves them sound against a register file: whatever the facts
said of the registers before the move, the maintained facts say of the
registers after it (`movX_sound`, `movW_sound`). Facts are true relative to
a world (`World`) that says which addresses carry a span of which length,
and which a region; a move touches no memory, so the world is fixed.
`asm/span_alias_refinement_test.go` renders the Go's maintenance of six
states as the examples stated at the end.

Registers are numbered as the Go numbers them (`Register.Num`, 0–30); a
`w` read is the low 32 bits of the register's value
(`Oak.Assembler.narrow_canonical`), and `mov wD, wL` zero-extends. -/

namespace Oak.SpanAlias

abbrev Reg := Nat

/-- `asm.region`: a memory extent a register addresses. -/
structure Region where
  size : Int
  writable : Bool
  deriving Repr, DecidableEq

/-- `asm.idxFact`: the dominating guard on an index register — `boundReg`
    holds the bound (a length register), or `boundReg < 0` and `bound` is
    an immediate; `slack` is the `i + bound ≤ len` form. -/
structure IdxFact where
  boundReg : Int
  bound : Int
  slack : Bool
  deriving Repr, DecidableEq

/-- `asm.spanFact` as the alias rules see it: the element size, writability,
    the proven minimum length, and every `w` register holding the length,
    kept sorted so a state renders one way. -/
structure SpanFact where
  elem : Int
  writable : Bool
  hasMin : Bool
  minLen : Int
  lenRegs : List Reg
  deriving Repr, DecidableEq

/-- The checker's register facts, keyed by register number. -/
structure Facts where
  spans : List (Reg × SpanFact)
  regions : List (Reg × Region)
  idx : List (Reg × IdxFact)
  deriving Repr, DecidableEq

/-- `m[r]` on a fact map. -/
def lookupReg {α : Type} (l : List (Reg × α)) (r : Reg) : Option α :=
  (l.find? (fun p => p.1 == r)).map Prod.snd

/-- `m[r] = v` on a fact map. -/
def insertReg {α : Type} (l : List (Reg × α)) (r : Reg) (v : α) : List (Reg × α) :=
  (r, v) :: l.filter (fun p => p.1 != r)

/-- `delete(m, r)`. -/
def deleteReg {α : Type} (l : List (Reg × α)) (r : Reg) : List (Reg × α) :=
  l.filter (fun p => p.1 != r)

def insertSorted (n : Reg) : List Reg → List Reg
  | [] => [n]
  | x :: xs => if n ≤ x then n :: x :: xs else x :: insertSorted n xs

/-- `spanFact.dropLen`: the register no longer holds the length; the proven
    minimum lapses when no register does. -/
def SpanFact.dropLen (f : SpanFact) (n : Reg) : SpanFact :=
  let regs := f.lenRegs.filter (fun l => l != n)
  { f with lenRegs := regs, hasMin := f.hasMin && !regs.isEmpty }

/-- `fact.lenRegs[n] = true`. -/
def SpanFact.addLen (f : SpanFact) (n : Reg) : SpanFact :=
  if f.lenRegs.contains n then f else { f with lenRegs := insertSorted n f.lenRegs }

/-- `checker.equalRegister` over the alias facts: the smallest other
    length register of the first span `d` measures — a register proven
    to hold `d`'s value, which takes `d`'s place as the bound of the
    guards naming it when `d` is written (docs/spec/94-assembler.md §7
    "Bounds through arithmetic"). -/
def equalRegister (st : Facts) (d : Reg) : Option Reg :=
  match st.spans.find? (fun p => p.2.lenRegs.contains d && !(p.2.lenRegs.filter (fun l => l != d)).isEmpty) with
  | some p => (p.2.lenRegs.filter (fun l => l != d)).head?
  | none => none

/-- A guard bounded by the written register rebounds to the register
    equal to it, or dies; any other guard stays. -/
def rebound (st : Facts) (d : Reg) (p : Reg × IdxFact) : Option (Reg × IdxFact) :=
  if p.2.boundReg != (d : Int) then some p
  else match equalRegister st d with
    | some e => some (p.1, { p.2 with boundReg := (e : Int) })
    | none => none

/-- `checker.forgetRegisterFacts`, over the facts the alias rules touch. -/
def forget (st : Facts) (d : Reg) : Facts :=
  { spans := (deleteReg st.spans d).map (fun p => (p.1, p.2.dropLen d)),
    regions := deleteReg st.regions d,
    idx := (deleteReg st.idx d).filterMap (rebound st d) }

/-- `aliasSpan` for `mov xD, xS`. -/
def aliasX (st : Facts) (d s : Reg) : Facts :=
  let st1 := match lookupReg st.spans s with
    | some f => { st with spans := insertReg st.spans d f }
    | none => st
  match lookupReg st.regions s with
    | some e => { st1 with regions := insertReg st1.regions d e }
    | none => st1

/-- `aliasSpan` for `mov wD, wS`. -/
def aliasW (st : Facts) (d s : Reg) : Facts :=
  { st with
    spans := st.spans.map (fun p => (p.1, if p.2.lenRegs.contains s then p.2.addLen d else p.2)),
    idx := match lookupReg st.idx s with
      | some g => insertReg st.idx d g
      | none => st.idx }

/-- The checker at `mov xD, xS`: the write forgets, the move aliases. -/
def movX (st : Facts) (d s : Reg) : Facts := aliasX (forget st d) d s

/-- The checker at `mov wD, wS`. -/
def movW (st : Facts) (d s : Reg) : Facts := aliasW (forget st d) d s

/-! ## Meaning -/

/-- A register file: the 64-bit value of each general register. -/
abbrev RegFile := Reg → Int

/-- The `w` view: the low 32 bits. -/
def w (σ : RegFile) (r : Reg) : Int := σ r % 4294967296

/-- What memory says: `span addr len elem writable` — a span of `len`
    elements of `elem` bytes lies at `addr`, writable or not — and
    `region addr e` — the extent `e` lies at `addr`. A register move
    changes neither. -/
structure World where
  span : Int → Int → Int → Bool → Prop
  region : Int → Region → Prop

/-- Register `b` bases the span the fact describes, and every register the
    fact names holds its length, at least the proven minimum. -/
def SpanMeans (W : World) (σ : RegFile) (b : Reg) (f : SpanFact) : Prop :=
  ∃ addr len, σ b = addr ∧ W.span addr len f.elem f.writable ∧
    (∀ l ∈ f.lenRegs, w σ l = len) ∧ (f.hasMin = true → f.minLen ≤ len)

def RegionMeans (W : World) (σ : RegFile) (r : Reg) (e : Region) : Prop :=
  W.region (σ r) e

/-- The guard on index register `i`: below the immediate, or below (or
    `bound` short of) the length register's value. -/
def IdxMeans (σ : RegFile) (i : Reg) (g : IdxFact) : Prop :=
  (g.boundReg < 0 → w σ i < g.bound) ∧
  (0 ≤ g.boundReg →
    (g.slack = false → w σ i < w σ g.boundReg.toNat) ∧
    (g.slack = true → w σ i + g.bound ≤ w σ g.boundReg.toNat))

/-- Every fact holds of the register file. -/
def Means (W : World) (σ : RegFile) (st : Facts) : Prop :=
  (∀ p ∈ st.spans, SpanMeans W σ p.1 p.2) ∧
  (∀ p ∈ st.regions, RegionMeans W σ p.1 p.2) ∧
  (∀ p ∈ st.idx, IdxMeans σ p.1 p.2)

/-- `σ'` is `σ` with register `d` written. -/
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

theorem mem_insertSorted {n x : Reg} {l : List Reg} (h : x ∈ insertSorted n l) : x = n ∨ x ∈ l := by
  induction l with
  | nil => simp [insertSorted] at h; exact Or.inl h
  | cons y ys ih =>
    unfold insertSorted at h
    split at h
    · simp only [List.mem_cons] at h
      rcases h with h | h | h
      · exact Or.inl h
      · exact Or.inr (List.mem_cons.mpr (Or.inl h))
      · exact Or.inr (List.mem_cons.mpr (Or.inr h))
    · simp only [List.mem_cons] at h
      rcases h with h | h
      · exact Or.inr (List.mem_cons.mpr (Or.inl h))
      · rcases ih h with h | h
        · exact Or.inl h
        · exact Or.inr (List.mem_cons.mpr (Or.inr h))

theorem mem_dropLen {f : SpanFact} {n l : Reg} (h : l ∈ (f.dropLen n).lenRegs) : l ∈ f.lenRegs ∧ l ≠ n := by
  unfold SpanFact.dropLen at h
  simp only at h
  rw [List.mem_filter] at h
  exact ⟨h.1, bne_iff_ne.mp h.2⟩

theorem hasMin_dropLen {f : SpanFact} {n : Reg} (h : (f.dropLen n).hasMin = true) : f.hasMin = true := by
  unfold SpanFact.dropLen at h
  simp only [Bool.and_eq_true] at h
  exact h.1

theorem mem_addLen {f : SpanFact} {n l : Reg} (h : l ∈ (f.addLen n).lenRegs) : l = n ∨ l ∈ f.lenRegs := by
  unfold SpanFact.addLen at h
  split at h
  · exact Or.inr h
  · exact mem_insertSorted h

theorem addLen_elem (f : SpanFact) (n : Reg) : (f.addLen n).elem = f.elem := by
  unfold SpanFact.addLen; split <;> rfl
theorem addLen_writable (f : SpanFact) (n : Reg) : (f.addLen n).writable = f.writable := by
  unfold SpanFact.addLen; split <;> rfl
theorem addLen_hasMin (f : SpanFact) (n : Reg) : (f.addLen n).hasMin = f.hasMin := by
  unfold SpanFact.addLen; split <;> rfl
theorem addLen_minLen (f : SpanFact) (n : Reg) : (f.addLen n).minLen = f.minLen := by
  unfold SpanFact.addLen; split <;> rfl

theorem w_eq_of_eq {σ σ' : RegFile} {r : Reg} (h : σ' r = σ r) : w σ' r = w σ r := by
  unfold w; rw [h]

theorem w_low32 (σ : RegFile) (v : Int) (d : Reg) (h : σ d = v % 4294967296) : w σ d = v % 4294967296 := by
  unfold w; rw [h]; exact Int.emod_emod_of_dvd v (Int.dvd_refl _)

/-! ## Soundness -/

/-- A span fact survives a write to another register: `d` leaves its
    length registers, and what remains still holds. -/
theorem spanMeans_dropLen {W : World} {σ σ' : RegFile} {d b : Reg} {f : SpanFact}
    (hw : WritesOnly σ σ' d) (hb : b ≠ d) (h : SpanMeans W σ b f) : SpanMeans W σ' b (f.dropLen d) := by
  obtain ⟨addr, len, hbase, hspan, hlen, hmin⟩ := h
  refine ⟨addr, len, ?_, hspan, ?_, ?_⟩
  · rw [hw b hb]; exact hbase
  · intro l hl
    obtain ⟨hl, hne⟩ := mem_dropLen hl
    rw [w_eq_of_eq (hw l hne)]; exact hlen l hl
  · intro hm; exact hmin (hasMin_dropLen hm)

theorem idxMeans_of_writesOnly {σ σ' : RegFile} {d i : Reg} {g : IdxFact}
    (hw : WritesOnly σ σ' d) (hi : i ≠ d) (hg : g.boundReg ≠ (d : Int)) (h : IdxMeans σ i g) : IdxMeans σ' i g := by
  obtain ⟨himm, hreg⟩ := h
  refine ⟨fun hlt => ?_, fun hge => ?_⟩
  · rw [w_eq_of_eq (hw i hi)]; exact himm hlt
  · have hne : g.boundReg.toNat ≠ d := by
      intro heq; apply hg; rw [← heq]; exact (Int.toNat_of_nonneg hge).symm
    obtain ⟨h0, h1⟩ := hreg hge
    rw [w_eq_of_eq (hw i hi), w_eq_of_eq (hw _ hne)]
    exact ⟨h0, h1⟩

/-- A guard is a statement about its two registers: any transition that
    leaves them as they were keeps it — a `mov` or `add #0` into a fresh
    register (the copy reads the same values), or a call that preserves
    callee-saved registers under AAPCS64. -/
theorem idxMeans_preserved {σ σ' : RegFile} {i : Reg} {g : IdxFact}
    (hi : σ' i = σ i) (hb : 0 ≤ g.boundReg → σ' g.boundReg.toNat = σ g.boundReg.toNat)
    (h : IdxMeans σ i g) : IdxMeans σ' i g := by
  obtain ⟨himm, hreg⟩ := h
  refine ⟨fun hlt => ?_, fun hge => ?_⟩
  · rw [w_eq_of_eq hi]; exact himm hlt
  · obtain ⟨h0, h1⟩ := hreg hge
    rw [w_eq_of_eq hi, w_eq_of_eq (hb hge)]
    exact ⟨h0, h1⟩

/-- The register `equalRegister` names measures a span `d` measures too,
    and is not `d`. -/
theorem equalRegister_spec {st : Facts} {d e : Reg} (h : equalRegister st d = some e) :
    ∃ p ∈ st.spans, d ∈ p.2.lenRegs ∧ e ∈ p.2.lenRegs ∧ e ≠ d := by
  unfold equalRegister at h
  split at h
  · rename_i p hfind
    refine ⟨p, List.mem_of_find?_eq_some hfind, ?_, ?_⟩
    · have hp := List.find?_some hfind
      simp only [Bool.and_eq_true, List.contains_iff_mem] at hp
      exact hp.1
    · cases hl : p.2.lenRegs.filter (fun l => l != d) with
      | nil => rw [hl] at h; simp at h
      | cons x xs =>
        rw [hl] at h
        simp only [List.head?_cons, Option.some.injEq] at h
        have hx : x ∈ p.2.lenRegs.filter (fun l => l != d) := by rw [hl]; exact List.mem_cons_self
        rw [h] at hx
        rw [List.mem_filter] at hx
        exact ⟨hx.1, bne_iff_ne.mp hx.2⟩
  · simp at h

/-- Rebinding keeps the guard's register. -/
theorem rebound_key {st : Facts} {d : Reg} {q p : Reg × IdxFact} (h : rebound st d q = some p) : p.1 = q.1 := by
  unfold rebound at h
  split at h
  · rw [← Option.some.inj h]
  · split at h
    · rw [← Option.some.inj h]
    · simp at h

/-- No guard the write forgets is on the written register. -/
theorem mem_forget_idx {st : Facts} {d : Reg} {p : Reg × IdxFact} (h : p ∈ (forget st d).idx) : p.1 ≠ d := by
  unfold forget at h
  simp only at h
  rw [List.mem_filterMap] at h
  obtain ⟨q, hq, hpq⟩ := h
  rw [rebound_key hpq]
  exact (mem_deleteReg hq).2

/-- A guard bounded by `d` holds of the register equal to `d` after the
    write: both held the span's length before it. -/
theorem idxMeans_rebound {W : World} {σ σ' : RegFile} {st : Facts} {d e i : Reg} {g : IdxFact}
    (hw : WritesOnly σ σ' d) (hs : ∀ p ∈ st.spans, SpanMeans W σ p.1 p.2)
    (hi : i ≠ d) (hbd : g.boundReg = (d : Int)) (he : equalRegister st d = some e)
    (h : IdxMeans σ i g) : IdxMeans σ' i { g with boundReg := (e : Int) } := by
  obtain ⟨sp, hsp, hd, he', hed⟩ := equalRegister_spec he
  obtain ⟨addr, len, _, _, hlen, _⟩ := hs sp hsp
  obtain ⟨_, hreg⟩ := h
  have hge : 0 ≤ g.boundReg := by rw [hbd]; exact Int.natCast_nonneg d
  obtain ⟨h0, h1⟩ := hreg hge
  have htn : g.boundReg.toNat = d := by rw [hbd]; simp
  rw [htn] at h0 h1
  have hwd : w σ d = len := hlen d hd
  have hwe : w σ e = len := hlen e he'
  have hi' : w σ' i = w σ i := w_eq_of_eq (hw i hi)
  have he'' : w σ' e = w σ e := w_eq_of_eq (hw e hed)
  refine ⟨fun hlt => ?_, fun _ => ⟨fun hs' => ?_, fun hs' => ?_⟩⟩
  · exfalso
    simp only at hlt
    exact absurd hlt (Int.not_lt.mpr (Int.natCast_nonneg e))
  · simp only [Int.toNat_natCast]
    rw [hi', he'', hwe, ← hwd]
    exact h0 hs'
  · simp only [Int.toNat_natCast]
    rw [hi', he'', hwe, ← hwd]
    exact h1 hs'

/-- Forgetting is sound under any write to `d`. -/
theorem forget_sound {W : World} {σ σ' : RegFile} {st : Facts} {d : Reg}
    (hw : WritesOnly σ σ' d) (h : Means W σ st) : Means W σ' (forget st d) := by
  obtain ⟨hs, hr, hi⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · intro p hp
    unfold forget at hp
    simp only [List.mem_map] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    obtain ⟨hq, hne⟩ := mem_deleteReg hq
    exact spanMeans_dropLen hw hne (hs q hq)
  · intro p hp
    obtain ⟨hp, hne⟩ := mem_deleteReg hp
    unfold RegionMeans; rw [hw p.1 hne]; exact hr p hp
  · intro p hp
    unfold forget at hp
    simp only at hp
    rw [List.mem_filterMap] at hp
    obtain ⟨q, hq, hpq⟩ := hp
    obtain ⟨hq, hne⟩ := mem_deleteReg hq
    unfold rebound at hpq
    split at hpq
    · rename_i hb
      rw [← Option.some.inj hpq]
      exact idxMeans_of_writesOnly hw hne (bne_iff_ne.mp hb) (hi q hq)
    · rename_i hb
      have hbd : q.2.boundReg = (d : Int) := by simpa using hb
      split at hpq
      · rename_i e he
        rw [← Option.some.inj hpq]
        exact idxMeans_rebound hw hs hne hbd he (hi q hq)
      · simp at hpq

/-- `mov xD, xS`: with `σ' d = σ s`, the maintained facts hold. -/
theorem movX_sound {W : World} {σ σ' : RegFile} {st : Facts} {d s : Reg}
    (hw : WritesOnly σ σ' d) (hd : σ' d = σ s) (h : Means W σ st) : Means W σ' (movX st d s) := by
  have h1 := forget_sound hw h
  obtain ⟨hs1, hr1, hi1⟩ := h1
  -- a fact copied from s came through forget, so s ≠ d and σ' s = σ s
  have copyX : ∀ f, lookupReg (forget st d).spans s = some f → SpanMeans W σ' d f := by
    intro f hf
    have hmem := lookupReg_mem hf
    have hne : s ≠ d := by
      unfold forget at hmem
      simp only [List.mem_map] at hmem
      obtain ⟨q, hq, hqf⟩ := hmem
      have h1 : q.1 = s := by have := congrArg Prod.fst hqf; simpa using this
      rw [← h1]; exact (mem_deleteReg hq).2
    obtain ⟨addr, len, hbase, hspan, hlen, hmin⟩ := hs1 (s, f) hmem
    exact ⟨addr, len, by rw [hd, ← hw s hne]; exact hbase, hspan, hlen, hmin⟩
  have copyR : ∀ e, lookupReg (forget st d).regions s = some e → RegionMeans W σ' d e := by
    intro e he
    have hmem := lookupReg_mem he
    have hne := (mem_deleteReg hmem).2
    have := hr1 (s, e) hmem
    unfold RegionMeans at this ⊢
    rw [hd, ← hw s hne]; exact this
  unfold movX aliasX
  -- the two matches
  generalize hsp : lookupReg (forget st d).spans s = osp
  generalize hrg : lookupReg (forget st d).regions s = org
  have spans_ok : ∀ p ∈ (match osp with
      | some f => { forget st d with spans := insertReg (forget st d).spans d f }
      | none => forget st d).spans, SpanMeans W σ' p.1 p.2 := by
    intro p hp
    cases osp with
    | none => exact hs1 p hp
    | some f =>
      simp only at hp
      rcases mem_insertReg hp with rfl | ⟨hp, _⟩
      · exact copyX f hsp
      · exact hs1 p hp
  have regions_ok : ∀ p ∈ (match osp with
      | some f => { forget st d with spans := insertReg (forget st d).spans d f }
      | none => forget st d).regions, RegionMeans W σ' p.1 p.2 := by
    intro p hp
    cases osp <;> exact hr1 p hp
  have idx_ok : ∀ p ∈ (match osp with
      | some f => { forget st d with spans := insertReg (forget st d).spans d f }
      | none => forget st d).idx, IdxMeans σ' p.1 p.2 := by
    intro p hp
    cases osp <;> exact hi1 p hp
  cases org with
  | none => exact ⟨spans_ok, regions_ok, idx_ok⟩
  | some e =>
    refine ⟨spans_ok, ?_, idx_ok⟩
    intro p hp
    simp only at hp
    rcases mem_insertReg hp with rfl | ⟨hp, _⟩
    · exact copyR e hrg
    · exact regions_ok p hp

/-- `mov wD, wS`: with `σ' d` the low 32 bits of `σ s`, the maintained
    facts hold. -/
theorem movW_sound {W : World} {σ σ' : RegFile} {st : Facts} {d s : Reg}
    (hw : WritesOnly σ σ' d) (hd : σ' d = σ s % 4294967296) (h : Means W σ st) : Means W σ' (movW st d s) := by
  have h1 := forget_sound hw h
  obtain ⟨hs1, hr1, hi1⟩ := h1
  have hwd : ∀ (hne : s ≠ d), w σ' d = w σ' s := by
    intro hne
    rw [w_low32 σ' (σ s) d hd, w_eq_of_eq (hw s hne)]; rfl
  refine ⟨?_, hr1, ?_⟩
  · intro p hp
    unfold movW aliasW at hp
    simp only [List.mem_map] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    obtain ⟨addr, len, hbase, hspan, hlen, hmin⟩ := hs1 q hq
    simp only
    split
    · rename_i hcontains
      have hs_mem : s ∈ q.2.lenRegs := List.contains_iff_mem.mp hcontains
      have hne : s ≠ d := by
        intro heq; rw [heq] at hs_mem
        -- forget dropped d from every span's length registers
        unfold forget at hq
        simp only [List.mem_map] at hq
        obtain ⟨q0, _, hq0⟩ := hq
        rw [← hq0] at hs_mem
        exact (mem_dropLen hs_mem).2 rfl
      refine ⟨addr, len, hbase, ?_, ?_, ?_⟩
      · simpa [addLen_elem, addLen_writable] using hspan
      · intro l hl
        rcases mem_addLen hl with rfl | hl
        · rw [hwd hne]; exact hlen s hs_mem
        · exact hlen l hl
      · simpa [addLen_hasMin, addLen_minLen] using hmin
    · exact ⟨addr, len, hbase, hspan, hlen, hmin⟩
  · intro p hp
    unfold movW aliasW at hp
    simp only at hp
    generalize hg : lookupReg (forget st d).idx s = og at hp
    cases og with
    | none => exact hi1 p hp
    | some g =>
      rcases mem_insertReg hp with rfl | ⟨hp, _⟩
      · have hmem := lookupReg_mem hg
        have hne : s ≠ d := mem_forget_idx hmem
        obtain ⟨himm, hreg⟩ := hi1 (s, g) hmem
        refine ⟨fun hlt => ?_, fun hge => ?_⟩
        · simp only; rw [hwd hne]; exact himm hlt
        · obtain ⟨h0, h1⟩ := hreg hge
          simp only; rw [hwd hne]; exact ⟨h0, h1⟩
      · exact hi1 p hp

/-! ## The Go maintenance, as Lean checks it

Rendered by `TestSpanAliasMatchesLeanTransliteration`
(`asm/span_alias_refinement_test.go`): each state is the checker's fact
maps before a `mov`, each example the fact it holds for a register after.
-/

def st0 : Facts := ⟨[(0, ⟨8, true, true, 4, [1, 5]⟩)], [(2, ⟨24, false⟩)], [(3, ⟨1, 0, false⟩), (4, ⟨-1, 16, false⟩), (6, ⟨5, 2, true⟩)]⟩
def st1 : Facts := ⟨[(0, ⟨1, false, true, 4, [5]⟩)], [], []⟩

example : lookupReg (movX st0 19 0).spans 0 = some ⟨8, true, true, 4, [1, 5]⟩ := by decide
example : lookupReg (movX st0 19 0).regions 0 = none := by decide
example : lookupReg (movX st0 19 0).idx 0 = none := by decide
example : lookupReg (movX st0 19 0).regions 2 = some ⟨24, false⟩ := by decide
example : lookupReg (movX st0 19 0).idx 3 = some ⟨1, 0, false⟩ := by decide
example : lookupReg (movX st0 19 0).idx 4 = some ⟨-1, 16, false⟩ := by decide
example : lookupReg (movX st0 19 0).idx 6 = some ⟨5, 2, true⟩ := by decide
example : lookupReg (movX st0 19 0).spans 19 = some ⟨8, true, true, 4, [1, 5]⟩ := by decide
example : lookupReg (movX st0 19 0).regions 19 = none := by decide
example : lookupReg (movX st0 19 0).idx 19 = none := by decide
example : lookupReg (movX st0 20 2).spans 0 = some ⟨8, true, true, 4, [1, 5]⟩ := by decide
example : lookupReg (movX st0 20 2).spans 2 = none := by decide
example : lookupReg (movX st0 20 2).regions 2 = some ⟨24, false⟩ := by decide
example : lookupReg (movX st0 20 2).idx 2 = none := by decide
example : lookupReg (movX st0 20 2).idx 3 = some ⟨1, 0, false⟩ := by decide
example : lookupReg (movX st0 20 2).idx 4 = some ⟨-1, 16, false⟩ := by decide
example : lookupReg (movX st0 20 2).idx 6 = some ⟨5, 2, true⟩ := by decide
example : lookupReg (movX st0 20 2).spans 20 = none := by decide
example : lookupReg (movX st0 20 2).regions 20 = some ⟨24, false⟩ := by decide
example : lookupReg (movX st0 20 2).idx 20 = none := by decide
example : lookupReg (movW st0 21 1).spans 0 = some ⟨8, true, true, 4, [1, 5, 21]⟩ := by decide
example : lookupReg (movW st0 21 1).spans 1 = none := by decide
example : lookupReg (movW st0 21 1).regions 1 = none := by decide
example : lookupReg (movW st0 21 1).idx 1 = none := by decide
example : lookupReg (movW st0 21 1).regions 2 = some ⟨24, false⟩ := by decide
example : lookupReg (movW st0 21 1).idx 3 = some ⟨1, 0, false⟩ := by decide
example : lookupReg (movW st0 21 1).idx 4 = some ⟨-1, 16, false⟩ := by decide
example : lookupReg (movW st0 21 1).idx 6 = some ⟨5, 2, true⟩ := by decide
example : lookupReg (movW st0 21 1).spans 21 = none := by decide
example : lookupReg (movW st0 21 1).regions 21 = none := by decide
example : lookupReg (movW st0 21 1).idx 21 = none := by decide
example : lookupReg (movW st0 22 3).spans 0 = some ⟨8, true, true, 4, [1, 5]⟩ := by decide
example : lookupReg (movW st0 22 3).regions 2 = some ⟨24, false⟩ := by decide
example : lookupReg (movW st0 22 3).spans 3 = none := by decide
example : lookupReg (movW st0 22 3).regions 3 = none := by decide
example : lookupReg (movW st0 22 3).idx 3 = some ⟨1, 0, false⟩ := by decide
example : lookupReg (movW st0 22 3).idx 4 = some ⟨-1, 16, false⟩ := by decide
example : lookupReg (movW st0 22 3).idx 6 = some ⟨5, 2, true⟩ := by decide
example : lookupReg (movW st0 22 3).spans 22 = none := by decide
example : lookupReg (movW st0 22 3).regions 22 = none := by decide
example : lookupReg (movW st0 22 3).idx 22 = some ⟨1, 0, false⟩ := by decide
example : lookupReg (movW st0 7 6).spans 0 = some ⟨8, true, true, 4, [1, 5]⟩ := by decide
example : lookupReg (movW st0 7 6).regions 2 = some ⟨24, false⟩ := by decide
example : lookupReg (movW st0 7 6).idx 3 = some ⟨1, 0, false⟩ := by decide
example : lookupReg (movW st0 7 6).idx 4 = some ⟨-1, 16, false⟩ := by decide
example : lookupReg (movW st0 7 6).spans 6 = none := by decide
example : lookupReg (movW st0 7 6).regions 6 = none := by decide
example : lookupReg (movW st0 7 6).idx 6 = some ⟨5, 2, true⟩ := by decide
example : lookupReg (movW st0 7 6).spans 7 = none := by decide
example : lookupReg (movW st0 7 6).regions 7 = none := by decide
example : lookupReg (movW st0 7 6).idx 7 = some ⟨5, 2, true⟩ := by decide
example : lookupReg (movX st0 1 0).spans 0 = some ⟨8, true, true, 4, [5]⟩ := by decide
example : lookupReg (movX st0 1 0).regions 0 = none := by decide
example : lookupReg (movX st0 1 0).idx 0 = none := by decide
example : lookupReg (movX st0 1 0).spans 1 = some ⟨8, true, true, 4, [5]⟩ := by decide
example : lookupReg (movX st0 1 0).regions 1 = none := by decide
example : lookupReg (movX st0 1 0).idx 1 = none := by decide
example : lookupReg (movX st0 1 0).regions 2 = some ⟨24, false⟩ := by decide
example : lookupReg (movX st0 1 0).idx 3 = some ⟨5, 0, false⟩ := by decide
example : lookupReg (movX st0 1 0).idx 4 = some ⟨-1, 16, false⟩ := by decide
example : lookupReg (movX st0 1 0).idx 6 = some ⟨5, 2, true⟩ := by decide
example : lookupReg (movX st1 5 9).spans 0 = some ⟨1, false, false, 4, []⟩ := by decide
example : lookupReg (movX st1 5 9).spans 5 = none := by decide
example : lookupReg (movX st1 5 9).regions 5 = none := by decide
example : lookupReg (movX st1 5 9).idx 5 = none := by decide
example : lookupReg (movX st1 5 9).spans 9 = none := by decide
example : lookupReg (movX st1 5 9).regions 9 = none := by decide
example : lookupReg (movX st1 5 9).idx 9 = none := by decide
example : lookupReg (movX st0 0 0).spans 0 = none := by decide
example : lookupReg (movX st0 0 0).regions 0 = none := by decide
example : lookupReg (movX st0 0 0).idx 0 = none := by decide
example : lookupReg (movX st0 0 0).regions 2 = some ⟨24, false⟩ := by decide
example : lookupReg (movX st0 0 0).idx 3 = some ⟨1, 0, false⟩ := by decide
example : lookupReg (movX st0 0 0).idx 4 = some ⟨-1, 16, false⟩ := by decide
example : lookupReg (movX st0 0 0).idx 6 = some ⟨5, 2, true⟩ := by decide

end Oak.SpanAlias
