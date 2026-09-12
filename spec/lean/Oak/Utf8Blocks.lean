import Oak.Utf8Flat

/-!
# The vector program computes the stream

`stdlib/utf8.oak` never sees the stream a byte at a time. It sees blocks of
sixteen lanes, shifts each block against the block before it to recover the
three previous bytes (`simd.prev_u8x16`), classifies all sixteen lanes at
once, ORs the error lanes of every block into one accumulator, and decides
at the end. It takes the stream sixty-four bytes at a step and skips the
classification of a step with no high bit set, ORing in the carried
`incomplete` lanes instead.

This file is that program, transcribed onto lane functions, and the proof
that its verdict is the stream theorem:

* `checkBlock` is `check_block` lane for lane; `checkBlock_lane` shows lane
  `i` of block `b` is the lane error at stream position `16 * b + i`
  (`Oak.Utf8Flat.flatError`) — the block shift composes exactly.
* `ascii_block` is the shortcut: for a block with no high bit, the error
  lanes are nonzero iff the previous block's `incomplete` lanes are.
* `program` is the loop structure — the sixty-four-byte steps, the
  sixteen-byte remainder, the zero-padded tail — with both shortcuts, and
  `program_valid` is the theorem: it accepts exactly the valid streams
  (`Oak.Utf8Validity.Valid`).

The differential test `compiler/e2e_stdlib_utf8_test.go` checks the emitted
C against this model's scalar twin; the emitted lane operations are the
`Oak.Simd` lane semantics.
-/

namespace Oak.Utf8Blocks

open Oak.Utf8Stream Oak.Utf8Flat

/-- A block of lanes, by lane number; lanes 16 and up are never read. -/
abbrev V := Nat → BitVec 8

def vand (a b : V) : V := fun i => a i &&& b i
def vor (a b : V) : V := fun i => a i ||| b i
def vxor (a b : V) : V := fun i => a i ^^^ b i
def vshr (n : Nat) (v : V) : V := fun i => v i >>> n
def vsplat (x : BitVec 8) : V := fun _ => x
def vsubs (a b : V) : V := fun i => satSub (a i) (b i)
def vtbl (t : BitVec 8 → BitVec 8) (idx : V) : V := fun i => t (idx i)
/-- `simd.prev_u8x16`: the lanes shifted `n` back, the first `n` from the
previous block (`Oak.Simd.prev_lane_from_prev`, `prev_lane_from_cur`). -/
def vprev (n : Nat) (p c : V) : V := fun i => if i < n then p (16 - n + i) else c (i - n)
/-- `simd.any_u8x16` over the sixteen lanes. -/
def vany (v : V) : Bool := (List.range 16).any (fun i => v i != 0)

theorem vany_iff (v : V) : vany v = true ↔ ∃ i, i < 16 ∧ v i ≠ 0 := by
  simp [vany, List.any_eq_true, List.mem_range]

theorem vany_vor (a b : V) : vany (vor a b) = true ↔ vany a = true ∨ vany b = true := by
  simp only [vany_iff, vor]
  constructor
  · intro ⟨i, hi, h⟩
    by_cases ha : a i = 0
    · exact Or.inr ⟨i, hi, by intro hb; apply h; rw [ha, hb]; rfl⟩
    · exact Or.inl ⟨i, hi, ha⟩
  · intro h
    rcases h with ⟨i, hi, h⟩ | ⟨i, hi, h⟩
    · exact ⟨i, hi, by intro hz; apply h; bv_decide⟩
    · exact ⟨i, hi, by intro hz; apply h; bv_decide⟩

theorem vany_congr (a b : V) (h : ∀ i, i < 16 → a i = b i) : vany a = vany b := by
  rw [Bool.eq_iff_iff, vany_iff, vany_iff]
  constructor
  · rintro ⟨i, hi, hne⟩; exact ⟨i, hi, by rw [← h i hi]; exact hne⟩
  · rintro ⟨i, hi, hne⟩; exact ⟨i, hi, by rw [h i hi]; exact hne⟩

/-! ## The block functions of the Oak source -/

/-- `special_cases`. -/
def specialCasesV (input prev1 : V) : V :=
  vand (vand (vtbl high1Tbl (vshr 4 prev1)) (vtbl low1Tbl (vand prev1 (vsplat 15))))
    (vtbl high2Tbl (vshr 4 input))

/-- `check_block`. -/
def checkBlock (prevInput input : V) : V :=
  let prev1 := vprev 1 prevInput input
  let prev2 := vprev 2 prevInput input
  let prev3 := vprev 3 prevInput input
  let sc := specialCasesV input prev1
  let third := vsubs prev2 (vsplat 96)
  let fourth := vsubs prev3 (vsplat 112)
  let must23 := vand (vor third fourth) (vsplat 128)
  vxor must23 sc

/-- `check_blocks`: four consecutive blocks, each against the one before. -/
def checkBlocks (prevInput a b c d : V) : V :=
  vor (vor (checkBlock prevInput a) (checkBlock a b)) (vor (checkBlock b c) (checkBlock c d))

/-- `incomplete_max`. -/
def maxima : V := fun i => if i = 13 then 239 else if i = 14 then 223 else if i = 15 then 191 else 255

/-- `subs(input, maxima)`: the lanes that start a sequence the block cannot finish. -/
def incomplete (input : V) : V := vsubs input maxima

def highBit : V := vsplat 128
def zero : V := vsplat 0

theorem checkBlock_lane_def (p c : V) (i : Nat) :
    checkBlock p c i = laneError (vprev 3 p c i) (vprev 2 p c i) (vprev 1 p c i) (c i) := rfl

/-- `checkBlock` reads only lanes below sixteen of the previous block. -/
theorem checkBlock_congr (p p' c : V) (hp : ∀ i, i < 16 → p i = p' i) (i : Nat) (hi : i < 16) :
    checkBlock p c i = checkBlock p' c i := by
  rw [checkBlock_lane_def, checkBlock_lane_def]
  unfold vprev
  have e3 : (if i < 3 then p (16 - 3 + i) else c (i - 3)) =
      (if i < 3 then p' (16 - 3 + i) else c (i - 3)) := by
    by_cases h : i < 3
    · rw [if_pos h, if_pos h, hp _ (by omega)]
    · rw [if_neg h, if_neg h]
  have e2 : (if i < 2 then p (16 - 2 + i) else c (i - 2)) =
      (if i < 2 then p' (16 - 2 + i) else c (i - 2)) := by
    by_cases h : i < 2
    · rw [if_pos h, if_pos h, hp _ (by omega)]
    · rw [if_neg h, if_neg h]
  have e1 : (if i < 1 then p (16 - 1 + i) else c (i - 1)) =
      (if i < 1 then p' (16 - 1 + i) else c (i - 1)) := by
    by_cases h : i < 1
    · rw [if_pos h, if_pos h, hp _ (by omega)]
    · rw [if_neg h, if_neg h]
  rw [e3, e2, e1]

/-! ## Blocks of the stream -/

/-- Block `b` of the stream: lane `i` is byte `16 * b + i`, zero past the end. -/
def blockOf (bs : List (BitVec 8)) (b : Nat) : V := fun i => byteAt bs (16 * b + i)

/-- The block before block `b`: zero lanes for the first. -/
def prevBlockOf (bs : List (BitVec 8)) (b : Nat) : V :=
  fun i => if b = 0 then 0 else byteAt bs (16 * (b - 1) + i)

theorem vprev_lane (bs : List (BitVec 8)) (b n i : Nat) (hn : 1 ≤ n) (hn' : n ≤ 16) (hi : i < 16) :
    vprev n (prevBlockOf bs b) (blockOf bs b) i = back bs (16 * b + i) n := by
  unfold vprev prevBlockOf blockOf back
  by_cases hin : i < n
  · rw [if_pos hin]
    by_cases hb : b = 0
    · subst hb
      rw [if_pos rfl, if_neg (by omega)]
    · rw [if_neg hb, if_pos (by omega)]
      congr 1
      omega
  · rw [if_neg hin, if_pos (by omega)]
    congr 1
    omega

/-- **Composition.** Lane `i` of block `b`, checked against the block before
it, is the lane error at stream position `16 * b + i`. -/
theorem checkBlock_lane (bs : List (BitVec 8)) (b i : Nat) (hi : i < 16) :
    checkBlock (prevBlockOf bs b) (blockOf bs b) i = flatError bs (16 * b + i) := by
  rw [checkBlock_lane_def, vprev_lane bs b 3 i (by omega) (by omega) hi,
    vprev_lane bs b 2 i (by omega) (by omega) hi, vprev_lane bs b 1 i (by omega) (by omega) hi]
  rfl

/-! ## The ASCII shortcut -/

theorem highBit_iff (x : BitVec 8) : x &&& 128 = 0 ↔ x < 0x80#8 := by bv_decide

theorem ascii_lanes (input : V) (h : vany (vand input highBit) = false) :
    ∀ i, i < 16 → input i < 0x80#8 := by
  intro i hi
  have : ¬ (vany (vand input highBit) = true) := by simp [h]
  rw [vany_iff] at this
  have hz : input i &&& 128 = 0 :=
    Decidable.byContradiction fun hne => this ⟨i, hi, hne⟩
  exact (highBit_iff _).mp hz

theorem maxima_ge (i : Nat) : 191#8 ≤ maxima i := by
  unfold maxima
  split
  · decide
  · split
    · decide
    · split
      · decide
      · decide

theorem satSub_small (x m : BitVec 8) (hx : x < 0x80#8) (hm : 191#8 ≤ m) : satSub x m = 0 := by
  unfold satSub; bv_decide

theorem satSub_zero_left (m : BitVec 8) : satSub 0 m = 0 := by
  unfold satSub; bv_decide

/-- An ASCII block leaves nothing open. -/
theorem ascii_incomplete (input : V) (hA : ∀ i, i < 16 → input i < 0x80#8) :
    ∀ i, i < 16 → incomplete input i = 0 := by
  intro i hi
  exact satSub_small _ _ (hA i hi) (maxima_ge i)

theorem incomplete_any_iff (p : V) :
    vany (incomplete p) = true ↔
      (satSub (p 13) 239 ≠ 0 ∨ satSub (p 14) 223 ≠ 0 ∨ satSub (p 15) 191 ≠ 0) := by
  rw [vany_iff]
  constructor
  · intro ⟨i, hi, h⟩
    unfold incomplete vsubs maxima at h
    by_cases h13 : i = 13
    · subst h13; simp at h; exact Or.inl h
    by_cases h14 : i = 14
    · subst h14; simp at h; exact Or.inr (Or.inl h)
    by_cases h15 : i = 15
    · subst h15; simp at h; exact Or.inr (Or.inr h)
    · rw [if_neg h13, if_neg h14, if_neg h15] at h
      exact absurd (show satSub (p i) 255 = 0 by unfold satSub; bv_decide) h
  · intro h
    rcases h with h | h | h
    · exact ⟨13, by omega, by unfold incomplete vsubs maxima; simpa using h⟩
    · exact ⟨14, by omega, by unfold incomplete vsubs maxima; simpa using h⟩
    · exact ⟨15, by omega, by unfold incomplete vsubs maxima; simpa using h⟩

theorem laneError_ascii_window (p3 p2 p1 c : BitVec 8) (h3 : p3 < 0x80#8) (h2 : p2 < 0x80#8)
    (h1 : p1 < 0x80#8) (hc : c < 0x80#8) : laneError p3 p2 p1 c = 0 := by
  unfold laneError must23 specialCases satSub high1Tbl low1Tbl high2Tbl
  bv_decide

/-- The first three lanes of an ASCII block against the last three of the
block before: nonzero exactly where that block's `incomplete` lanes are. -/
theorem ascii_head (p13 p14 p15 c0 c1 c2 : BitVec 8) (h0 : c0 < 0x80#8) (h1 : c1 < 0x80#8)
    (h2 : c2 < 0x80#8) :
    (laneError p13 p14 p15 c0 ≠ 0 ∨ laneError p14 p15 c0 c1 ≠ 0 ∨ laneError p15 c0 c1 c2 ≠ 0) ↔
      (satSub p13 239 ≠ 0 ∨ satSub p14 223 ≠ 0 ∨ satSub p15 191 ≠ 0) := by
  unfold laneError must23 specialCases satSub high1Tbl low1Tbl high2Tbl
  bv_decide

/-- **The shortcut.** For a block with no high bit set, the error lanes are
nonzero iff the previous block's `incomplete` lanes are: ORing in the
carried `incomplete` instead of classifying changes no verdict. -/
theorem ascii_block (p input : V) (hA : ∀ i, i < 16 → input i < 0x80#8) :
    vany (checkBlock p input) = true ↔ vany (incomplete p) = true := by
  rw [incomplete_any_iff, ← ascii_head (p 13) (p 14) (p 15) (input 0) (input 1) (input 2)
    (hA 0 (by omega)) (hA 1 (by omega)) (hA 2 (by omega))]
  rw [vany_iff]
  constructor
  · intro ⟨i, hi, h⟩
    rw [checkBlock_lane_def] at h
    unfold vprev at h
    by_cases hi0 : i = 0
    · subst hi0; simp at h; exact Or.inl h
    by_cases hi1 : i = 1
    · subst hi1; simp at h; exact Or.inr (Or.inl h)
    by_cases hi2 : i = 2
    · subst hi2; simp at h; exact Or.inr (Or.inr h)
    · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)] at h
      exact absurd (laneError_ascii_window _ _ _ _ (hA _ (by omega)) (hA _ (by omega))
        (hA _ (by omega)) (hA _ hi)) h
  · intro h
    rcases h with h | h | h
    · exact ⟨0, by omega, by rw [checkBlock_lane_def]; unfold vprev; simpa using h⟩
    · exact ⟨1, by omega, by rw [checkBlock_lane_def]; unfold vprev; simpa using h⟩
    · exact ⟨2, by omega, by rw [checkBlock_lane_def]; unfold vprev; simpa using h⟩

/-! ## The program -/

/-- The loop state of `valid`: the accumulated error lanes, the previous
block, and the carried `incomplete` lanes. -/
structure St where
  error : V
  prev : V
  incomplete : V

def init : St := ⟨zero, zero, zero⟩

/-- A block with a high bit set: classify it against the previous block. -/
def stepChecked (st : St) (input : V) : St :=
  ⟨vor st.error (checkBlock st.prev input), input, incomplete input⟩

/-- An ASCII block: the carried `incomplete` lanes are the errors, and the
block leaves nothing open. -/
def stepAscii (st : St) (input : V) : St := ⟨vor st.error st.incomplete, input, zero⟩

/-- One sixteen-byte iteration, and the tail block. -/
def step (st : St) (input : V) : St :=
  if vany (vand input highBit) then stepChecked st input else stepAscii st input

/-- One sixty-four-byte iteration. -/
def step64 (st : St) (a b c d : V) : St :=
  if vany (vand (vor (vor a b) (vor c d)) highBit)
  then ⟨vor st.error (checkBlocks st.prev a b c d), d, incomplete d⟩
  else ⟨vor st.error st.incomplete, d, zero⟩

/-- `!simd.any_u8x16(simd.or_u8x16(error, prev_incomplete))`. -/
def verdict (st : St) : Prop := ¬ vany (vor st.error st.incomplete) = true

/-- The sixteen-byte loop: `count` blocks from block `b`. -/
def runBlocks (bs : List (BitVec 8)) : St → Nat → Nat → St
  | st, _, 0 => st
  | st, b, count + 1 => runBlocks bs (step st (blockOf bs b)) (b + 1) count

/-- The sixty-four-byte loop: `groups` steps of four blocks from block `b`. -/
def runSteps (bs : List (BitVec 8)) : St → Nat → Nat → St
  | st, _, 0 => st
  | st, b, g + 1 =>
    runSteps bs (step64 st (blockOf bs b) (blockOf bs (b + 1)) (blockOf bs (b + 2)) (blockOf bs (b + 3)))
      (b + 4) g

/-- `valid` as the program runs it: the sixty-four-byte loop over the full
steps, the sixteen-byte loop over the remaining full blocks, then the
zero-padded tail block — block `n / 16`, whose lanes past the input read
zero. -/
def program (bs : List (BitVec 8)) : St :=
  let n := bs.length
  let afterSteps := runSteps bs init 0 (n / 64)
  let afterBlocks := runBlocks bs afterSteps (4 * (n / 64)) (n / 16 - 4 * (n / 64))
  step afterBlocks (blockOf bs (n / 16))

/-! ## The always-classifying reference -/

/-- Every block classified, in order from the zero block. -/
def ref (bs : List (BitVec 8)) : Nat → St
  | 0 => init
  | b + 1 => stepChecked (ref bs b) (blockOf bs b)

/-- Two states the verdict cannot tell apart: the same error verdict and the
same previous-block and `incomplete` lanes. -/
def Equiv (s t : St) : Prop :=
  (vany s.error = true ↔ vany t.error = true) ∧ (∀ i, i < 16 → s.prev i = t.prev i) ∧
    (∀ i, i < 16 → s.incomplete i = t.incomplete i)

/-- The carried `incomplete` lanes are those of the previous block. -/
def Inv (s : St) : Prop := ∀ i, i < 16 → s.incomplete i = incomplete s.prev i

theorem Equiv.refl (s : St) : Equiv s s := ⟨Iff.rfl, fun _ _ => rfl, fun _ _ => rfl⟩

theorem Equiv.trans {s t u : St} (h1 : Equiv s t) (h2 : Equiv t u) : Equiv s u :=
  ⟨h1.1.trans h2.1, fun i hi => (h1.2.1 i hi).trans (h2.2.1 i hi),
    fun i hi => (h1.2.2 i hi).trans (h2.2.2 i hi)⟩

theorem verdict_of_equiv {s t : St} (h : Equiv s t) : verdict s ↔ verdict t := by
  unfold verdict
  rw [vany_vor, vany_vor, h.1, vany_congr s.incomplete t.incomplete h.2.2]

theorem inv_init : Inv init := by
  intro i _
  show (0 : BitVec 8) = satSub 0 (maxima i)
  rw [satSub_zero_left]

theorem inv_stepChecked (s : St) (input : V) : Inv (stepChecked s input) := fun _ _ => rfl

theorem inv_step (s : St) (input : V) : Inv (step s input) := by
  unfold step
  split <;> rename_i h
  · exact inv_stepChecked s input
  · intro i hi
    show (0 : BitVec 8) = incomplete input i
    rw [ascii_incomplete input (ascii_lanes input (by simpa using h)) i hi]

theorem stepChecked_equiv {s t : St} (h : Equiv s t) (input : V) :
    Equiv (stepChecked s input) (stepChecked t input) := by
  refine ⟨?_, fun _ _ => rfl, fun _ _ => rfl⟩
  show vany (vor s.error (checkBlock s.prev input)) = true ↔
    vany (vor t.error (checkBlock t.prev input)) = true
  rw [vany_vor, vany_vor, h.1, vany_congr (checkBlock s.prev input) (checkBlock t.prev input)
    (fun i hi => checkBlock_congr _ _ _ h.2.1 i hi)]

/-- The sixteen-byte step is the classifying step up to the verdict. -/
theorem step_equiv (s : St) (hs : Inv s) (input : V) : Equiv (step s input) (stepChecked s input) := by
  unfold step
  split <;> rename_i h
  · exact Equiv.refl _
  · have hA := ascii_lanes input (by simpa using h)
    refine ⟨?_, fun _ _ => rfl, ?_⟩
    · show vany (vor s.error s.incomplete) = true ↔ vany (vor s.error (checkBlock s.prev input)) = true
      rw [vany_vor, vany_vor, ascii_block s.prev input hA,
        vany_congr s.incomplete (incomplete s.prev) hs]
    · intro i hi
      show (0 : BitVec 8) = incomplete input i
      rw [ascii_incomplete input hA i hi]

/-- The sixty-four-byte step is four classifying steps up to the verdict. -/
theorem step64_equiv (s : St) (hs : Inv s) (a b c d : V) :
    Equiv (step64 s a b c d) (stepChecked (stepChecked (stepChecked (stepChecked s a) b) c) d) := by
  unfold step64
  split <;> rename_i h
  · refine ⟨?_, fun _ _ => rfl, fun _ _ => rfl⟩
    show vany (vor s.error (checkBlocks s.prev a b c d)) = true ↔
      vany (vor (vor (vor (vor s.error (checkBlock s.prev a)) (checkBlock a b)) (checkBlock b c))
        (checkBlock c d)) = true
    unfold checkBlocks
    simp only [vany_vor]
    constructor
    · rintro (h | (h | h) | (h | h))
      · exact Or.inl (Or.inl (Or.inl (Or.inl h)))
      · exact Or.inl (Or.inl (Or.inl (Or.inr h)))
      · exact Or.inl (Or.inl (Or.inr h))
      · exact Or.inl (Or.inr h)
      · exact Or.inr h
    · rintro ((((h | h) | h) | h) | h)
      · exact Or.inl h
      · exact Or.inr (Or.inl (Or.inl h))
      · exact Or.inr (Or.inl (Or.inr h))
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr h))
  · have hall : ∀ i, i < 16 → (vor (vor a b) (vor c d)) i < 0x80#8 :=
      ascii_lanes _ (by simpa using h)
    have hA : ∀ i, i < 16 → a i < 0x80#8 := fun i hi => by
      have := hall i hi; unfold vor at this; bv_decide
    have hB : ∀ i, i < 16 → b i < 0x80#8 := fun i hi => by
      have := hall i hi; unfold vor at this; bv_decide
    have hC : ∀ i, i < 16 → c i < 0x80#8 := fun i hi => by
      have := hall i hi; unfold vor at this; bv_decide
    have hD : ∀ i, i < 16 → d i < 0x80#8 := fun i hi => by
      have := hall i hi; unfold vor at this; bv_decide
    have noA : ¬ vany (checkBlock a b) = true := by
      rw [ascii_block a b hB, vany_iff]
      intro ⟨i, hi, hne⟩; exact hne (ascii_incomplete a hA i hi)
    have noB : ¬ vany (checkBlock b c) = true := by
      rw [ascii_block b c hC, vany_iff]
      intro ⟨i, hi, hne⟩; exact hne (ascii_incomplete b hB i hi)
    have noC : ¬ vany (checkBlock c d) = true := by
      rw [ascii_block c d hD, vany_iff]
      intro ⟨i, hi, hne⟩; exact hne (ascii_incomplete c hC i hi)
    refine ⟨?_, fun _ _ => rfl, ?_⟩
    · show vany (vor s.error s.incomplete) = true ↔
        vany (vor (vor (vor (vor s.error (checkBlock s.prev a)) (checkBlock a b)) (checkBlock b c))
          (checkBlock c d)) = true
      simp only [vany_vor]
      rw [ascii_block s.prev a hA, vany_congr s.incomplete (incomplete s.prev) hs]
      constructor
      · intro h; exact Or.inl (Or.inl (Or.inl h))
      · intro h
        rcases h with ((h | h) | h) | h
        · exact h
        · exact absurd h noA
        · exact absurd h noB
        · exact absurd h noC
    · intro i hi
      show (0 : BitVec 8) = incomplete d i
      rw [ascii_incomplete d hD i hi]

theorem inv_step64 (s : St) (a b c d : V) : Inv (step64 s a b c d) := by
  unfold step64
  split <;> rename_i h
  · intro _ _; rfl
  · have hall : ∀ i, i < 16 → (vor (vor a b) (vor c d)) i < 0x80#8 :=
      ascii_lanes _ (by simpa using h)
    have hD : ∀ i, i < 16 → d i < 0x80#8 := fun i hi => by
      have := hall i hi; unfold vor at this; bv_decide
    intro i hi
    show (0 : BitVec 8) = incomplete d i
    rw [ascii_incomplete d hD i hi]

theorem runBlocks_equiv (bs : List (BitVec 8)) :
    ∀ (count : Nat) (s : St) (b : Nat), Inv s → Equiv s (ref bs b) →
      Inv (runBlocks bs s b count) ∧ Equiv (runBlocks bs s b count) (ref bs (b + count)) := by
  intro count
  induction count with
  | zero => intro s b hs h; exact ⟨hs, h⟩
  | succ count ih =>
    intro s b hs h
    show Inv (runBlocks bs (step s (blockOf bs b)) (b + 1) count) ∧
      Equiv (runBlocks bs (step s (blockOf bs b)) (b + 1) count) (ref bs (b + (count + 1)))
    rw [show b + (count + 1) = (b + 1) + count by omega]
    exact ih _ _ (inv_step s _) ((step_equiv s hs _).trans (stepChecked_equiv h _))

theorem runSteps_equiv (bs : List (BitVec 8)) :
    ∀ (g : Nat) (s : St) (b : Nat), Inv s → Equiv s (ref bs b) →
      Inv (runSteps bs s b g) ∧ Equiv (runSteps bs s b g) (ref bs (b + 4 * g)) := by
  intro g
  induction g with
  | zero => intro s b hs h; exact ⟨hs, h⟩
  | succ g ih =>
    intro s b hs h
    show Inv (runSteps bs (step64 s (blockOf bs b) (blockOf bs (b + 1)) (blockOf bs (b + 2))
        (blockOf bs (b + 3))) (b + 4) g) ∧
      Equiv (runSteps bs (step64 s (blockOf bs b) (blockOf bs (b + 1)) (blockOf bs (b + 2))
        (blockOf bs (b + 3))) (b + 4) g) (ref bs (b + 4 * (g + 1)))
    rw [show b + 4 * (g + 1) = (b + 4) + 4 * g by omega]
    refine ih _ _ (inv_step64 s _ _ _ _) ((step64_equiv s hs _ _ _ _).trans ?_)
    show Equiv _ (stepChecked (stepChecked (stepChecked (stepChecked (ref bs b) (blockOf bs b))
      (blockOf bs (b + 1))) (blockOf bs (b + 2))) (blockOf bs (b + 3)))
    exact stepChecked_equiv (stepChecked_equiv (stepChecked_equiv (stepChecked_equiv h _) _) _) _

/-- The program is the reference over `n / 16 + 1` blocks, up to the verdict:
the sixty-four-byte steps cover the first `4 * (n / 64)` blocks, the
sixteen-byte loop the rest up to `n / 16`, and the tail is block `n / 16`. -/
theorem program_equiv (bs : List (BitVec 8)) :
    Equiv (program bs) (ref bs (bs.length / 16 + 1)) := by
  unfold program
  obtain ⟨inv1, h1⟩ := runSteps_equiv bs (bs.length / 64) init 0 inv_init (Equiv.refl init)
  rw [Nat.zero_add] at h1
  obtain ⟨inv2, h2⟩ := runBlocks_equiv bs (bs.length / 16 - 4 * (bs.length / 64)) _
    (4 * (bs.length / 64)) inv1 h1
  have hb : 4 * (bs.length / 64) + (bs.length / 16 - 4 * (bs.length / 64)) = bs.length / 16 := by
    omega
  rw [hb] at h2
  exact (step_equiv _ inv2 _).trans (stepChecked_equiv h2 _)

/-! ## The reference decides the flat stream -/

theorem ref_spec (bs : List (BitVec 8)) : ∀ b : Nat,
    (∀ i, i < 16 → (ref bs b).prev i = prevBlockOf bs b i) ∧
    (∀ i, i < 16 → (ref bs b).incomplete i = incomplete (prevBlockOf bs b) i) ∧
    (vany (ref bs b).error = true ↔
      ∃ b', b' < b ∧ vany (checkBlock (prevBlockOf bs b') (blockOf bs b')) = true)
  | 0 => by
    refine ⟨fun i _ => ?_, fun i _ => ?_, ?_⟩
    · simp [ref, init, zero, vsplat, prevBlockOf]
    · show (0 : BitVec 8) = satSub (prevBlockOf bs 0 i) (maxima i)
      unfold prevBlockOf
      rw [if_pos rfl, satSub_zero_left]
    · simp [ref, init, zero, vsplat, vany_iff]
  | b + 1 => by
    obtain ⟨hp, _, herr⟩ := ref_spec bs b
    have hblock : ∀ i, blockOf bs b i = prevBlockOf bs (b + 1) i := by
      intro i
      unfold blockOf prevBlockOf
      rw [if_neg (Nat.succ_ne_zero b), Nat.add_sub_cancel]
    refine ⟨fun i _ => hblock i, fun i _ => ?_, ?_⟩
    · show incomplete (blockOf bs b) i = incomplete (prevBlockOf bs (b + 1)) i
      unfold incomplete vsubs
      rw [hblock]
    · show vany (vor (ref bs b).error (checkBlock (ref bs b).prev (blockOf bs b))) = true ↔ _
      rw [vany_vor, herr, vany_congr _ (checkBlock (prevBlockOf bs b) (blockOf bs b))
        (fun i hi => checkBlock_congr _ _ _ hp i hi)]
      constructor
      · rintro (⟨b', hb', h⟩ | h)
        · exact ⟨b', by omega, h⟩
        · exact ⟨b, by omega, h⟩
      · rintro ⟨b', hb', h⟩
        by_cases hlt : b' < b
        · exact Or.inl ⟨b', hlt, h⟩
        · have : b' = b := by omega
          subst this
          exact Or.inr h

theorem ref_verdict (bs : List (BitVec 8)) (B : Nat) :
    verdict (ref bs B) ↔
      (∀ b, b < B → ∀ i, i < 16 → checkBlock (prevBlockOf bs b) (blockOf bs b) i = 0) ∧
        (∀ i, i < 16 → incomplete (prevBlockOf bs B) i = 0) := by
  obtain ⟨_, hinc, herr⟩ := ref_spec bs B
  unfold verdict
  rw [vany_vor, herr, vany_congr _ _ hinc, vany_iff]
  constructor
  · intro h
    refine ⟨fun b hb i hi => ?_, fun i hi => ?_⟩
    · exact Decidable.byContradiction fun hne => h (Or.inl ⟨b, hb, (vany_iff _).mpr ⟨i, hi, hne⟩⟩)
    · exact Decidable.byContradiction fun hne => h (Or.inr ⟨i, hi, hne⟩)
  · rintro ⟨hz, hinc0⟩ (⟨b, hb, h⟩ | ⟨i, hi, h⟩)
    · obtain ⟨i, hi, hne⟩ := (vany_iff _).mp h
      exact hne (hz b hb i hi)
    · exact h (hinc0 i hi)

/-- No `incomplete` lane iff the block's last three bytes are a boundary. -/
theorem incomplete_zero_iff (p : V) :
    (∀ i, i < 16 → incomplete p i = 0) ↔ Boundary (p 13) (p 14) (p 15) := by
  have key := incomplete_any_iff p
  rw [vany_iff] at key
  constructor
  · intro h
    have hno : ¬ (satSub (p 13) 239 ≠ 0 ∨ satSub (p 14) 223 ≠ 0 ∨ satSub (p 15) 191 ≠ 0) := by
      rw [← key]
      rintro ⟨i, hi, hne⟩
      exact hne (h i hi)
    unfold Boundary; unfold satSub at hno
    bv_decide
  · intro hb i hi
    refine Decidable.byContradiction fun hne => ?_
    have := key.mp ⟨i, hi, hne⟩
    unfold Boundary at hb; unfold satSub at this
    bv_decide

theorem prevBlockOf_ctx (bs : List (BitVec 8)) (B : Nat) (hB : 1 ≤ B) :
    prevBlockOf bs B 13 = back bs (16 * B) 3 ∧ prevBlockOf bs B 14 = back bs (16 * B) 2 ∧
      prevBlockOf bs B 15 = back bs (16 * B) 1 := by
  have hB0 : ¬ B = 0 := by omega
  have h3 : 3 ≤ 16 * B := by omega
  have h2 : 2 ≤ 16 * B := by omega
  have h1 : 1 ≤ 16 * B := by omega
  unfold prevBlockOf back
  simp only [hB0, h1, h2, h3, if_false, if_true]
  refine ⟨?_, ?_, ?_⟩ <;> congr 1 <;> omega

/-- **The program decides the flat stream.** -/
theorem program_flat (bs : List (BitVec 8)) : verdict (program bs) ↔ ∀ k, flatError bs k = 0 := by
  rw [verdict_of_equiv (program_equiv bs), ref_verdict]
  have hnB : bs.length ≤ 16 * (bs.length / 16 + 1) := by omega
  have hB1 : 1 ≤ bs.length / 16 + 1 := by omega
  obtain ⟨c13, c14, c15⟩ := prevBlockOf_ctx bs (bs.length / 16 + 1) hB1
  rw [incomplete_zero_iff, c13, c14, c15]
  constructor
  · rintro ⟨hz, hb⟩ k
    by_cases hk : k < 16 * (bs.length / 16 + 1)
    · have := hz (k / 16) (by omega) (k % 16) (by omega)
      rw [checkBlock_lane bs _ _ (by omega)] at this
      rwa [show 16 * (k / 16) + k % 16 = k by omega] at this
    · exact flat_beyond bs _ hnB hb k (by omega)
  · intro h
    refine ⟨fun b _ i hi => ?_, ?_⟩
    · rw [checkBlock_lane bs b i hi]
      exact h _
    · exact (flatError_at_end bs _ hnB).mp (h _)

/-- **The program theorem.** `utf8.valid`, as the vector program runs it —
sixty-four-byte steps, the sixteen-byte remainder, the zero-padded tail,
both ASCII shortcuts — accepts exactly the valid UTF-8 streams of Unicode
Table 3-7 (`Oak.Utf8Validity.Valid`). -/
theorem program_valid (bs : List (BitVec 8)) :
    verdict (program bs) ↔ Oak.Utf8Validity.Valid (bs.map BitVec.toNat) := by
  rw [program_flat, flat_valid]

end Oak.Utf8Blocks
