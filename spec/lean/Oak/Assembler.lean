import Std.Tactic.BVDecide
/-!
# The typed assembler: seam laws

`docs/spec/94-assembler.md` §3–§4. The asm checker (`asm/check.go`) is
maintained as the transliteration of the laws here:

* **register aliasing** — `wN` and `xN` name one physical register, so a
  write through either width is a write of the same authority slot
  (`asm.checker.write` keys on the physical number);
* **alignment extents** — every AArch64 instruction is 4 bytes, so an
  aligned region of `k` instructions fits its `N`-byte stride exactly when
  `4k ≤ N`, and a table of `n` such regions occupies `n·N` bytes: sixteen
  128-byte entries are exactly a 2 KiB vector table
  (`asm.checker.closeRegion`);
* **frame bounds** — an access at `addr` (relative to the entry sp) of
  `size` bytes lies inside the declared frame `[-frame, 0)` exactly when
  `-frame ≤ addr` and `addr + size ≤ 0`, and a chain of such accesses never
  touches memory the frame does not own (`asm.checker.checkAccess`).
-/

namespace Oak.Assembler

/-- Register width views of the general-purpose file. -/
inductive Width where
  | x   -- 64-bit view
  | w   -- 32-bit view
  deriving DecidableEq, Repr

/-- A general register operand: a width view of a physical register. -/
structure Reg where
  width : Width
  num : Nat
  deriving DecidableEq, Repr

/-- The physical register an operand names: the view is erased. -/
def physical (r : Reg) : Nat := r.num

/-- Aliasing: the 32-bit and 64-bit views of register `n` are one
    authority slot. A clobber declaration or binding for either covers
    both, and a write through either is a write of the same register. -/
theorem alias_same_physical (n : Nat) :
    physical ⟨Width.w, n⟩ = physical ⟨Width.x, n⟩ := rfl

/-- Two operands touch the same register iff their numbers agree,
    whatever their widths. -/
theorem same_register_iff (a b : Reg) :
    physical a = physical b ↔ a.num = b.num := Iff.rfl

/-- AArch64 instructions are fixed-width. -/
def instructionBytes : Nat := 4

/-- The byte extent of a region of `k` instructions. -/
def regionBytes (k : Nat) : Nat := k * instructionBytes

/-- A region fits its alignment stride when its bytes do not exceed it. -/
def Fits (k stride : Nat) : Prop := regionBytes k ≤ stride

theorem fits_iff (k stride : Nat) : Fits k stride ↔ 4 * k ≤ stride := by
  unfold Fits regionBytes instructionBytes
  constructor <;> intro h <;> omega

/-- The transliterated extent check. -/
def fitsCheck (k stride : Nat) : Bool := decide (k * 4 ≤ stride)

theorem fitsCheck_sound (k stride : Nat) (h : fitsCheck k stride = true) :
    Fits k stride := by
  unfold fitsCheck at h
  unfold Fits regionBytes instructionBytes
  exact of_decide_eq_true h

theorem fitsCheck_complete (k stride : Nat) (h : Fits k stride) :
    fitsCheck k stride = true := by
  unfold Fits regionBytes instructionBytes at h
  unfold fitsCheck
  exact decide_eq_true h

/-- A table of `n` aligned entries at stride `N` occupies `n * N` bytes
    when every entry fits: the entries are laid end to end at exactly one
    stride each. -/
def tableBytes (entries stride : Nat) : Nat := entries * stride

/-- The exception vector table: sixteen 128-byte entries are exactly 2 KiB,
    so a table aligned to 2048 whose entries each fit 128 bytes has no
    padding between entries and its extent equals its alignment. -/
theorem vector_table_extent : tableBytes 16 128 = 2048 := rfl

/-- An entry of at most 32 instructions fits a 128-byte slot. -/
theorem vector_entry_fits (k : Nat) (h : k ≤ 32) : Fits k 128 := by
  rw [fits_iff]; omega

/-- Frame bounds: the declared frame is `[-frame, 0)` relative to the
    entry sp. Integers model signed byte addresses. -/
def InFrame (frame addr size : Int) : Prop :=
  -frame ≤ addr ∧ addr + size ≤ 0

/-- The transliterated access check. -/
def accessCheck (frame addr size : Int) : Bool :=
  decide (-frame ≤ addr ∧ addr + size ≤ 0)

theorem accessCheck_sound (frame addr size : Int)
    (h : accessCheck frame addr size = true) : InFrame frame addr size := by
  unfold accessCheck at h
  unfold InFrame
  exact of_decide_eq_true h

theorem accessCheck_complete (frame addr size : Int)
    (h : InFrame frame addr size) : accessCheck frame addr size = true := by
  unfold InFrame at h
  unfold accessCheck
  exact decide_eq_true h

/-- Every byte of an in-frame access lies inside the frame interval: the
    access cannot reach memory the frame does not own. -/
theorem inFrame_bytes (frame addr size b : Int) (h : InFrame frame addr size)
    (hb : addr ≤ b ∧ b < addr + size) : -frame ≤ b ∧ b < 0 := by
  obtain ⟨hlo, hhi⟩ := h
  obtain ⟨hb1, hb2⟩ := hb
  constructor <;> omega

/-- The static sp displacement stays inside `[0, frame]` under a move by
    `delta` exactly when the checker's bound holds — the invariant that
    makes `checkAccess`'s `-disp + offset` arithmetic meaningful. -/
def DispOk (frame disp : Int) : Prop := 0 ≤ disp ∧ disp ≤ frame

theorem disp_move (frame disp delta : Int) (h : DispOk frame (disp + delta)) :
    0 ≤ disp + delta ∧ disp + delta ≤ frame := h

/-- Typed pointer memory: a span of `len` elements of `elem` bytes owns
    bytes `[0, elem*len)`. A dominating guard establishes `minLen ≤ len`;
    the checker admits an access `[off, off+size)` when
    `off + size ≤ elem * minLen` — which places every accessed byte inside
    the span for every runtime length the guard admits
    (`asm.checker.spanAccess`). -/
def SpanAccessOk (elem minLen off size : Nat) : Prop :=
  off + size ≤ elem * minLen

theorem span_access (elem minLen len off size : Nat)
    (hguard : minLen ≤ len) (hacc : SpanAccessOk elem minLen off size) :
    off + size ≤ elem * len := by
  unfold SpanAccessOk at hacc
  calc off + size ≤ elem * minLen := hacc
    _ ≤ elem * len := Nat.mul_le_mul_left elem hguard

/-- **A wide load assembles the elements** (the executor's model of a load
    wider than the span's element, docs/spec/94-assembler.md §8): eight
    consecutive bytes read as one 64-bit little-endian word are the or of
    each byte zero-extended and shifted to its position — the term Oak's
    `u64(v[i]) | u64(v[i+1]) << 8 | … | u64(v[i+7]) << 56` spells — so the
    native backend's one `ldr x` is the same value as the eight byte reads. -/
theorem wide_load_assembles (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0 : BitVec 64) =
      b0.zeroExtend 64 ||| (b1.zeroExtend 64 <<< 8) ||| (b2.zeroExtend 64 <<< 16) |||
      (b3.zeroExtend 64 <<< 24) ||| (b4.zeroExtend 64 <<< 32) ||| (b5.zeroExtend 64 <<< 40) |||
      (b6.zeroExtend 64 <<< 48) ||| (b7.zeroExtend 64 <<< 56) := by
  bv_decide

/-- The 32-bit form: four bytes. -/
theorem wide_load_assembles32 (b0 b1 b2 b3 : BitVec 8) :
    (b3 ++ b2 ++ b1 ++ b0 : BitVec 32) =
      b0.zeroExtend 32 ||| (b1.zeroExtend 32 <<< 8) ||| (b2.zeroExtend 32 <<< 16) ||| (b3.zeroExtend 32 <<< 24) := by
  bv_decide

/-- **The sum shape of a slack guard** (the checker's `sumFacts`,
    docs/spec/94-assembler.md §7): `len(v) >= i + K` as the generator spells
    it — `add wS, wI, #K; cmp wL, wS; b.lo <exit>` — proves `i + K ≤ len` on
    the fall-through, the slack fact under which element `i + k` for every
    `k < K` lies inside the span. -/
theorem sum_guard_slack (len i K k : Nat) (hguard : i + K ≤ len) (hk : k < K) : i + k < len := by
  omega

/-- **Index under an equal length** (the checker's `lenEqual` fact,
    docs/spec/94-assembler.md §7): `cmp wA, wB; b.ne <exit>` proves the two
    lengths equal on the fall-through path, so an index guarded below one
    span's length is below the other's — the second span walked in step
    (`len(a) == len(b) ? { ... a[i] ... b[i] ... }`) needs no guard of its
    own. -/
theorem index_under_equal_len (i la lb : Nat) (hi : i < la) (heq : la = lb) : i < lb := by
  omega

/-! ### Bounds through arithmetic (asm/bounds_arith.go, docs/spec/94-assembler.md §7)

The checker follows a proven bound through the arithmetic between the
guard and the access: the binary search midpoint, a bound narrowed by a
copy, an index scaled back to the units of a length divided by a power of
two. Each rule is one of the lemmas below; the register values are
naturals below `2^32`, and each lemma's conclusion is below its
hypotheses' bound, so none of the operations wraps. -/

/-- **The midpoint** (`midFact`): `sub wT, wHi, wLo` under `wLo < wHi`,
    `lsr wT, wT, #1`, `add wMid, wLo, wT` — `lo + (hi - lo) / 2 < hi`, so
    the element at the midpoint is below the bound `hi` is. The subtraction
    is exact under `lo < hi` and the sum is below `hi`, so neither wraps. -/
theorem midpoint_below (lo hi : Nat) (h : lo < hi) : lo + (hi - lo) / 2 < hi := by
  omega

/-- Halving more than once keeps the midpoint below `hi`. -/
theorem midpoint_below_shift (lo hi k : Nat) (h : lo < hi) (hk : 1 ≤ k) :
    lo + (hi - lo) / 2 ^ k < hi := by
  have h2 : 2 ≤ 2 ^ k := by
    have := Nat.pow_le_pow_right (show 2 > 0 by decide) hk
    rwa [Nat.pow_one] at this
  have hdiv : (hi - lo) / 2 ^ k ≤ (hi - lo) / 2 := Nat.div_le_div_left h2 (by decide)
  omega

/-- **The narrowing copy** (`upperFact`): `mov wHi, wMid` under `wMid < wHi`
    with `wHi ≤ len` leaves the new `hi` at most `len`. -/
theorem narrowed_upper (m h len : Nat) (hm : m < h) (hh : h ≤ len) : m ≤ len := by
  omega

/-- **An index under an upper bound**: guarded below a register that is at
    most the length, the index is below the length — the access rule's
    reading of an upper chain (`checker.boundsLen`). -/
theorem index_under_upper (i b len : Nat) (hi : i < b) (hb : b ≤ len) : i < len := by
  omega

/-- An upper chain composes: `r ≤ s >>> a` and `s ≤ t >>> b` give
    `r ≤ t >>> (a + b)` (`checker.resolveUpper` sums the shifts). -/
theorem upper_chain (r s t a b : Nat) (hr : r ≤ s / 2 ^ a) (hs : s ≤ t / 2 ^ b) :
    r ≤ t / 2 ^ (a + b) := by
  have h1 : s / 2 ^ a ≤ (t / 2 ^ b) / 2 ^ a := Nat.div_le_div_right hs
  rw [Nat.div_div_eq_div_mul, ← Nat.pow_add, Nat.add_comm] at h1
  omega

/-- **The scaled index** (`lsl wD, wI, #k`): under `wI < wB`, `wB ≤ len / 2^s`,
    and `k ≤ s`, the `2^k` elements from `wI · 2^k` lie inside the span —
    the slack fact `wD + 2^k ≤ len` — and `wI · 2^k` is below `len`, so the
    32-bit shift does not wrap. -/
theorem shifted_index_slack (i b len k s : Nat) (hi : i < b) (hb : b ≤ len / 2 ^ s) (hk : k ≤ s) :
    i * 2 ^ k + 2 ^ k ≤ len := by
  have h1 : (i + 1) * 2 ^ k ≤ b * 2 ^ k := Nat.mul_le_mul_right _ hi
  have h2 : b * 2 ^ k ≤ b * 2 ^ s := Nat.mul_le_mul_left b (Nat.pow_le_pow_right (show 2 > 0 by decide) hk)
  have h3 : b * 2 ^ s ≤ (len / 2 ^ s) * 2 ^ s := Nat.mul_le_mul_right _ hb
  have h4 : (len / 2 ^ s) * 2 ^ s ≤ len := Nat.div_mul_le_self len (2 ^ s)
  have h5 : (i + 1) * 2 ^ k = i * 2 ^ k + 2 ^ k := by rw [Nat.add_mul, Nat.one_mul]
  omega

/-- A slack fact carried through `add wJ, wD, #j` with `j < 2^k` admits the
    element `wD + j` (the rule `add` carries, restated for the scaled index). -/
theorem shifted_index_element (i len k j : Nat) (hslack : i * 2 ^ k + 2 ^ k ≤ len) (hj : j < 2 ^ k) :
    i * 2 ^ k + j < len := by
  omega

/-! ### The divided bound (`udiv`, `mul`; docs/spec/94-assembler.md §7)

A length divided by a constant that is not a power of two — `entries =
len(table) / 3` before a binary search over a three-word table — and the
index multiplied back by it. The shift rules above are these with the
divisor `2 ^ s`; `checker.resolveUpper` multiplies the divisors along a
chain where it summed the shifts. -/

/-- An upper chain composes through arbitrary divisors: `r ≤ s / a` and
    `s ≤ t / b` give `r ≤ t / (b * a)` (`checker.resolveUpper`). Generalizes
    `upper_chain`, whose divisors are `2 ^ a` and `2 ^ b`. -/
theorem upper_chain_div (r s t a b : Nat) (hr : r ≤ s / a) (hs : s ≤ t / b) :
    r ≤ t / (b * a) := by
  have h1 : s / a ≤ (t / b) / a := Nat.div_le_div_right hs
  rw [Nat.div_div_eq_div_mul] at h1
  omega

/-- **The divided bound** (`udiv wE, wS, wD` with `wD` a known constant `d`):
    a source already at most `t / a` leaves the quotient at most `t / (a * d)`,
    which is the upper fact the checker records on the quotient. With no fact
    on the source, `a = 1`. -/
theorem divided_upper (s t a d : Nat) (hs : s ≤ t / a) : s / d ≤ t / (a * d) := by
  have h1 : s / d ≤ (t / a) / d := Nat.div_le_div_right hs
  rw [Nat.div_div_eq_div_mul] at h1
  omega

/-- **The scaled index** (`mul wD, wI, wK` with `wK` a known constant `k`):
    under `wI < wB`, `wB ≤ len / d` and `k ≤ d`, the `k` elements from
    `wI · k` lie inside the span — the slack fact `wD + k ≤ len`. Generalizes
    `shifted_index_slack`, whose `k` and `d` are `2 ^ k` and `2 ^ s`. -/
theorem scaled_index_slack (i b len k d : Nat) (hi : i < b) (hb : b ≤ len / d) (hk : k ≤ d) :
    i * k + k ≤ len := by
  have h1 : (i + 1) * k ≤ b * k := Nat.mul_le_mul_right _ hi
  have h2 : b * k ≤ b * d := Nat.mul_le_mul_left b hk
  have h3 : b * d ≤ (len / d) * d := Nat.mul_le_mul_right _ hb
  have h4 : (len / d) * d ≤ len := Nat.div_mul_le_self len d
  have h5 : (i + 1) * k = i * k + k := by rw [Nat.add_mul, Nat.one_mul]
  omega

/-- A slack fact carried through `add wJ, wD, #j` with `j < k` admits the
    element `wD + j` — `table[mid * 3 + 1]` under `mid < len / 3`. -/
theorem scaled_index_element (i len k j : Nat) (hslack : i * k + k ≤ len) (hj : j < k) :
    i * k + j < len := by
  omega

/-- The same slack fact carried through a wider index: an access of `w`
    elements at `wD + j` stays inside when `j + w ≤ k`. -/
theorem scaled_index_run (i len k j w : Nat) (hslack : i * k + k ≤ len) (hj : j + w ≤ k) :
    i * k + j + w ≤ len := by
  omega

/-! ### A ceiling that survives a loop (docs/spec/94-assembler.md §9.ak)

A binary search rewrites its bound register on the back edge, so the
register holds no constant at the loop header and only a fact both
predecessors state survives the meet. These three carry the ceiling
across it. -/

/-- **The midpoint through a division** (`udiv wT, wT, wD` with `wD` a
    constant `d ≥ 2`): the generator spells `(hi - lo) / 2` as a division
    rather than a shift, and the quotient is still below the difference, so
    the midpoint stays below `hi`. Generalizes `midpoint_below_shift`. -/
theorem midpoint_below_div (lo hi d : Nat) (h : lo < hi) (hd : 2 ≤ d) :
    lo + (hi - lo) / d < hi := by
  have h1 : (hi - lo) / d ≤ (hi - lo) / 2 := Nat.div_le_div_left hd (by decide)
  have h2 : (hi - lo) / 2 < hi - lo := Nat.div_lt_self (by omega) (by decide)
  omega

/-- **The transitive ceiling** (`checker.constBound`): an index below a
    register that is itself below `K` is below `K - 1`, since the register
    is at most `K - 1` and the index is strictly below it. Stated for
    `2 ≤ K`, which is what the checker requires before it subtracts. -/
theorem transitive_const_bound (i b K : Nat) (hi : i < b) (hb : b < K) (hK : 2 ≤ K) :
    i < K - 1 := by
  omega

/-- **The select of two ceilings** (`csel wD, wA, wB, cond`): the result is
    one of its arms, so it is below the larger ceiling. This is what a
    search's bound register carries across its back edge. -/
theorem select_const_bound (a b Ka Kb : Nat) (ha : a < Ka) (hb : b < Kb) :
    a < max Ka Kb ∧ b < max Ka Kb := by
  constructor
  · exact Nat.lt_of_lt_of_le ha (Nat.le_max_left Ka Kb)
  · exact Nat.lt_of_lt_of_le hb (Nat.le_max_right Ka Kb)

/-- The whole chain of the binary search, as the checker reads it: the
    midpoint of a search bounded by `entries = len / k` scaled back by `k`
    with an offset below `k` lands inside the table. -/
theorem search_midpoint_in_table (lo hi entries len k j d : Nat)
    (hlo : lo < hi) (hhi : hi ≤ entries) (hd : 2 ≤ d) (hk : 1 ≤ k)
    (hentries : entries * k ≤ len) (hj : j < k) :
    (lo + (hi - lo) / d) * k + j < len := by
  have hmid : lo + (hi - lo) / d < hi := midpoint_below_div lo hi d hlo hd
  have h1 : (lo + (hi - lo) / d) + 1 ≤ entries := by omega
  have h2 : ((lo + (hi - lo) / d) + 1) * k ≤ entries * k := Nat.mul_le_mul_right k h1
  have h3 : ((lo + (hi - lo) / d) + 1) * k = (lo + (hi - lo) / d) * k + k := by
    rw [Nat.add_mul, Nat.one_mul]
  omega

/-! ### If-conversion (nativegen/select.go, docs/spec/94-assembler.md §9)

A conditional chain over one comparison lowers as one compare and a select
per assigned variable. The comparison has three outcomes; an operator
accepts a set of them; an arm fires on the outcomes its operator accepts
less those the arms before it accept, so the arms' conditions are disjoint
and the nested selects, from the last arm to the first, equal the first
matching arm. The checker's rule: a select of two bounded values is bounded. -/

/-- The outcomes of one integer comparison: below, equal, above. -/
inductive Outcome where
  | below | equal | above
  deriving DecidableEq

/-- An operator accepts a set of outcomes; an arm carries its acceptance
    and the value it assigns. -/
abbrev Accepts := Outcome → Bool

/-- The chain's meaning: the value of the first arm whose operator accepts
    the outcome, or the variable's old value. -/
def firstArm (arms : List (Accepts × Nat)) (o : Outcome) (old : Nat) : Nat :=
  match arms with
  | [] => old
  | (m, v) :: rest => if m o then v else firstArm rest o old

/-- An arm's exclusive condition: its operator's outcomes less the earlier
    arms' (`outcomeMasks[op] &^ seen`). -/
def exclusive (seen m : Accepts) (o : Outcome) : Bool := m o && !seen o

/-- The lowered chain: `csel` under each arm's exclusive condition, the
    first arm outermost, the old value innermost. -/
def selectChain (arms : List (Accepts × Nat)) (seen : Accepts) (o : Outcome) (old : Nat) : Nat :=
  match arms with
  | [] => old
  | (m, v) :: rest => if exclusive seen m o then v else selectChain rest (fun o' => seen o' || m o') o old

/-- **If-conversion is the chain**: with nothing seen before the first
    arm, the selects equal the first matching arm. -/
theorem selectChain_firstArm (arms : List (Accepts × Nat)) (seen : Accepts) (o : Outcome) (old : Nat)
    (h : seen o = false) : selectChain arms seen o old = firstArm arms o old := by
  induction arms generalizing seen with
  | nil => rfl
  | cons a rest ih =>
    obtain ⟨m, v⟩ := a
    simp only [selectChain, firstArm, exclusive, h, Bool.not_false, Bool.and_true]
    by_cases hm : m o = true
    · simp [hm]
    · simp only [Bool.not_eq_true] at hm
      simp only [hm, Bool.false_eq_true, ↓reduceIte]
      exact ih _ (by simp [h, hm])

/-- **A select of bounded values is bounded** (the checker's `csel` rule,
    asm/bounds_arith.go): both sources at most the referent, the result is. -/
theorem select_upper (c : Bool) (a b bound : Nat) (ha : a ≤ bound) (hb : b ≤ bound) :
    (if c then a else b) ≤ bound := by
  cases c <;> simp [ha, hb]

/-- The same for an index fact: both sources below the bound. -/
theorem select_index (c : Bool) (a b bound : Nat) (ha : a < bound) (hb : b < bound) :
    (if c then a else b) < bound := by
  cases c <;> simp [ha, hb]

/-- Every byte of an admitted span access lies inside the span. -/
theorem span_access_bytes (elem minLen len off size b : Nat)
    (hguard : minLen ≤ len) (hacc : SpanAccessOk elem minLen off size)
    (hb : off ≤ b ∧ b < off + size) : b < elem * len := by
  have h := span_access elem minLen len off size hguard hacc
  omega

/-- The transliterated check. -/
def spanAccessCheck (elem minLen off size : Nat) : Bool :=
  decide (off + size ≤ elem * minLen)

theorem spanAccessCheck_sound (elem minLen off size : Nat)
    (h : spanAccessCheck elem minLen off size = true) :
    SpanAccessOk elem minLen off size := by
  unfold spanAccessCheck at h
  unfold SpanAccessOk
  exact of_decide_eq_true h

/-- **Indexed span access**: an element access `[base, wI, uxtw #s]` with
    `1 << s = elem` touches bytes `[i*elem, (i+1)*elem)`; under the index
    guard `i < len` every one of them lies inside the span's `elem * len`
    bytes. The constant-bound form composes this with the length guard:
    `i < K` and `K ≤ len` give `i < len`. -/
theorem index_access (elem len i : Nat) (hguard : i < len) :
    (i + 1) * elem ≤ elem * len := by
  have h : i + 1 ≤ len := hguard
  calc (i + 1) * elem = elem * (i + 1) := Nat.mul_comm _ _
    _ ≤ elem * len := Nat.mul_le_mul_left elem h

theorem index_access_const (elem len i K : Nat) (hidx : i < K) (hlen : K ≤ len) :
    (i + 1) * elem ≤ elem * len :=
  index_access elem len i (Nat.lt_of_lt_of_le hidx hlen)

/-- **Vector access**: a `K`-lane access at element index `i` touches bytes
    `[i*elem, (i+K)*elem)`; under the slack guard `i + K ≤ len` (the
    checker's `sub wT, wL, #K; cmp wI, wT; b.hi trap`, with `len ≥ K` so
    the subtraction did not wrap) every one of them lies inside the span's
    `elem * len` bytes. `K = 1` is `index_access`. -/
theorem index_access_lanes (elem len i K : Nat) (hguard : i + K ≤ len) :
    (i + K) * elem ≤ elem * len := by
  calc (i + K) * elem = elem * (i + K) := Nat.mul_comm _ _
    _ ≤ elem * len := Nat.mul_le_mul_left elem hguard

/-- The slack guard is what the checker reads off the two compares: with
    `len ≥ K`, `wT = len - K` is exact and `i ≤ wT` is `i + K ≤ len`. -/
theorem slack_guard (len i K : Nat) (hmin : K ≤ len) (hle : i ≤ len - K) : i + K ≤ len := by
  omega

/-- The exclusive form of the slack guard, `sub wT, wL, #K; cmp wI, wT; b.hs
    trap`: with `len ≥ K`, `i < len - K` gives `i + K ≤ len` as well — the
    checker records the same slack fact for it, one element weaker than
    the guard, so the reads at `i + k` for `k < K` are admitted. -/
theorem slack_guard_strict (len i K : Nat) (hmin : K ≤ len) (hlt : i < len - K) : i + K ≤ len := by
  omega

/-- A masked index is bounded by its mask: `and wD, wS, #M` leaves `wD ≤ M`,
    so `wD < M + 1` — the constant guard the checker records for it, under
    which a table or frame array of at least `M + 1` elements admits the
    access (`regionAdmits`, `frameArrayAdmits`). -/
theorem masked_index_bound (x M : Nat) : x &&& M < M + 1 :=
  Nat.lt_succ_of_le (Nat.and_le_right)

/-- A byte or halfword loaded or extended into a register is below its
    width's bound: the constant guard `ldrb`, `ldrh`, `uxtb`, `uxth` leave
    on their destination, under which a table of 256 or 65536 entries
    admits the access without a compare. -/
theorem narrow_value_bound (w : Nat) (x : BitVec w) : x.toNat < 2 ^ w := x.isLt

/-- A register holding the constant `k` is an index below `k + 1`: the
    checker's fact for a materialized constant, under which a span with a
    proven minimum of `k + 1` elements admits the constant element read
    without a compare. -/
theorem constant_index_bound (k : Nat) : k < k + 1 := Nat.lt_succ_self k

/-- A value reloaded from a frame slot is the value stored there, so a
    guard on the one bounds the other: the checker carries an index fact
    through a slot the store and the load bracket unchanged (`slotIdx`). -/
theorem guard_through_slot (i j len : Nat) (h : i = j) (g : j < len) : i < len := h ▸ g

/-- A condition materialized and tested: `cset wB, cond` writes 1 when the
    compare's condition held and 0 otherwise, so the fall-through of
    `cbz wB, L` has the condition and that of `cbnz wB, L` its negation —
    the same facts as `b.<not cond>` and `b.cond` on the compare. -/
theorem cset_cbz (c : Prop) [Decidable c] (h : (if c then (1 : Nat) else 0) ≠ 0) : c := by
  by_cases hc : c
  · exact hc
  · simp [hc] at h

theorem cset_cbnz (c : Prop) [Decidable c] (h : (if c then (1 : Nat) else 0) = 0) : ¬ c := by
  by_cases hc : c
  · simp [hc] at h
  · exact hc

/-- **Guard facts across a merge.** A label holds the meet of its
    predecessors' facts: for proven minimum lengths, the smaller of the
    two — which is a valid minimum whichever predecessor control came
    from — and for index bounds, only a fact both sides carry. -/
theorem meet_sound_left (a b len : Nat) (h : a ≤ len) : min a b ≤ len :=
  Nat.le_trans (Nat.min_le_left a b) h

theorem meet_sound_right (a b len : Nat) (h : b ≤ len) : min a b ≤ len :=
  Nat.le_trans (Nat.min_le_right a b) h

/-- The merged minimum is a lower bound on the length however the label was
    reached: from a predecessor proving `a ≤ len` or one proving `b ≤ len`. -/
theorem meet_sound (a b len : Nat) (h : a ≤ len ∨ b ≤ len) : min a b ≤ len := by
  rcases h with h | h
  · exact meet_sound_left a b len h
  · exact meet_sound_right a b len h

/-- Every byte of an admitted indexed access lies inside the span. -/
theorem index_access_bytes (elem len i b : Nat) (hguard : i < len)
    (hb : i * elem ≤ b ∧ b < (i + 1) * elem) : b < elem * len := by
  have h := index_access elem len i hguard
  omega

/-! ## Derived element regions (the seam checker's `elementRegion`,
`frameArrayAccess`, `regionAccess`; refined in `Oak.CheckerRefinement`)

Integers model signed byte addresses and Go's `int64`. An element index
`i` read from a register is non-negative. -/

/-- A frame array's element: with the `K` elements of `size` bytes at
    `addr` inside the frame (`-frame ≤ addr`, `addr + K·size ≤ 0`), the
    element `i < K` lies inside it. -/
theorem frame_element (frame addr size K i : Int)
    (hlo : -frame ≤ addr) (hhi : addr + K * size ≤ 0)
    (hi : 0 ≤ i) (hidx : i < K) (hsize : 0 ≤ size) :
    InFrame frame (addr + i * size) size := by
  have h1 : (i + 1) * size ≤ K * size := Int.mul_le_mul_of_nonneg_right (by omega) hsize
  rw [Int.add_mul, Int.one_mul] at h1
  have h2 : 0 ≤ i * size := Int.mul_nonneg hi hsize
  unfold InFrame
  constructor <;> omega

/-- A span element under `i < len`: its `size` bytes at `i·size` lie inside
    the span's `size·len` (the `Int` twin of `index_access`). -/
theorem span_element (size len i : Int) (hi : 0 ≤ i) (hsize : 0 ≤ size) (hlt : i < len) :
    i * size + size ≤ size * len := by
  have h1 : (i + 1) * size ≤ len * size := Int.mul_le_mul_of_nonneg_right (by omega) hsize
  rw [Int.add_mul, Int.one_mul, Int.mul_comm len size] at h1
  exact h1

/-- `K` elements from `i` under the slack guard `i + K ≤ len`: their
    `K·size` bytes lie inside the span (the `Int` twin of
    `index_access_lanes`). -/
theorem span_element_lanes (size len i K : Int) (hsize : 0 ≤ size) (hsum : i + K ≤ len) :
    i * size + size * K ≤ size * len := by
  have h1 : (i + K) * size ≤ len * size := Int.mul_le_mul_of_nonneg_right hsum hsize
  rw [Int.add_mul, Int.mul_comm K size, Int.mul_comm len size] at h1
  exact h1

/-- An element of a bounded region: with `K` elements of `size` bytes
    inside `extent` bytes, the element `i < K` lies inside it. -/
theorem region_element (extent size K i : Int) (hfit : K * size ≤ extent)
    (hi : 0 ≤ i) (hidx : i < K) (hsize : 0 ≤ size) :
    i * size + size ≤ extent := by
  have h1 : (i + 1) * size ≤ K * size := Int.mul_le_mul_of_nonneg_right (by omega) hsize
  rw [Int.add_mul, Int.one_mul] at h1
  omega

/-- Every byte of an access `[off, off+size)` admitted inside `extent`
    bytes lies inside them. -/
theorem region_offset_bytes (extent off size b : Int) (hlo : 0 ≤ off) (hhi : off + size ≤ extent)
    (hb : off ≤ b ∧ b < off + size) : 0 ≤ b ∧ b < extent := by
  obtain ⟨hb1, hb2⟩ := hb
  constructor <;> omega

/-! ## Entry padding

`asm/object.go` (`textLayout.pad`) fills the gap before an entry with the
lane's no-ops. AArch64 gaps are whole words. An RV64 function under RVC
(docs/spec/94-assembler.md, "Compressed encodings") ends on a half word
when it holds an odd number of two-byte instructions, so its gap is
filled in words and closed by one two-byte `c.nop`. -/

/-- The bytes needed to reach the next multiple of `align` from `len`. -/
def gap (len align : Nat) : Nat := (align - len % align) % align

/-- Reaching the boundary: `len + gap` is a multiple of the alignment. -/
theorem gap_reaches (len align : Nat) (h : 0 < align) :
    (len + gap len align) % align = 0 := by
  unfold gap
  rcases Nat.eq_zero_or_pos (len % align) with hz | hp
  · rw [hz, Nat.sub_zero, Nat.mod_self, Nat.add_zero]
    exact hz
  · have hlt := Nat.mod_lt len h
    rw [Nat.mod_eq_of_lt (Nat.sub_lt h hp)]
    have hdiv := Nat.div_add_mod len align
    have hsum : len + (align - len % align) = align * (len / align + 1) := by
      rw [Nat.mul_succ]
      omega
    rw [hsum, Nat.mul_mod_right]

/-- Filling in halfwords: an even gap is `w` words and at most one
    halfword, so the RV64 fill (words, then a `c.nop` when two bytes remain)
    produces exactly the gap. -/
theorem pad_halfwords_reaches (g : Nat) (h : g % 2 = 0) :
    4 * (g / 4) + (if g % 4 = 2 then 2 else 0) = g := by
  split <;> omega

/-- Filling in words alone misses: when the gap is not a multiple of four,
    no number of four-byte no-ops equals it — the fixed word pad of the
    earlier layout would never reach the boundary. -/
theorem pad_words_misses (g : Nat) (h : g % 4 ≠ 0) : ∀ w : Nat, 4 * w ≠ g := by
  intro w hw
  apply h
  omega

/-- A compressed RV64 entry ends on a half word exactly when it holds an
    odd number of two-byte instructions among its words. -/
theorem rvc_entry_half_word (words halves : Nat) :
    (4 * words + 2 * halves) % 4 = 2 ↔ halves % 2 = 1 := by
  constructor <;> intro h <;> omega

end Oak.Assembler
