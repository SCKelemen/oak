import Std.Tactic.BVDecide

/-!
# Assembler semantics: registers, width views, data processing

`docs/spec/94-assembler.md` §8. The symbolic executor of `asm/verify.go`
transliterates this model: the general register file as 32 values of
64 bits (register 31 reads zero), the `wN`/`xN` width views — a 32-bit
write zero-extends into the 64-bit register, a 32-bit read truncates —
and the data-processing instructions as total bitvector operations that
wrap to their width, exactly Oak's fixed-width arithmetic (`20-types.md`
§11.1), which is what makes the Oak fallback body a usable specification.
-/

namespace Oak.AssemblerSemantics

/-- The general register file. -/
def Regs := Fin 32 → BitVec 64

/-- Register 31 is the zero register on read. -/
def readX (r : Regs) (n : Fin 32) : BitVec 64 :=
  if n = 31 then 0 else r n

def readW (r : Regs) (n : Fin 32) : BitVec 32 :=
  (readX r n).truncate 32

def writeX (r : Regs) (n : Fin 32) (v : BitVec 64) : Regs :=
  fun m => if m = n then v else r m

/-- A 32-bit write zero-extends: the upper half is cleared. -/
def writeW (r : Regs) (n : Fin 32) (v : BitVec 32) : Regs :=
  writeX r n (v.zeroExtend 64)

/-- Reading back a 32-bit write at 32 bits returns the value. -/
theorem readW_writeW (r : Regs) (n : Fin 32) (v : BitVec 32) (h : n ≠ 31) :
    readW (writeW r n v) n = v := by
  simp [readW, writeW, writeX, readX, h]

/-- Reading a 32-bit write at 64 bits is the zero-extension: the aliasing
    law of `Oak.Assembler.alias_same_physical` made concrete. -/
theorem readX_writeW (r : Regs) (n : Fin 32) (v : BitVec 32) (h : n ≠ 31) :
    readX (writeW r n v) n = v.zeroExtend 64 := by
  simp [writeW, writeX, readX, h]

/-- Writes to one register leave every other register unchanged. -/
theorem readX_writeX_other (r : Regs) (n m : Fin 32) (v : BitVec 64)
    (hne : m ≠ n) (hz : m ≠ 31) : readX (writeX r n v) m = readX r m := by
  simp [writeX, readX, hne, hz]

/-- Data-processing operations, total and wrapping at the width. -/
inductive Op where
  | add | sub | and | orr | eor | lsl | lsr | asr | mul
  deriving DecidableEq, Repr

def apply {w : Nat} (op : Op) (a b : BitVec w) : BitVec w :=
  match op with
  | .add => a + b
  | .sub => a - b
  | .and => a &&& b
  | .orr => a ||| b
  | .eor => a ^^^ b
  | .lsl => a <<< (b.toNat % w)
  | .lsr => a >>> (b.toNat % w)
  | .asr => a.sshiftRight (b.toNat % w)
  | .mul => a * b

/-- `neg` and `mvn` are `sub` from zero and `eor` with all ones. -/
theorem neg_as_sub {w : Nat} (a : BitVec w) : -a = apply .sub 0 a := by
  simp [apply, BitVec.zero_sub]

theorem mvn_as_eor {w : Nat} (a : BitVec w) : ~~~a = apply .eor a (BitVec.allOnes w) := by
  simp [apply, BitVec.xor_allOnes]

/-- A 64-bit data-processing instruction on registers. -/
def execX (op : Op) (r : Regs) (d n m : Fin 32) : Regs :=
  writeX r d (apply op (readX r n) (readX r m))

/-- A 32-bit data-processing instruction: operands read at 32 bits, the
    result written with zero-extension. -/
def execW (op : Op) (r : Regs) (d n m : Fin 32) : Regs :=
  writeW r d (apply op (readW r n) (readW r m))

/-- The 32-bit result of a 32-bit instruction is the 32-bit operation on
    the 32-bit views — the executor's `truncate`/`zeroExtend` discipline. -/
theorem readW_execW (op : Op) (r : Regs) (d n m : Fin 32) (h : d ≠ 31) :
    readW (execW op r d n m) d = apply op (readW r n) (readW r m) := by
  unfold execW
  exact readW_writeW _ _ _ h

/-- Addition commutes: `add w0, w0, w1` and `add w0, w1, w0` are one
    program — the simplest fact the linear normal form relies on. -/
theorem add_comm' {w : Nat} (a b : BitVec w) : apply .add a b = apply .add b a := by
  simp [apply, BitVec.add_comm]

/-- Subtraction is addition of the negation: `sub` normalizes into the
    same linear form as `add` with a negated coefficient. -/
theorem sub_as_add {w : Nat} (a b : BitVec w) : apply .sub a b = apply .add a (-b) := by
  simp [apply, BitVec.sub_eq_add_neg]

/-- The bit-blaster's justification: two bitvectors are equal exactly when
    every bit agrees, so equality of every bit's canonical decision diagram
    is equality of the values (`asm/blast.go`). -/
theorem eq_of_bits {w : Nat} (a b : BitVec w) (h : ∀ i : Nat, a.getLsbD i = b.getLsbD i) : a = b := by
  apply BitVec.eq_of_getLsbD_eq
  intros
  exact h _

/-- The pointwise laws the blaster applies for `and`, `orr`, `eor`. -/
theorem and_bit {w : Nat} (a b : BitVec w) (i : Nat) :
    (a &&& b).getLsbD i = (a.getLsbD i && b.getLsbD i) := BitVec.getLsbD_and

theorem or_bit {w : Nat} (a b : BitVec w) (i : Nat) :
    (a ||| b).getLsbD i = (a.getLsbD i || b.getLsbD i) := BitVec.getLsbD_or

theorem xor_bit {w : Nat} (a b : BitVec w) (i : Nat) :
    (a ^^^ b).getLsbD i = (a.getLsbD i ^^ b.getLsbD i) := BitVec.getLsbD_xor

/-! ## The ripple-carry chain is `BitVec` addition

`asm/blast.go` blasts `add` as sum_i = a_i ⊕ b_i ⊕ c_i with
c_{i+1} = (a_i ∧ b_i) ∨ (c_i ∧ (a_i ⊕ b_i)), and `sub` as the same chain over
the complement with carry-in 1. These are the definitions below; the
theorems refine them to `BitVec.add`/`BitVec.sub` bit by bit, so equality
of the blasted bits is equality of the machine's results. -/

/-- The blaster's carry recurrence, verbatim. -/
def rippleCarry {w : Nat} (a b : BitVec w) (c₀ : Bool) : Nat → Bool
  | 0 => c₀
  | i + 1 => (a.getLsbD i && b.getLsbD i) || (rippleCarry a b c₀ i && (a.getLsbD i ^^ b.getLsbD i))

/-- The blaster's sum bit, verbatim. -/
def rippleSum {w : Nat} (a b : BitVec w) (c₀ : Bool) (i : Nat) : Bool :=
  (a.getLsbD i ^^ b.getLsbD i) ^^ rippleCarry a b c₀ i

/-- The chain's carry is the arithmetic carry of the standard library's
    bit-blasting theory. -/
theorem rippleCarry_eq_carry {w : Nat} (a b : BitVec w) (c₀ : Bool) (i : Nat) :
    rippleCarry a b c₀ i = BitVec.carry i a b c₀ := by
  induction i with
  | zero => simp [rippleCarry]
  | succ i ih =>
    rw [BitVec.carry_succ, rippleCarry, ih]
    cases a.getLsbD i <;> cases b.getLsbD i <;> cases BitVec.carry i a b c₀ <;>
      simp [Bool.atLeastTwo]

/-- Bit i of the chain with carry-in 0 is bit i of `a + b`. -/
theorem rippleSum_eq_add {w : Nat} (a b : BitVec w) (i : Nat) (h : i < w) :
    rippleSum a b false i = (a + b).getLsbD i := by
  rw [BitVec.getLsbD_add h, rippleSum, rippleCarry_eq_carry]
  cases a.getLsbD i <;> cases b.getLsbD i <;> cases BitVec.carry i a b false <;> rfl

/-- `a - b` is `a + ~~~b + 1`: the subtraction chain's justification. -/
theorem sub_eq_add_not_add_one {w : Nat} (a b : BitVec w) :
    a - b = a + ~~~b + BitVec.setWidth w (BitVec.ofBool true) := by
  rw [BitVec.sub_eq_add_neg, BitVec.neg_eq_not_add, BitVec.add_assoc]
  congr 2
  apply BitVec.eq_of_toNat_eq
  simp

/-- Bit i of the complement chain with carry-in 1 is bit i of `a - b`. -/
theorem rippleSum_eq_sub {w : Nat} (a b : BitVec w) (i : Nat) (h : i < w) :
    rippleSum a (~~~b) true i = (a - b).getLsbD i := by
  rw [sub_eq_add_not_add_one, BitVec.getLsbD_add_add_bool h, rippleSum, rippleCarry_eq_carry]
  cases a.getLsbD i <;> cases (~~~b).getLsbD i <;> cases BitVec.carry i a (~~~b) true <;> rfl

/-! ## Flags and conditional selects

`cmp l, r` sets NZCV as the flags of `l - r`; `csel`/`cset` read a condition
code as a comparison of the two operands. The verifier's `condition`
(`asm/blast.go`) computes the flags from the subtraction chain — N the
result's sign, Z its zero test, C the chain's carry-out, V the signed
overflow — and applies the ARM condition table; `conditionHolds`
(`asm/verify.go`) evaluates the comparison directly. The theorems below tie
the two readings together. -/

structure Flags where
  n : Bool
  z : Bool
  c : Bool
  v : Bool
  deriving DecidableEq, Repr

/-- The flags of `l - r`. C is "no borrow": `r ≤ l` unsigned. V is a signed
    overflow of the subtraction: operand signs differ and the result's sign
    differs from the left operand's. -/
def flagsOf {w : Nat} (l r : BitVec w) : Flags :=
  { n := (l - r).msb
    z := decide (l - r = 0)
    c := decide (r.toNat ≤ l.toNat)
    v := (l.msb != r.msb) && ((l - r).msb != l.msb) }

/-- The condition codes: the comparisons, and the single-flag reads. -/
inductive Cond where
  | eq | ne | hs | lo | hi | ls | ge | lt | gt | le | mi | pl | vs | vc
  deriving DecidableEq, Repr

/-- The ARM condition table. -/
def Cond.holds (f : Flags) : Cond → Bool
  | .eq => f.z
  | .ne => !f.z
  | .hs => f.c
  | .lo => !f.c
  | .hi => f.c && !f.z
  | .ls => !f.c || f.z
  | .ge => f.n == f.v
  | .lt => f.n != f.v
  | .gt => !f.z && (f.n == f.v)
  | .le => f.z || (f.n != f.v)
  | .mi => f.n
  | .pl => !f.n
  | .vs => f.v
  | .vc => !f.v

/-- The flags of `adds l, r`: those of `l + r` — C the carry out of the
    addition, V a signed overflow (equal operand signs, a differing result
    sign). -/
def addFlagsOf {w : Nat} (l r : BitVec w) : Flags :=
  { n := (l + r).msb
    z := decide (l + r = 0)
    c := decide (2 ^ w ≤ l.toNat + r.toNat)
    v := (l.msb == r.msb) && ((l + r).msb != l.msb) }

/-- The carry of an addition is its unsigned overflow: `cs` after `adds`
    holds exactly when the wrapped sum is below the left operand — which is
    how Oak spells a saturating add (`a + b < a ? max | a + b`). -/
theorem add_carry_iff {w : Nat} (l r : BitVec w) :
    (addFlagsOf l r).c = true ↔ (l + r).toNat < l.toNat := by
  have hl := l.isLt
  have hr := r.isLt
  simp only [addFlagsOf, decide_eq_true_eq, BitVec.toNat_add]
  rcases Nat.lt_or_ge (l.toNat + r.toNat) (2 ^ w) with hlt | hge
  · rw [Nat.mod_eq_of_lt hlt]
    omega
  · have hsub : (l.toNat + r.toNat) % 2 ^ w = l.toNat + r.toNat - 2 ^ w := by
      rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt (by omega)]
    rw [hsub]
    omega

/-- The flags of `tst l, r`: those of `l &&& r`, with C and V cleared. -/
def andFlagsOf {w : Nat} (l r : BitVec w) : Flags :=
  { n := (l &&& r).msb, z := decide (l &&& r = 0), c := false, v := false }

/-- `ne` after `tst` is the bit test: some tested bit is set. -/
theorem tst_ne_iff {w : Nat} (l r : BitVec w) : Cond.holds (andFlagsOf l r) .ne = true ↔ l &&& r ≠ 0 := by
  simp [Cond.holds, andFlagsOf]

/-- `mi` after `cmp l, r` is the sign bit of the difference. -/
theorem mi_iff_msb {w : Nat} (l r : BitVec w) : Cond.holds (flagsOf l r) .mi = (l - r).msb := rfl

/-- Compare-and-branch: `cbz x` takes the branch exactly when `x = 0`,
    `tbz x, #i` exactly when bit i is clear — conditions without flags. -/
def cbz {w : Nat} (x : BitVec w) : Bool := decide (x = 0)
def tbz {w : Nat} (x : BitVec w) (i : Nat) : Bool := !(x.getLsbD i)

theorem cbz_iff {w : Nat} (x : BitVec w) : cbz x = true ↔ x = 0 := by simp [cbz]
theorem tbz_iff {w : Nat} (x : BitVec w) (i : Nat) : tbz x i = true ↔ x.getLsbD i = false := by
  simp [tbz]

def condHolds {w : Nat} (c : Cond) (l r : BitVec w) : Bool := c.holds (flagsOf l r)

/-- The C flag is the carry-out of the complement chain — what
    `asm/blast.go` computes. -/
theorem c_eq_carry {w : Nat} (l r : BitVec w) :
    (flagsOf l r).c = BitVec.carry w l (~~~r) true := by
  have hl := l.isLt
  have hr := r.isLt
  simp only [flagsOf, BitVec.carry, BitVec.toNat_not, Bool.toNat_true]
  rw [Nat.mod_eq_of_lt hl, Nat.mod_eq_of_lt (by omega)]
  by_cases h : r.toNat ≤ l.toNat
  · simp [h]; omega
  · simp [h]; omega

/-- `eq` is equality. -/
theorem eq_holds_iff {w : Nat} (l r : BitVec w) : condHolds .eq l r = true ↔ l = r := by
  simp only [condHolds, Cond.holds, flagsOf, decide_eq_true_eq]
  constructor
  · intro h
    have hc := BitVec.sub_add_cancel l r
    rw [h] at hc
    simpa using hc.symm
  · intro h
    subst h
    exact BitVec.sub_self l

/-- `hs` (`cs`) is unsigned ≥ — the Oak `>=` on unsigned operands. -/
theorem hs_holds_iff {w : Nat} (l r : BitVec w) : condHolds .hs l r = true ↔ r.toNat ≤ l.toNat := by
  simp [condHolds, Cond.holds, flagsOf]

/-- `lo` (`cc`) is unsigned < — the Oak `<` on unsigned operands. -/
theorem lo_holds_iff {w : Nat} (l r : BitVec w) : condHolds .lo l r = true ↔ l.ult r := by
  simp [condHolds, Cond.holds, flagsOf, BitVec.ult_iff_toNat_lt]

/-- `hi` is unsigned >: C set and Z clear. -/
theorem hi_holds_iff {w : Nat} (l r : BitVec w) : condHolds .hi l r = true ↔ r.ult l := by
  simp only [condHolds, Cond.holds, flagsOf, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq,
    decide_eq_false_iff_not, BitVec.ult_iff_toNat_lt]
  constructor
  · rintro ⟨hle, hne⟩
    rcases Nat.lt_or_eq_of_le hle with hlt | heq
    · exact hlt
    · exact absurd (BitVec.eq_of_toNat_eq heq.symm ▸ BitVec.sub_self l) hne
  · intro hlt
    refine ⟨Nat.le_of_lt hlt, fun hz => ?_⟩
    have := (eq_holds_iff l r).mp (by simp [condHolds, Cond.holds, flagsOf, hz])
    subst this
    exact Nat.lt_irrefl _ hlt

/-- The signed codes agree with `BitVec.slt`, checked exhaustively at width
    4 (the kernel evaluates every case) — the executable cross-check the
    spec asks of the normalizer. -/
theorem lt_holds_eq_slt_w4 : ∀ l r : BitVec 4, condHolds .lt l r = l.slt r := by decide
theorem ge_holds_eq_not_slt_w4 : ∀ l r : BitVec 4, condHolds .ge l r = !(l.slt r) := by decide
theorem gt_holds_eq_slt_w4 : ∀ l r : BitVec 4, condHolds .gt l r = r.slt l := by decide
theorem le_holds_eq_not_slt_w4 : ∀ l r : BitVec 4, condHolds .le l r = !(r.slt l) := by decide

/-- At the contract widths the signed codes are proved by bit-blasting
    (`bv_decide`: a SAT certificate checked by the kernel) — the same
    decision the Go verifier makes, now as a theorem about the flag
    definitions for every 32- and 64-bit operand pair. -/
theorem lt_holds_eq_slt_w32 (l r : BitVec 32) : condHolds .lt l r = l.slt r := by
  simp only [condHolds, Cond.holds, flagsOf]; bv_decide
theorem ge_holds_eq_not_slt_w32 (l r : BitVec 32) : condHolds .ge l r = !(l.slt r) := by
  simp only [condHolds, Cond.holds, flagsOf]; bv_decide
theorem gt_holds_eq_slt_w32 (l r : BitVec 32) : condHolds .gt l r = r.slt l := by
  simp only [condHolds, Cond.holds, flagsOf]; bv_decide
theorem le_holds_eq_not_slt_w32 (l r : BitVec 32) : condHolds .le l r = !(r.slt l) := by
  simp only [condHolds, Cond.holds, flagsOf]; bv_decide
theorem lt_holds_eq_slt_w64 (l r : BitVec 64) : condHolds .lt l r = l.slt r := by
  simp only [condHolds, Cond.holds, flagsOf]; bv_decide
theorem ge_holds_eq_not_slt_w64 (l r : BitVec 64) : condHolds .ge l r = !(l.slt r) := by
  simp only [condHolds, Cond.holds, flagsOf]; bv_decide
theorem gt_holds_eq_slt_w64 (l r : BitVec 64) : condHolds .gt l r = r.slt l := by
  simp only [condHolds, Cond.holds, flagsOf]; bv_decide
theorem le_holds_eq_not_slt_w64 (l r : BitVec 64) : condHolds .le l r = !(r.slt l) := by
  simp only [condHolds, Cond.holds, flagsOf]; bv_decide

/-- `csel d, n, m, cond`: the first operand when the condition holds. -/
def csel {w : Nat} (c : Cond) (f : Flags) (a b : BitVec w) : BitVec w :=
  if c.holds f then a else b

/-- `cset d, cond`: 1 when the condition holds, else 0. -/
def cset (_w : Nat) (c : Cond) (f : Flags) : BitVec _w :=
  if c.holds f then 1 else 0

theorem csel_of_holds {w : Nat} (c : Cond) (f : Flags) (a b : BitVec w) (h : c.holds f = true) :
    csel c f a b = a := by simp [csel, h]

theorem csel_of_not_holds {w : Nat} (c : Cond) (f : Flags) (a b : BitVec w) (h : c.holds f = false) :
    csel c f a b = b := by simp [csel, h]

/-- `cset` is `csel` between the constants 1 and 0 — the executor lowers it
    so. -/
theorem cset_eq_csel {w : Nat} (c : Cond) (f : Flags) : cset w c f = csel c f 1 0 := rfl

/-- A cmp/csel pair on registers: `cmp n, m; csel d, a, b, cond`. -/
def execCsel (c : Cond) (r : Regs) (d n m a b : Fin 32) : Regs :=
  writeX r d (csel c (flagsOf (readX r n) (readX r m)) (readX r a) (readX r b))

/-- Unsigned maximum: `cmp a, b; csel a, b, a, lo` yields `b` exactly when
    `a < b` — the verifier's first conditional theorem, on the semantics. -/
theorem csel_lo_max {w : Nat} (a b : BitVec w) :
    csel .lo (flagsOf a b) b a = if a.ult b then b else a := by
  simp [csel, Cond.holds, flagsOf, BitVec.ult_iff_toNat_lt]

/-! ## Acyclic branches

A conditional branch splits the machine's future: the path executor of
`asm/verify.go` continues at the label under the branch condition and at
the next instruction under its negation, and the two results meet as a
select. `branch_as_select` is the law that makes the unfolding sound: the
value a body computes is the select, on the branch condition, of the values
its two continuations compute. -/

/-- The result of `b.cond L` followed by continuations `taken` (at L) and
    `fall` (next instruction), each already a function of the state. -/
def branch {α : Type} (c : Cond) (f : Flags) (taken fall : α) : α :=
  if c.holds f then taken else fall

theorem branch_as_select {w : Nat} (c : Cond) (f : Flags) (taken fall : BitVec w) :
    branch c f taken fall = csel c f taken fall := rfl

/-- The branch is transparent to any later computation: continuing the
    paths and selecting is selecting and continuing (the executor may fork
    early and rejoin at a shared tail). -/
theorem branch_map {α β : Type} (c : Cond) (f : Flags) (taken fall : α) (k : α → β) :
    k (branch c f taken fall) = branch c f (k taken) (k fall) := by
  unfold branch
  split <;> rfl

/-! ## Span memory

A span or view parameter arrives as its `{base, len}` pair (`Oak.Assembler`
§7). The verifier models it as the executor does: an opaque base, a 32-bit
length, and one element value per index — unconstrained, since the seam
checker has already placed every load under a dominating guard proving the
index inside the length (`Oak.Assembler.span_access`). A load at byte offset
`off` over `elem`-byte elements reads element `off / elem` when `off` is a
whole number of elements; the Oak body's `v[k]` is the same element. -/

structure Span (w : Nat) where
  len : BitVec 32
  elems : Nat → BitVec w

/-- `ldr rD, [base, #off]` through a span base, when the offset is a whole
    element. -/
def loadElem {w : Nat} (s : Span w) (elem off : Nat) : BitVec w :=
  s.elems (off / elem)

/-- A load at offset `k * elem` is element `k` — the executor's element
    naming `v[k]`. -/
theorem loadElem_at {w : Nat} (s : Span w) (elem k : Nat) (h : 0 < elem) :
    loadElem s elem (k * elem) = s.elems k := by
  simp [loadElem, Nat.mul_div_cancel _ h]

/-- Under the guard `¬ (len < N)` every element index below `N` is inside
    the span: the Oak side's `len(v) < N ? default | ...v[k]...` and the
    asm's `cmp wL, #N; b.lo` read the same elements on the same inputs. -/
theorem guarded_index_in_bounds (len N k : Nat) (hguard : ¬ len < N) (hk : k < N) : k < len := by
  omega

/-! ## Counted loops unroll

Both executors run a `while` under fuel (the unrolling budget): the body is
applied while the condition holds, and the loop is outside the subset when
the fuel runs out or the condition is not a constant. A counted loop —
a counter from 0 to N incremented once per iteration — makes exactly N
iterations under fuel N + 1, so its unfolding is the N-fold iterate of the
body: the term both sides compute. -/

/-- `while cond { body }` under fuel; `none` when the fuel is exhausted. -/
def whileFuel {σ : Type} (cond : σ → Bool) (body : σ → σ) : Nat → σ → Option σ
  | 0, _ => none
  | fuel + 1, s => if cond s then whileFuel cond body fuel (body s) else some s

/-- The n-fold iterate, in the tail form the unrolling produces. -/
def iter {α : Type} (f : α → α) : Nat → α → α
  | 0, a => a
  | n + 1, a => iter f n (f a)

/-- The invariant of the counted loop: from counter `N - m` with fuel
    `m + 1`, the loop ends at counter `N` having applied the body `m`
    times. -/
theorem whileFuel_counted {α : Type} (N : Nat) (f : α → α) :
    ∀ (m : Nat) (a : α), m ≤ N →
      whileFuel (fun s : Nat × α => decide (s.1 < N)) (fun s => (s.1 + 1, f s.2)) (m + 1) (N - m, a)
        = some (N, iter f m a) := by
  intro m
  induction m with
  | zero =>
    intro a _
    simp [whileFuel, iter]
  | succ m ih =>
    intro a hm
    have hlt : decide (N - (m + 1) < N) = true := by
      rw [decide_eq_true_eq]
      omega
    have hstep : N - (m + 1) + 1 = N - m := by omega
    rw [whileFuel]
    simp only [hlt, ↓reduceIte, iter]
    rw [hstep]
    exact ih (f a) (by omega)

/-! ## Coupled loops

A loop whose trip count depends on the inputs is verified by coupling
(`asm/loops.go`): a relation R between the Oak locals and the asm
registers that holds at the header, under which the two continue
conditions agree and one iteration of each body preserves R. Then the two
loops, run under the same fuel, produce related results — both exhaust the
fuel together or both stop together, at related states. R is arbitrary
here; the verifier instantiates it as a conjunction of affine relations
between paired variables (`r = x + b`, `r = b - x`) and an invariant read
off the Oak guard (`i ≤ n` from `i < n`), which is why the hypotheses
below only ask for agreement and preservation on R-related states. -/

/-- Related optional results: both absent, or both present and related. -/
def optionRel {σ τ : Type} (R : σ → τ → Prop) : Option σ → Option τ → Prop
  | none, none => True
  | some s, some t => R s t
  | _, _ => False

theorem whileFuel_coupled {σ τ : Type} (R : σ → τ → Prop)
    (c₁ : σ → Bool) (c₂ : τ → Bool) (b₁ : σ → σ) (b₂ : τ → τ)
    (hcond : ∀ s t, R s t → c₁ s = c₂ t)
    (hbody : ∀ s t, R s t → c₁ s = true → R (b₁ s) (b₂ t)) :
    ∀ (fuel : Nat) (s : σ) (t : τ), R s t →
      optionRel R (whileFuel c₁ b₁ fuel s) (whileFuel c₂ b₂ fuel t) := by
  intro fuel
  induction fuel with
  | zero =>
    intro s t _
    simp [whileFuel, optionRel]
  | succ fuel ih =>
    intro s t hR
    have hc := hcond s t hR
    simp only [whileFuel]
    rw [← hc]
    cases h : c₁ s with
    | true =>
      simp only [if_true]
      exact ih (b₁ s) (b₂ t) (hbody s t hR h)
    | false =>
      simp only [optionRel]
      exact hR

/-- The verifier's use: when R also fixes the results (`f s = g t`), the
    two loops compute the same value whenever both finish. -/
theorem whileFuel_coupled_result {σ τ α : Type} (R : σ → τ → Prop) (f : σ → α) (g : τ → α)
    (c₁ : σ → Bool) (c₂ : τ → Bool) (b₁ : σ → σ) (b₂ : τ → τ)
    (hcond : ∀ s t, R s t → c₁ s = c₂ t)
    (hbody : ∀ s t, R s t → c₁ s = true → R (b₁ s) (b₂ t))
    (hres : ∀ s t, R s t → f s = g t)
    (fuel : Nat) (s : σ) (t : τ) (hR : R s t) (s' : σ) (t' : τ)
    (hs : whileFuel c₁ b₁ fuel s = some s') (ht : whileFuel c₂ b₂ fuel t = some t') :
    f s' = g t' := by
  have h := whileFuel_coupled R c₁ c₂ b₁ b₂ hcond hbody fuel s t hR
  rw [hs, ht] at h
  exact hres s' t' h

/-- A counted loop from 0 runs exactly N times: its result is `iter f N`. -/
theorem counted_loop_unrolls {α : Type} (N : Nat) (f : α → α) (a : α) :
    whileFuel (fun s : Nat × α => decide (s.1 < N)) (fun s => (s.1 + 1, f s.2)) (N + 1) (0, a)
      = some (N, iter f N a) := by
  have h := whileFuel_counted N f N a (Nat.le_refl N)
  simpa using h

end Oak.AssemblerSemantics
