import Oak.AssemblerSemantics

/-!
# The RV64 lane (docs/spec/94-assembler.md §9)

The instruction semantics the Go verifier's RV64 lane transliterates
(`asm/rv64_verify.go`), over 64-bit registers:

* the W-forms compute at 32 bits and sign-extend (`addw`, `subw`, `sllw`,
  `srlw`, `sraw`, `mulw`, and `sext.w`);
* `slt`/`sltu` are the signed and unsigned comparisons as 0/1 values;
* the divisions are total: a zero divisor yields all ones for the quotient
  and the dividend for the remainder; the signed overflow yields the
  dividend and remainder 0 (`rv64Divide` in `asm/isa_semantics.go`);
* a conditional branch compares two registers — there are no flags. The
  bridge to the AArch64 lane is `Br.holds_eq_condHolds`: each branch holds
  exactly when the AArch64 condition code the verifier assigns to it
  (`rv64BranchCodes`) holds on the flags of the same subtraction. So the
  comparison term the two lanes share (`cmpTerm`) has one meaning.

The LP64 psABI's widening of narrow integer parameters is `widen`: a value
narrower than 64 bits is extended by its own sign to 32 bits, then
sign-extended to 64 (so a `u32` arrives sign-extended, its upper half
determined, unlike AAPCS64's unspecified bits).
-/

namespace Oak.RiscV

open Oak.AssemblerSemantics

abbrev X := BitVec 64

/-- Sign-extend a 32-bit result to the register. -/
def sextW (v : BitVec 32) : X := v.signExtend 64

def addw (a b : X) : X := sextW (a.truncate 32 + b.truncate 32)
def subw (a b : X) : X := sextW (a.truncate 32 - b.truncate 32)
def mulw (a b : X) : X := sextW (a.truncate 32 * b.truncate 32)
def sllw (a b : X) : X := sextW (a.truncate 32 <<< (b.truncate 5).toNat)
def srlw (a b : X) : X := sextW (a.truncate 32 >>> (b.truncate 5).toNat)
def sraw (a b : X) : X := sextW ((a.truncate 32).sshiftRight (b.truncate 5).toNat)
/-- `sext.w rd, rs` is `addiw rd, rs, 0`. -/
def sextw (a : X) : X := addw a 0

def sll (a b : X) : X := a <<< (b.truncate 6).toNat
def srl (a b : X) : X := a >>> (b.truncate 6).toNat
def sra (a b : X) : X := a.sshiftRight (b.truncate 6).toNat

def slt (a b : X) : X := if a.slt b then 1 else 0
def sltu (a b : X) : X := if a.ult b then 1 else 0

def divu (a b : X) : X := if b = 0 then BitVec.allOnes 64 else a / b
def remu (a b : X) : X := if b = 0 then a else a % b
def div (a b : X) : X :=
  if b = 0 then BitVec.allOnes 64
  else if a = BitVec.intMin 64 ∧ b = BitVec.allOnes 64 then a
  else a.sdiv b
def rem (a b : X) : X :=
  if b = 0 then a
  else if a = BitVec.intMin 64 ∧ b = BitVec.allOnes 64 then 0
  else a.srem b

/-- The W-forms are the 64-bit operation truncated and sign-extended: the
    verifier may compute either way. -/
theorem addw_eq (a b : X) : addw a b = sextW ((a + b).truncate 32) := by
  simp only [addw, sextW]; bv_decide
theorem subw_eq (a b : BitVec 64) : subw a b = sextW ((a - b).truncate 32) := by
  simp only [subw, sextW]; bv_decide
theorem mulw_eq (a b : X) : mulw a b = sextW ((a * b).truncate 32) := by
  simp only [mulw, sextW]; bv_decide

/-- A W-form result is a fixed point of `sext.w`. -/
theorem sextw_addw (a b : X) : sextw (addw a b) = addw a b := by
  simp only [sextw, addw, sextW]; bv_decide

/-- The low 32 bits of a W-form result are the 32-bit operation. -/
theorem addw_truncate (a b : X) : (addw a b).truncate 32 = a.truncate 32 + b.truncate 32 := by
  simp only [addw, sextW]; bv_decide

/-- The total divisions at the edges. -/
theorem divu_zero (a : X) : divu a 0 = BitVec.allOnes 64 := by simp [divu]
theorem remu_zero (a : X) : remu a 0 = a := by simp [remu]
theorem div_zero (a : X) : div a 0 = BitVec.allOnes 64 := by simp [div]
theorem rem_zero (a : X) : rem a 0 = a := by simp [rem]
theorem div_overflow : div (BitVec.intMin 64) (BitVec.allOnes 64) = BitVec.intMin 64 := by
  simp [div]
theorem rem_overflow : rem (BitVec.intMin 64) (BitVec.allOnes 64) = 0 := by
  simp [rem]

/-- The conditional branches: two registers compared, no flags. -/
inductive Br where
  | beq | bne | blt | bge | bltu | bgeu
  deriving DecidableEq, Repr

def Br.holds : Br → X → X → Bool
  | .beq, a, b => decide (a = b)
  | .bne, a, b => !decide (a = b)
  | .blt, a, b => a.slt b
  | .bge, a, b => !(a.slt b)
  | .bltu, a, b => a.ult b
  | .bgeu, a, b => !(a.ult b)

/-- The AArch64 condition code the verifier assigns to each branch
    (`rv64BranchCodes` in `asm/rv64_verify.go`). -/
def Br.cond : Br → Cond
  | .beq => .eq
  | .bne => .ne
  | .blt => .lt
  | .bge => .ge
  | .bltu => .lo
  | .bgeu => .hs

/-- `bltu` is the `lo` code on the flags of `a - b`. -/
theorem bltu_holds (a b : X) : a.ult b = condHolds .lo a b := by
  cases hc : condHolds .lo a b
  · apply Bool.eq_false_iff.mpr
    intro h
    have := (lo_holds_iff a b).mpr h
    rw [hc] at this
    exact Bool.false_ne_true this
  · exact (lo_holds_iff a b).mp hc

/-- `beq` is the `eq` code. -/
theorem beq_holds (a b : X) : decide (a = b) = condHolds .eq a b := by
  cases hc : condHolds .eq a b
  · apply Bool.eq_false_iff.mpr
    intro h
    have := (eq_holds_iff a b).mpr (of_decide_eq_true h)
    rw [hc] at this
    exact Bool.false_ne_true this
  · exact decide_eq_true ((eq_holds_iff a b).mp hc)

/-- The bridge: a branch holds exactly when its condition code holds on
    the flags of `a - b`. The comparison term is shared between the lanes
    with one meaning. -/
theorem Br.holds_eq_condHolds (br : Br) (a b : X) : br.holds a b = condHolds br.cond a b := by
  cases br
  · exact beq_holds a b
  · show (!decide (a = b)) = condHolds .ne a b
    have : condHolds .ne a b = !condHolds .eq a b := by simp [condHolds, Cond.holds]
    rw [this, beq_holds]
  · exact (lt_holds_eq_slt_w64 a b).symm
  · exact (ge_holds_eq_not_slt_w64 a b).symm
  · exact bltu_holds a b
  · show (!(a.ult b)) = condHolds .hs a b
    have : condHolds .hs a b = !condHolds .lo a b := by simp [condHolds, Cond.holds]
    rw [this, bltu_holds]

/-- `slt` is the `lt` comparison term as a 0/1 value; `sltu` the `lo` one. -/
theorem slt_eq_cond (a b : X) : slt a b = (if condHolds .lt a b then 1 else 0) := by
  simp only [slt, lt_holds_eq_slt_w64]
theorem sltu_eq_cond (a b : X) : sltu a b = (if condHolds .lo a b then 1 else 0) := by
  simp only [sltu]
  by_cases h : a.ult b
  · rw [if_pos h, if_pos ((lo_holds_iff a b).mpr h)]
  · have hc : condHolds .lo a b = false := by
      cases hc : condHolds .lo a b
      · rfl
      · exact absurd ((lo_holds_iff a b).mp hc) h
    rw [if_neg h, if_neg (by simp [hc])]

/-- The psABI widening of a `w`-bit integer parameter (`w ≤ 32`): by its
    own sign to 32 bits, then sign-extended to 64. -/
def widen (w : Nat) (signed : Bool) (v : BitVec w) : X :=
  sextW (if signed then v.signExtend 32 else v.zeroExtend 32)

/-- The low bits of a widened parameter are the parameter: the verifier's
    binding reads them back at the declared width. -/
theorem widen_truncate_u32 (v : BitVec 32) : (widen 32 false v).truncate 32 = v := by
  simp only [widen, sextW]; bv_decide
theorem widen_truncate_i32 (v : BitVec 32) : (widen 32 true v).truncate 32 = v := by
  simp only [widen, sextW]; bv_decide
theorem widen_truncate_u8 (v : BitVec 8) : (widen 8 false v).truncate 8 = v := by
  simp only [widen, sextW]; bv_decide
theorem widen_truncate_i8 (v : BitVec 8) : (widen 8 true v).truncate 8 = v := by
  simp only [widen, sextW]; bv_decide

/-- A widened `u32` parameter is already a W-form fixed point: `sext.w`
    on it is the identity, which is why `addw` on two widened `u32`s is
    their 32-bit sum widened. -/
theorem addw_widen (x y : BitVec 32) :
    addw (widen 32 false x) (widen 32 false y) = widen 32 false (x + y) := by
  simp only [addw, widen, sextW]; bv_decide

/-! ## The index guard (span element memory, `94-assembler.md` §9)

The LP64 pair leaves a span's `u32` length in the low half of its register
with padding above; the checker admits a bound only from the *normalized*
copy `(len << 32) >> 32`. On the fall-through of `bgeu idx, lenN, exit`
the branch did not hold, so `idx <u lenN`; since `lenN < 2^32`, the index
is below the length and fits 32 bits, and `idx << s` for `2^s` the element
size addresses element `idx` without wrapping — what `deriveRegion`
relies on. -/

/-- The normalized length as the checker's instruction pair computes it:
    `slli 32` then `srli 32`, the low 32 bits zero-extended. -/
def normalize (len : X) : X := (len <<< 32) >>> 32

theorem normalize_lt (len : X) : (normalize len).toNat < 2 ^ 32 := by
  have h := (len <<< 32).isLt
  simp only [normalize, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  omega

/-- The fall-through of `bgeu idx, lenN, exit` proves the index below the
    normalized length. -/
theorem index_guard (idx len : X) (h : Br.holds .bgeu idx (normalize len) = false) :
    idx.toNat < (normalize len).toNat := by
  simp only [Br.holds, Bool.not_eq_false'] at h
  exact BitVec.ult_iff_toNat_lt.mp h

/-- A guarded index fits 32 bits. -/
theorem index_guard_lt32 (idx len : X) (h : Br.holds .bgeu idx (normalize len) = false) :
    idx.toNat < 2 ^ 32 :=
  Nat.lt_trans (index_guard idx len h) (normalize_lt len)

/-- The scaled index does not wrap: for `s ≤ 31`, `idx << s` is exactly
    `idx · 2^s` as a number, so `base + (idx << s)` is the address of
    element `idx` of `2^s`-byte elements. -/
theorem scaled_index_exact (idx len : X) (s : Nat) (hs : s ≤ 31)
    (h : Br.holds .bgeu idx (normalize len) = false) :
    (idx <<< s).toNat = idx.toNat * 2 ^ s := by
  have hidx := index_guard_lt32 idx len h
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  apply Nat.mod_eq_of_lt
  calc idx.toNat * 2 ^ s < 2 ^ 32 * 2 ^ s := Nat.mul_lt_mul_of_pos_right hidx (Nat.two_pow_pos s)
    _ = 2 ^ (32 + s) := by rw [Nat.pow_add]
    _ ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) (by omega)

/-! ## Loop couplings of widened variables (`94-assembler.md` §9)

The verifier couples a 64-bit register to a 32-bit Oak loop variable as
`r = ext(x) + b` for one of the two widenings the ISA produces, and one
iteration must preserve it. The two lemmas are the preservation steps:
a 64-bit increment of a zero-extended counter stays its zero extension
while the counter is below `2^32 - 1` (the loop's guard `i < len` with
`len < 2^32` supplies it), and `addw` on sign-extended operands is the
sign extension of the 32-bit sum. -/

theorem zext_increment (x : BitVec 32) (h : x ≠ BitVec.allOnes 32) :
    x.zeroExtend 64 + 1 = (x + 1).zeroExtend 64 := by
  bv_decide

/-- The loop guard supplies the side condition: a counter below any bound
    is not all ones. -/
theorem lt_bound_ne_allOnes (x n : BitVec 32) (h : x.ult n) : x ≠ BitVec.allOnes 32 := by
  intro hx
  subst hx
  simp [BitVec.ult_iff_toNat_lt, BitVec.toNat_allOnes] at h
  have := n.isLt
  omega

theorem addw_sext (x y : BitVec 32) :
    addw (x.signExtend 64) (y.signExtend 64) = (x + y).signExtend 64 := by
  simp only [addw, sextW]; bv_decide

/-- The accumulator's coupling is a fixed point of `sext.w`, so reading it
    at 32 bits (the contract width of the result) gives the Oak sum. -/
theorem addw_sext_truncate (x y : BitVec 32) :
    (addw (x.signExtend 64) (y.signExtend 64)).truncate 32 = x + y := by
  rw [addw_sext]; bv_decide

/-! ## The LP64D contract (`94-assembler.md` §9)

Parameters are placed in two independent files: integers (and span pairs)
in `a0`–`a7` in declaration order, `f32`/`f64` in `fa0`–`fa7` in
declaration order; the result in `a0` or `fa0` by its type. The checker
computes exactly this (`bindContract`); the model states that the
placement is injective and order-preserving within each file, so two
parameters never share a register and a binding names each register at
most once. -/

inductive Kind where
  | int | float
  deriving DecidableEq, Repr

/-- A register of the contract: the file and the index into `a0`–`a7` or
    `fa0`–`fa7`. -/
structure Reg where
  kind : Kind
  index : Nat
  deriving DecidableEq, Repr

/-- The placement of a parameter list: the k-th parameter of each kind
    takes the k-th register of its file. -/
def lp64dBinding : List Kind → List Reg
  | ks => go ks 0 0
where
  go : List Kind → Nat → Nat → List Reg
    | [], _, _ => []
    | .int :: rest, i, f => ⟨.int, i⟩ :: go rest (i + 1) f
    | .float :: rest, i, f => ⟨.float, f⟩ :: go rest i (f + 1)

theorem lp64dBinding_length (ks : List Kind) : (lp64dBinding ks).length = ks.length := by
  suffices h : ∀ ks i f, (lp64dBinding.go ks i f).length = ks.length from h ks 0 0
  intro ks
  induction ks with
  | nil => intros; rfl
  | cons k rest ih => intro i f; cases k <;> simp [lp64dBinding.go, ih]

/-- Each parameter keeps its kind's file. -/
theorem lp64dBinding_kinds (ks : List Kind) : (lp64dBinding ks).map Reg.kind = ks := by
  suffices h : ∀ ks i f, (lp64dBinding.go ks i f).map Reg.kind = ks from h ks 0 0
  intro ks
  induction ks with
  | nil => intros; rfl
  | cons k rest ih => intro i f; cases k <;> simp [lp64dBinding.go, ih]

/-- Every list of kinds up to the contract's width (eight of each file)
    places its parameters in distinct registers: decided exhaustively. -/
def allKinds : Nat → List (List Kind)
  | 0 => [[]]
  | n + 1 => [] :: ((allKinds n).flatMap fun ks => [Kind.int :: ks, Kind.float :: ks])

set_option maxRecDepth 20000 in
theorem lp64dBinding_nodup_upto8 : ∀ ks ∈ allKinds 8, (lp64dBinding ks).Nodup := by decide

/-- Two examples the tests use: `(a, b, c : f64)` and `(n : u32, x : f64)`. -/
theorem lp64dBinding_fma : lp64dBinding [.float, .float, .float] = [⟨.float, 0⟩, ⟨.float, 1⟩, ⟨.float, 2⟩] := rfl
theorem lp64dBinding_mixed : lp64dBinding [.int, .float, .int, .float] = [⟨.int, 0⟩, ⟨.float, 0⟩, ⟨.int, 1⟩, ⟨.float, 1⟩] := rfl

/-- The move instructions between the files are bit identities: a value
    moved to the floating-point file and back is unchanged, so an integer
    carrier of an `f64` pattern survives the round trip (`fmv.d.x`/`fmv.x.d`
    in the differential's constant loading). -/
def fmvDX (x : X) : BitVec 64 := x
def fmvXD (f : BitVec 64) : X := f

theorem fmv_round_trip (x : X) : fmvXD (fmvDX x) = x := rfl

end Oak.RiscV

/-! ## The vector configuration as checker state (`94-assembler.md` §9, RVV 1.0 §6.3)

`vsetvli rd, rs1, vtype` chooses the vector length `vl` for the application
vector length `avl` in `rs1` under the hardware maximum `vlmax`: `avl` when
it fits, otherwise any `vl` with `ceil(avl/2) ≤ vl ≤ vlmax` (the
implementation's choice; QEMU and Sail take `vlmax`). What every choice
satisfies — and all the checker relies on — is `vl ≤ avl`, `vl ≤ vlmax`,
and progress: `vl > 0` when `avl > 0`. A strip-mining loop hands
`len - idx` to vsetvli under the guard `idx < len` and loads `vl` elements
at `&v[idx]`: the access lies within the span, and the loop advances. -/

namespace Oak.RiscV

/-- The constraint every legal vsetvl choice satisfies (RVV 1.0 §6.3). -/
def vsetvlOK (avl vlmax vl : Nat) : Prop :=
  vl ≤ avl ∧ vl ≤ vlmax ∧ (avl ≤ vlmax → vl = avl) ∧ (0 < avl → 0 < vl)

/-- QEMU's and Sail's choice, `min avl vlmax`, is a legal one. -/
theorem vsetvl_min_ok (avl vlmax : Nat) (h : 0 < vlmax) : vsetvlOK avl vlmax (min avl vlmax) := by
  refine ⟨Nat.min_le_left _ _, Nat.min_le_right _ _, fun hle => Nat.min_eq_left hle, fun hpos => ?_⟩
  omega

/-- The strip-mining access: `vl` elements at index `idx`, with `vl` chosen
    for the remaining count `len - idx`, stay within `len`. -/
theorem strip_access_in_bounds (len idx vlmax vl : Nat) (hguard : idx < len)
    (hv : vsetvlOK (len - idx) vlmax vl) : idx + vl ≤ len := by
  have hle : vl ≤ len - idx := hv.1
  omega

/-- The loop advances: under the guard the remaining count is positive, so
    `vl` is, and `idx + vl > idx`. -/
theorem strip_progress (len idx vlmax vl : Nat) (hguard : idx < len)
    (hv : vsetvlOK (len - idx) vlmax vl) : idx < idx + vl := by
  have hpos : 0 < vl := hv.2.2.2 (by omega)
  omega

/-- An immediate AVL within a proven minimum length keeps the access from the
    span's base within the span (`bltu len, K` then `vsetivli rd, k`, k ≤ K). -/
theorem immediate_access_in_bounds (len minLen k vlmax vl : Nat) (hmin : minLen ≤ len)
    (hk : k ≤ minLen) (hv : vsetvlOK k vlmax vl) : vl ≤ len := by
  have := hv.1
  omega

/-- The vtype immediate (RVV 1.0 §3.4): vlmul in bits 2:0, vsew in bits 5:3,
    vta bit 6, vma bit 7. -/
def vtype (vsew vlmul : Nat) (ta ma : Bool) : Nat :=
  vlmul + vsew * 8 + (if ta then 64 else 0) + (if ma then 128 else 0)

/-- `e32, m1, ta, ma` is 0xd0 — the field GNU as places in `vsetvli t0, a1, e32, m1, ta, ma`
    (`0d05f2d7`, bits 30:20). -/
theorem vtype_e32_m1_ta_ma : vtype 2 0 true true = 0xd0 := by decide

/-- `e8, m1, tu, mu` is 0. -/
theorem vtype_e8_m1_tu_mu : vtype 0 0 false false = 0 := by decide

/-- The vtype fits its 8 significant bits, so an 11-bit (vsetvli) or 10-bit
    (vsetivli) field carries it with the reserved bits zero. -/
theorem vtype_lt (vsew vlmul : Nat) (ta ma : Bool) (hs : vsew < 8) (hl : vlmul < 8) :
    vtype vsew vlmul ta ma < 256 := by
  unfold vtype
  split <;> split <;> omega

end Oak.RiscV
