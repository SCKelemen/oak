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

/-- The high halves of the 128-bit products (`mulhu`, `mulh`): the operands
    zero- or sign-extended, as the verifier's `umulh`/`smulh` terms compute
    them (`asm/isa_semantics.go`). -/
def mulhu (a b : X) : X := ((a.zeroExtend 128 * b.zeroExtend 128) >>> 64).truncate 64
def mulh (a b : X) : X := ((a.signExtend 128 * b.signExtend 128) >>> 64).truncate 64

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

The LP64 pair carries a span's `u32` length widened like any `u32`
argument (sign-extended from bit 31); the checker admits a bound from the
*normalized* copy `(len << 32) >> 32` against any index, or from the raw
pair when both are widened `u32` parameters (`index_guard_widened`,
below). On the fall-through of `bgeu idx, lenN, exit`
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

/-- The normalization pair is the zero extension of the low half: the
    verifier folds `(x << 32) >> 32` to it (`asm/rv64_verify.go`). -/
theorem normalize_eq (len : X) : normalize len = (len.truncate 32).zeroExtend 64 := by
  apply BitVec.eq_of_toNat_eq
  have h := len.isLt
  rw [normalize, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, BitVec.toNat_setWidth,
    Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  simp only [Nat.reducePow] at *
  omega

/-! ### GCC's shape of the guarded read

A C compiler compares the psABI pair raw: `bgeu idx, len` with both
registers holding widened `u32` parameters (`widen`), then zero-extends
and scales the index in one `slli 32; srli 32-s`, and adds into the base
register. The widening makes the raw comparison the 32-bit comparison, and
the fused pair is the scaled zero extension — the shapes `deriveRegion`
admits through the `widened` and `half` facts. -/

/-- The fall-through of `bgeu idx, len` on two widened `u32` values proves
    the 32-bit comparison: sign extension preserves unsigned order between
    values of one width. -/
theorem index_guard_widened (i len : BitVec 32)
    (h : Br.holds .bgeu (widen 32 false i) (widen 32 false len) = false) :
    i.toNat < len.toNat := by
  simp only [Br.holds, Bool.not_eq_false', widen, sextW] at h
  have hlt : i.ult len = true := by bv_decide
  exact BitVec.ult_iff_toNat_lt.mp hlt

/-- A widened `u32` is the parameter modulo `2^32`. -/
theorem widen_toNat_mod (i : BitVec 32) : (widen 32 false i).toNat % 2 ^ 32 = i.toNat := by
  have h := congrArg BitVec.toNat (widen_truncate_u32 i)
  simpa [BitVec.toNat_setWidth] using h

/-- `slli 32` then `srli 32-s` on a widened index is the zero extension
    shifted by `s`: the index scaled by `2^s`, without wrap. -/
theorem widened_scale (i : BitVec 32) (s : Nat) (hs : s ≤ 32) :
    ((widen 32 false i) <<< 32) >>> (32 - s) = (i.zeroExtend 64) <<< s := by
  apply BitVec.eq_of_toNat_eq
  have hi := i.isLt
  have hmod := widen_toNat_mod i
  have hW := (widen 32 false i).isLt
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth,
    Nat.shiftLeft_eq, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  have hpow : 2 ^ s * 2 ^ (32 - s) = (2:Nat) ^ 32 := by
    rw [← Nat.pow_add, Nat.add_sub_of_le hs]
  have hs' : (2:Nat) ^ s ≤ 2 ^ 32 := Nat.pow_le_pow_right (by decide) hs
  have hleft : (widen 32 false i).toNat * 2 ^ 32 % 2 ^ 64 = i.toNat * 2 ^ 32 := by
    generalize (widen 32 false i).toNat = W at *
    simp only [Nat.reducePow] at *
    omega
  have hsmall : i.toNat * 2 ^ s < 2 ^ 64 :=
    calc i.toNat * 2 ^ s < 2 ^ 32 * 2 ^ 32 := Nat.mul_lt_mul_of_lt_of_le hi hs' (by decide)
      _ = 2 ^ 64 := by decide
  rw [hleft, ← hpow, ← Nat.mul_assoc, Nat.mul_div_cancel _ (Nat.two_pow_pos _),
    Nat.mod_eq_of_lt (Nat.lt_trans hi (by decide)), Nat.mod_eq_of_lt hsmall]

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
  | int | float | vector
  deriving DecidableEq, Repr

/-- A register of the contract: the file and the index into `a0`–`a7`,
    `fa0`–`fa7`, or `v8`–`v23` (the vector kind's index `i` is register
    `v(8 + i)`, RVV psABI: vector arguments in `v8`–`v23`, a vector result in
    `v8`). -/
structure Reg where
  kind : Kind
  index : Nat
  deriving DecidableEq, Repr

/-- The placement of a parameter list: the k-th parameter of each kind
    takes the k-th register of its file. -/
def lp64dBinding : List Kind → List Reg
  | ks => go ks 0 0 0
where
  go : List Kind → Nat → Nat → Nat → List Reg
    | [], _, _, _ => []
    | .int :: rest, i, f, v => ⟨.int, i⟩ :: go rest (i + 1) f v
    | .float :: rest, i, f, v => ⟨.float, f⟩ :: go rest i (f + 1) v
    | .vector :: rest, i, f, v => ⟨.vector, v⟩ :: go rest i f (v + 1)

theorem lp64dBinding_length (ks : List Kind) : (lp64dBinding ks).length = ks.length := by
  suffices h : ∀ ks i f v, (lp64dBinding.go ks i f v).length = ks.length from h ks 0 0 0
  intro ks
  induction ks with
  | nil => intros; rfl
  | cons k rest ih => intro i f v; cases k <;> simp [lp64dBinding.go, ih]

/-- Each parameter keeps its kind's file. -/
theorem lp64dBinding_kinds (ks : List Kind) : (lp64dBinding ks).map Reg.kind = ks := by
  suffices h : ∀ ks i f v, (lp64dBinding.go ks i f v).map Reg.kind = ks from h ks 0 0 0
  intro ks
  induction ks with
  | nil => intros; rfl
  | cons k rest ih => intro i f v; cases k <;> simp [lp64dBinding.go, ih]

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

/-! ### Vectors across the call boundary

A function whose signature carries a fixed `simd` vector follows the RVV
psABI's vector calling convention at its native entry (`<name>_rvv_abi`,
docs/spec/94-assembler.md §9): the k-th vector parameter arrives in
`v(8 + k)`, independently of the integer and float files, and a vector
result leaves in `v8`. The C backend's lane-array struct crosses in the
integer registers instead, so the C emitter converts at the boundary. -/

/-- The vector register of the k-th vector parameter. -/
def vectorArgReg (k : Nat) : Nat := 8 + k

/-- The argument registers are `v8`–`v23`: sixteen of them. -/
theorem vectorArgReg_within (k : Nat) (hk : k < 16) : 8 ≤ vectorArgReg k ∧ vectorArgReg k ≤ 23 := by
  unfold vectorArgReg; omega

/-- The result register is the first argument register (a unary vector
function's parameter and result share `v8`). -/
theorem vectorResultReg_eq : vectorArgReg 0 = 8 := rfl

/-- The vector file is placed beside the others: `(a : simd.U8x16, k : u32,
b : simd.U8x16)` binds `v8`, `a0`, `v9`. -/
theorem lp64dBinding_vector : lp64dBinding [.vector, .int, .vector] = [⟨.vector, 0⟩, ⟨.int, 0⟩, ⟨.vector, 1⟩] := rfl

/-- Every list of kinds of up to six parameters over the three files places
    its parameters in distinct registers: decided exhaustively. -/
def allKinds3 : Nat → List (List Kind)
  | 0 => [[]]
  | n + 1 => [] :: ((allKinds3 n).flatMap fun ks => [Kind.int :: ks, Kind.float :: ks, Kind.vector :: ks])

set_option maxRecDepth 20000 in
theorem lp64dBinding_nodup_vectors_upto6 : ∀ ks ∈ allKinds3 6, (lp64dBinding ks).Nodup := by decide

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

/-! ## Register groups and masks (`94-assembler.md` §9, RVV 1.0 §3.4.2, §5.3)

Under LMUL > 1 every vector register operand names a group of LMUL
registers starting at a multiple of LMUL; a group so aligned lies within
the file. A masked operation touches a subset of the vl elements, so the
bound the unmasked access carries covers it. -/

namespace Oak.RiscV

/-- An aligned register group of `lmul` registers starting at `n < 32` ends
    within the 32-register file. -/
theorem group_within_file (lmul n : Nat) (hdiv : lmul ∣ 32) (hpos : 0 < lmul) (hn : n < 32)
    (ha : lmul ∣ n) : n + lmul ≤ 32 := by
  obtain ⟨q, hq⟩ := ha
  obtain ⟨p, hp⟩ := hdiv
  subst hq
  have hqp : q < p := by
    rcases Nat.lt_or_ge q p with h | h
    · exact h
    · exfalso
      have : lmul * p ≤ lmul * q := Nat.mul_le_mul_left lmul h
      omega
  have : lmul * (q + 1) ≤ lmul * p := Nat.mul_le_mul_left lmul hqp
  rw [Nat.mul_succ] at this
  omega

/-- The legal LMULs divide the file. -/
theorem lmul_divides_file : ∀ lmul ∈ [1, 2, 4, 8], lmul ∣ 32 := by decide

/-- VLMAX at LMUL: `lmul * vlen / sew` elements. -/
def vlmax (vlen sew lmul : Nat) : Nat := lmul * vlen / sew

theorem vlmax_m1_e32_128 : vlmax 128 32 1 = 4 := by decide
theorem vlmax_m2_e32_128 : vlmax 128 32 2 = 8 := by decide

/-! ### Fractional LMUL (`94-assembler.md` §9, RVV 1.0 §3.4.2)

The checker keeps LMUL in eighths: `mf8 = 1`, `mf4 = 2`, `mf2 = 4`,
`m1 = 8`, …, `m8 = 64`. A fractional LMUL fills part of one register, so
its operand group is one register and every alignment fact holds trivially
(`groupOf`); the element width it may hold is bounded by ELEN — the
configuration is reserved when `SEW / LMUL > ELEN` — and widening from a
fractional LMUL doubles the eighths without leaving the single register
until `m1`. -/

/-- The register count of an operand group at `lmul8 / 8`. -/
def groupOf (lmul8 : Nat) : Nat := if lmul8 < 8 then 1 else lmul8 / 8

theorem groupOf_fractional (lmul8 : Nat) (h : lmul8 < 8) : groupOf lmul8 = 1 := by
  simp [groupOf, h]

theorem groupOf_integral : ∀ lmul8 ∈ [8, 16, 32, 64], groupOf lmul8 = lmul8 / 8 := by decide

/-- VLMAX in eighths: `lmul8 * vlen / (8 * sew)`. -/
def vlmax8 (vlen sew lmul8 : Nat) : Nat := lmul8 * vlen / (8 * sew)

theorem vlmax8_mf2_e32_128 : vlmax8 128 32 4 = 2 := by decide
theorem vlmax8_agrees (vlen sew lmul : Nat) : vlmax8 vlen sew (lmul * 8) = vlmax vlen sew lmul := by
  unfold vlmax8 vlmax
  rw [show lmul * 8 * vlen = 8 * (lmul * vlen) by ac_rfl]
  exact Nat.mul_div_mul_left _ _ (by decide)

/-- The configurations the checker admits: `SEW / LMUL ≤ ELEN`, that is
`sew * 8 ≤ elen * lmul8` over eighths. -/
def withinElen (sew elen lmul8 : Nat) : Prop := sew * 8 ≤ elen * lmul8

theorem fractional_within_elen : withinElen 32 64 4 ∧ withinElen 16 64 2 ∧ withinElen 8 64 1 ∧ ¬ withinElen 64 64 4 := by
  unfold withinElen
  decide

/-- Widening from a fractional LMUL stays in one register until `m1`: the
wide group of `mf2` is `m1`, one register. -/
theorem wide_group_fractional : ∀ lmul8 ∈ [1, 2, 4], groupOf (2 * lmul8) = 1 := by decide

/-! ### The vector floating-point forms (fifth increment)

Floating-point addition is not associative, so a reduction's result depends
on the order it adds in. `vfredosum.vs` (RVV 1.0 §14.3) is the *ordered*
form: it folds the strip's elements left to right into the scalar it was
handed. A strip-mining loop hands each strip the previous strip's result,
and the whole is one left fold over the span in element order — the
sequential sum the differential expects from Go. The unordered
`vfredusum.vs`, whose grouping is implementation-defined, is not in the
table. -/

/-- One strip: the ordered reduction of `xs` from the running scalar `acc`. -/
def orderedStrip (f : α → β → α) (acc : α) (xs : List β) : α := xs.foldl f acc

/-- The strips in order: each starts from the previous one's result. -/
def orderedStrips (f : α → β → α) (acc : α) (strips : List (List β)) : α :=
  strips.foldl (orderedStrip f) acc

/-- Two consecutive strips fold as one strip over their concatenation. -/
theorem ordered_strip_append (f : α → β → α) (acc : α) (xs ys : List β) :
    orderedStrip f (orderedStrip f acc xs) ys = orderedStrip f acc (xs ++ ys) := by
  simp [orderedStrip, List.foldl_append]

/-- The strip-mined ordered reduction is the sequential fold over the
whole span in element order, whatever the strip boundaries (the `vl`
each `vsetvli` chose). -/
theorem ordered_strips_fold (f : α → β → α) (acc : α) (strips : List (List β)) :
    orderedStrips f acc strips = orderedStrip f acc strips.flatten := by
  induction strips generalizing acc with
  | nil => rfl
  | cons xs rest ih =>
    simp only [orderedStrips, List.foldl_cons, List.flatten_cons]
    rw [← ordered_strip_append]
    exact ih (orderedStrip f acc xs)

/-- The element widths the floating-point forms admit: `e32` (Zve32f) and
`e64` (Zve64d); `e8` has no float format and `e16` would need Zvfh. -/
def floatSewOK (sew : Nat) : Prop := sew = 32 ∨ sew = 64

theorem float_sew_admitted : floatSewOK 32 ∧ floatSewOK 64 ∧ ¬ floatSewOK 16 ∧ ¬ floatSewOK 8 := by
  unfold floatSewOK; omega

/-! ### Fixed vectors on the native lane: the slack guard

The native backend's fixed 128-bit vectors (docs/spec/93-simd.md §1.4) load
K elements at a guarded index. The guard is spelled `bltu len, k, trap`
(len ≥ K), `sub t, len, k` (t = len − K, no wrap), `bltu t, idx, trap`
(idx ≤ len − K): together idx + K ≤ len, and every one of the K elements
from idx lies inside the span. A vector local's sixteen-byte slot and an
owned array's element are frame memory: an immediate AVL of K elements at
an entry-relative address inside the declared frame. -/

/-- The three instructions of the slack guard prove idx + K ≤ len. -/
theorem slack_guard (len idx k t : Nat) (hmin : k ≤ len) (ht : t = len - k) (hguard : ¬ t < idx) :
    idx + k ≤ len := by
  omega

/-- Under idx + K ≤ len, the K elements from idx are inside the span. -/
theorem slack_access_in_bounds (len idx k i : Nat) (h : idx + k ≤ len) (hi : i < k) : idx + i < len := by
  omega

/-- The AVL the configuration sets is at most K (`vsetivli` with an immediate
    within the guard's K), and vl ≤ AVL: every accessed element is inside. -/
theorem slack_vector_in_bounds (len idx k avl vlmax vl i : Nat) (h : idx + k ≤ len) (havl : avl ≤ k)
    (hv : vsetvlOK avl vlmax vl) (hi : i < vl) : idx + i < len := by
  unfold vsetvlOK at hv
  omega

/-- A fixed vector in the frame: K elements of `width` bytes at an
    entry-relative address `addr` (negative, above `-frame`) end at or before
    the entry sp, so every byte lies inside the declared frame. -/
theorem frame_vector_in_bounds (frame addr k width i : Int) (hlo : -frame ≤ addr) (hhi : addr + k * width ≤ 0)
    (hi : 0 ≤ i) (hik : i < k * width) : -frame ≤ addr + i ∧ addr + i < 0 := by
  omega

/-! ### Fixed configurations in the verifier (asm/rv64_verify_vector.go)

The verifier models the vector file under `vsetivli zero, K, eS, m1` when
`K · S ≤ 128`: on every implementation with `VLEN ≥ 128` the maximum
length at `eS/m1` is at least `K`, so `vl = min(K, VLMAX) = K` exactly and
the instructions act on `K` lanes whatever the VLEN. The lanes past `vl`
are tail-agnostic (RVV 1.0 §3.4.3): the verifier gives them fresh unknown
values, so a unit whose result depends on them is a mismatch and one that
masks them out is proven. -/

/-- With `VLEN ≥ 128`, `K` lanes of `S` bits with `K · S ≤ 128` fit: `K ≤ VLMAX`. -/
theorem fixed_lanes_fit (vlen K S : Nat) (hS : 0 < S) (hvlen : 128 ≤ vlen) (hKS : K * S ≤ 128) :
    K ≤ vlmax vlen S 1 := by
  unfold vlmax
  rw [Nat.one_mul]
  exact (Nat.le_div_iff_mul_le hS).2 (by omega)

/-- Under such a configuration `vl` is `K` exactly, on every VLEN. -/
theorem fixed_config_vl (vlen K S : Nat) (hK : 0 < K) (hS : 0 < S) (hvlen : 128 ≤ vlen) (hKS : K * S ≤ 128) :
    vsetvlOK K (vlmax vlen S 1) (min K (vlmax vlen S 1)) ∧ min K (vlmax vlen S 1) = K := by
  refine ⟨vsetvl_min_ok _ _ ?_, Nat.min_eq_left (fixed_lanes_fit vlen K S hS hvlen hKS)⟩
  unfold vlmax
  rw [Nat.one_mul]
  have hSK : S ≤ K * S := Nat.le_mul_of_pos_left S hK
  exact Nat.div_pos (by omega) hS

/-- The sixteen bytes, eight halfwords, four words, and two doublewords of
the fixed vectors all fit, as does the one-element `e32` read of a mask. -/
theorem fixed_shapes_fit : 16 * 8 ≤ 128 ∧ 8 * 16 ≤ 128 ∧ 4 * 32 ≤ 128 ∧ 2 * 64 ≤ 128 ∧ 1 * 32 ≤ 128 := by decide

/-- A masked element is one of the vl elements: whatever the mask, the
    strip-mining bound covers it. -/
theorem masked_access_in_bounds (len idx vlmax vl i : Nat) (hguard : idx < len)
    (hv : vsetvlOK (len - idx) vlmax vl) (hi : i < vl) (_mask : Bool) : idx + i < len := by
  have := strip_access_in_bounds len idx vlmax vl hguard hv
  omega

end Oak.RiscV

/-! ## Compressed immediates (RVC, `94-assembler.md` §9)

A compressed instruction denotes its base instruction: the 6-bit signed
field carries exactly the values -32..31 the encoder admits, and a scaled
offset field carries exactly the aligned offsets below its bound. -/

namespace Oak.RiscV

/-- Every value the encoder places in a 6-bit two's-complement field reads
    back as itself. -/
theorem imm6_round_trip : ∀ v : Fin 64, (BitVec.ofInt 6 ((v.val : Int) - 32)).toInt = (v.val : Int) - 32 := by
  decide

/-- A scaled offset field is exact for aligned offsets below the bound:
    `off = scale * (off / scale)` when `scale ∣ off`. -/
theorem scaled_offset_exact (scale off bound : Nat) (hs : 0 < scale) (hdiv : scale ∣ off) (hlt : off < bound * scale) :
    scale * (off / scale) = off ∧ off / scale < bound := by
  obtain ⟨q, hq⟩ := hdiv
  subst hq
  rw [Nat.mul_div_cancel_left q hs]
  refine ⟨rfl, ?_⟩
  rw [Nat.mul_comm bound scale] at hlt
  exact Nat.lt_of_mul_lt_mul_left hlt

/-- c.lwsp: word offsets below 256 bytes; c.ldsp: doubleword offsets below 512. -/
theorem lwsp_offsets (off : Nat) (h4 : 4 ∣ off) (hlt : off < 256) : 4 * (off / 4) = off ∧ off / 4 < 64 :=
  scaled_offset_exact 4 off 64 (by decide) h4 hlt

theorem ldsp_offsets (off : Nat) (h8 : 8 ∣ off) (hlt : off < 512) : 8 * (off / 8) = off ∧ off / 8 < 64 :=
  scaled_offset_exact 8 off 64 (by decide) h8 hlt

end Oak.RiscV

/-! ## Wide groups (RVV 1.0 §11.2)

A widening destination or a narrowing source is a group of `2 * lmul`
registers with `2 * sew` elements: it stays within the file when `lmul ≤ 4`
and within 64-bit elements when `sew ≤ 32`. -/

namespace Oak.RiscV

theorem wide_lmul_divides_file : ∀ lmul ∈ [1, 2, 4], (2 * lmul) ∣ 32 := by decide

/-- An aligned wide group lies within the file. -/
theorem wide_group_within_file (lmul n : Nat) (hl : lmul ∈ [1, 2, 4]) (hn : n < 32) (ha : (2 * lmul) ∣ n) :
    n + 2 * lmul ≤ 32 :=
  group_within_file (2 * lmul) n (wide_lmul_divides_file lmul hl) (by simp at hl; omega) hn ha

/-- Widening doubles the element width: within 64 bits exactly when the
    configured width is at most 32. -/
theorem widening_within_64 (sew : Nat) : 2 * sew ≤ 64 ↔ sew ≤ 32 := by omega

end Oak.RiscV

/-! ## Encodings (`asm/rv64_encode.go`, `asm/rv64_encodings_gen.go`)

The encoder writes each base instruction as its table entry's fixed bits
(riscv-opcodes, `asm/rv64_encodings_gen.go`) with the operand fields placed
by name at `[hi:lo]`: `word |= uint32(uint64(v) & (2^width - 1)) << lo`.
These definitions restate the entries the verifier decides, generated from
the table by `asm/rv64_encoding_lean_test.go` (which holds them equal to
it), and `spec/lean-sail/OakSailBridge/Encoding.lean` proves each equal to
the Sail model's `encdec_forwards` of the instruction it spells — the
machine words as a consequence of the ISA's specification. -/

namespace Oak.RiscV.Enc

-- OAK-DEF-BEGIN
/-- One operand field of an encoding: the bits `[hi:lo]` of the word. -/
structure Field where
  name : String
  hi : Nat
  lo : Nat
  deriving Repr, DecidableEq

/-- A table entry: the fixed bits, their mask, and the operand fields. -/
structure Encoding where
  mnemonic : String
  value : BitVec 32
  mask : BitVec 32
  fields : List Field
  deriving Repr

/-- The encoder's placement of one operand (`encodeRV64Instruction`): masked
    to the field's width, truncated to the word, shifted to its low bit. -/
def placeField (word : BitVec 32) (f : Field) (v : BitVec 64) : BitVec 32 :=
  word ||| (((v &&& BitVec.ofNat 64 (2 ^ (f.hi - f.lo + 1) - 1)).truncate 32) <<< f.lo)

/-- The word of an instruction: the fixed bits with every field placed. -/
def encode (e : Encoding) (operand : String → BitVec 64) : BitVec 32 :=
  e.fields.foldl (fun word f => placeField word f (operand f.name)) e.value

/-- Register operands, as the encoder numbers them. -/
def rOperands (rd rs1 rs2 : BitVec 5) : String → BitVec 64 := fun n =>
  if n = "rd" then rd.zeroExtend 64 else if n = "rs1" then rs1.zeroExtend 64 else if n = "rs2" then rs2.zeroExtend 64 else 0

/-- An I-type immediate is the 12-bit two's complement the operand carried
    (`fields["imm12"] = value`, a signed 64-bit value masked to 12 bits). -/
def iOperands (rd rs1 : BitVec 5) (imm : BitVec 12) : String → BitVec 64 := fun n =>
  if n = "rd" then rd.zeroExtend 64 else if n = "rs1" then rs1.zeroExtend 64 else if n = "imm12" then imm.signExtend 64 else 0

/-- A shift amount (`shamtd`, 0..63). -/
def shiftOperands (rd rs1 : BitVec 5) (shamt : BitVec 6) : String → BitVec 64 := fun n =>
  if n = "rd" then rd.zeroExtend 64 else if n = "rs1" then rs1.zeroExtend 64 else if n = "shamtd" then shamt.zeroExtend 64 else 0

/-- The branch immediate's permuted halves, from the 13-bit offset `delta`
    (bit 0 always zero): `bimm12hi = delta[12] ‖ delta[10:5]`,
    `bimm12lo = delta[4:1] ‖ delta[11]` (`encodeRV64Instruction`). -/
def bimm12hi (delta : BitVec 64) : BitVec 64 :=
  (((delta >>> 12) &&& 1) <<< 6) ||| ((delta >>> 5) &&& 0x3f)
def bimm12lo (delta : BitVec 64) : BitVec 64 :=
  (((delta >>> 1) &&& 0xf) <<< 1) ||| ((delta >>> 11) &&& 1)
def bOperands (rs1 rs2 : BitVec 5) (delta : BitVec 13) : String → BitVec 64 := fun n =>
  if n = "rs1" then rs1.zeroExtend 64 else if n = "rs2" then rs2.zeroExtend 64
  else if n = "bimm12hi" then bimm12hi (delta.signExtend 64) else if n = "bimm12lo" then bimm12lo (delta.signExtend 64) else 0

-- OAK-ENC-BEGIN (generated from asm/rv64_encodings_gen.go by asm/rv64_encoding_lean_test.go; do not edit)
def add : Encoding := ⟨"add", 0x00000033#32, 0xfe00707f#32, [⟨"rd", 11, 7⟩, ⟨"rs1", 19, 15⟩, ⟨"rs2", 24, 20⟩]⟩
def sub : Encoding := ⟨"sub", 0x40000033#32, 0xfe00707f#32, [⟨"rd", 11, 7⟩, ⟨"rs1", 19, 15⟩, ⟨"rs2", 24, 20⟩]⟩
def sll : Encoding := ⟨"sll", 0x00001033#32, 0xfe00707f#32, [⟨"rd", 11, 7⟩, ⟨"rs1", 19, 15⟩, ⟨"rs2", 24, 20⟩]⟩
def slt : Encoding := ⟨"slt", 0x00002033#32, 0xfe00707f#32, [⟨"rd", 11, 7⟩, ⟨"rs1", 19, 15⟩, ⟨"rs2", 24, 20⟩]⟩
def sltu : Encoding := ⟨"sltu", 0x00003033#32, 0xfe00707f#32, [⟨"rd", 11, 7⟩, ⟨"rs1", 19, 15⟩, ⟨"rs2", 24, 20⟩]⟩
def xor_ : Encoding := ⟨"xor", 0x00004033#32, 0xfe00707f#32, [⟨"rd", 11, 7⟩, ⟨"rs1", 19, 15⟩, ⟨"rs2", 24, 20⟩]⟩
def srl : Encoding := ⟨"srl", 0x00005033#32, 0xfe00707f#32, [⟨"rd", 11, 7⟩, ⟨"rs1", 19, 15⟩, ⟨"rs2", 24, 20⟩]⟩
def sra : Encoding := ⟨"sra", 0x40005033#32, 0xfe00707f#32, [⟨"rd", 11, 7⟩, ⟨"rs1", 19, 15⟩, ⟨"rs2", 24, 20⟩]⟩
def or_ : Encoding := ⟨"or", 0x00006033#32, 0xfe00707f#32, [⟨"rd", 11, 7⟩, ⟨"rs1", 19, 15⟩, ⟨"rs2", 24, 20⟩]⟩
def and_ : Encoding := ⟨"and", 0x00007033#32, 0xfe00707f#32, [⟨"rd", 11, 7⟩, ⟨"rs1", 19, 15⟩, ⟨"rs2", 24, 20⟩]⟩
def addw : Encoding := ⟨"addw", 0x0000003b#32, 0xfe00707f#32, [⟨"rd", 11, 7⟩, ⟨"rs1", 19, 15⟩, ⟨"rs2", 24, 20⟩]⟩
def subw : Encoding := ⟨"subw", 0x4000003b#32, 0xfe00707f#32, [⟨"rd", 11, 7⟩, ⟨"rs1", 19, 15⟩, ⟨"rs2", 24, 20⟩]⟩
def sllw : Encoding := ⟨"sllw", 0x0000103b#32, 0xfe00707f#32, [⟨"rd", 11, 7⟩, ⟨"rs1", 19, 15⟩, ⟨"rs2", 24, 20⟩]⟩
def srlw : Encoding := ⟨"srlw", 0x0000503b#32, 0xfe00707f#32, [⟨"rd", 11, 7⟩, ⟨"rs1", 19, 15⟩, ⟨"rs2", 24, 20⟩]⟩
def sraw : Encoding := ⟨"sraw", 0x4000503b#32, 0xfe00707f#32, [⟨"rd", 11, 7⟩, ⟨"rs1", 19, 15⟩, ⟨"rs2", 24, 20⟩]⟩
def addi : Encoding := ⟨"addi", 0x00000013#32, 0x0000707f#32, [⟨"rd", 11, 7⟩, ⟨"rs1", 19, 15⟩, ⟨"imm12", 31, 20⟩]⟩
def slti : Encoding := ⟨"slti", 0x00002013#32, 0x0000707f#32, [⟨"rd", 11, 7⟩, ⟨"rs1", 19, 15⟩, ⟨"imm12", 31, 20⟩]⟩
def sltiu : Encoding := ⟨"sltiu", 0x00003013#32, 0x0000707f#32, [⟨"rd", 11, 7⟩, ⟨"rs1", 19, 15⟩, ⟨"imm12", 31, 20⟩]⟩
def xori : Encoding := ⟨"xori", 0x00004013#32, 0x0000707f#32, [⟨"rd", 11, 7⟩, ⟨"rs1", 19, 15⟩, ⟨"imm12", 31, 20⟩]⟩
def ori : Encoding := ⟨"ori", 0x00006013#32, 0x0000707f#32, [⟨"rd", 11, 7⟩, ⟨"rs1", 19, 15⟩, ⟨"imm12", 31, 20⟩]⟩
def andi : Encoding := ⟨"andi", 0x00007013#32, 0x0000707f#32, [⟨"rd", 11, 7⟩, ⟨"rs1", 19, 15⟩, ⟨"imm12", 31, 20⟩]⟩
def slli : Encoding := ⟨"slli", 0x00001013#32, 0xfc00707f#32, [⟨"rd", 11, 7⟩, ⟨"rs1", 19, 15⟩, ⟨"shamtd", 25, 20⟩]⟩
def srli : Encoding := ⟨"srli", 0x00005013#32, 0xfc00707f#32, [⟨"rd", 11, 7⟩, ⟨"rs1", 19, 15⟩, ⟨"shamtd", 25, 20⟩]⟩
def srai : Encoding := ⟨"srai", 0x40005013#32, 0xfc00707f#32, [⟨"rd", 11, 7⟩, ⟨"rs1", 19, 15⟩, ⟨"shamtd", 25, 20⟩]⟩
def beq : Encoding := ⟨"beq", 0x00000063#32, 0x0000707f#32, [⟨"bimm12hi", 31, 25⟩, ⟨"rs1", 19, 15⟩, ⟨"rs2", 24, 20⟩, ⟨"bimm12lo", 11, 7⟩]⟩
def bne : Encoding := ⟨"bne", 0x00001063#32, 0x0000707f#32, [⟨"bimm12hi", 31, 25⟩, ⟨"rs1", 19, 15⟩, ⟨"rs2", 24, 20⟩, ⟨"bimm12lo", 11, 7⟩]⟩
def blt : Encoding := ⟨"blt", 0x00004063#32, 0x0000707f#32, [⟨"bimm12hi", 31, 25⟩, ⟨"rs1", 19, 15⟩, ⟨"rs2", 24, 20⟩, ⟨"bimm12lo", 11, 7⟩]⟩
def bge : Encoding := ⟨"bge", 0x00005063#32, 0x0000707f#32, [⟨"bimm12hi", 31, 25⟩, ⟨"rs1", 19, 15⟩, ⟨"rs2", 24, 20⟩, ⟨"bimm12lo", 11, 7⟩]⟩
def bltu : Encoding := ⟨"bltu", 0x00006063#32, 0x0000707f#32, [⟨"bimm12hi", 31, 25⟩, ⟨"rs1", 19, 15⟩, ⟨"rs2", 24, 20⟩, ⟨"bimm12lo", 11, 7⟩]⟩
def bgeu : Encoding := ⟨"bgeu", 0x00007063#32, 0x0000707f#32, [⟨"bimm12hi", 31, 25⟩, ⟨"rs1", 19, 15⟩, ⟨"rs2", 24, 20⟩, ⟨"bimm12lo", 11, 7⟩]⟩
-- OAK-ENC-END
-- OAK-DEF-END

end Oak.RiscV.Enc
