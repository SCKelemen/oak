import Oak.AssemblerSemantics

/-!
# The seam between the verifier's Oak lowering and the Lean extraction

`docs/spec/126-verification-chain.md` §4 names one unproved seam on the
arm64 lane. The assembler verifier lowers an Oak body into the term
language of `Oak.AssemblerSemantics` (`asm/verify.go`, `oakLowering.lower`)
and the Lean extraction embeds the same body as Lean's fixed-width integers
(`codegen/lean`, `95-extraction.md`); both were held to `20-types.md` §11.1
by tests, but no theorem related them. This module states both over one
typed expression language for the subset they share and proves them equal.

* `Expr t` is an Oak scalar expression of type `t` — parameters, checked
  literals, the wrapping arithmetic, the unsigned bitwise operators and
  shifts, unsigned division and remainder by a constant power of two,
  negation and complement, the conversions, comparisons, `&&`/`||`/`!`
  and Bool conditionals. `Bool` is the width-1 type both readers use.
* `evalX` is the extraction's reading: `UIntN`/`IntN` arithmetic is
  `BitVec` arithmetic at the width, a shift's count is taken modulo the
  width (Lean's `UInt32.shiftLeft` masks it), a comparison is `decide` of
  the unsigned or signed order, `toUIntN`/`toIntN` extend by the source's
  signedness or truncate, and a `Bool` is its 1/0 image (`ofBool_and`,
  `ofBool_or`, `ofBool_not` say the image is a homomorphism).
* `Term` is the verifier's term language and `Term.eval` its executor
  (`term.evalUncached`): every operand is masked to the node's width, the
  operation wraps to the width, a comparison is the ARM condition code on
  the flags of `l - r` at the operands' width (`conditionHolds`), and an
  `ite` picks an arm. `truncate`, `zeroExtend`, `adaptWidth` and
  `extendTerm` are the Go helpers as the Go spells them, shape cases
  included; `lowerT` is `oakLowering.lower` at the expression's own width.
* `lowerT_eval`: `(lowerT e).eval ρ = (evalX e ρ).toNat` for every
  expression and every parameter assignment.

Two things the Go does that the model leaves out, both eval-preserving:
the term constructors fold constant subterms and drop `x + 0`, and a
comparison in the condition of an `ite` keeps the operands' width where
`lowerT` re-widths it to 1 (the executor reads a comparison's width only
where its 1/0 result is used, and `String` does not print it).

`asm/lowering_refinement_test.go` pins the Go to `lowerT`: it lowers a
table of Oak expressions and compares the rendered terms with the renders
`lowerT` gives, stated at the end of this file; either side changing must
visit the other. With this theorem, a theorem about an Oak function's
extraction and the verifier's proof that an asm body equals the function's
lowering compose: source theorem, `lowerT_eval`, the verifier's equality,
`Oak.ArmASL`.
-/

set_option linter.unusedSimpArgs false

namespace Oak.LoweringRefinement

open Oak.AssemblerSemantics

/-! ## Types and expressions -/

/-- The scalar types both readers share; `bool` is `Bool`, width 1
(`contractBits`), unsigned. -/
inductive Ty
  | bool | u8 | u16 | u32 | u64 | i8 | i16 | i32 | i64
  deriving DecidableEq, Repr

def Ty.width : Ty → Nat
  | .bool => 1
  | .u8 | .i8 => 8
  | .u16 | .i16 => 16
  | .u32 | .i32 => 32
  | .u64 | .i64 => 64

def Ty.signed : Ty → Bool
  | .i8 | .i16 | .i32 | .i64 => true
  | _ => false

theorem Ty.width_pos (t : Ty) : 0 < t.width := by cases t <;> decide

theorem Ty.width_le (t : Ty) : t.width ≤ 64 := by cases t <;> decide

/-- Comparison operators; `lt`…`ge` read by the operands' signedness. -/
inductive CmpOp
  | eq | ne | lt | le | gt | ge
  deriving DecidableEq, Repr

/-- The wrapping arithmetic (`20-types.md` §11.1), on every integer type. -/
inductive ArithOp
  | add | sub | mul
  deriving DecidableEq, Repr

/-- The bitwise operators and shifts (`10-syntax.md` §3b: unsigned operands
only, so `>>` is the logical shift for both readers); on `Bool` the
`and`/`or` are `&&`/`||`. -/
inductive BitOp
  | and | or | xor | shl | shr
  deriving DecidableEq, Repr

/-- The shared subset. A literal carries its checked value at the type's
width (`Oak.LiteralFitRefinement`); `divPow2`/`modPow2` are `/` and `%` by
the unsigned constant `2^k`, the only division the verifier admits
(`k < width` because the constant is checked at the type); `not` is `^x`
on an integer and `!b` on `Bool`; `conv` is a `u8(x)`…`i64(x)` widening or
a `{t}_trunc_{s}`/`{t}_bits_{s}` narrowing; `ite` is `if c then a else b`
(a Bool `match`). -/
inductive Expr : Ty → Type
  | param (t : Ty) (name : String) : Expr t
  | lit (t : Ty) (v : BitVec t.width) : Expr t
  | arith (op : ArithOp) {t : Ty} (a b : Expr t) : Expr t
  | bit (op : BitOp) {t : Ty} (a b : Expr t) (h : t.signed = false) : Expr t
  | divPow2 {t : Ty} (a : Expr t) (k : Nat) (hk : k < t.width) (hu : t.signed = false) : Expr t
  | modPow2 {t : Ty} (a : Expr t) (k : Nat) (hk : k < t.width) (hu : t.signed = false) : Expr t
  | neg {t : Ty} (a : Expr t) : Expr t
  | not {t : Ty} (a : Expr t) : Expr t
  | conv {s : Ty} (t : Ty) (a : Expr s) : Expr t
  | cmp {s : Ty} (op : CmpOp) (l r : Expr s) : Expr .bool
  | ite {t : Ty} (c : Expr .bool) (a b : Expr t) : Expr t

/-- A parameter assignment: the value each parameter arrives with. Both
readers take it at the parameter's width (`ofNat`, `& mask`), so no
bound on it is assumed. -/
def Env := String → Nat

/-! ## The extraction's reading -/

/-- The comparison the extraction decides: `<` on `UIntN` is unsigned, on
`IntN` signed (`decide (l < r)` at the operands' type). -/
def cmpX (signed : Bool) (op : CmpOp) {w : Nat} (l r : BitVec w) : Bool :=
  match op with
  | .eq => decide (l = r)
  | .ne => decide (l ≠ r)
  | .lt => if signed then l.slt r else l.ult r
  | .le => if signed then l.sle r else l.ule r
  | .gt => if signed then r.slt l else r.ult l
  | .ge => if signed then r.sle l else r.ule l

def arithX (op : ArithOp) {w : Nat} (x y : BitVec w) : BitVec w :=
  match op with
  | .add => x + y
  | .sub => x - y
  | .mul => x * y

/-- The bitwise operators; a shift by the count modulo the width, as
`UInt32.shiftLeft` and its siblings take it. -/
def bitX (op : BitOp) {w : Nat} (x y : BitVec w) : BitVec w :=
  match op with
  | .and => x &&& y
  | .or => x ||| y
  | .xor => x ^^^ y
  | .shl => x <<< (y.toNat % w)
  | .shr => x >>> (y.toNat % w)

/-- A conversion: `toUIntN`/`toIntN` widen by the source's signedness
(`Int8.toInt64` sign-extends, `UInt8.toUInt64` zero-extends) and narrow by
truncation. -/
def convX (s t : Ty) (v : BitVec s.width) : BitVec t.width :=
  if s.width < t.width then
    (if s.signed then v.signExtend t.width else v.setWidth t.width)
  else v.setWidth t.width

def evalX : {t : Ty} → Expr t → Env → BitVec t.width
  | t, .param _ name, ρ => BitVec.ofNat t.width (ρ name)
  | _, .lit _ v, _ => v
  | _, .arith op a b, ρ => arithX op (evalX a ρ) (evalX b ρ)
  | _, .bit op a b _, ρ => bitX op (evalX a ρ) (evalX b ρ)
  | t, .divPow2 a k _ _, ρ => evalX a ρ / BitVec.ofNat t.width (2 ^ k)
  | t, .modPow2 a k _ _, ρ => evalX a ρ % BitVec.ofNat t.width (2 ^ k)
  | _, .neg a, ρ => 0 - evalX a ρ
  | _, .not a, ρ => ~~~ evalX a ρ
  | t, .conv (s := s) _ a, ρ => convX s t (evalX a ρ)
  | _, .cmp (s := s) op l r, ρ => BitVec.ofBool (cmpX s.signed op (evalX l ρ) (evalX r ρ))
  | _, .ite c a b, ρ => if evalX c ρ = 1 then evalX a ρ else evalX b ρ

/-- The 1/0 image of `Bool` is a homomorphism for `&&`, `||`, `!`: reading
the extraction's `Bool` as `BitVec 1` loses nothing. -/
theorem ofBool_and (a b : Bool) : BitVec.ofBool (a && b) = BitVec.ofBool a &&& BitVec.ofBool b := by
  cases a <;> cases b <;> decide
theorem ofBool_or (a b : Bool) : BitVec.ofBool (a || b) = BitVec.ofBool a ||| BitVec.ofBool b := by
  cases a <;> cases b <;> decide
theorem ofBool_not (a : Bool) : BitVec.ofBool (!a) = ~~~ BitVec.ofBool a := by
  cases a <;> decide

/-! ## The verifier's term language -/

/-- The executor's binary operations (`term.op`). -/
inductive TOp
  | add | sub | and | or | xor | shl | shr | sar | mul
  deriving DecidableEq, Repr

/-- A term: `termParam`, `termConst`, `termBinary`, `termCmp`, `termIte`
with the width the Go node carries. -/
inductive Term
  | param (name : String) (w : Nat)
  | const (v : Nat) (w : Nat)
  | bin (op : TOp) (w : Nat) (l r : Term)
  | cmp (code : Cond) (w : Nat) (l r : Term)
  | ite (w : Nat) (c l r : Term)

def Term.width : Term → Nat
  | .param _ w => w
  | .const _ w => w
  | .bin _ w _ _ => w
  | .cmp _ w _ _ => w
  | .ite w _ _ _ => w

@[simp] theorem Term.width_param (n : String) (w : Nat) : (Term.param n w).width = w := rfl
@[simp] theorem Term.width_const (v w : Nat) : (Term.const v w).width = w := rfl
@[simp] theorem Term.width_bin (op : TOp) (w : Nat) (l r : Term) : (Term.bin op w l r).width = w := rfl
@[simp] theorem Term.width_cmp (c : Cond) (w : Nat) (l r : Term) : (Term.cmp c w l r).width = w := rfl
@[simp] theorem Term.width_ite (w : Nat) (c l r : Term) : (Term.ite w c l r).width = w := rfl

/-- `mask(width)`. -/
def mask (w : Nat) : Nat := 2 ^ w - 1

/-- The binary operation at width `w` on operands already masked to `w`
(`evalUncached`'s switch on `t.op`; `sar` sign-extends the operand from
the width before the arithmetic shift). -/
def Term.evalBin (op : TOp) (w : Nat) (a b : Nat) : Nat :=
  match op with
  | .add => (a + b) % 2 ^ w
  | .sub => (a + (2 ^ w - b)) % 2 ^ w
  | .and => (a &&& b) % 2 ^ w
  | .or => (a ||| b) % 2 ^ w
  | .xor => (a ^^^ b) % 2 ^ w
  | .shl => (a <<< (b % w)) % 2 ^ w
  | .shr => (a >>> (b % w)) % 2 ^ w
  | .sar => ((BitVec.ofNat w a).sshiftRight (b % w)).toNat % 2 ^ w
  | .mul => (a * b) % 2 ^ w

/-- `term.evalUncached`: a parameter or constant masked to its width; a
binary node's operands evaluate at their own widths and are masked to
this node's; a comparison is the condition code on the flags of `l - r` at
the operands' width (`conditionHolds` masks both to that width), 1 or 0;
an `ite` picks an arm and masks it. -/
def Term.eval : Term → Env → Nat
  | .param name w, ρ => ρ name % 2 ^ w
  | .const v w, _ => v % 2 ^ w
  | .bin op w l r, ρ => Term.evalBin op w (l.eval ρ % 2 ^ w) (r.eval ρ % 2 ^ w)
  | .cmp code _ l r, ρ =>
    if condHolds code (BitVec.ofNat l.width (l.eval ρ)) (BitVec.ofNat l.width (r.eval ρ)) then 1 else 0
  | .ite w c l r, ρ => if c.eval ρ ≠ 0 then l.eval ρ % 2 ^ w else r.eval ρ % 2 ^ w

/-- `truncate(t, width)`: a constant (its value already masked to its
width), a parameter or a comparison is re-widthed; anything else is masked
to the width. -/
def truncate (t : Term) (w : Nat) : Term :=
  if t.width = w then t else
  match t with
  | .const v w₀ => .const (v % 2 ^ w₀) w
  | .param n _ => .param n w
  | .cmp code _ l r => .cmp code w l r
  | _ => .bin .and w t (.const (mask w) w)

/-- `zeroExtend(t, width)`: the narrow computation's wrap is kept by masking
to its own width. -/
def zeroExtend (t : Term) (w : Nat) : Term :=
  if t.width = w then t else
  match t with
  | .const v w₀ => .const (v % 2 ^ w₀) w
  | .param n _ => .param n w
  | .cmp code _ l r => .cmp code w l r
  | _ => .bin .and w t (.const (mask t.width) w)

def adaptWidth (t : Term) (w : Nat) : Term :=
  if t.width < w then zeroExtend t w else truncate t w

/-- `extendTerm(t, from, width, signed)` (asm/isa_semantics.go): the low
`src` bits at the wider width, then for a signed source shifted up and
arithmetically back down. -/
def extendTerm (t : Term) (src w : Nat) (signed : Bool) : Term :=
  let low := Term.bin .and w (adaptWidth t w) (.const (mask src) w)
  if !signed then low else
  Term.bin .sar w (Term.bin .shl w low (.const (w - src) w)) (.const (w - src) w)

/-- `oakComparisons`: the condition code of an Oak comparison, by
signedness (unsigned first, signed second in the Go table). -/
def codeOf (signed : Bool) : CmpOp → Cond
  | .eq => .eq
  | .ne => .ne
  | .lt => if signed then .lt else .lo
  | .le => if signed then .le else .ls
  | .gt => if signed then .gt else .hi
  | .ge => if signed then .ge else .hs

/-- `oakOps`. -/
def arithTOp : ArithOp → TOp
  | .add => .add | .sub => .sub | .mul => .mul

def bitTOp : BitOp → TOp
  | .and => .and | .or => .or | .xor => .xor | .shl => .shl | .shr => .shr

/-- `oakLowering.lower` at the expression's own width, each case as the Go
spells it: a parameter is `truncate(paramTerm(name, w), width)`, the
identity at its own width; a literal `constTerm(value, width)`; an infix
`binaryTerm(op, left, right)`; `/` and `%` by `2^k` a shift by `k` and a
mask by `2^k - 1`; `-x` is `0 - x`; `^x` and `!b` are `xor` with the mask;
a conversion the operand at its own width through `extendTerm` or
`truncate`, then `truncate` to the context (the identity here); a
comparison in value position `zeroExtend(truncate(cmpTerm(code, l, r),
width), width)` at the Bool width 1; a Bool conditional `iteTerm`. -/
def lowerT : {t : Ty} → Expr t → Term
  | t, .param _ name => .param name t.width
  | t, .lit _ v => .const v.toNat t.width
  | t, .arith op a b => .bin (arithTOp op) t.width (lowerT a) (lowerT b)
  | t, .bit op a b _ => .bin (bitTOp op) t.width (lowerT a) (lowerT b)
  | t, .divPow2 a k _ _ => .bin .shr t.width (lowerT a) (.const k t.width)
  | t, .modPow2 a k _ _ => .bin .and t.width (lowerT a) (.const (2 ^ k - 1) t.width)
  | t, .neg a => .bin .sub t.width (.const 0 t.width) (lowerT a)
  | t, .not a => .bin .xor t.width (lowerT a) (.const (mask t.width) t.width)
  | t, .conv (s := s) _ a =>
    let operand := lowerT a
    let converted :=
      if s.width < t.width then extendTerm operand s.width t.width s.signed
      else truncate operand t.width
    truncate converted t.width
  | _, .cmp (s := s) op l r =>
    zeroExtend (truncate (.cmp (codeOf s.signed op) s.width (lowerT l) (lowerT r)) 1) 1
  | t, .ite c a b => .ite t.width (lowerT c) (lowerT a) (lowerT b)

/-! ## Widths -/

@[simp] theorem truncate_width (t : Term) (w : Nat) : (truncate t w).width = w := by
  unfold truncate
  split
  · assumption
  · split <;> rfl

@[simp] theorem zeroExtend_width (t : Term) (w : Nat) : (zeroExtend t w).width = w := by
  unfold zeroExtend
  split
  · assumption
  · split <;> rfl

@[simp] theorem adaptWidth_width (t : Term) (w : Nat) : (adaptWidth t w).width = w := by
  unfold adaptWidth; split <;> simp

@[simp] theorem extendTerm_width (t : Term) (src w : Nat) (signed : Bool) :
    (extendTerm t src w signed).width = w := by
  unfold extendTerm; split <;> rfl

@[simp] theorem lowerT_width {t : Ty} (e : Expr t) : (lowerT e).width = t.width := by
  cases e <;> first | rfl | (simp only [lowerT, truncate_width, zeroExtend_width]; try rfl)

theorem truncate_self (t : Term) (w : Nat) (h : t.width = w) : truncate t w = t := by
  simp [truncate, h]

theorem zeroExtend_self (t : Term) (w : Nat) (h : t.width = w) : zeroExtend t w = t := by
  simp [zeroExtend, h]

/-! ## Evaluation facts about the width helpers -/

/-- The executor never lets a value exceed its node's width, except a
comparison at width 0 — a width the Go never builds (`contractBits`
gives 1 for `Bool`). -/
def Term.topPositive : Term → Prop
  | .cmp _ w _ _ => 0 < w
  | _ => True

theorem Term.evalBin_lt (op : TOp) (w a b : Nat) : Term.evalBin op w a b < 2 ^ w := by
  cases op <;> simp only [Term.evalBin] <;> exact Nat.mod_lt _ (Nat.two_pow_pos w)

theorem Term.eval_lt (t : Term) (ρ : Env) (hp : t.topPositive) : t.eval ρ < 2 ^ t.width := by
  cases t with
  | param n w => exact Nat.mod_lt _ (Nat.two_pow_pos w)
  | const v w => exact Nat.mod_lt _ (Nat.two_pow_pos w)
  | bin op w l r => exact Term.evalBin_lt _ _ _ _
  | cmp code w l r =>
    simp only [Term.topPositive] at hp
    simp only [Term.eval, Term.width_param, Term.width_const, Term.width_bin, Term.width_cmp, Term.width_ite]
    by_cases hc : condHolds code (BitVec.ofNat l.width (l.eval ρ)) (BitVec.ofNat l.width (r.eval ρ)) = true
    · rw [if_pos hc]; exact Nat.one_lt_two_pow (Nat.pos_iff_ne_zero.mp hp)
    · rw [if_neg hc]; exact Nat.two_pow_pos w
  | ite w c l r =>
    simp only [Term.eval, Term.width_param, Term.width_const, Term.width_bin, Term.width_cmp, Term.width_ite]
    split <;> exact Nat.mod_lt _ (Nat.two_pow_pos w)

theorem mask_lt (w : Nat) : mask w < 2 ^ w := by
  unfold mask; have := Nat.two_pow_pos w; omega

theorem mask_mod (w : Nat) : mask w % 2 ^ w = mask w := Nat.mod_eq_of_lt (mask_lt w)

/-- A masked operand: `(x % 2^w) &&& mask w₀`, `w₀ ≤ w`, is `x % 2^w₀`. -/
theorem and_mask_of_le (x w₀ w : Nat) (h : w₀ ≤ w) : (x % 2 ^ w) &&& mask w₀ = x % 2 ^ w₀ := by
  unfold mask
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 h)]

/-- `truncate` to a width at most the term's is the value modulo `2^w`. -/
theorem truncate_eval (t : Term) (w : Nat) (ρ : Env) (hw : 0 < w) (hle : w ≤ t.width) (hp : t.topPositive) :
    (truncate t w).eval ρ = t.eval ρ % 2 ^ w := by
  by_cases heq : t.width = w
  · rw [truncate_self t w heq, Nat.mod_eq_of_lt (heq ▸ Term.eval_lt t ρ hp)]
  have hdvd : 2 ^ w ∣ 2 ^ t.width := Nat.pow_dvd_pow 2 hle
  cases t with
  | const v w₀ =>
    simp only [truncate, Term.width_param, Term.width_const, Term.width_bin, Term.width_cmp, Term.width_ite] at heq ⊢
    simp only [heq, ite_false, Term.eval]
    try exact Nat.mod_mod_of_dvd _ hdvd
  | param n w₀ =>
    simp only [truncate, Term.width_param, Term.width_const, Term.width_bin, Term.width_cmp, Term.width_ite] at heq ⊢
    simp only [heq, ite_false, Term.eval]
    try exact (Nat.mod_mod_of_dvd _ hdvd).symm
  | cmp code w₀ l r =>
    simp only [truncate, Term.width_param, Term.width_const, Term.width_bin, Term.width_cmp, Term.width_ite] at heq ⊢
    simp only [heq, ite_false, Term.eval]
    split
    · exact (Nat.mod_eq_of_lt (Nat.one_lt_two_pow (Nat.pos_iff_ne_zero.mp hw))).symm
    · simp
  | bin op w₀ l r =>
    simp only [truncate, Term.width_param, Term.width_const, Term.width_bin, Term.width_cmp, Term.width_ite] at heq ⊢
    simp only [heq, ite_false, Term.eval, Term.evalBin, mask_mod, Nat.mod_mod]
    rw [and_mask_of_le _ _ _ (Nat.le_refl w), Nat.mod_mod]
  | ite w₀ c l r =>
    simp only [truncate, Term.width_param, Term.width_const, Term.width_bin, Term.width_cmp, Term.width_ite] at heq ⊢
    simp only [heq, ite_false, Term.eval, Term.evalBin, mask_mod, Nat.mod_mod]
    rw [and_mask_of_le _ _ _ (Nat.le_refl w), Nat.mod_mod]

/-- The comparison a `truncate` re-widths is the same 1/0. -/
theorem truncate_cmp_eval (code : Cond) (w₀ w : Nat) (l r : Term) (ρ : Env) :
    (truncate (.cmp code w₀ l r) w).eval ρ = (Term.cmp code w₀ l r).eval ρ := by
  unfold truncate
  split
  · rfl
  · rfl

/-- `zeroExtend` under the mask of the term's own width (the shape
`extendTerm` builds) is the value modulo `2^w₀`, whatever the shape. -/
theorem zeroExtend_masked_eval (t : Term) (w₀ w : Nat) (ρ : Env) (h₀ : t.width = w₀) (hle : w₀ ≤ w) :
    (Term.bin .and w (zeroExtend t w) (.const (mask w₀) w)).eval ρ = t.eval ρ % 2 ^ w₀ := by
  have hm : mask w₀ % 2 ^ w % 2 ^ w = mask w₀ := by
    rw [Nat.mod_mod, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (mask_lt w₀) (Nat.pow_le_pow_right (by decide) hle))]
  have hlt : ∀ x, x % 2 ^ w₀ % 2 ^ w = x % 2 ^ w₀ := fun x =>
    Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos w₀)) (Nat.pow_le_pow_right (by decide) hle))
  have hself : ∀ x, (x % 2 ^ w₀ &&& mask w₀) % 2 ^ w = x % 2 ^ w₀ := fun x => by
    rw [and_mask_of_le _ _ _ (Nat.le_refl _), hlt]
  by_cases heq : t.width = w
  · rw [zeroExtend_self t w heq]
    simp only [Term.eval, Term.evalBin, hm, and_mask_of_le _ _ _ hle, hlt]
  subst h₀
  cases t with
  | const v w₀ =>
    simp only [Term.width_param, Term.width_const, Term.width_bin, Term.width_cmp, Term.width_ite] at heq hle hlt hm hself
    simp only [zeroExtend, Term.width_param, Term.width_const, Term.width_bin, Term.width_cmp, Term.width_ite, heq, ite_false, Term.eval, Term.evalBin, hm, hlt, and_mask_of_le _ _ _ hle, Nat.mod_mod]
    try exact hself _
  | param n w₀ =>
    simp only [Term.width_param, Term.width_const, Term.width_bin, Term.width_cmp, Term.width_ite] at heq hle hlt hm hself
    simp only [zeroExtend, Term.width_param, Term.width_const, Term.width_bin, Term.width_cmp, Term.width_ite, heq, ite_false, Term.eval, Term.evalBin, hm, hlt, and_mask_of_le _ _ _ hle, Nat.mod_mod]
    try exact hself _
  | cmp code w₀ l r =>
    simp only [Term.width_param, Term.width_const, Term.width_bin, Term.width_cmp, Term.width_ite] at heq hle hlt hm hself
    simp only [zeroExtend, Term.width_param, Term.width_const, Term.width_bin, Term.width_cmp, Term.width_ite, heq, ite_false, Term.eval, Term.evalBin, hm]
    split <;> simp [hlt, and_mask_of_le _ _ _ hle, hself]
  | bin op w₀ l r =>
    simp only [Term.width_param, Term.width_const, Term.width_bin, Term.width_cmp, Term.width_ite] at heq hle hlt hm hself
    simp only [zeroExtend, Term.width_param, Term.width_const, Term.width_bin, Term.width_cmp, Term.width_ite, heq, ite_false, Term.eval, Term.evalBin, hm, hlt, and_mask_of_le _ _ _ hle, Nat.mod_mod]
    try exact hself _
  | ite w₀ c l r =>
    simp only [Term.width_param, Term.width_const, Term.width_bin, Term.width_cmp, Term.width_ite] at heq hle hlt hm hself
    simp only [zeroExtend, Term.width_param, Term.width_const, Term.width_bin, Term.width_cmp, Term.width_ite, heq, ite_false, Term.eval, Term.evalBin, hm, hlt, and_mask_of_le _ _ _ hle, Nat.mod_mod]
    try exact hself _

/-- A value shifted up to the top of a wider word and arithmetically back
down is its sign extension. -/
theorem sshiftRight_shiftLeft_setWidth {s : Nat} (x : BitVec s) (w : Nat) (hs : 0 < s) (h : s ≤ w) :
    ((x.setWidth w) <<< (w - s)).sshiftRight (w - s) = x.signExtend w := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_sshiftRight, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_signExtend, BitVec.msb_eq_getLsbD_last]
  have h1 : w - s + i - (w - s) = i := by omega
  have h2 : w - 1 - (w - s) = s - 1 := by omega
  rw [h1, h2]
  have hw : ¬ (w ≤ i) := by omega
  have hw1 : w - 1 < w := by omega
  have hw2 : ¬ (w - 1 < w - s) := by omega
  have hw3 : s - 1 < w := by omega
  by_cases hs' : i < s
  · have h3 : w - s + i < w := by omega
    have h4 : ¬ (w - s + i < w - s) := by omega
    simp [hw, hi, hs', h3, h4]
  · have h3 : ¬ (w - s + i < w) := by omega
    simp [hw, hi, hs', h3, hw1, hw2, hw3]

/-! ## Condition codes against the extraction's comparisons -/

theorem ne_holds_iff {w : Nat} (l r : BitVec w) : condHolds .ne l r = true ↔ l ≠ r := by
  have he := eq_holds_iff l r
  simp only [condHolds, Cond.holds, flagsOf, decide_eq_true_eq] at he
  simp only [condHolds, Cond.holds, flagsOf, Bool.not_eq_true', decide_eq_false_iff_not]
  exact not_congr he

/-- `ls` is unsigned ≤ — the Oak `<=` on unsigned operands. -/
theorem ls_holds_iff {w : Nat} (l r : BitVec w) : condHolds .ls l r = true ↔ l.toNat ≤ r.toNat := by
  have he := eq_holds_iff l r
  simp only [condHolds, Cond.holds, flagsOf, decide_eq_true_eq] at he
  simp only [condHolds, Cond.holds, flagsOf, Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
    decide_eq_true_eq]
  constructor
  · rintro (h | h)
    · omega
    · rw [he.mp h]; exact Nat.le_refl _
  · intro h
    rcases Nat.lt_or_eq_of_le h with hlt | heq
    · left; omega
    · right; exact he.mpr (BitVec.eq_of_toNat_eq heq)

theorem lt_holds_eq_slt_w8 (l r : BitVec 8) : condHolds .lt l r = l.slt r := by
  simp only [condHolds, Cond.holds, flagsOf]; bv_decide
theorem ge_holds_eq_not_slt_w8 (l r : BitVec 8) : condHolds .ge l r = !(l.slt r) := by
  simp only [condHolds, Cond.holds, flagsOf]; bv_decide
theorem gt_holds_eq_slt_w8 (l r : BitVec 8) : condHolds .gt l r = r.slt l := by
  simp only [condHolds, Cond.holds, flagsOf]; bv_decide
theorem le_holds_eq_not_slt_w8 (l r : BitVec 8) : condHolds .le l r = !(r.slt l) := by
  simp only [condHolds, Cond.holds, flagsOf]; bv_decide
theorem lt_holds_eq_slt_w16 (l r : BitVec 16) : condHolds .lt l r = l.slt r := by
  simp only [condHolds, Cond.holds, flagsOf]; bv_decide
theorem ge_holds_eq_not_slt_w16 (l r : BitVec 16) : condHolds .ge l r = !(l.slt r) := by
  simp only [condHolds, Cond.holds, flagsOf]; bv_decide
theorem gt_holds_eq_slt_w16 (l r : BitVec 16) : condHolds .gt l r = r.slt l := by
  simp only [condHolds, Cond.holds, flagsOf]; bv_decide
theorem le_holds_eq_not_slt_w16 (l r : BitVec 16) : condHolds .le l r = !(r.slt l) := by
  simp only [condHolds, Cond.holds, flagsOf]; bv_decide

/-- The unsigned codes decide the extraction's unsigned comparisons. -/
theorem codeOf_holds_unsigned (op : CmpOp) {w : Nat} (l r : BitVec w) :
    condHolds (codeOf false op) l r = cmpX false op l r := by
  cases op <;> simp only [codeOf, cmpX, Bool.false_eq_true, if_false] <;> apply Bool.eq_iff_iff.mpr
  · exact (eq_holds_iff l r).trans (by simp)
  · exact (ne_holds_iff l r).trans (by simp)
  · exact lo_holds_iff l r
  · exact (ls_holds_iff l r).trans BitVec.ule_iff_toNat_le.symm
  · exact hi_holds_iff l r
  · exact (hs_holds_iff l r).trans BitVec.ule_iff_toNat_le.symm

/-- The signed codes decide the extraction's signed comparisons at the four
integer widths. -/
theorem codeOf_holds_signed (op : CmpOp) {w : Nat} (hw : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64) (l r : BitVec w) :
    condHolds (codeOf true op) l r = cmpX true op l r := by
  cases op
  · exact Bool.eq_iff_iff.mpr ((eq_holds_iff l r).trans (by simp [cmpX]))
  · exact Bool.eq_iff_iff.mpr ((ne_holds_iff l r).trans (by simp [cmpX]))
  all_goals simp only [codeOf, cmpX, if_true, BitVec.sle_eq_not_slt]
  all_goals rcases hw with rfl | rfl | rfl | rfl
  all_goals first
    | exact lt_holds_eq_slt_w8 l r | exact lt_holds_eq_slt_w16 l r
    | exact lt_holds_eq_slt_w32 l r | exact lt_holds_eq_slt_w64 l r
    | exact le_holds_eq_not_slt_w8 l r | exact le_holds_eq_not_slt_w16 l r
    | exact le_holds_eq_not_slt_w32 l r | exact le_holds_eq_not_slt_w64 l r
    | exact gt_holds_eq_slt_w8 l r | exact gt_holds_eq_slt_w16 l r
    | exact gt_holds_eq_slt_w32 l r | exact gt_holds_eq_slt_w64 l r
    | exact ge_holds_eq_not_slt_w8 l r | exact ge_holds_eq_not_slt_w16 l r
    | exact ge_holds_eq_not_slt_w32 l r | exact ge_holds_eq_not_slt_w64 l r

theorem codeOf_holds (s : Ty) (op : CmpOp) (l r : BitVec s.width) :
    condHolds (codeOf s.signed op) l r = cmpX s.signed op l r := by
  cases s
  all_goals first
    | exact codeOf_holds_unsigned op l r
    | exact codeOf_holds_signed op (by simp [Ty.width]) l r

/-! ## The theorem -/

theorem truncate_topPositive (t : Term) (w : Nat) (hw : 0 < w) (hp : t.topPositive) : (truncate t w).topPositive := by
  unfold truncate
  split
  · exact hp
  · split <;> first | trivial | exact hw

theorem zeroExtend_topPositive (t : Term) (w : Nat) (hw : 0 < w) (hp : t.topPositive) : (zeroExtend t w).topPositive := by
  unfold zeroExtend
  split
  · exact hp
  · split <;> first | trivial | exact hw

theorem extendTerm_topPositive (t : Term) (src w : Nat) (signed : Bool) : (extendTerm t src w signed).topPositive := by
  unfold extendTerm; split <;> trivial

theorem lowerT_topPositive {t : Ty} (e : Expr t) : (lowerT e).topPositive := by
  induction e with
  | cmp op l r _ _ =>
    exact zeroExtend_topPositive _ _ (by decide) (truncate_topPositive _ _ (by decide) (Ty.width_pos _))
  | conv t a ih =>
    simp only [lowerT]
    apply truncate_topPositive _ _ t.width_pos
    split
    · exact extendTerm_topPositive _ _ _ _
    · exact truncate_topPositive _ _ t.width_pos ih
  | _ => simp [lowerT, Term.topPositive]

/-- A one-bit value is 1 exactly when it is not 0. -/
theorem BitVec1_ne_zero_iff (c : BitVec 1) : c.toNat ≠ 0 ↔ c = 1 := by
  revert c; decide

theorem const_eval_of_lt (v w : Nat) (ρ : Env) (h : v < 2 ^ w) : (Term.const v w).eval ρ % 2 ^ w = v := by
  simp only [Term.eval, Nat.mod_mod]; exact Nat.mod_eq_of_lt h

/-- The verifier's lowering and the extraction's reading agree on every
expression of the shared subset: the seam of `126-verification-chain.md`
§4, closed. -/
theorem lowerT_eval {t : Ty} (e : Expr t) (ρ : Env) : (lowerT e).eval ρ = (evalX e ρ).toNat := by
  induction e with
  | param t name =>
    simp [lowerT, evalX, Term.eval]
  | lit t v =>
    simp [lowerT, evalX, Term.eval]
  | @arith op t a b iha ihb =>
    cases op <;> simp [lowerT, evalX, arithX, arithTOp, Term.eval, Term.evalBin, iha, ihb, Nat.add_comm]
  | @bit op t a b h iha ihb =>
    have hw := (evalX a ρ).isLt
    cases op <;> simp only [lowerT, evalX, bitX, bitTOp, Term.eval, Term.evalBin, iha, ihb, BitVec.toNat_mod_cancel]
    · rw [BitVec.toNat_and]; exact Nat.mod_eq_of_lt (Nat.and_lt_two_pow _ (evalX b ρ).isLt)
    · rw [BitVec.toNat_or]; exact Nat.mod_eq_of_lt (Nat.or_lt_two_pow hw (evalX b ρ).isLt)
    · rw [BitVec.toNat_xor]; exact Nat.mod_eq_of_lt (Nat.xor_lt_two_pow hw (evalX b ρ).isLt)
    · rw [BitVec.toNat_shiftLeft]
    · rw [BitVec.toNat_ushiftRight]
      exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _) hw)
  | @divPow2 t a k hk hu iha =>
    have hw := (evalX a ρ).isLt
    have hk2 : 2 ^ k < 2 ^ t.width := Nat.pow_lt_pow_right (by decide) hk
    have hkw : k < 2 ^ t.width := Nat.lt_of_lt_of_le hk (Nat.le_of_lt Nat.lt_two_pow_self)
    simp only [lowerT, evalX, Term.eval, Term.evalBin, iha, BitVec.toNat_mod_cancel, BitVec.toNat_udiv,
      BitVec.toNat_ofNat, Nat.mod_mod, Nat.mod_eq_of_lt hkw, Nat.mod_eq_of_lt hk, Nat.mod_eq_of_lt hk2,
      Nat.shiftRight_eq_div_pow]
    exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hw)
  | @modPow2 t a k hk hu iha =>
    have hk2 : 2 ^ k < 2 ^ t.width := Nat.pow_lt_pow_right (by decide) hk
    have hm : 2 ^ k - 1 < 2 ^ t.width := by omega
    simp only [lowerT, evalX, Term.eval, Term.evalBin, iha, BitVec.toNat_mod_cancel, BitVec.toNat_umod,
      BitVec.toNat_ofNat, Nat.mod_mod, Nat.mod_eq_of_lt hm, Nat.mod_eq_of_lt hk2,
      Nat.and_two_pow_sub_one_eq_mod]
    exact Nat.mod_eq_of_lt (Nat.lt_trans (Nat.mod_lt _ (Nat.two_pow_pos k)) hk2)
  | @neg t a iha =>
    simp [lowerT, evalX, Term.eval, Term.evalBin, iha]
  | @not t a iha =>
    have hx : (evalX a ρ).toNat ^^^ mask t.width = (~~~ evalX a ρ).toNat := by
      rw [← BitVec.xor_allOnes, BitVec.toNat_xor, BitVec.toNat_allOnes]; rfl
    simp only [lowerT, evalX, Term.eval, Term.evalBin, iha, BitVec.toNat_mod_cancel, mask_mod, hx]
  | @conv s t a iha =>
    have hs := s.width_pos
    simp only [lowerT, evalX, convX]
    rw [truncate_self _ _ (by split <;> simp)]
    by_cases hlt : s.width < t.width
    · simp only [hlt, if_true]
      unfold extendTerm
      simp only [adaptWidth, lowerT_width, hlt, if_true]
      have hlow := zeroExtend_masked_eval (lowerT a) s.width t.width ρ (lowerT_width a) (Nat.le_of_lt hlt)
      rw [iha, BitVec.toNat_mod_cancel] at hlow
      have hxw : (evalX a ρ).toNat < 2 ^ t.width :=
        Nat.lt_of_lt_of_le (evalX a ρ).isLt (Nat.pow_le_pow_right (by decide) (Nat.le_of_lt hlt))
      by_cases hsig : s.signed = true
      · simp only [hsig, Bool.not_true, Bool.false_eq_true, if_false, if_true]
        have hsh : (t.width - s.width) % 2 ^ t.width % t.width = t.width - s.width := by
          have : t.width - s.width < 2 ^ t.width := Nat.lt_of_le_of_lt (Nat.sub_le _ _) Nat.lt_two_pow_self
          rw [Nat.mod_eq_of_lt this, Nat.mod_eq_of_lt (by omega)]
        have hsh' : (t.width - s.width) % 2 ^ t.width % 2 ^ t.width % t.width = t.width - s.width := by
          rw [Nat.mod_mod, hsh]
        rw [Term.eval.eq_3, Term.eval.eq_3, hlow]
        simp only [Term.eval, Term.evalBin, hsh, hsh', Nat.mod_mod]
        rw [← BitVec.toNat_setWidth t.width (evalX a ρ), ← BitVec.toNat_shiftLeft, BitVec.ofNat_toNat,
          BitVec.setWidth_eq, sshiftRight_shiftLeft_setWidth _ _ hs (Nat.le_of_lt hlt), BitVec.toNat_mod_cancel]
      · have hsig' : s.signed = false := by simpa using hsig
        simp only [hsig', Bool.not_false, Bool.false_eq_true, if_false, if_true, BitVec.toNat_setWidth, hlow,
          Nat.mod_eq_of_lt hxw]
    · simp only [hlt, if_false]
      rw [truncate_eval _ _ _ t.width_pos (by rw [lowerT_width]; omega) (lowerT_topPositive a), iha,
        BitVec.toNat_setWidth]
  | @cmp s op l r ihl ihr =>
    simp only [lowerT]
    rw [zeroExtend_self _ _ (truncate_width _ _), truncate_cmp_eval]
    simp only [Term.eval, ihl, ihr]
    rw [lowerT_width l]
    simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq, codeOf_holds, evalX]
    cases cmpX s.signed op (evalX l ρ) (evalX r ρ) <;> simp
  | @ite t c a b ihc iha ihb =>
    simp only [lowerT, evalX, Term.eval, ihc, iha, ihb, BitVec.toNat_mod_cancel]
    have key : ((evalX c ρ).toNat ≠ 0) ↔ (evalX c ρ = 1) := BitVec1_ne_zero_iff (evalX c ρ)
    by_cases h : evalX c ρ = 1
    · rw [if_pos (key.mpr h), if_pos h]
    · rw [if_neg (fun hne => h (key.mp hne)), if_neg h]

end Oak.LoweringRefinement

namespace Oak.LoweringRefinement

open Oak.AssemblerSemantics

/-! ## Renders pinned against the Go lowering

`term.String()` prints a parameter as its name, a constant as its value,
and every other node as `(left op right)` / `(cond ? left : right)`, with
the condition code as the comparison's operator. `asm/lowering_refinement_test.go`
lowers each Oak expression below through `oakLowering.lower` and compares
the print with the string stated here, so the Go lowering is pinned to
`lowerT` case by case: a change to either side has to visit the other. -/

def TOp.render : TOp → String
  | .add => "add" | .sub => "sub" | .and => "and" | .or => "or" | .xor => "xor"
  | .shl => "shl" | .shr => "shr" | .sar => "sar" | .mul => "mul"

def condRender : Cond → String
  | .eq => "eq" | .ne => "ne" | .hs => "hs" | .lo => "lo" | .hi => "hi" | .ls => "ls"
  | .ge => "ge" | .lt => "lt" | .gt => "gt" | .le => "le" | .mi => "mi" | .pl => "pl"
  | .vs => "vs" | .vc => "vc"

def Term.render : Term → String
  | .param name _ => name
  | .const v w => toString (v % 2 ^ w)
  | .bin op _ l r => "(" ++ l.render ++ " " ++ op.render ++ " " ++ r.render ++ ")"
  | .cmp code _ l r => "(" ++ l.render ++ " " ++ condRender code ++ " " ++ r.render ++ ")"
  | .ite _ c l r => "(" ++ c.render ++ " ? " ++ l.render ++ " : " ++ r.render ++ ")"

/-- `(a, b: u32) -> u32 = a + b` -/
example : (lowerT (.arith .add (.param .u32 "a") (.param .u32 "b"))).render = "(a add b)" := by decide
/-- `(a, b: u32) -> u32 = a - b` -/
example : (lowerT (.arith .sub (.param .u32 "a") (.param .u32 "b"))).render = "(a sub b)" := by decide
/-- `(a: u32) -> u32 = a * 3` -/
example : (lowerT (.arith .mul (.param .u32 "a") (.lit .u32 3))).render = "(a mul 3)" := by decide
/-- `(a: u32) -> u32 = a / 8` -/
example : (lowerT (.divPow2 (.param .u32 "a") 3 (by decide) rfl)).render = "(a shr 3)" := by decide
/-- `(a: u32) -> u32 = a % 8` -/
example : (lowerT (.modPow2 (.param .u32 "a") 3 (by decide) rfl)).render = "(a and 7)" := by decide
/-- `(a: u32) -> u32 = -a` -/
example : (lowerT (.neg (.param .u32 "a"))).render = "(0 sub a)" := by decide
/-- `(a: u32) -> u32 = ^a` -/
example : (lowerT (.not (.param .u32 "a"))).render = "(a xor 4294967295)" := by decide
/-- `(a, b: u32) -> u32 = (a << 3) | (b >> 5)` -/
example : (lowerT (.bit .or (.bit .shl (.param .u32 "a") (.lit .u32 3) rfl) (.bit .shr (.param .u32 "b") (.lit .u32 5) rfl) rfl)).render
    = "((a shl 3) or (b shr 5))" := by decide
/-- `(a, b: u32) -> u32 = (a & b) ^ b` -/
example : (lowerT (.bit .xor (.bit .and (.param .u32 "a") (.param .u32 "b") rfl) (.param .u32 "b") rfl)).render
    = "((a and b) xor b)" := by decide
/-- `(a: u8) -> u32 = u32(a)` -/
example : (lowerT (.conv .u32 (.param .u8 "a"))).render = "(a and 255)" := by decide
/-- `(a: i8) -> i32 = i32(a)` -/
example : (lowerT (.conv .i32 (.param .i8 "a"))).render = "(((a and 255) shl 24) sar 24)" := by decide
/-- `(a: i32) -> i64 = i64(a) + 1` -/
example : (lowerT (.arith .add (.conv .i64 (.param .i32 "a")) (.lit .i64 1))).render
    = "((((a and 4294967295) shl 32) sar 32) add 1)" := by decide
/-- `(a: u32) -> u8 = u8_trunc_u32(a)` — a re-widthed parameter prints as itself. -/
example : (lowerT (.conv .u8 (.param .u32 "a"))).render = "a" := by decide
/-- `(a, b: u16) -> u32 = u32(a) * u32(b)` -/
example : (lowerT (.arith .mul (.conv .u32 (.param .u16 "a")) (.conv .u32 (.param .u16 "b")))).render
    = "((a and 65535) mul (b and 65535))" := by decide
/-- `(a, b: u32) -> Bool = a < b` and the other five unsigned comparisons -/
example : (lowerT (.cmp .lt (.param .u32 "a") (.param .u32 "b"))).render = "(a lo b)" := by decide
example : (lowerT (.cmp .le (.param .u32 "a") (.param .u32 "b"))).render = "(a ls b)" := by decide
example : (lowerT (.cmp .gt (.param .u32 "a") (.param .u32 "b"))).render = "(a hi b)" := by decide
example : (lowerT (.cmp .ge (.param .u32 "a") (.param .u32 "b"))).render = "(a hs b)" := by decide
example : (lowerT (.cmp .eq (.param .u32 "a") (.param .u32 "b"))).render = "(a eq b)" := by decide
example : (lowerT (.cmp .ne (.param .u32 "a") (.param .u32 "b"))).render = "(a ne b)" := by decide
/-- `(a, b: i32) -> Bool = a < b` and the other three signed orders -/
example : (lowerT (.cmp .lt (.param .i32 "a") (.param .i32 "b"))).render = "(a lt b)" := by decide
example : (lowerT (.cmp .le (.param .i32 "a") (.param .i32 "b"))).render = "(a le b)" := by decide
example : (lowerT (.cmp .gt (.param .i32 "a") (.param .i32 "b"))).render = "(a gt b)" := by decide
example : (lowerT (.cmp .ge (.param .i32 "a") (.param .i32 "b"))).render = "(a ge b)" := by decide
/-- `(a, b, c: u32) -> Bool = a < b && b < c` -/
example : (lowerT (.bit .and (.cmp .lt (.param .u32 "a") (.param .u32 "b")) (.cmp .lt (.param .u32 "b") (.param .u32 "c")) rfl)).render
    = "((a lo b) and (b lo c))" := by decide
/-- `(a, b: u32) -> Bool = a < b || a == b` -/
example : (lowerT (.bit .or (.cmp .lt (.param .u32 "a") (.param .u32 "b")) (.cmp .eq (.param .u32 "a") (.param .u32 "b")) rfl)).render
    = "((a lo b) or (a eq b))" := by decide
/-- `(a, b: u32) -> Bool = !(a < b)` -/
example : (lowerT (.not (.cmp .lt (.param .u32 "a") (.param .u32 "b")))).render = "((a lo b) xor 1)" := by decide
/-- `(a, b: u32) -> u32 = a < b ? a | b` -/
example : (lowerT (.ite (.cmp .lt (.param .u32 "a") (.param .u32 "b")) (.param .u32 "a") (.param .u32 "b"))).render
    = "((a lo b) ? a : b)" := by decide
/-- `(a, b: i64) -> i64 = a < b ? b - a | a - b` -/
example : (lowerT (.ite (.cmp .lt (.param .i64 "a") (.param .i64 "b")) (.arith .sub (.param .i64 "b") (.param .i64 "a")) (.arith .sub (.param .i64 "a") (.param .i64 "b")))).render
    = "((a lt b) ? (b sub a) : (a sub b))" := by decide

end Oak.LoweringRefinement
