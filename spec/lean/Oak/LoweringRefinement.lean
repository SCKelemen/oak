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

* `Expr P Γ t` is an Oak scalar expression of type `t` over the function's
  parameters `P` and the locals in scope `Γ` — variables, checked
  literals, the wrapping arithmetic, the unsigned bitwise operators and
  shifts, unsigned division and remainder by a constant power of two,
  negation and complement, the conversions, comparisons, `&&`/`||`/`!`,
  Bool conditionals, block-scoped locals and rebindings (`x: T = e`,
  `x = e`, then the rest of the block), and calls to program functions,
  which both readers inline. `Bool` is the width-1 type both readers use.
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
* `lowerT_eval`: `(lowerT σ e).eval ρ = (evalX e ρ λ).toNat` for every
  expression, every parameter assignment `ρ`, and every scope — a term
  environment `σ` (the verifier's `locals`: each local's lowered term)
  and a value environment `λ` (the extraction's `let`-bound values) that
  agree (`Agree`). A local is lowered once and substituted (`declareLocal`,
  `assignLocal`, an identifier through `adaptWidth(local.value, width)`);
  a call binds the callee's parameters to the lowered arguments as a fresh
  scope and lowers the body (`enterCall`, `inlineCall`). Parameters and
  locals are read from separate environments because the verifier's terms
  name parameters and only parameters: a local that shadows a parameter
  changes what the source means by the name, never what a term means.

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

/-- The function's parameters: name to type (`contractBits` per
parameter). -/
def Params := String → Option Ty

/-- The locals in scope: name to type. Empty at a function's entry; a
callee's scope is its parameters, bound as locals (`enterCall`). -/
def Locals := String → Option Ty

def Locals.set (Γ : Locals) (x : String) (t : Ty) : Locals :=
  fun y => if y = x then some t else Γ y

/-- Name resolution: a local first, then a parameter (`lower`'s identifier
case: `lo.locals`, then `lo.params`). -/
def resolve (P : Params) (Γ : Locals) (x : String) : Option Ty :=
  match Γ x with
  | some t => some t
  | none => P x

/-- The callee's scope: its parameters bound in order (a later duplicate
wins, as `bound[param] = …` does). -/
def bindTypes (Γ : Locals) : List (String × Ty) → Locals
  | [] => Γ
  | (x, s) :: ps => bindTypes (Γ.set x s) ps

mutual
/-- The shared subset. A literal carries its checked value at the type's
width (`Oak.LiteralFitRefinement`); `divPow2`/`modPow2` are `/` and `%` by
the unsigned constant `2^k`, the only division the verifier admits
(`k < width` because the constant is checked at the type); `not` is `^x`
on an integer and `!b` on `Bool`; `conv` is a `u8(x)`…`i64(x)` widening or
a `{t}_trunc_{s}`/`{t}_bits_{s}` narrowing; `ite` is `if c then a else b`
(a Bool `match`); `letIn x v b` is the block `x: s = v` (or the rebinding
`x = v`) followed by `b`; `call params ret body args` is a call to a
program function with those parameters and body; `condSet c armT armF rest`
is the statement-level Bool conditional `c ? { armT } | { armF }` whose
arms assign existing locals, followed by `rest`. -/
inductive Expr (P : Params) : Locals → Ty → Type
  | var {Γ : Locals} (t : Ty) (x : String) (h : resolve P Γ x = some t) : Expr P Γ t
  | lit {Γ : Locals} (t : Ty) (v : BitVec t.width) : Expr P Γ t
  | arith {Γ : Locals} (op : ArithOp) {t : Ty} (a b : Expr P Γ t) : Expr P Γ t
  | bit {Γ : Locals} (op : BitOp) {t : Ty} (a b : Expr P Γ t) (h : t.signed = false) : Expr P Γ t
  | divPow2 {Γ : Locals} {t : Ty} (a : Expr P Γ t) (k : Nat) (hk : k < t.width) (hu : t.signed = false) : Expr P Γ t
  | modPow2 {Γ : Locals} {t : Ty} (a : Expr P Γ t) (k : Nat) (hk : k < t.width) (hu : t.signed = false) : Expr P Γ t
  | neg {Γ : Locals} {t : Ty} (a : Expr P Γ t) : Expr P Γ t
  | not {Γ : Locals} {t : Ty} (a : Expr P Γ t) : Expr P Γ t
  | conv {Γ : Locals} {s : Ty} (t : Ty) (a : Expr P Γ s) : Expr P Γ t
  | cmp {Γ : Locals} {s : Ty} (op : CmpOp) (l r : Expr P Γ s) : Expr P Γ .bool
  | ite {Γ : Locals} {t : Ty} (c : Expr P Γ .bool) (a b : Expr P Γ t) : Expr P Γ t
  | letIn {Γ : Locals} {s t : Ty} (x : String) (v : Expr P Γ s) (b : Expr P (Γ.set x s) t) : Expr P Γ t
  | call {Γ : Locals} (params : List (String × Ty)) (ret : Ty)
      (body : Expr P (bindTypes (fun _ => none) params) ret) (args : Args P Γ params) : Expr P Γ ret
  | condSet {Γ : Locals} {t : Ty} (c : Expr P Γ .bool) (armT armF : Assigns P Γ) (rest : Expr P Γ t) : Expr P Γ t
/-- A conditional arm in statement position: assignments `x = e` to locals
already in scope, in order (a declaration inside an arm is scoped to the
arm and is not in the subset). -/
inductive Assigns (P : Params) : Locals → Type
  | nil {Γ : Locals} : Assigns P Γ
  | cons {Γ : Locals} (x : String) {s : Ty} (h : Γ x = some s) (e : Expr P Γ s) (rest : Assigns P Γ) : Assigns P Γ
/-- A call's arguments, one per callee parameter, in the caller's scope. -/
inductive Args (P : Params) : Locals → List (String × Ty) → Type
  | nil {Γ : Locals} : Args P Γ []
  | cons {Γ : Locals} {x : String} {s : Ty} {ps : List (String × Ty)} (a : Expr P Γ s) (rest : Args P Γ ps) : Args P Γ ((x, s) :: ps)
end

/-- A parameter assignment: the value each parameter arrives with. Both
readers take it at the parameter's width (`ofNat`, `& mask`), so no bound
on it is assumed. -/
def Env := String → Nat

/-- The extraction's `let`-bound values: each local's value. -/
def Vals := String → Nat

def Vals.set (l : Vals) (x : String) (v : Nat) : Vals :=
  fun y => if y = x then v else l y

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

/-- The value of a variable: a local's `let`-bound value, else the
parameter, at the variable's width. -/
def varX (Γ : Locals) (ρ : Env) (l : Vals) (x : String) : Nat :=
  match Γ x with
  | some _ => l x
  | none => ρ x

mutual
/-- The extraction's reading: `let x := v` binds the value for the rest of
the block; a call is the callee's body under its parameters bound to the
argument values (`let (r, …) ← g args`, the callee's own `def`); a
statement-level conditional rebinds the variables its arms assign to the
taken arm's values (`let (vars) ← if c then do A; pure (vars) else do B;
pure (vars)`), the untouched ones being equal on both sides. -/
def evalX {P : Params} : {Γ : Locals} → {t : Ty} → Expr P Γ t → Env → Vals → BitVec t.width
  | Γ, t, .var _ x _, ρ, l => BitVec.ofNat t.width (varX Γ ρ l x)
  | _, _, .lit _ v, _, _ => v
  | _, _, .arith op a b, ρ, l => arithX op (evalX a ρ l) (evalX b ρ l)
  | _, _, .bit op a b _, ρ, l => bitX op (evalX a ρ l) (evalX b ρ l)
  | _, t, .divPow2 a k _ _, ρ, l => evalX a ρ l / BitVec.ofNat t.width (2 ^ k)
  | _, t, .modPow2 a k _ _, ρ, l => evalX a ρ l % BitVec.ofNat t.width (2 ^ k)
  | _, _, .neg a, ρ, l => 0 - evalX a ρ l
  | _, _, .not a, ρ, l => ~~~ evalX a ρ l
  | _, t, .conv (s := s) _ a, ρ, l => convX s t (evalX a ρ l)
  | _, _, .cmp (s := s) op lhs rhs, ρ, l => BitVec.ofBool (cmpX s.signed op (evalX lhs ρ l) (evalX rhs ρ l))
  | _, _, .ite c a b, ρ, l => if evalX c ρ l = 1 then evalX a ρ l else evalX b ρ l
  | _, _, .letIn x v b, ρ, l => evalX b ρ (l.set x (evalX v ρ l).toNat)
  | _, _, .call _ _ body args, ρ, l => evalX body ρ (bindVals args ρ l (fun _ => 0))
  | _, _, .condSet c armT armF rest, ρ, l =>
    evalX rest ρ (if evalX c ρ l = 1 then runVals armT ρ l else runVals armF ρ l)
/-- An arm's assignments, in order (`let x := e` each). -/
def runVals {P : Params} : {Γ : Locals} → Assigns P Γ → Env → Vals → Vals
  | _, .nil, _, l => l
  | _, .cons x _ e rest, ρ, l => runVals rest ρ (l.set x (evalX e ρ l).toNat)
/-- The callee's values: each argument evaluated in the caller's scope and
bound to its parameter, in order. -/
def bindVals {P : Params} : {Γ : Locals} → {ps : List (String × Ty)} → Args P Γ ps → Env → Vals → Vals → Vals
  | _, _, .nil, _, _, acc => acc
  | _, _, .cons (x := x) a rest, ρ, l, acc => bindVals rest ρ l (acc.set x (evalX a ρ l).toNat)
end

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

/-- The verifier's term environment, `lo.locals`: each local's lowered
term (`oakLocal.value`); `none` for a name that is not a local. -/
def Scope := String → Option Term

def Scope.set (σ : Scope) (x : String) (t : Term) : Scope :=
  fun y => if y = x then some t else σ y

/-- The locals an arm assigns, in order. -/
def Assigns.names {P : Params} : {Γ : Locals} → Assigns P Γ → List String
  | _, .nil => []
  | _, .cons x _ _ rest => x :: rest.names

/-- `lowerConditionalStatement`'s merge: a local either arm assigned takes
`iteTerm(cond, afterTrue, afterFalse)` at the true arm's width
(`iteTerm`'s width is its left operand's); every other local keeps its
term. The Go skips the select when both arms left the same term object,
which the model does not track; the select of equal arms is the same
value. -/
def mergeScope (c : Term) (names : List String) (σT σF σ : Scope) : Scope :=
  fun y =>
    if y ∈ names then
      match σT y, σF y with
      | some a, some b => some (.ite a.width c a b)
      | _, _ => σ y
    else σ y

mutual
/-- `oakLowering.lower` at the expression's own width, each case as the Go
spells it: an identifier is its local's term through `adaptWidth` or, for a
parameter, `truncate(paramTerm(name, w), width)`, the identity at its own
width; a literal `constTerm(value, width)`; an infix `binaryTerm(op, left,
right)`; `/` and `%` by `2^k` a shift by `k` and a mask by `2^k - 1`; `-x`
is `0 - x`; `^x` and `!b` are `xor` with the mask; a conversion the operand
at its own width through `extendTerm` or `truncate`, then `truncate` to the
context (the identity here); a comparison in value position
`zeroExtend(truncate(cmpTerm(code, l, r), width), width)` at the Bool
width 1; a Bool conditional `iteTerm`; a local's declaration or rebinding
lowers the value at the local's width into `lo.locals` and goes on
(`declareLocal`, `assignLocal`); a call binds the callee's parameters to
the lowered arguments as a fresh `lo.locals` and lowers the body
(`enterCall`, `inlineCall`); a statement-level conditional runs each arm
on the locals before it and, for every local an arm assigned, selects
between the arms' terms by the condition (`lowerConditionalStatement`:
`iteTerm(truncate(cond, 1), afterTrue, afterFalse)`). -/
def lowerT {P : Params} : Scope → {Γ : Locals} → {t : Ty} → Expr P Γ t → Term
  | σ, _, t, .var _ x _ =>
    match σ x with
    | some term => adaptWidth term t.width
    | none => .param x t.width
  | _, _, t, .lit _ v => .const v.toNat t.width
  | σ, _, t, .arith op a b => .bin (arithTOp op) t.width (lowerT σ a) (lowerT σ b)
  | σ, _, t, .bit op a b _ => .bin (bitTOp op) t.width (lowerT σ a) (lowerT σ b)
  | σ, _, t, .divPow2 a k _ _ => .bin .shr t.width (lowerT σ a) (.const k t.width)
  | σ, _, t, .modPow2 a k _ _ => .bin .and t.width (lowerT σ a) (.const (2 ^ k - 1) t.width)
  | σ, _, t, .neg a => .bin .sub t.width (.const 0 t.width) (lowerT σ a)
  | σ, _, t, .not a => .bin .xor t.width (lowerT σ a) (.const (mask t.width) t.width)
  | σ, _, t, .conv (s := s) _ a =>
    let operand := lowerT σ a
    let converted :=
      if s.width < t.width then extendTerm operand s.width t.width s.signed
      else truncate operand t.width
    truncate converted t.width
  | σ, _, _, .cmp (s := s) op l r =>
    zeroExtend (truncate (.cmp (codeOf s.signed op) s.width (lowerT σ l) (lowerT σ r)) 1) 1
  | σ, _, t, .ite c a b => .ite t.width (lowerT σ c) (lowerT σ a) (lowerT σ b)
  | σ, _, _, .letIn x v b => lowerT (σ.set x (lowerT σ v)) b
  | σ, _, _, .call _ _ body args => lowerT (bindTerms σ args (fun _ => none)) body
  | σ, _, _, .condSet c armT armF rest =>
    lowerT (mergeScope (lowerT σ c) (armT.names ++ armF.names) (runTerms σ armT) (runTerms σ armF) σ) rest
/-- An arm's assignments as `assignLocal` executes them: each value lowered
at the local's width replaces the local's term, in order. -/
def runTerms {P : Params} : Scope → {Γ : Locals} → Assigns P Γ → Scope
  | σ, _, .nil => σ
  | σ, _, .cons x _ e rest => runTerms (σ.set x (lowerT σ e)) rest
/-- `enterCall`'s `bound`: each argument lowered in the caller's scope at
the parameter's width and bound to the parameter, in order. -/
def bindTerms {P : Params} (σ : Scope) : {Γ : Locals} → {ps : List (String × Ty)} → Args P Γ ps → Scope → Scope
  | _, _, .nil, acc => acc
  | _, _, .cons (x := x) a rest, acc => bindTerms σ rest (acc.set x (lowerT σ a))
end

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

theorem lowerT_width {P : Params} {Γ : Locals} {t : Ty} (e : Expr P Γ t) : ∀ σ : Scope, (lowerT σ e).width = t.width := by
  intro σ
  match e with
  | .var t x h =>
    simp only [lowerT]
    split <;> simp
  | .conv t a => simp only [lowerT, truncate_width]
  | .cmp op l r => simp only [lowerT, zeroExtend_width]; rfl
  | .letIn x v b => exact lowerT_width b _
  | .call params ret body args => exact lowerT_width body _
  | .condSet c armT armF rest => exact lowerT_width rest _
  | .lit _ _ => rfl
  | .arith _ _ _ => rfl
  | .bit _ _ _ _ => rfl
  | .divPow2 _ _ _ _ => rfl
  | .modPow2 _ _ _ _ => rfl
  | .neg _ => rfl
  | .not _ => rfl
  | .ite _ _ _ => rfl
termination_by structural e

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

theorem adaptWidth_topPositive (t : Term) (w : Nat) (hw : 0 < w) (hp : t.topPositive) : (adaptWidth t w).topPositive := by
  unfold adaptWidth
  split
  · exact zeroExtend_topPositive t w hw hp
  · exact truncate_topPositive t w hw hp

/-- Every term a scope holds is well formed. -/
def Scope.wf (σ : Scope) : Prop := ∀ x term, σ x = some term → term.topPositive

theorem Scope.wf_set {σ : Scope} (hσ : σ.wf) {x : String} {t : Term} (ht : t.topPositive) : (σ.set x t).wf := by
  intro y term h
  unfold Scope.set at h
  split at h
  · cases h; exact ht
  · exact hσ y term h

theorem Scope.wf_empty : Scope.wf (fun _ => none) := by
  intro y term h; cases h

theorem mergeScope_wf {c : Term} {names : List String} {σT σF σ : Scope} (hσ : σ.wf) : (mergeScope c names σT σF σ).wf := by
  intro y term h
  unfold mergeScope at h
  split at h
  · split at h
    · cases h; trivial
    · exact hσ y term h
  · exact hσ y term h

mutual
theorem lowerT_topPositive {P : Params} {Γ : Locals} {t : Ty} (e : Expr P Γ t) : ∀ σ : Scope, σ.wf → (lowerT σ e).topPositive := by
  intro σ hσ
  match e with
  | .var t x h =>
    simp only [lowerT]
    split
    · rename_i term hterm; exact adaptWidth_topPositive term _ t.width_pos (hσ x term hterm)
    · trivial
  | .cmp op l r =>
    exact zeroExtend_topPositive _ _ (by decide) (truncate_topPositive _ _ (by decide) (Ty.width_pos _))
  | .conv t a =>
    simp only [lowerT]
    apply truncate_topPositive _ _ t.width_pos
    split
    · exact extendTerm_topPositive _ _ _ _
    · exact truncate_topPositive _ _ t.width_pos (lowerT_topPositive a σ hσ)
  | .letIn x v b => exact lowerT_topPositive b _ (Scope.wf_set hσ (lowerT_topPositive v σ hσ))
  | .call params ret body args => exact lowerT_topPositive body _ (bindTerms_wf args σ hσ _ Scope.wf_empty)
  | .condSet c armT armF rest => exact lowerT_topPositive rest _ (mergeScope_wf hσ)
  | .lit _ _ => trivial
  | .arith _ _ _ => trivial
  | .bit _ _ _ _ => trivial
  | .divPow2 _ _ _ _ => trivial
  | .modPow2 _ _ _ _ => trivial
  | .neg _ => trivial
  | .not _ => trivial
  | .ite _ _ _ => trivial
termination_by structural e
theorem bindTerms_wf {P : Params} {Γ : Locals} {ps : List (String × Ty)} (args : Args P Γ ps) : ∀ σ : Scope, σ.wf → ∀ acc : Scope, acc.wf → (bindTerms σ args acc).wf := by
  intro σ hσ acc hacc
  match args with
  | .nil => exact hacc
  | .cons a rest => exact bindTerms_wf rest σ hσ _ (Scope.wf_set hacc (lowerT_topPositive a σ hσ))
termination_by structural args
end

/-- A one-bit value is 1 exactly when it is not 0. -/
theorem BitVec1_ne_zero_iff (c : BitVec 1) : c.toNat ≠ 0 ↔ c = 1 := by
  revert c; decide

theorem const_eval_of_lt (v w : Nat) (ρ : Env) (h : v < 2 ^ w) : (Term.const v w).eval ρ % 2 ^ w = v := by
  simp only [Term.eval, Nat.mod_mod]; exact Nat.mod_eq_of_lt h

theorem Locals.set_same {Γ : Locals} {x : String} {s : Ty} (h : Γ x = some s) : Γ.set x s = Γ := by
  funext y
  unfold Locals.set
  split
  · rename_i heq; subst heq; exact h.symm
  · rfl

/-- A name an arm assigns is a local. -/
theorem Assigns.names_local {P : Params} {Γ : Locals} (arm : Assigns P Γ) : ∀ {y : String}, y ∈ arm.names → ∃ s, Γ y = some s := by
  intro y hy
  match arm with
  | .nil => simp [Assigns.names] at hy
  | .cons x h e rest =>
    simp only [Assigns.names, List.mem_cons] at hy
    rcases hy with rfl | hy
    · exact ⟨_, h⟩
    · exact rest.names_local hy
termination_by structural arm

/-- A name an arm does not assign keeps its term and its value. -/
theorem run_unassigned {P : Params} {Γ : Locals} (arm : Assigns P Γ) : ∀ (σ : Scope) (ρ : Env) (l : Vals) {y : String}, y ∉ arm.names →
    runTerms σ arm y = σ y ∧ runVals arm ρ l y = l y := by
  intro σ ρ l y hy
  match arm with
  | .nil => exact ⟨rfl, rfl⟩
  | .cons x h e rest =>
    simp only [Assigns.names, List.mem_cons, not_or] at hy
    obtain ⟨hne, hrest⟩ := hy
    simp only [runTerms, runVals]
    obtain ⟨h1, h2⟩ := run_unassigned rest (σ.set x (lowerT σ e)) ρ (l.set x (evalX e ρ l).toNat) hrest
    rw [h1, h2]
    unfold Scope.set Vals.set
    rw [if_neg hne, if_neg hne]
    exact ⟨rfl, rfl⟩
termination_by structural arm

/-- A scope's two readings agree: a name that is not a local has no term;
a local's term has the local's width, is well formed, and evaluates to the
local's `let`-bound value. -/
def Agree (Γ : Locals) (σ : Scope) (ρ : Env) (l : Vals) : Prop :=
  (∀ x, Γ x = none → σ x = none) ∧
  (∀ x t, Γ x = some t → ∃ term, σ x = some term ∧ term.width = t.width ∧ term.topPositive ∧ term.eval ρ = l x)

theorem Agree.wf {Γ : Locals} {σ : Scope} {ρ : Env} {l : Vals} (h : Agree Γ σ ρ l) : σ.wf := by
  intro x term hx
  cases hΓ : Γ x with
  | none => rw [h.1 x hΓ] at hx; cases hx
  | some t =>
    obtain ⟨term', hσ, _, hp, _⟩ := h.2 x t hΓ
    rw [hσ] at hx; cases hx; exact hp

theorem Agree.empty (ρ : Env) (l : Vals) : Agree (fun _ => none) (fun _ => none) ρ l :=
  ⟨fun _ _ => rfl, fun _ _ h => by cases h⟩

theorem Agree.set {Γ : Locals} {σ : Scope} {ρ : Env} {l : Vals} (h : Agree Γ σ ρ l) (x : String) {s : Ty} {term : Term} {v : Nat}
    (hw : term.width = s.width) (hp : term.topPositive) (hv : term.eval ρ = v) :
    Agree (Γ.set x s) (σ.set x term) ρ (l.set x v) := by
  constructor
  · intro y hy
    unfold Locals.set at hy; unfold Scope.set
    split at hy
    · cases hy
    · rename_i hne; rw [if_neg hne]; exact h.1 y hy
  · intro y t hy
    unfold Locals.set at hy; unfold Scope.set; unfold Vals.set
    split at hy
    · rename_i heq; cases hy; subst heq
      exact ⟨term, by rw [if_pos rfl], hw, hp, by rw [if_pos rfl]; exact hv⟩
    · rename_i hne
      obtain ⟨term', hσ, hw', hp', hv'⟩ := h.2 y t hy
      exact ⟨term', by rw [if_neg hne]; exact hσ, hw', hp', by rw [if_neg hne]; exact hv'⟩

mutual
/-- The merge of two arms agrees with the selected arm's values. -/
theorem merge_agree {Γ : Locals} {σ σT σF : Scope} {ρ : Env} {l lT lF : Vals} (c : Term) (cv : BitVec 1) (hc : c.eval ρ = cv.toNat)
    (names : List String) (hA : Agree Γ σ ρ l) (hT : Agree Γ σT ρ lT) (hF : Agree Γ σF ρ lF)
    (hloc : ∀ y, y ∈ names → ∃ s, Γ y = some s)
    (hout : ∀ y, y ∉ names → σT y = σ y ∧ lT y = l y ∧ σF y = σ y ∧ lF y = l y) :
    Agree Γ (mergeScope c names σT σF σ) ρ (if cv = 1 then lT else lF) := by
  constructor
  · intro y hy
    have hn : y ∉ names := fun hin => by obtain ⟨s, hs⟩ := hloc y hin; rw [hs] at hy; cases hy
    unfold mergeScope
    rw [if_neg hn]
    exact hA.1 y hy
  · intro y t hy
    unfold mergeScope
    by_cases hin : y ∈ names
    · obtain ⟨a, haσ, haw, hap, hav⟩ := hT.2 y t hy
      obtain ⟨b, hbσ, hbw, hbp, hbv⟩ := hF.2 y t hy
      rw [if_pos hin, haσ, hbσ]
      refine ⟨.ite a.width c a b, rfl, haw, trivial, ?_⟩
      have key : (c.eval ρ ≠ 0) ↔ (cv = 1) := by rw [hc]; exact BitVec1_ne_zero_iff cv
      simp only [Term.eval]
      by_cases h1 : cv = 1
      · rw [if_pos (key.mpr h1), if_pos h1, hav, ← hav, Nat.mod_eq_of_lt (Term.eval_lt a ρ hap)]
      · rw [if_neg (fun hne => h1 (key.mp hne)), if_neg h1, hbv, ← hbv, haw.trans hbw.symm,
          Nat.mod_eq_of_lt (Term.eval_lt b ρ hbp)]
    · rw [if_neg hin]
      obtain ⟨hσT, hlT, hσF, hlF⟩ := hout y hin
      obtain ⟨term, hσ, hw, hp, hv⟩ := hA.2 y t hy
      refine ⟨term, hσ, hw, hp, ?_⟩
      split
      · rw [hlT]; exact hv
      · rw [hlF]; exact hv

/-- The verifier's lowering and the extraction's reading agree on every
expression of the shared subset, in every agreeing scope: the seam of
`126-verification-chain.md` §4, closed for expressions, locals, calls and
statement-level conditionals. -/
theorem lowerT_eval {P : Params} {Γ : Locals} {t : Ty} (e : Expr P Γ t) :
    ∀ (σ : Scope) (ρ : Env) (l : Vals), Agree Γ σ ρ l → (lowerT σ e).eval ρ = (evalX e ρ l).toNat := by
  intro σ ρ l hA
  match e with
  | .var t x h =>
    simp only [lowerT, evalX, varX]
    cases hΓ : Γ x with
    | none =>
      rw [hA.1 x hΓ]
      simp [Term.eval]
    | some t' =>
      have ht : t' = t := by simp [resolve, hΓ] at h; exact h
      subst ht
      obtain ⟨term, hσ, hw, hp, hv⟩ := hA.2 x t' hΓ
      rw [hσ]
      simp only [adaptWidth, hw, Nat.lt_irrefl, if_false, truncate_self term _ hw, hv, BitVec.toNat_ofNat]
      rw [← hv, Nat.mod_eq_of_lt (hw ▸ Term.eval_lt term ρ hp)]
  | .lit t v =>
    simp [lowerT, evalX, Term.eval]
  | .arith (t := t) op a b =>
    have iha := lowerT_eval a σ ρ l hA
    have ihb := lowerT_eval b σ ρ l hA
    cases op <;> simp [lowerT, evalX, arithX, arithTOp, Term.eval, Term.evalBin, iha, ihb, Nat.add_comm]
  | .bit (t := t) op a b h =>
    have iha := lowerT_eval a σ ρ l hA
    have ihb := lowerT_eval b σ ρ l hA
    have hw := (evalX a ρ l).isLt
    cases op <;> simp only [lowerT, evalX, bitX, bitTOp, Term.eval, Term.evalBin, iha, ihb, BitVec.toNat_mod_cancel]
    · rw [BitVec.toNat_and]; exact Nat.mod_eq_of_lt (Nat.and_lt_two_pow _ (evalX b ρ l).isLt)
    · rw [BitVec.toNat_or]; exact Nat.mod_eq_of_lt (Nat.or_lt_two_pow hw (evalX b ρ l).isLt)
    · rw [BitVec.toNat_xor]; exact Nat.mod_eq_of_lt (Nat.xor_lt_two_pow hw (evalX b ρ l).isLt)
    · rw [BitVec.toNat_shiftLeft]
    · rw [BitVec.toNat_ushiftRight]
      exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _) hw)
  | .divPow2 (t := t) a k hk hu =>
    have iha := lowerT_eval a σ ρ l hA
    have hw := (evalX a ρ l).isLt
    have hk2 : 2 ^ k < 2 ^ t.width := Nat.pow_lt_pow_right (by decide) hk
    have hkw : k < 2 ^ t.width := Nat.lt_of_lt_of_le hk (Nat.le_of_lt Nat.lt_two_pow_self)
    simp only [lowerT, evalX, Term.eval, Term.evalBin, iha, BitVec.toNat_mod_cancel, BitVec.toNat_udiv,
      BitVec.toNat_ofNat, Nat.mod_mod, Nat.mod_eq_of_lt hkw, Nat.mod_eq_of_lt hk, Nat.mod_eq_of_lt hk2,
      Nat.shiftRight_eq_div_pow]
    exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hw)
  | .modPow2 (t := t) a k hk hu =>
    have iha := lowerT_eval a σ ρ l hA
    have hk2 : 2 ^ k < 2 ^ t.width := Nat.pow_lt_pow_right (by decide) hk
    have hm : 2 ^ k - 1 < 2 ^ t.width := by omega
    simp only [lowerT, evalX, Term.eval, Term.evalBin, iha, BitVec.toNat_mod_cancel, BitVec.toNat_umod,
      BitVec.toNat_ofNat, Nat.mod_mod, Nat.mod_eq_of_lt hm, Nat.mod_eq_of_lt hk2,
      Nat.and_two_pow_sub_one_eq_mod]
    exact Nat.mod_eq_of_lt (Nat.lt_trans (Nat.mod_lt _ (Nat.two_pow_pos k)) hk2)
  | .neg (t := t) a =>
    have iha := lowerT_eval a σ ρ l hA
    simp [lowerT, evalX, Term.eval, Term.evalBin, iha]
  | .not (t := t) a =>
    have iha := lowerT_eval a σ ρ l hA
    have hx : (evalX a ρ l).toNat ^^^ mask t.width = (~~~ evalX a ρ l).toNat := by
      rw [← BitVec.xor_allOnes, BitVec.toNat_xor, BitVec.toNat_allOnes]; rfl
    simp only [lowerT, evalX, Term.eval, Term.evalBin, iha, BitVec.toNat_mod_cancel, mask_mod, hx]
  | .conv (s := s) t a =>
    have iha := lowerT_eval a σ ρ l hA
    have hs := s.width_pos
    simp only [lowerT, evalX, convX]
    rw [truncate_self _ _ (by split <;> simp)]
    by_cases hlt : s.width < t.width
    · simp only [hlt, if_true]
      unfold extendTerm
      simp only [adaptWidth, lowerT_width, hlt, if_true]
      have hlow := zeroExtend_masked_eval (lowerT σ a) s.width t.width ρ (lowerT_width a σ) (Nat.le_of_lt hlt)
      rw [iha, BitVec.toNat_mod_cancel] at hlow
      have hxw : (evalX a ρ l).toNat < 2 ^ t.width :=
        Nat.lt_of_lt_of_le (evalX a ρ l).isLt (Nat.pow_le_pow_right (by decide) (Nat.le_of_lt hlt))
      by_cases hsig : s.signed = true
      · simp only [hsig, Bool.not_true, Bool.false_eq_true, if_false, if_true]
        have hsh : (t.width - s.width) % 2 ^ t.width % t.width = t.width - s.width := by
          have : t.width - s.width < 2 ^ t.width := Nat.lt_of_le_of_lt (Nat.sub_le _ _) Nat.lt_two_pow_self
          rw [Nat.mod_eq_of_lt this, Nat.mod_eq_of_lt (by omega)]
        have hsh' : (t.width - s.width) % 2 ^ t.width % 2 ^ t.width % t.width = t.width - s.width := by
          rw [Nat.mod_mod, hsh]
        rw [Term.eval.eq_3, Term.eval.eq_3, hlow]
        simp only [Term.eval, Term.evalBin, hsh, hsh', Nat.mod_mod]
        rw [← BitVec.toNat_setWidth t.width (evalX a ρ l), ← BitVec.toNat_shiftLeft, BitVec.ofNat_toNat,
          BitVec.setWidth_eq, sshiftRight_shiftLeft_setWidth _ _ hs (Nat.le_of_lt hlt), BitVec.toNat_mod_cancel]
      · have hsig' : s.signed = false := by simpa using hsig
        simp only [hsig', Bool.not_false, Bool.false_eq_true, if_false, if_true, BitVec.toNat_setWidth, hlow,
          Nat.mod_eq_of_lt hxw]
    · simp only [hlt, if_false]
      rw [truncate_eval _ _ _ t.width_pos (by rw [lowerT_width]; omega) (lowerT_topPositive a σ (Agree.wf hA)), iha,
        BitVec.toNat_setWidth]
  | .cmp (s := s) op lhs rhs =>
    have ihl := lowerT_eval lhs σ ρ l hA
    have ihr := lowerT_eval rhs σ ρ l hA
    simp only [lowerT]
    rw [zeroExtend_self _ _ (truncate_width _ _), truncate_cmp_eval]
    simp only [Term.eval, ihl, ihr]
    rw [lowerT_width lhs σ]
    simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq, codeOf_holds, evalX]
    cases cmpX s.signed op (evalX lhs ρ l) (evalX rhs ρ l) <;> simp
  | .ite (t := t) c a b =>
    have ihc := lowerT_eval c σ ρ l hA
    have iha := lowerT_eval a σ ρ l hA
    have ihb := lowerT_eval b σ ρ l hA
    simp only [lowerT, evalX, Term.eval, ihc, iha, ihb, BitVec.toNat_mod_cancel]
    have key : ((evalX c ρ l).toNat ≠ 0) ↔ (evalX c ρ l = 1) := BitVec1_ne_zero_iff (evalX c ρ l)
    by_cases h : evalX c ρ l = 1
    · rw [if_pos (key.mpr h), if_pos h]
    · rw [if_neg (fun hne => h (key.mp hne)), if_neg h]
  | .letIn (s := s) (t := t) x v b =>
    exact lowerT_eval b _ ρ _ (Agree.set hA x (lowerT_width v σ) (lowerT_topPositive v σ (Agree.wf hA)) (lowerT_eval v σ ρ l hA))
  | .call params ret body args =>
    exact lowerT_eval body _ ρ _ (bindArgs_agree args σ ρ l hA _ _ _ (Agree.empty ρ _))
  | .condSet c armT armF rest =>
    have hT := runTerms_agree armT σ ρ l hA
    have hF := runTerms_agree armF σ ρ l hA
    have hc := lowerT_eval c σ ρ l hA
    refine lowerT_eval rest _ ρ _ (merge_agree (lowerT σ c) (evalX c ρ l) hc _ hA hT hF ?_ ?_)
    · intro y hy
      rcases List.mem_append.mp hy with h | h
      · exact armT.names_local h
      · exact armF.names_local h
    · intro y hy
      have hyT : y ∉ armT.names := fun h => hy (List.mem_append.mpr (Or.inl h))
      have hyF : y ∉ armF.names := fun h => hy (List.mem_append.mpr (Or.inr h))
      obtain ⟨h1, h2⟩ := run_unassigned armT σ ρ l hyT
      obtain ⟨h3, h4⟩ := run_unassigned armF σ ρ l hyF
      exact ⟨h1, h2, h3, h4⟩
termination_by structural e
/-- Running an arm's assignments keeps the scope agreeing. -/
theorem runTerms_agree {P : Params} {Γ : Locals} (arm : Assigns P Γ) :
    ∀ (σ : Scope) (ρ : Env) (l : Vals), Agree Γ σ ρ l → Agree Γ (runTerms σ arm) ρ (runVals arm ρ l) := by
  intro σ ρ l hA
  match arm with
  | .nil => exact hA
  | .cons x h e rest =>
    have hA' := Agree.set hA x (lowerT_width e σ) (lowerT_topPositive e σ (Agree.wf hA)) (lowerT_eval e σ ρ l hA)
    rw [Locals.set_same h] at hA'
    exact runTerms_agree rest _ ρ _ hA'
termination_by structural arm
/-- Binding a call's arguments keeps the callee's scope agreeing: each
parameter's term has the parameter's width and evaluates to the argument's
value. -/
theorem bindArgs_agree {P : Params} {Γ : Locals} {ps : List (String × Ty)} (args : Args P Γ ps) :
    ∀ (σ : Scope) (ρ : Env) (l : Vals), Agree Γ σ ρ l → ∀ (Γ0 : Locals) (acc : Scope) (l0 : Vals), Agree Γ0 acc ρ l0 →
      Agree (bindTypes Γ0 ps) (bindTerms σ args acc) ρ (bindVals args ρ l l0) := by
  intro σ ρ l hA Γ0 acc l0 h0
  match args with
  | .nil => exact h0
  | .cons (x := x) a rest =>
    exact bindArgs_agree rest σ ρ l hA _ _ _ (h0.set x (lowerT_width a σ) (lowerT_topPositive a σ (Agree.wf hA)) (lowerT_eval a σ ρ l hA))
termination_by structural args
end

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

/-- Parameters from a list; the empty local scope and term scope. -/
def ps (l : List (String × Ty)) : Params := fun x => (l.find? (fun p => p.1 = x)).map (·.2)
abbrev Γ0 : Locals := fun _ => none
abbrev σ0 : Scope := fun _ => none
/-- An expression over parameters `P` at a function's entry. -/
abbrev X (P : Params) (t : Ty) := Expr P Γ0 t

/-- `(a, b: u32) -> u32 = a + b` -/
example : (lowerT σ0 (.arith .add (.var .u32 "a" (by decide)) (.var .u32 "b" (by decide)) : X (ps [("a", .u32), ("b", .u32)]) .u32)).render = "(a add b)" := by decide
/-- `(a, b: u32) -> u32 = a - b` -/
example : (lowerT σ0 (.arith .sub (.var .u32 "a" (by decide)) (.var .u32 "b" (by decide)) : X (ps [("a", .u32), ("b", .u32)]) .u32)).render = "(a sub b)" := by decide
/-- `(a: u32) -> u32 = a * 3` -/
example : (lowerT σ0 (.arith .mul (.var .u32 "a" (by decide)) (.lit .u32 3) : X (ps [("a", .u32)]) .u32)).render = "(a mul 3)" := by decide
/-- `(a: u32) -> u32 = a / 8` -/
example : (lowerT σ0 (.divPow2 (.var .u32 "a" (by decide)) 3 (by decide) rfl : X (ps [("a", .u32)]) .u32)).render = "(a shr 3)" := by decide
/-- `(a: u32) -> u32 = a % 8` -/
example : (lowerT σ0 (.modPow2 (.var .u32 "a" (by decide)) 3 (by decide) rfl : X (ps [("a", .u32)]) .u32)).render = "(a and 7)" := by decide
/-- `(a: u32) -> u32 = -a` -/
example : (lowerT σ0 (.neg (.var .u32 "a" (by decide)) : X (ps [("a", .u32)]) .u32)).render = "(0 sub a)" := by decide
/-- `(a: u32) -> u32 = ^a` -/
example : (lowerT σ0 (.not (.var .u32 "a" (by decide)) : X (ps [("a", .u32)]) .u32)).render = "(a xor 4294967295)" := by decide
/-- `(a, b: u32) -> u32 = (a << 3) | (b >> 5)` -/
example : (lowerT σ0 (.bit .or (.bit .shl (.var .u32 "a" (by decide)) (.lit .u32 3) rfl) (.bit .shr (.var .u32 "b" (by decide)) (.lit .u32 5) rfl) rfl : X (ps [("a", .u32), ("b", .u32)]) .u32)).render
    = "((a shl 3) or (b shr 5))" := by decide
/-- `(a, b: u32) -> u32 = (a & b) ^ b` -/
example : (lowerT σ0 (.bit .xor (.bit .and (.var .u32 "a" (by decide)) (.var .u32 "b" (by decide)) rfl) (.var .u32 "b" (by decide)) rfl : X (ps [("a", .u32), ("b", .u32)]) .u32)).render
    = "((a and b) xor b)" := by decide
/-- `(a: u8) -> u32 = u32(a)` -/
example : (lowerT σ0 (.conv .u32 (.var .u8 "a" (by decide)) : X (ps [("a", .u8)]) .u32)).render = "(a and 255)" := by decide
/-- `(a: i8) -> i32 = i32(a)` -/
example : (lowerT σ0 (.conv .i32 (.var .i8 "a" (by decide)) : X (ps [("a", .i8)]) .i32)).render = "(((a and 255) shl 24) sar 24)" := by decide
/-- `(a: i32) -> i64 = i64(a) + 1` -/
example : (lowerT σ0 (.arith .add (.conv .i64 (.var .i32 "a" (by decide))) (.lit .i64 1) : X (ps [("a", .i32)]) .i64)).render
    = "((((a and 4294967295) shl 32) sar 32) add 1)" := by decide
/-- `(a: u32) -> u8 = u8_trunc_u32(a)` — a re-widthed parameter prints as itself. -/
example : (lowerT σ0 (.conv .u8 (.var .u32 "a" (by decide)) : X (ps [("a", .u32)]) .u8)).render = "a" := by decide
/-- `(a, b: u16) -> u32 = u32(a) * u32(b)` -/
example : (lowerT σ0 (.arith .mul (.conv .u32 (.var .u16 "a" (by decide))) (.conv .u32 (.var .u16 "b" (by decide))) : X (ps [("a", .u16), ("b", .u16)]) .u32)).render
    = "((a and 65535) mul (b and 65535))" := by decide
/-- `(a, b: u32) -> Bool = a < b` and the other five unsigned comparisons -/
example : (lowerT σ0 (.cmp .lt (.var .u32 "a" (by decide)) (.var .u32 "b" (by decide)) : X (ps [("a", .u32), ("b", .u32)]) .bool)).render = "(a lo b)" := by decide
example : (lowerT σ0 (.cmp .le (.var .u32 "a" (by decide)) (.var .u32 "b" (by decide)) : X (ps [("a", .u32), ("b", .u32)]) .bool)).render = "(a ls b)" := by decide
example : (lowerT σ0 (.cmp .gt (.var .u32 "a" (by decide)) (.var .u32 "b" (by decide)) : X (ps [("a", .u32), ("b", .u32)]) .bool)).render = "(a hi b)" := by decide
example : (lowerT σ0 (.cmp .ge (.var .u32 "a" (by decide)) (.var .u32 "b" (by decide)) : X (ps [("a", .u32), ("b", .u32)]) .bool)).render = "(a hs b)" := by decide
example : (lowerT σ0 (.cmp .eq (.var .u32 "a" (by decide)) (.var .u32 "b" (by decide)) : X (ps [("a", .u32), ("b", .u32)]) .bool)).render = "(a eq b)" := by decide
example : (lowerT σ0 (.cmp .ne (.var .u32 "a" (by decide)) (.var .u32 "b" (by decide)) : X (ps [("a", .u32), ("b", .u32)]) .bool)).render = "(a ne b)" := by decide
/-- `(a, b: i32) -> Bool = a < b` and the other three signed orders -/
example : (lowerT σ0 (.cmp .lt (.var .i32 "a" (by decide)) (.var .i32 "b" (by decide)) : X (ps [("a", .i32), ("b", .i32)]) .bool)).render = "(a lt b)" := by decide
example : (lowerT σ0 (.cmp .le (.var .i32 "a" (by decide)) (.var .i32 "b" (by decide)) : X (ps [("a", .i32), ("b", .i32)]) .bool)).render = "(a le b)" := by decide
example : (lowerT σ0 (.cmp .gt (.var .i32 "a" (by decide)) (.var .i32 "b" (by decide)) : X (ps [("a", .i32), ("b", .i32)]) .bool)).render = "(a gt b)" := by decide
example : (lowerT σ0 (.cmp .ge (.var .i32 "a" (by decide)) (.var .i32 "b" (by decide)) : X (ps [("a", .i32), ("b", .i32)]) .bool)).render = "(a ge b)" := by decide
/-- `(a, b, c: u32) -> Bool = a < b && b < c` -/
example : (lowerT σ0 (.bit .and (.cmp .lt (.var .u32 "a" (by decide)) (.var .u32 "b" (by decide))) (.cmp .lt (.var .u32 "b" (by decide)) (.var .u32 "c" (by decide))) rfl : X (ps [("a", .u32), ("b", .u32), ("c", .u32)]) .bool)).render
    = "((a lo b) and (b lo c))" := by decide
/-- `(a, b: u32) -> Bool = a < b || a == b` -/
example : (lowerT σ0 (.bit .or (.cmp .lt (.var .u32 "a" (by decide)) (.var .u32 "b" (by decide))) (.cmp .eq (.var .u32 "a" (by decide)) (.var .u32 "b" (by decide))) rfl : X (ps [("a", .u32), ("b", .u32)]) .bool)).render
    = "((a lo b) or (a eq b))" := by decide
/-- `(a, b: u32) -> Bool = !(a < b)` -/
example : (lowerT σ0 (.not (.cmp .lt (.var .u32 "a" (by decide)) (.var .u32 "b" (by decide))) : X (ps [("a", .u32), ("b", .u32)]) .bool)).render = "((a lo b) xor 1)" := by decide
/-- `(a, b: u32) -> u32 = a < b ? a | b` -/
example : (lowerT σ0 (.ite (.cmp .lt (.var .u32 "a" (by decide)) (.var .u32 "b" (by decide))) (.var .u32 "a" (by decide)) (.var .u32 "b" (by decide)) : X (ps [("a", .u32), ("b", .u32)]) .u32)).render
    = "((a lo b) ? a : b)" := by decide
/-- `(a, b: i64) -> i64 = a < b ? b - a | a - b` -/
example : (lowerT σ0 (.ite (.cmp .lt (.var .i64 "a" (by decide)) (.var .i64 "b" (by decide))) (.arith .sub (.var .i64 "b" (by decide)) (.var .i64 "a" (by decide))) (.arith .sub (.var .i64 "a" (by decide)) (.var .i64 "b" (by decide))) : X (ps [("a", .i64), ("b", .i64)]) .i64)).render
    = "((a lt b) ? (b sub a) : (a sub b))" := by decide

/-! Locals and calls: a local is substituted, a call is inlined, so the
renders are the terms the source would have without them. -/

/-- `(a, b: u32) -> u32 = { y: u32 = a + b; y * y }` -/
example : (lowerT σ0 (.letIn "y" (.arith .add (.var .u32 "a" (by decide)) (.var .u32 "b" (by decide)))
    (.arith .mul (.var .u32 "y" (by decide)) (.var .u32 "y" (by decide))) : X (ps [("a", .u32), ("b", .u32)]) .u32)).render
    = "((a add b) mul (a add b))" := by decide
/-- `(a: u32) -> u32 = { y: u32 = a; y = y + 1; y * 2 }` — a rebinding replaces the term. -/
example : (lowerT σ0 (.letIn "y" (.var .u32 "a" (by decide))
    (.letIn "y" (.arith .add (.var .u32 "y" (by decide)) (.lit .u32 1))
      (.arith .mul (.var .u32 "y" (by decide)) (.lit .u32 2))) : X (ps [("a", .u32)]) .u32)).render
    = "((a add 1) mul 2)" := by decide
/-- `(a: u32) -> u32 = { y: u8 = u8_trunc_u32(a); u32(y) }` — a narrow local read at its own width. -/
example : (lowerT σ0 (.letIn "y" (.conv .u8 (.var .u32 "a" (by decide)))
    (.conv .u32 (.var .u8 "y" (by decide))) : X (ps [("a", .u32)]) .u32)).render
    = "(a and 255)" := by decide
/-- `g: (x: u32) -> u32 = x * x`; `f: (a: u32) -> u32 = g(a + 1)` -/
example : (lowerT σ0 (.call [("x", .u32)] .u32
    (.arith .mul (.var .u32 "x" (by decide)) (.var .u32 "x" (by decide)))
    (.cons (.arith .add (.var .u32 "a" (by decide)) (.lit .u32 1)) .nil) : X (ps [("a", .u32)]) .u32)).render
    = "((a add 1) mul (a add 1))" := by decide
/-- `h: (x, y: u32) -> u32 = { d: u32 = x - y; d & 255 }`; `f: (a, b: u32) -> u32 = h(b, a)` -/
example : (lowerT σ0 (.call [("x", .u32), ("y", .u32)] .u32
    (.letIn "d" (.arith .sub (.var .u32 "x" (by decide)) (.var .u32 "y" (by decide)))
      (.bit .and (.var .u32 "d" (by decide)) (.lit .u32 255) rfl))
    (.cons (.var .u32 "b" (by decide)) (.cons (.var .u32 "a" (by decide)) .nil)) : X (ps [("a", .u32), ("b", .u32)]) .u32)).render
    = "((b sub a) and 255)" := by decide

/-- `(a, b: u32) -> u32 = { m: u32 = a; a < b ? { m = b } | { }; m * 2 }` -/
example : (lowerT σ0 (.letIn "m" (.var .u32 "a" (by decide))
    (.condSet (.cmp .lt (.var .u32 "a" (by decide)) (.var .u32 "b" (by decide)))
      (.cons "m" (by decide) (.var .u32 "b" (by decide)) .nil) .nil
      (.arith .mul (.var .u32 "m" (by decide)) (.lit .u32 2))) : X (ps [("a", .u32), ("b", .u32)]) .u32)).render
    = "(((a lo b) ? b : a) mul 2)" := by decide
/-- `(a, b: u32) -> u32 = { x: u32 = a; y: u32 = b; a < b ? { x = b; y = a } | { x = x + 1 }; x - y }` -/
example : (lowerT σ0 (.letIn "x" (.var .u32 "a" (by decide)) (.letIn "y" (.var .u32 "b" (by decide))
    (.condSet (.cmp .lt (.var .u32 "a" (by decide)) (.var .u32 "b" (by decide)))
      (.cons "x" (by decide) (.var .u32 "b" (by decide)) (.cons "y" (by decide) (.var .u32 "a" (by decide)) .nil))
      (.cons "x" (by decide) (.arith .add (.var .u32 "x" (by decide)) (.lit .u32 1)) .nil)
      (.arith .sub (.var .u32 "x" (by decide)) (.var .u32 "y" (by decide))))) : X (ps [("a", .u32), ("b", .u32)]) .u32)).render
    = "(((a lo b) ? b : (a add 1)) sub ((a lo b) ? a : b))" := by decide

/-- `(a, b: u32) -> u32 = { m: u32 = a; a < b ? { m = b } | { }; m * 2 }` -/
example : (lowerT σ0 (.letIn "m" (.var .u32 "a" (by decide))
    (.condSet (.cmp .lt (.var .u32 "a" (by decide)) (.var .u32 "b" (by decide)))
      (.cons "m" (by decide) (.var .u32 "b" (by decide)) .nil) .nil
      (.arith .mul (.var .u32 "m" (by decide)) (.lit .u32 2))) : X (ps [("a", .u32), ("b", .u32)]) .u32)).render
    = "(((a lo b) ? b : a) mul 2)" := by decide
/-- `(a, b: u32) -> u32 = { x: u32 = a; y: u32 = b; a < b ? { x = b; y = a } | { x = x + 1 }; x - y }` -/
example : (lowerT σ0 (.letIn "x" (.var .u32 "a" (by decide)) (.letIn "y" (.var .u32 "b" (by decide))
    (.condSet (.cmp .lt (.var .u32 "a" (by decide)) (.var .u32 "b" (by decide)))
      (.cons "x" (by decide) (.var .u32 "b" (by decide)) (.cons "y" (by decide) (.var .u32 "a" (by decide)) .nil))
      (.cons "x" (by decide) (.arith .add (.var .u32 "x" (by decide)) (.lit .u32 1)) .nil)
      (.arith .sub (.var .u32 "x" (by decide)) (.var .u32 "y" (by decide))))) : X (ps [("a", .u32), ("b", .u32)]) .u32)).render
    = "(((a lo b) ? b : (a add 1)) sub ((a lo b) ? a : b))" := by decide

end Oak.LoweringRefinement
