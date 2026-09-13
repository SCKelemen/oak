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

* `Expr P S Γ t` is an Oak scalar expression of type `t` over the function's
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
* `lowerT_eval`: whenever the lowering admits an expression
  (`lowerT σ e = some T`; `none` is the Go's "outside the subset"), the
  extraction computes a value under any fuel above the unrolling budget
  (`evalX e ρ λ F = some v`) and `T.eval ρ = v.toNat` — for every
  parameter assignment `ρ` and every scope: a term environment `σ` (the
  verifier's `locals`, each local's lowered term) and a value environment
  `λ` (the extraction's `let`-bound values) that agree (`Agree`). A local
  is lowered once and substituted (`declareLocal`, `assignLocal`, an
  identifier through `adaptWidth(local.value, width)`); a call binds the
  callee's parameters to the lowered arguments as a fresh scope and lowers
  the body (`enterCall`, `inlineCall`); a statement conditional selects
  between its arms' terms (`lowerConditionalStatement`); a loop unrolls
  while its folded condition is a non-zero constant (`lowerWhile`), against
  the extraction's fuel-indexed recursion. Parameters and locals are read
  from separate environments because the verifier's terms name parameters
  and only parameters: a local that shadows a parameter changes what the
  source means by the name, never what a term means.

The term constructors fold as the Go's do (`Term.binary`, `cmpT`, `iteT`,
`selectT`: constant operands fold, `x + 0` is `x`, a constant condition
picks its arm, a constant index names the element parameter), each proved
to evaluate as the node it folds. Two things the Go does that the model
leaves out, both eval-preserving: a comparison in the condition of an
`ite` keeps the operands' width where `lowerT` re-widths it to 1 (the
executor reads a comparison's width only where its 1/0 result is used, and
`String` does not print it), and `lowerConditionalStatement` skips the
select when both arms left the same term object.

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

/-- The function's span and view parameters (`[]T`, `[*]T`): name to
element type (`lo.spans`, `spanContract`). -/
def Spans := String → Option Ty

/-- The verifier's name for element `k` of span `v` (`spanElemName`): the
parameter a constant-index read is, and the cell a select reads. Both
readers read the same memory through it. -/
def elemName (v : String) (k : Nat) : String := v ++ "[" ++ toString k ++ "]"

/-- The verifier's name for a span's length (`spanLenName`). -/
def lenName (v : String) : String := "len(" ++ v ++ ")"

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
arms assign existing locals, followed by `rest`; `whileLoop c body rest`
is `while c { body }` followed by `rest`; `matchInt x arms` is the
integer-constant match `x ? | k₁ => e₁ | … | _ => e` in value position and
`matchSet x arms rest` the same in statement position, its arms assigning
locals; `elem s v h i` is the element read `v[i]` of a span parameter and
`len v h` its `len(v)`. -/
inductive Expr (P : Params) (S : Spans) : Locals → Ty → Type
  | var {Γ : Locals} (t : Ty) (x : String) (h : resolve P Γ x = some t) : Expr P S Γ t
  | lit {Γ : Locals} (t : Ty) (v : BitVec t.width) : Expr P S Γ t
  | arith {Γ : Locals} (op : ArithOp) {t : Ty} (a b : Expr P S Γ t) : Expr P S Γ t
  | bit {Γ : Locals} (op : BitOp) {t : Ty} (a b : Expr P S Γ t) (h : t.signed = false) : Expr P S Γ t
  | divPow2 {Γ : Locals} {t : Ty} (a : Expr P S Γ t) (k : Nat) (hk : k < t.width) (hu : t.signed = false) : Expr P S Γ t
  | modPow2 {Γ : Locals} {t : Ty} (a : Expr P S Γ t) (k : Nat) (hk : k < t.width) (hu : t.signed = false) : Expr P S Γ t
  | neg {Γ : Locals} {t : Ty} (a : Expr P S Γ t) : Expr P S Γ t
  | not {Γ : Locals} {t : Ty} (a : Expr P S Γ t) : Expr P S Γ t
  | conv {Γ : Locals} {s : Ty} (t : Ty) (a : Expr P S Γ s) : Expr P S Γ t
  | cmp {Γ : Locals} {s : Ty} (op : CmpOp) (l r : Expr P S Γ s) : Expr P S Γ .bool
  | ite {Γ : Locals} {t : Ty} (c : Expr P S Γ .bool) (a b : Expr P S Γ t) : Expr P S Γ t
  | letIn {Γ : Locals} {s t : Ty} (x : String) (v : Expr P S Γ s) (b : Expr P S (Γ.set x s) t) : Expr P S Γ t
  | call {Γ : Locals} (params : List (String × Ty)) (ret : Ty)
      (body : Expr P S (bindTypes (fun _ => none) params) ret) (args : Args P S Γ params) : Expr P S Γ ret
  | condSet {Γ : Locals} {t : Ty} (c : Expr P S Γ .bool) (armT armF : Stmts P S Γ) (rest : Expr P S Γ t) : Expr P S Γ t
  | whileLoop {Γ : Locals} {t : Ty} (c : Expr P S Γ .bool) (body : Stmts P S Γ) (rest : Expr P S Γ t) : Expr P S Γ t
  | matchInt {Γ : Locals} {s t : Ty} (x : Expr P S Γ s) (arms : Arms P S Γ s t) : Expr P S Γ t
  | matchSet {Γ : Locals} {s t : Ty} (x : Expr P S Γ s) (arms : ArmsS P S Γ s) (rest : Expr P S Γ t) : Expr P S Γ t
  | elem {Γ : Locals} (s : Ty) (v : String) (h : S v = some s) (i : Expr P S Γ .u32) : Expr P S Γ s
  | len {Γ : Locals} {s : Ty} (v : String) (h : S v = some s) : Expr P S Γ .u32
/-- Statements in a conditional arm or a loop body: assignments `x = e` to
locals already in scope, statement-level conditionals, and nested loops,
in order (a declaration inside an arm or a body is scoped to it and is not
in the subset). -/
inductive Stmts (P : Params) (S : Spans) : Locals → Type
  | nil {Γ : Locals} : Stmts P S Γ
  | assign {Γ : Locals} (x : String) {s : Ty} (h : Γ x = some s) (e : Expr P S Γ s) (rest : Stmts P S Γ) : Stmts P S Γ
  | cond {Γ : Locals} (c : Expr P S Γ .bool) (armT armF : Stmts P S Γ) (rest : Stmts P S Γ) : Stmts P S Γ
  | loop {Γ : Locals} (c : Expr P S Γ .bool) (body : Stmts P S Γ) (rest : Stmts P S Γ) : Stmts P S Γ
  | matchS {Γ : Locals} {s : Ty} (x : Expr P S Γ s) (arms : ArmsS P S Γ s) (rest : Stmts P S Γ) : Stmts P S Γ
/-- The arms of an integer-constant match in value position: literal
cases in order, then the fallback (the wildcard arm; a match without one
has its last arm as the fallback, `matchArms` dropping that arm's
condition). -/
inductive Arms (P : Params) (S : Spans) : Locals → Ty → Ty → Type
  | fallback {Γ : Locals} {s t : Ty} (e : Expr P S Γ t) : Arms P S Γ s t
  | case {Γ : Locals} {s t : Ty} (k : BitVec s.width) (e : Expr P S Γ t) (rest : Arms P S Γ s t) : Arms P S Γ s t
/-- The arms of an integer-constant match in statement position. -/
inductive ArmsS (P : Params) (S : Spans) : Locals → Ty → Type
  | fallback {Γ : Locals} {s : Ty} (st : Stmts P S Γ) : ArmsS P S Γ s
  | case {Γ : Locals} {s : Ty} (k : BitVec s.width) (st : Stmts P S Γ) (rest : ArmsS P S Γ s) : ArmsS P S Γ s
/-- A call's arguments, one per callee parameter, in the caller's scope. -/
inductive Args (P : Params) (S : Spans) : Locals → List (String × Ty) → Type
  | nil {Γ : Locals} : Args P S Γ []
  | cons {Γ : Locals} {x : String} {s : Ty} {ps : List (String × Ty)} (a : Expr P S Γ s) (rest : Args P S Γ ps) : Args P S Γ ((x, s) :: ps)
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

/-- The extraction's `while` (`95-extraction.md` §2): a fuel-indexed helper
that returns `none` when the fuel runs out, otherwise tests the condition
and either runs the body and recurses on the remaining fuel or returns the
variables as they stand. -/
def loopX (cond : Vals → Option (BitVec 1)) (body : Vals → Option Vals) : Nat → Vals → Option Vals
  | 0, _ => none
  | n + 1, l => (cond l).bind fun cv => if cv = 1 then (body l).bind (loopX cond body n) else some l

mutual
/-- The extraction's reading, under a fuel every loop and call receives
(`95-extraction.md` §2: `Option`, `none` when the fuel runs out): `let x :=
v` binds the value for the rest of the block; a call is the callee's body
under its parameters bound to the argument values (`let (r, …) ← g args
fuel`, the callee's own `def`); a statement-level conditional rebinds the
variables its arms assign to the taken arm's values (`let (vars) ← if c
then do A; pure (vars) else do B; pure (vars)`), the untouched ones being
equal on both sides; a loop is `loopX`; an integer-constant match is the
if-chain `if x == k₁ then … else …` in value and statement position; a span element `v[i]` is the
memory cell `v[k]` at the index's value (the extraction's `v.getD i.toNat
zero`, the span's contents padded with zeros being the memory both readers
see), `len(v)` the span's length. -/
def evalX {P : Params} {S : Spans} : {Γ : Locals} → {t : Ty} → Expr P S Γ t → Env → Vals → Nat → Option (BitVec t.width)
  | Γ, t, .var _ x _, ρ, l, _ => some (BitVec.ofNat t.width (varX Γ ρ l x))
  | _, _, .lit _ v, _, _, _ => some v
  | _, _, .arith op a b, ρ, l, F => (evalX a ρ l F).bind fun x => (evalX b ρ l F).bind fun y => some (arithX op x y)
  | _, _, .bit op a b _, ρ, l, F => (evalX a ρ l F).bind fun x => (evalX b ρ l F).bind fun y => some (bitX op x y)
  | _, t, .divPow2 a k _ _, ρ, l, F => (evalX a ρ l F).bind fun x => some (x / BitVec.ofNat t.width (2 ^ k))
  | _, t, .modPow2 a k _ _, ρ, l, F => (evalX a ρ l F).bind fun x => some (x % BitVec.ofNat t.width (2 ^ k))
  | _, _, .neg a, ρ, l, F => (evalX a ρ l F).bind fun x => some (0 - x)
  | _, _, .not a, ρ, l, F => (evalX a ρ l F).bind fun x => some (~~~ x)
  | _, t, .conv (s := s) _ a, ρ, l, F => (evalX a ρ l F).bind fun x => some (convX s t x)
  | _, _, .cmp (s := s) op lhs rhs, ρ, l, F =>
    (evalX lhs ρ l F).bind fun x => (evalX rhs ρ l F).bind fun y => some (BitVec.ofBool (cmpX s.signed op x y))
  | _, _, .ite c a b, ρ, l, F => (evalX c ρ l F).bind fun cv => if cv = 1 then evalX a ρ l F else evalX b ρ l F
  | _, _, .letIn x v b, ρ, l, F => (evalX v ρ l F).bind fun x' => evalX b ρ (l.set x x'.toNat) F
  | _, _, .call _ _ body args, ρ, l, F => (bindVals args ρ l (fun _ => 0) F).bind fun l' => evalX body ρ l' F
  | _, _, .condSet c armT armF rest, ρ, l, F =>
    (evalX c ρ l F).bind fun cv => (if cv = 1 then runVals armT ρ l F else runVals armF ρ l F).bind fun l' => evalX rest ρ l' F
  | _, _, .whileLoop c body rest, ρ, l, F =>
    (loopX (fun l₀ => evalX c ρ l₀ F) (fun l₀ => runVals body ρ l₀ F) F l).bind fun l' => evalX rest ρ l' F
  | _, _, .matchInt x arms, ρ, l, F => (evalX x ρ l F).bind fun vx => armsX vx arms ρ l F
  | _, _, .matchSet x arms rest, ρ, l, F =>
    (evalX x ρ l F).bind fun vx => (armsVals vx arms ρ l F).bind fun l' => evalX rest ρ l' F
  | _, s, .elem _ v _ i, ρ, l, F => (evalX i ρ l F).bind fun k => some (BitVec.ofNat s.width (ρ (elemName v k.toNat)))
  | _, _, .len v _, ρ, _, _ => some (BitVec.ofNat 32 (ρ (lenName v)))
/-- Statements in order: `let x := e`, the conditional's rebinding, a loop. -/
def runVals {P : Params} {S : Spans} : {Γ : Locals} → Stmts P S Γ → Env → Vals → Nat → Option Vals
  | _, .nil, _, l, _ => some l
  | _, .assign x _ e rest, ρ, l, F => (evalX e ρ l F).bind fun x' => runVals rest ρ (l.set x x'.toNat) F
  | _, .cond c armT armF rest, ρ, l, F =>
    (evalX c ρ l F).bind fun cv => (if cv = 1 then runVals armT ρ l F else runVals armF ρ l F).bind fun l' => runVals rest ρ l' F
  | _, .loop c body rest, ρ, l, F =>
    (loopX (fun l₀ => evalX c ρ l₀ F) (fun l₀ => runVals body ρ l₀ F) F l).bind fun l' => runVals rest ρ l' F
  | _, .matchS x arms rest, ρ, l, F =>
    (evalX x ρ l F).bind fun vx => (armsVals vx arms ρ l F).bind fun l' => runVals rest ρ l' F
/-- A value-position match: `if x == k₁ then e₁ else if … else e`. -/
def armsX {P : Params} {S : Spans} : {Γ : Locals} → {s t : Ty} → BitVec s.width → Arms P S Γ s t → Env → Vals → Nat → Option (BitVec t.width)
  | _, _, _, _, .fallback e, ρ, l, F => evalX e ρ l F
  | _, _, _, vx, .case k e rest, ρ, l, F => if vx = k then evalX e ρ l F else armsX vx rest ρ l F
/-- A statement-position match: the taken arm's statements. -/
def armsVals {P : Params} {S : Spans} : {Γ : Locals} → {s : Ty} → BitVec s.width → ArmsS P S Γ s → Env → Vals → Nat → Option Vals
  | _, _, _, .fallback st, ρ, l, F => runVals st ρ l F
  | _, _, vx, .case k st rest, ρ, l, F => if vx = k then runVals st ρ l F else armsVals vx rest ρ l F
/-- The callee's values: each argument evaluated in the caller's scope and
bound to its parameter, in order. -/
def bindVals {P : Params} {S : Spans} : {Γ : Locals} → {ps : List (String × Ty)} → Args P S Γ ps → Env → Vals → Vals → Nat → Option Vals
  | _, _, .nil, _, _, acc, _ => some acc
  | _, _, .cons (x := x) a rest, ρ, l, acc, F => (evalX a ρ l F).bind fun x' => bindVals rest ρ l (acc.set x x'.toNat) F
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

/-- A term: `termParam`, `termConst`, `termBinary`, `termCmp`, `termIte`,
`termSelect` (`name[index]`, a span element at a symbolic 32-bit index)
with the width the Go node carries. -/
inductive Term
  | param (name : String) (w : Nat)
  | const (v : Nat) (w : Nat)
  | bin (op : TOp) (w : Nat) (l r : Term)
  | cmp (code : Cond) (w : Nat) (l r : Term)
  | ite (w : Nat) (c l r : Term)
  | select (span : String) (w : Nat) (idx : Term)
  deriving DecidableEq

def Term.width : Term → Nat
  | .param _ w => w
  | .const _ w => w
  | .bin _ w _ _ => w
  | .cmp _ w _ _ => w
  | .ite w _ _ _ => w
  | .select _ w _ => w

@[simp] theorem Term.width_param (n : String) (w : Nat) : (Term.param n w).width = w := rfl
@[simp] theorem Term.width_const (v w : Nat) : (Term.const v w).width = w := rfl
@[simp] theorem Term.width_bin (op : TOp) (w : Nat) (l r : Term) : (Term.bin op w l r).width = w := rfl
@[simp] theorem Term.width_cmp (c : Cond) (w : Nat) (l r : Term) : (Term.cmp c w l r).width = w := rfl
@[simp] theorem Term.width_ite (w : Nat) (c l r : Term) : (Term.ite w c l r).width = w := rfl
@[simp] theorem Term.width_select (n : String) (w : Nat) (i : Term) : (Term.select n w i).width = w := rfl

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
an `ite` picks an arm and masks it; a select reads the memory cell named
by the span and the index's low 32 bits (`elementValue`, the fixed memory
an element parameter also reads), masked to the width. -/
def Term.eval : Term → Env → Nat
  | .param name w, ρ => ρ name % 2 ^ w
  | .const v w, _ => v % 2 ^ w
  | .bin op w l r, ρ => Term.evalBin op w (l.eval ρ % 2 ^ w) (r.eval ρ % 2 ^ w)
  | .cmp code _ l r, ρ =>
    if condHolds code (BitVec.ofNat l.width (l.eval ρ)) (BitVec.ofNat l.width (r.eval ρ)) then 1 else 0
  | .ite w c l r, ρ => if c.eval ρ ≠ 0 then l.eval ρ % 2 ^ w else r.eval ρ % 2 ^ w
  | .select span w idx, ρ => ρ (elemName span (idx.eval ρ % 2 ^ 32)) % 2 ^ w

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

/-- `binaryTerm(op, left, right)`: two constant operands fold to the
constant the node evaluates to (at the node's width, the left operand's);
`x + 0`, `x - 0` and `0 + x` are `x` when `x` already has the node's
width; otherwise the node. -/
def Term.binary (op : TOp) (w : Nat) (l r : Term) : Term :=
  match l, r with
  | .const a wa, .const b wb => .const (Term.evalBin op w (a % 2 ^ wa % 2 ^ w) (b % 2 ^ wb % 2 ^ w)) w
  | l, .const b wb =>
    if b % 2 ^ wb = 0 ∧ (op = .add ∨ op = .sub) ∧ l.width = w then l else .bin op w l (.const b wb)
  | .const a wa, r =>
    if a % 2 ^ wa = 0 ∧ op = .add ∧ r.width = w then r else .bin op w (.const a wa) r
  | l, r => .bin op w l r

/-- `cmpTerm(code, left, right)`: two constant operands fold to the 1/0 the
comparison evaluates to, at the left operand's width. -/
def Term.cmpT (code : Cond) (w : Nat) (l r : Term) : Term :=
  match l, r with
  | .const a wa, .const b wb => .const ((Term.cmp code w (.const a wa) (.const b wb)).eval (fun _ => 0)) l.width
  | l, r => .cmp code w l r

/-- `iteTerm(cond, left, right)`: a constant condition picks an arm; the
node's width is the left arm's. -/
def Term.iteT (c l r : Term) : Term :=
  match c with
  | .const v wc => if v % 2 ^ wc ≠ 0 then l else r
  | c => .ite l.width c l r

/-- `selectTerm(span, index, width)`: a constant index names the element
parameter `v[k]` (the index's low 32 bits); a symbolic one is a select
over the index at width 32. -/
def Term.selectT (span : String) (w : Nat) (idx : Term) : Term :=
  match idx with
  | .const v wi => .param (elemName span (v % 2 ^ wi % 2 ^ 32)) w
  | idx => .select span w (truncate idx 32)

/-- `extendTerm(t, from, width, signed)` (asm/isa_semantics.go): the low
`src` bits at the wider width, then for a signed source shifted up and
arithmetically back down. -/
def extendTerm (t : Term) (src w : Nat) (signed : Bool) : Term :=
  let low := Term.binary .and w (adaptWidth t w) (.const (mask src) w)
  if !signed then low else
  Term.binary .sar w (Term.binary .shl w low (.const (w - src) w)) (.const (w - src) w)

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

/-- `loopBudget`: the iterations `lowerWhile` unrolls before giving up. -/
def loopBudget : Nat := 4096

/-- `lowerWhile`: lower the condition; a non-constant condition is outside
the subset (the data-dependent loop is summarized by another path); a
constant zero ends the loop; a constant non-zero runs one iteration and
goes on, at most `n` times. -/
def unroll (cond : Scope → Option Term) (body : Scope → Option Scope) : Nat → Scope → Option Scope
  | 0, _ => none
  | n + 1, σ =>
    (cond σ).bind fun tc =>
      match tc with
      | .const v w => if v % 2 ^ w = 0 then some σ else (body σ).bind (unroll cond body n)
      | _ => none

/-- `mergeValues`' select: `iteTerm(cond, whenTrue, whenFalse)` unless both
arms left the same term. The Go compares term objects (a local no arm
assigned is the same object on both sides); the model compares terms,
which differs only when two arms build equal terms separately, where the
select of equal arms is the same value. -/
def Term.selectArm (c a b : Term) : Term := if a = b then b else Term.iteT c a b

/-- `lowerConditionalStatement`'s and `lowerMatchStatement`'s merge: every
local takes the select of the arms' terms, the same term when the arms
agree. -/
def mergeScope (c : Term) (σT σF : Scope) : Scope :=
  fun y =>
    match σT y, σF y with
    | some a, some b => some (Term.selectArm c a b)
    | _, _ => σF y

/-- `matchArms`' condition for a literal case: `truncate(cmpTerm("eq",
scrutinee, literal), 1)`. -/
def caseCond (sx : Term) (w : Nat) (k : Nat) : Term := truncate (Term.cmpT .eq w sx (.const k w)) 1

mutual
/-- `oakLowering.lower` at the expression's own width, each case as the Go
spells it, `none` where the Go reports a construct outside the subset: an
identifier is its local's term through `adaptWidth` or, for a parameter,
`truncate(paramTerm(name, w), width)`, the identity at its own width; a
literal `constTerm(value, width)`; an infix `binaryTerm(op, left, right)`;
`/` and `%` by `2^k` a shift by `k` and a mask by `2^k - 1`; `-x` is
`0 - x`; `^x` and `!b` are `xor` with the mask; a conversion the operand
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
`iteTerm(truncate(cond, 1), afterTrue, afterFalse)`); a loop unrolls while
its lowered condition folds to a non-zero constant (`lowerWhile`); an
integer-constant match compares the scrutinee with each literal
(`matchArms`) and selects arm by arm into the fallback (`selectMatch`,
`lowerMatchStatement`); a span
element is `selectTerm(span, index at width 32, elemWidth)`
(`spanElementTerm`; a constant index is the element parameter `v[k]`, the
same cell under the same name), `len(v)` the length parameter. -/
def lowerT {P : Params} {S : Spans} : Scope → {Γ : Locals} → {t : Ty} → Expr P S Γ t → Option Term
  | σ, _, t, .var _ x _ =>
    some (match σ x with
    | some term => adaptWidth term t.width
    | none => .param x t.width)
  | _, _, t, .lit _ v => some (.const v.toNat t.width)
  | σ, _, t, .arith op a b => (lowerT σ a).bind fun l => (lowerT σ b).bind fun r => some (.binary (arithTOp op) t.width l r)
  | σ, _, t, .bit op a b _ => (lowerT σ a).bind fun l => (lowerT σ b).bind fun r => some (.binary (bitTOp op) t.width l r)
  | σ, _, t, .divPow2 a k _ _ => (lowerT σ a).bind fun l => some (.binary .shr t.width l (.const k t.width))
  | σ, _, t, .modPow2 a k _ _ => (lowerT σ a).bind fun l => some (.binary .and t.width l (.const (2 ^ k - 1) t.width))
  | σ, _, t, .neg a => (lowerT σ a).bind fun r => some (.binary .sub t.width (.const 0 t.width) r)
  | σ, _, t, .not a => (lowerT σ a).bind fun l => some (.binary .xor t.width l (.const (mask t.width) t.width))
  | σ, _, t, .conv (s := s) _ a =>
    (lowerT σ a).bind fun operand =>
      let converted :=
        if s.width < t.width then extendTerm operand s.width t.width s.signed
        else truncate operand t.width
      some (truncate converted t.width)
  | σ, _, _, .cmp (s := s) op l r =>
    (lowerT σ l).bind fun tl => (lowerT σ r).bind fun tr =>
      some (zeroExtend (truncate (.cmpT (codeOf s.signed op) s.width tl tr) 1) 1)
  | σ, _, _, .ite c a b =>
    (lowerT σ c).bind fun tc => (lowerT σ a).bind fun ta => (lowerT σ b).bind fun tb => some (.iteT tc ta tb)
  | σ, _, _, .letIn x v b => (lowerT σ v).bind fun tv => lowerT (σ.set x tv) b
  | σ, _, _, .call _ _ body args => (bindTerms σ args (fun _ => none)).bind fun σ' => lowerT σ' body
  | σ, _, _, .condSet c armT armF rest =>
    (lowerT σ c).bind fun tc => (runTerms σ armT).bind fun σT => (runTerms σ armF).bind fun σF =>
      lowerT (mergeScope tc σT σF) rest
  | σ, _, _, .whileLoop c body rest =>
    (unroll (fun σ₀ => lowerT σ₀ c) (fun σ₀ => runTerms σ₀ body) (loopBudget + 1) σ).bind fun σ' => lowerT σ' rest
  | σ, _, _, .matchInt x arms => (lowerT σ x).bind fun sx => armsT σ sx arms
  | σ, _, _, .matchSet x arms rest =>
    (lowerT σ x).bind fun sx => (armsST σ sx arms).bind fun σ' => lowerT σ' rest
  | σ, _, s, .elem _ v _ i => (lowerT σ i).bind fun ti => some (.selectT v s.width ti)
  | _, _, _, .len v _ => some (.param (lenName v) 32)
/-- Statements as `lowerLoopBody` executes them: `assignLocal` replaces the
local's term with the value lowered at its width, a conditional merges its
arms (`lowerConditionalStatement`), a loop unrolls (`lowerWhile`). -/
def runTerms {P : Params} {S : Spans} : Scope → {Γ : Locals} → Stmts P S Γ → Option Scope
  | σ, _, .nil => some σ
  | σ, _, .assign x _ e rest => (lowerT σ e).bind fun te => runTerms (σ.set x te) rest
  | σ, _, .cond c armT armF rest =>
    (lowerT σ c).bind fun tc => (runTerms σ armT).bind fun σT => (runTerms σ armF).bind fun σF =>
      runTerms (mergeScope tc σT σF) rest
  | σ, _, .loop c body rest =>
    (unroll (fun σ₀ => lowerT σ₀ c) (fun σ₀ => runTerms σ₀ body) (loopBudget + 1) σ).bind fun σ' => runTerms σ' rest
  | σ, _, .matchS x arms rest =>
    (lowerT σ x).bind fun sx => (armsST σ sx arms).bind fun σ' => runTerms σ' rest
/-- `selectMatch`: each arm's value merged into the fallback, the first
case outermost (`mergeValues` from the last case down). -/
def armsT {P : Params} {S : Spans} (σ : Scope) (sx : Term) : {Γ : Locals} → {s t : Ty} → Arms P S Γ s t → Option Term
  | _, _, _, .fallback e => lowerT σ e
  | _, s, _, .case k e rest =>
    (lowerT σ e).bind fun te => (armsT σ sx rest).bind fun tr => some (Term.selectArm (caseCond sx s.width k.toNat) te tr)
/-- `lowerMatchStatement`: every arm runs on the locals before the match,
and the locals after it are the arms' outcomes selected by the arms'
conditions, the fallback standing for every remaining value. -/
def armsST {P : Params} {S : Spans} (σ : Scope) (sx : Term) : {Γ : Locals} → {s : Ty} → ArmsS P S Γ s → Option Scope
  | _, _, .fallback st => runTerms σ st
  | _, s, .case k st rest =>
    (runTerms σ st).bind fun σk => (armsST σ sx rest).bind fun σr => some (mergeScope (caseCond sx s.width k.toNat) σk σr)
/-- `enterCall`'s `bound`: each argument lowered in the caller's scope at
the parameter's width and bound to the parameter, in order. -/
def bindTerms {P : Params} {S : Spans} (σ : Scope) : {Γ : Locals} → {ps : List (String × Ty)} → Args P S Γ ps → Scope → Option Scope
  | _, _, .nil, acc => some acc
  | _, _, .cons (x := x) a rest, acc => (lowerT σ a).bind fun ta => bindTerms σ rest (acc.set x ta)
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

theorem Term.binary_width (op : TOp) (w : Nat) (l r : Term) : (Term.binary op w l r).width = w := by
  unfold Term.binary
  split
  · rfl
  · split
    · rename_i h; exact h.2.2
    · rfl
  · split
    · rename_i h; exact h.2.2
    · rfl
  · rfl

theorem Term.cmpT_width (code : Cond) (w : Nat) {l r : Term} (hw : l.width = w) : (Term.cmpT code w l r).width = w := by
  unfold Term.cmpT
  split
  · exact hw
  · rfl

theorem Term.iteT_width {c l r : Term} (hw : r.width = l.width) : (Term.iteT c l r).width = l.width := by
  unfold Term.iteT
  split
  · split
    · rfl
    · exact hw
  · rfl

theorem Term.selectT_width (span : String) (w : Nat) (idx : Term) : (Term.selectT span w idx).width = w := by
  unfold Term.selectT
  split <;> rfl

theorem Term.selectArm_width {c a b : Term} (hw : b.width = a.width) : (Term.selectArm c a b).width = a.width := by
  unfold Term.selectArm
  split
  · rename_i h; rw [h]
  · exact Term.iteT_width hw

@[simp] theorem extendTerm_width (t : Term) (src w : Nat) (signed : Bool) :
    (extendTerm t src w signed).width = w := by
  unfold extendTerm; split <;> exact Term.binary_width _ _ _ _

mutual
theorem lowerT_width {P : Params} {S : Spans} {Γ : Locals} {t : Ty} (e : Expr P S Γ t) :
    ∀ (σ : Scope) (T : Term), lowerT σ e = some T → T.width = t.width := by
  intro σ T h
  match e with
  | .var t x h' =>
    simp only [lowerT, Option.some.injEq] at h
    subst h
    split <;> simp
  | .lit _ _ => simp only [lowerT, Option.some.injEq] at h; subst h; rfl
  | .arith _ a b =>
    simp only [lowerT, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨l, -, r, -, rfl⟩ := h
    exact Term.binary_width _ _ _ _
  | .bit _ a b _ =>
    simp only [lowerT, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨l, -, r, -, rfl⟩ := h
    exact Term.binary_width _ _ _ _
  | .divPow2 a _ _ _ =>
    simp only [lowerT, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨l, -, rfl⟩ := h
    exact Term.binary_width _ _ _ _
  | .modPow2 a _ _ _ =>
    simp only [lowerT, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨l, -, rfl⟩ := h
    exact Term.binary_width _ _ _ _
  | .neg a =>
    simp only [lowerT, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨r, -, rfl⟩ := h
    exact Term.binary_width _ _ _ _
  | .not a =>
    simp only [lowerT, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨l, -, rfl⟩ := h
    exact Term.binary_width _ _ _ _
  | .conv t a =>
    simp only [lowerT, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨operand, -, rfl⟩ := h
    exact truncate_width _ _
  | .cmp op l r =>
    simp only [lowerT, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨tl, -, tr, -, rfl⟩ := h
    exact zeroExtend_width _ _
  | .ite c a b =>
    simp only [lowerT, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨tc, -, ta, ha, tb, hb, rfl⟩ := h
    rw [Term.iteT_width (by rw [lowerT_width b _ _ hb, lowerT_width a _ _ ha]), lowerT_width a _ _ ha]
  | .letIn x v b =>
    simp only [lowerT, Option.bind_eq_some_iff] at h
    obtain ⟨tv, -, hb⟩ := h
    exact lowerT_width b _ _ hb
  | .call params ret body args =>
    simp only [lowerT, Option.bind_eq_some_iff] at h
    obtain ⟨σ', -, hb⟩ := h
    exact lowerT_width body _ _ hb
  | .condSet c armT armF rest =>
    simp only [lowerT, Option.bind_eq_some_iff] at h
    obtain ⟨tc, -, σT, -, σF, -, hr⟩ := h
    exact lowerT_width rest _ _ hr
  | .whileLoop c body rest =>
    simp only [lowerT, Option.bind_eq_some_iff] at h
    obtain ⟨σ', -, hr⟩ := h
    exact lowerT_width rest _ _ hr
  | .matchInt x arms =>
    simp only [lowerT, Option.bind_eq_some_iff] at h
    obtain ⟨sx, -, ha⟩ := h
    exact armsT_width arms σ sx T ha
  | .matchSet x arms rest =>
    simp only [lowerT, Option.bind_eq_some_iff] at h
    obtain ⟨sx, -, σ', -, hr⟩ := h
    exact lowerT_width rest _ _ hr
  | .elem _ _ _ i =>
    simp only [lowerT, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨ti, -, rfl⟩ := h
    exact Term.selectT_width _ _ _
  | .len _ _ => simp only [lowerT, Option.some.injEq] at h; subst h; rfl
termination_by structural e
theorem armsT_width {P : Params} {S : Spans} {Γ : Locals} {s t : Ty} (arms : Arms P S Γ s t) :
    ∀ (σ : Scope) (sx T : Term), armsT σ sx arms = some T → T.width = t.width := by
  intro σ sx T h
  match arms with
  | .fallback e => exact lowerT_width e σ T h
  | .case k e rest =>
    simp only [armsT, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨te, he, tr, hr, rfl⟩ := h
    rw [Term.selectArm_width (by rw [armsT_width rest σ sx tr hr, lowerT_width e σ te he]), lowerT_width e σ te he]
termination_by structural arms
end

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
  | select n w i => exact Nat.mod_lt _ (Nat.two_pow_pos w)

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
  | select n w₀ i =>
    simp only [truncate, Term.width_select] at heq ⊢
    simp only [heq, ite_false, Term.eval, Term.evalBin, mask_mod, Nat.mod_mod]
    rw [and_mask_of_le _ _ _ (Nat.le_refl w), Nat.mod_mod]

/-- The comparison a `truncate` re-widths is the same 1/0. -/
theorem truncate_cmp_eval (code : Cond) (w₀ w : Nat) (l r : Term) (ρ : Env) :
    (truncate (.cmp code w₀ l r) w).eval ρ = (Term.cmp code w₀ l r).eval ρ := by
  unfold truncate
  split
  · rfl
  · rfl

/-! ## The folding constructors evaluate as the nodes they fold -/

theorem Term.binary_topPositive (op : TOp) (w : Nat) {l r : Term} (hl : l.topPositive) (hr : r.topPositive) :
    (Term.binary op w l r).topPositive := by
  unfold Term.binary
  split
  · trivial
  · split
    · exact hl
    · trivial
  · split
    · exact hr
    · trivial
  · trivial

theorem Term.binary_eval (op : TOp) (w : Nat) {l r : Term} (ρ : Env) (hl : l.topPositive) (hr : r.topPositive) :
    (Term.binary op w l r).eval ρ = (Term.bin op w l r).eval ρ := by
  unfold Term.binary
  split
  · simp only [Term.eval]
    exact Nat.mod_eq_of_lt (Term.evalBin_lt _ _ _ _)
  · split
    · rename_i h
      obtain ⟨hb, hop, hw⟩ := h
      have hlt : l.eval ρ < 2 ^ w := hw ▸ Term.eval_lt l ρ hl
      simp only [Term.eval, hb, Nat.zero_mod, Nat.mod_eq_of_lt hlt]
      rcases hop with rfl | rfl
      · simp [Term.evalBin, Nat.mod_eq_of_lt hlt]
      · simp [Term.evalBin, Nat.add_mod_right, Nat.mod_eq_of_lt hlt]
    · rfl
  · split
    · rename_i h
      obtain ⟨ha, hop, hw⟩ := h
      subst hop
      have hlt : r.eval ρ < 2 ^ w := hw ▸ Term.eval_lt r ρ hr
      simp [Term.eval, Term.evalBin, ha, Nat.mod_eq_of_lt hlt]
    · rfl
  · rfl

theorem Term.cmpT_topPositive (code : Cond) (w : Nat) {l r : Term} (hw : 0 < w) : (Term.cmpT code w l r).topPositive := by
  unfold Term.cmpT
  split
  · trivial
  · exact hw

/-- A folded comparison re-widthed to 1 is the comparison's 1/0. -/
theorem truncate_cmpT_eval (code : Cond) (w : Nat) {l r : Term} (ρ : Env) (hw : l.width = w) (hpos : 0 < w) :
    (truncate (Term.cmpT code w l r) 1).eval ρ = (Term.cmp code w l r).eval ρ := by
  unfold Term.cmpT
  split
  · rename_i a wa b wb
    simp only [Term.width_const] at hw
    subst hw
    have h1 : 1 % 2 ^ wa = 1 := Nat.mod_eq_of_lt (Nat.one_lt_two_pow (Nat.pos_iff_ne_zero.mp hpos))
    unfold truncate
    split
    · simp only [Term.eval, Term.width_const]
      by_cases hc : condHolds code (BitVec.ofNat wa (a % 2 ^ wa)) (BitVec.ofNat wa (b % 2 ^ wb)) = true <;> simp [hc, h1]
    · simp only [Term.eval, Term.width_const]
      by_cases hc : condHolds code (BitVec.ofNat wa (a % 2 ^ wa)) (BitVec.ofNat wa (b % 2 ^ wb)) = true <;> simp [hc, h1]
  · exact truncate_cmp_eval _ _ _ _ _ _

theorem Term.iteT_topPositive {c l r : Term} (hl : l.topPositive) (hr : r.topPositive) : (Term.iteT c l r).topPositive := by
  unfold Term.iteT
  split
  · split
    · exact hl
    · exact hr
  · trivial

theorem Term.iteT_eval {c l r : Term} (ρ : Env) (hl : l.topPositive) (hr : r.topPositive) (hw : r.width = l.width) :
    (Term.iteT c l r).eval ρ = (Term.ite l.width c l r).eval ρ := by
  unfold Term.iteT
  split
  · rename_i v wc
    split
    · rename_i h
      have h' : (Term.const v wc).eval ρ ≠ 0 := by simpa [Term.eval] using h
      rw [Term.eval.eq_5, if_pos h', Nat.mod_eq_of_lt (Term.eval_lt l ρ hl)]
    · rename_i h
      have h' : ¬ (Term.const v wc).eval ρ ≠ 0 := by simpa [Term.eval] using h
      rw [Term.eval.eq_5, if_neg h', ← hw, Nat.mod_eq_of_lt (Term.eval_lt r ρ hr)]
  · rfl

theorem Term.selectT_topPositive (span : String) (w : Nat) (idx : Term) : (Term.selectT span w idx).topPositive := by
  unfold Term.selectT
  split <;> trivial

theorem Term.selectT_eval (span : String) (w : Nat) (idx : Term) (ρ : Env) :
    (Term.selectT span w idx).eval ρ = (Term.select span w (truncate idx 32)).eval ρ := by
  unfold Term.selectT
  split
  · rename_i v wi
    unfold truncate
    split
    · rename_i h
      simp only [Term.width_const] at h
      subst h
      simp [Term.eval, Nat.mod_mod]
    · simp [Term.eval, Nat.mod_mod]
  · rfl

theorem Term.selectArm_topPositive {c a b : Term} (ha : a.topPositive) (hb : b.topPositive) : (Term.selectArm c a b).topPositive := by
  unfold Term.selectArm
  split
  · exact hb
  · exact Term.iteT_topPositive ha hb

theorem Term.selectArm_eval {c a b : Term} (ρ : Env) (ha : a.topPositive) (hb : b.topPositive) (hw : b.width = a.width) :
    (Term.selectArm c a b).eval ρ = (Term.ite a.width c a b).eval ρ := by
  unfold Term.selectArm
  split
  · rename_i h
    subst h
    rw [Term.eval.eq_5]
    split <;> exact (Nat.mod_eq_of_lt (Term.eval_lt a ρ ha)).symm
  · exact Term.iteT_eval ρ ha hb hw

/-- A case's condition is 1 exactly when the scrutinee equals the literal. -/
theorem caseCond_eval (sx : Term) (w : Nat) (k vx : BitVec w) (ρ : Env) (hw : sx.width = w) (hpos : 0 < w)
    (hx : sx.eval ρ = vx.toNat) : (caseCond sx w k.toNat).eval ρ = if vx = k then 1 else 0 := by
  unfold caseCond
  rw [truncate_cmpT_eval _ _ ρ hw hpos]
  simp only [Term.eval]
  rw [hw, hx]
  simp only [BitVec.toNat_mod_cancel, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have : condHolds .eq vx k = decide (vx = k) := Bool.eq_iff_iff.mpr ((eq_holds_iff vx k).trans (by simp))
  rw [this]
  by_cases h : vx = k <;> simp [h]

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
  | select n w₀ i =>
    simp only [Term.width_select] at heq hle hlt hm hself
    simp only [zeroExtend, Term.width_select, heq, ite_false, Term.eval, Term.evalBin, hm, hlt, and_mask_of_le _ _ _ hle, Nat.mod_mod]
    rw [and_mask_of_le _ _ _ (Nat.le_refl w₀), Nat.mod_mod]

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

theorem adaptWidth_topPositive (t : Term) (w : Nat) (hw : 0 < w) (hp : t.topPositive) : (adaptWidth t w).topPositive := by
  unfold adaptWidth
  split
  · exact zeroExtend_topPositive t w hw hp
  · exact truncate_topPositive t w hw hp

theorem extendTerm_topPositive (t : Term) (src w : Nat) (signed : Bool) (hw : 0 < w) (ht : t.topPositive) :
    (extendTerm t src w signed).topPositive := by
  unfold extendTerm
  split
  · exact Term.binary_topPositive _ _ (adaptWidth_topPositive t w hw ht) trivial
  · exact Term.binary_topPositive _ _ (Term.binary_topPositive _ _ (Term.binary_topPositive _ _ (adaptWidth_topPositive t w hw ht) trivial) trivial) trivial

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

theorem mergeScope_wf {c : Term} {σT σF : Scope} (hT : σT.wf) (hF : σF.wf) : (mergeScope c σT σF).wf := by
  intro y term h
  unfold mergeScope at h
  split at h
  · rename_i a b ha hb
    cases h; exact Term.selectArm_topPositive (hT y a ha) (hF y b hb)
  · exact hF y term h

/-- Unrolling keeps scopes well formed when each iteration does. -/
theorem unroll_wf {cond : Scope → Option Term} {body : Scope → Option Scope}
    (hb : ∀ σ σ', σ.wf → body σ = some σ' → σ'.wf) :
    ∀ n σ σ', σ.wf → unroll cond body n σ = some σ' → σ'.wf := by
  intro n
  induction n with
  | zero => intro σ σ' _ h; simp [unroll] at h
  | succ n ih =>
    intro σ σ' hσ h
    simp only [unroll, Option.bind_eq_some_iff] at h
    obtain ⟨tc, -, h⟩ := h
    split at h
    · split at h
      · simp only [Option.some.injEq] at h; subst h; exact hσ
      · simp only [Option.bind_eq_some_iff] at h
        obtain ⟨σ₁, h1, h2⟩ := h
        exact ih σ₁ σ' (hb σ σ₁ hσ h1) h2
    · simp at h

mutual
theorem lowerT_topPositive {P : Params} {S : Spans} {Γ : Locals} {t : Ty} (e : Expr P S Γ t) :
    ∀ (σ : Scope) (T : Term), σ.wf → lowerT σ e = some T → T.topPositive := by
  intro σ T hσ h
  match e with
  | .var t x h' =>
    simp only [lowerT, Option.some.injEq] at h
    subst h
    split
    · rename_i term hterm; exact adaptWidth_topPositive term _ t.width_pos (hσ x term hterm)
    · trivial
  | .lit _ _ => simp only [lowerT, Option.some.injEq] at h; subst h; trivial
  | .arith _ a b =>
    simp only [lowerT, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨l, hl, r, hr, rfl⟩ := h
    exact Term.binary_topPositive _ _ (lowerT_topPositive a σ l hσ hl) (lowerT_topPositive b σ r hσ hr)
  | .bit _ a b _ =>
    simp only [lowerT, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨l, hl, r, hr, rfl⟩ := h
    exact Term.binary_topPositive _ _ (lowerT_topPositive a σ l hσ hl) (lowerT_topPositive b σ r hσ hr)
  | .divPow2 a _ _ _ =>
    simp only [lowerT, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨l, hl, rfl⟩ := h
    exact Term.binary_topPositive _ _ (lowerT_topPositive a σ l hσ hl) trivial
  | .modPow2 a _ _ _ =>
    simp only [lowerT, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨l, hl, rfl⟩ := h
    exact Term.binary_topPositive _ _ (lowerT_topPositive a σ l hσ hl) trivial
  | .neg a =>
    simp only [lowerT, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨r, hr, rfl⟩ := h
    exact Term.binary_topPositive _ _ trivial (lowerT_topPositive a σ r hσ hr)
  | .not a =>
    simp only [lowerT, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨l, hl, rfl⟩ := h
    exact Term.binary_topPositive _ _ (lowerT_topPositive a σ l hσ hl) trivial
  | .conv t a =>
    simp only [lowerT, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨operand, ho, rfl⟩ := h
    apply truncate_topPositive _ _ t.width_pos
    split
    · exact extendTerm_topPositive _ _ _ _ t.width_pos (lowerT_topPositive a σ operand hσ ho)
    · exact truncate_topPositive _ _ t.width_pos (lowerT_topPositive a σ operand hσ ho)
  | .cmp op l r =>
    simp only [lowerT, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨tl, -, tr, -, rfl⟩ := h
    exact zeroExtend_topPositive _ _ (by decide) (truncate_topPositive _ _ (by decide) (Term.cmpT_topPositive _ _ (Ty.width_pos _)))
  | .ite c a b =>
    simp only [lowerT, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨tc, -, ta, ha, tb, hb, rfl⟩ := h
    exact Term.iteT_topPositive (lowerT_topPositive a σ ta hσ ha) (lowerT_topPositive b σ tb hσ hb)
  | .letIn x v b =>
    simp only [lowerT, Option.bind_eq_some_iff] at h
    obtain ⟨tv, hv, hb⟩ := h
    exact lowerT_topPositive b _ T (Scope.wf_set hσ (lowerT_topPositive v σ tv hσ hv)) hb
  | .call params ret body args =>
    simp only [lowerT, Option.bind_eq_some_iff] at h
    obtain ⟨σ', hσ', hb⟩ := h
    exact lowerT_topPositive body _ T (bindTerms_wf args σ _ σ' hσ Scope.wf_empty hσ') hb
  | .condSet c armT armF rest =>
    simp only [lowerT, Option.bind_eq_some_iff] at h
    obtain ⟨tc, -, σT, hT, σF, hF, hr⟩ := h
    exact lowerT_topPositive rest _ T (mergeScope_wf (runTerms_wf armT σ σT hσ hT) (runTerms_wf armF σ σF hσ hF)) hr
  | .whileLoop c body rest =>
    simp only [lowerT, Option.bind_eq_some_iff] at h
    obtain ⟨σ', hσ', hr⟩ := h
    exact lowerT_topPositive rest _ T (unroll_wf (fun σ₀ σ₁ h₀ h₁ => runTerms_wf body σ₀ σ₁ h₀ h₁) _ σ σ' hσ hσ') hr
  | .matchInt x arms =>
    simp only [lowerT, Option.bind_eq_some_iff] at h
    obtain ⟨sx, -, ha⟩ := h
    exact armsT_topPositive arms σ sx T hσ ha
  | .matchSet x arms rest =>
    simp only [lowerT, Option.bind_eq_some_iff] at h
    obtain ⟨sx, -, σ', h', hr⟩ := h
    exact lowerT_topPositive rest _ T (armsST_wf arms σ sx σ' hσ h') hr
  | .elem _ _ _ i =>
    simp only [lowerT, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨ti, -, rfl⟩ := h
    exact Term.selectT_topPositive _ _ _
  | .len _ _ => simp only [lowerT, Option.some.injEq] at h; subst h; trivial
termination_by structural e
theorem bindTerms_wf {P : Params} {S : Spans} {Γ : Locals} {ps : List (String × Ty)} (args : Args P S Γ ps) :
    ∀ (σ acc σ' : Scope), σ.wf → acc.wf → bindTerms σ args acc = some σ' → σ'.wf := by
  intro σ acc σ' hσ hacc h
  match args with
  | .nil => simp only [bindTerms, Option.some.injEq] at h; subst h; exact hacc
  | .cons a rest =>
    simp only [bindTerms, Option.bind_eq_some_iff] at h
    obtain ⟨ta, ha, hr⟩ := h
    exact bindTerms_wf rest σ _ σ' hσ (Scope.wf_set hacc (lowerT_topPositive a σ ta hσ ha)) hr
termination_by structural args
theorem runTerms_wf {P : Params} {S : Spans} {Γ : Locals} (st : Stmts P S Γ) :
    ∀ (σ σ' : Scope), σ.wf → runTerms σ st = some σ' → σ'.wf := by
  intro σ σ' hσ h
  match st with
  | .nil => simp only [runTerms, Option.some.injEq] at h; subst h; exact hσ
  | .assign x hx e rest =>
    simp only [runTerms, Option.bind_eq_some_iff] at h
    obtain ⟨te, he, hr⟩ := h
    exact runTerms_wf rest _ σ' (Scope.wf_set hσ (lowerT_topPositive e σ te hσ he)) hr
  | .cond c armT armF rest =>
    simp only [runTerms, Option.bind_eq_some_iff] at h
    obtain ⟨tc, -, σT, hT, σF, hF, hr⟩ := h
    exact runTerms_wf rest _ σ' (mergeScope_wf (runTerms_wf armT σ σT hσ hT) (runTerms_wf armF σ σF hσ hF)) hr
  | .loop c body rest =>
    simp only [runTerms, Option.bind_eq_some_iff] at h
    obtain ⟨σ₁, hσ₁, hr⟩ := h
    exact runTerms_wf rest _ σ' (unroll_wf (fun σ₀ σ₂ h₀ h₂ => runTerms_wf body σ₀ σ₂ h₀ h₂) _ σ σ₁ hσ hσ₁) hr
  | .matchS x arms rest =>
    simp only [runTerms, Option.bind_eq_some_iff] at h
    obtain ⟨sx, -, σ₁, h₁, hr⟩ := h
    exact runTerms_wf rest _ σ' (armsST_wf arms σ sx σ₁ hσ h₁) hr
termination_by structural st
theorem armsT_topPositive {P : Params} {S : Spans} {Γ : Locals} {s t : Ty} (arms : Arms P S Γ s t) :
    ∀ (σ : Scope) (sx T : Term), σ.wf → armsT σ sx arms = some T → T.topPositive := by
  intro σ sx T hσ h
  match arms with
  | .fallback e => exact lowerT_topPositive e σ T hσ h
  | .case k e rest =>
    simp only [armsT, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨te, he, tr, hr, rfl⟩ := h
    exact Term.selectArm_topPositive (lowerT_topPositive e σ te hσ he) (armsT_topPositive rest σ sx tr hσ hr)
termination_by structural arms
theorem armsST_wf {P : Params} {S : Spans} {Γ : Locals} {s : Ty} (arms : ArmsS P S Γ s) :
    ∀ (σ : Scope) (sx : Term) (σ' : Scope), σ.wf → armsST σ sx arms = some σ' → σ'.wf := by
  intro σ sx σ' hσ h
  match arms with
  | .fallback st => exact runTerms_wf st σ σ' hσ h
  | .case k st rest =>
    simp only [armsST, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨σk, hk, σr, hr, rfl⟩ := h
    exact mergeScope_wf (runTerms_wf st σ σk hσ hk) (armsST_wf rest σ sx σr hσ hr)
termination_by structural arms
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

/-- Unrolling agrees with the fuel-indexed loop: while the folded condition
is a non-zero constant the extraction's condition is `1` and both run the
body; a zero constant is `0` and both stop. -/
theorem unroll_agree {Γ : Locals} {ρ : Env} {condT : Scope → Option Term} {bodyT : Scope → Option Scope}
    {condX : Vals → Option (BitVec 1)} {bodyX : Vals → Option Vals}
    (hc : ∀ σ l tc, Agree Γ σ ρ l → condT σ = some tc → ∃ cv, condX l = some cv ∧ tc.eval ρ = cv.toNat)
    (hb : ∀ σ l σ', Agree Γ σ ρ l → bodyT σ = some σ' → ∃ l', bodyX l = some l' ∧ Agree Γ σ' ρ l') :
    ∀ n F σ l σ', n ≤ F → Agree Γ σ ρ l → unroll condT bodyT n σ = some σ' →
      ∃ l', loopX condX bodyX F l = some l' ∧ Agree Γ σ' ρ l' := by
  intro n
  induction n with
  | zero => intro F σ l σ' _ _ h; simp [unroll] at h
  | succ n ih =>
    intro F σ l σ' hF hA h
    obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
    simp only [unroll, Option.bind_eq_some_iff] at h
    obtain ⟨tc, htc, h⟩ := h
    obtain ⟨cv, hcv, heq⟩ := hc σ l tc hA htc
    simp only [loopX, hcv, Option.bind_some]
    split at h
    · rename_i v w
      simp only [Term.eval] at heq
      split at h
      · rename_i hz
        simp only [Option.some.injEq] at h
        subst h
        have hcv0 : cv.toNat = 0 := by rw [← heq, hz]
        have hne : cv ≠ 1 := fun h1 => (BitVec1_ne_zero_iff cv).mpr h1 hcv0
        rw [if_neg hne]
        exact ⟨l, rfl, hA⟩
      · rename_i hnz
        have h1 : cv = 1 := (BitVec1_ne_zero_iff cv).mp (by rw [← heq]; exact hnz)
        rw [if_pos h1]
        simp only [Option.bind_eq_some_iff] at h
        obtain ⟨σ₁, hσ₁, hrest⟩ := h
        obtain ⟨l₁, hl₁, hA₁⟩ := hb σ l σ₁ hA hσ₁
        rw [hl₁, Option.bind_some]
        exact ih F' σ₁ l₁ σ' (by omega) hA₁ hrest
    · simp at h

mutual
/-- The merge of two arms agrees with the selected arm's values. -/
theorem merge_agree {Γ : Locals} {σT σF : Scope} {ρ : Env} {lT lF : Vals} (c : Term) (cv : BitVec 1) (hc : c.eval ρ = cv.toNat)
    (hT : Agree Γ σT ρ lT) (hF : Agree Γ σF ρ lF) :
    Agree Γ (mergeScope c σT σF) ρ (if cv = 1 then lT else lF) := by
  constructor
  · intro y hy
    unfold mergeScope
    rw [hT.1 y hy, hF.1 y hy]
  · intro y t hy
    obtain ⟨a, haσ, haw, hap, hav⟩ := hT.2 y t hy
    obtain ⟨b, hbσ, hbw, hbp, hbv⟩ := hF.2 y t hy
    unfold mergeScope
    rw [haσ, hbσ]
    have hba : b.width = a.width := hbw.trans haw.symm
    refine ⟨Term.selectArm c a b, rfl, by rw [Term.selectArm_width hba, haw], Term.selectArm_topPositive hap hbp, ?_⟩
    have key : (c.eval ρ ≠ 0) ↔ (cv = 1) := by rw [hc]; exact BitVec1_ne_zero_iff cv
    rw [Term.selectArm_eval ρ hap hbp hba, Term.eval.eq_5]
    by_cases h1 : cv = 1
    · rw [if_pos (key.mpr h1), if_pos h1, hav, ← hav, Nat.mod_eq_of_lt (Term.eval_lt a ρ hap)]
    · rw [if_neg (fun hne => h1 (key.mp hne)), if_neg h1, hbv, ← hbv, haw.trans hbw.symm,
        Nat.mod_eq_of_lt (Term.eval_lt b ρ hbp)]

/-- The verifier's lowering and the extraction's reading agree on every
expression of the shared subset, in every agreeing scope and under any
fuel above the unrolling budget: whatever the lowering admits, the
extraction computes, and the term evaluates to it. The seam of
`126-verification-chain.md` §4, closed for expressions, locals, calls,
statement-level conditionals, span elements and counted loops. -/
theorem lowerT_eval {P : Params} {S : Spans} {Γ : Locals} {t : Ty} (e : Expr P S Γ t) :
    ∀ (σ : Scope) (ρ : Env) (l : Vals) (F : Nat) (T : Term), loopBudget < F → Agree Γ σ ρ l → lowerT σ e = some T →
      ∃ v, evalX e ρ l F = some v ∧ T.eval ρ = v.toNat := by
  intro σ ρ l F T hF hA h
  match e with
  | .var t x h' =>
    simp only [lowerT, Option.some.injEq] at h
    subst h
    refine ⟨BitVec.ofNat t.width (varX Γ ρ l x), by simp only [evalX], ?_⟩
    simp only [varX]
    cases hΓ : Γ x with
    | none =>
      rw [hA.1 x hΓ]
      simp [Term.eval]
    | some t' =>
      have ht : t' = t := by simp [resolve, hΓ] at h'; exact h'
      subst ht
      obtain ⟨term, hσ, hw, hp, hv⟩ := hA.2 x t' hΓ
      rw [hσ]
      simp only [adaptWidth, hw, Nat.lt_irrefl, if_false, truncate_self term _ hw, hv, BitVec.toNat_ofNat]
      rw [← hv, Nat.mod_eq_of_lt (hw ▸ Term.eval_lt term ρ hp)]
  | .lit t v =>
    simp only [lowerT, Option.some.injEq] at h
    subst h
    exact ⟨v, by simp only [evalX], by simp [Term.eval]⟩
  | .arith (t := t) op a b =>
    simp only [lowerT, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨ta, ha, tb, hb, rfl⟩ := h
    obtain ⟨va, hva, iha⟩ := lowerT_eval a σ ρ l F ta hF hA ha
    obtain ⟨vb, hvb, ihb⟩ := lowerT_eval b σ ρ l F tb hF hA hb
    refine ⟨arithX op va vb, by simp only [evalX, hva, hvb, Option.bind_some], ?_⟩
    rw [Term.binary_eval _ _ ρ (lowerT_topPositive a σ ta (Agree.wf hA) ha) (lowerT_topPositive b σ tb (Agree.wf hA) hb)]
    cases op <;> simp [arithX, arithTOp, Term.eval, Term.evalBin, iha, ihb, Nat.add_comm]
  | .bit (t := t) op a b hs =>
    simp only [lowerT, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨ta, ha, tb, hb, rfl⟩ := h
    obtain ⟨va, hva, iha⟩ := lowerT_eval a σ ρ l F ta hF hA ha
    obtain ⟨vb, hvb, ihb⟩ := lowerT_eval b σ ρ l F tb hF hA hb
    have hw := va.isLt
    refine ⟨bitX op va vb, by simp only [evalX, hva, hvb, Option.bind_some], ?_⟩
    rw [Term.binary_eval _ _ ρ (lowerT_topPositive a σ ta (Agree.wf hA) ha) (lowerT_topPositive b σ tb (Agree.wf hA) hb)]
    cases op <;> simp only [bitX, bitTOp, Term.eval, Term.evalBin, iha, ihb, BitVec.toNat_mod_cancel]
    · rw [BitVec.toNat_and]; exact Nat.mod_eq_of_lt (Nat.and_lt_two_pow _ vb.isLt)
    · rw [BitVec.toNat_or]; exact Nat.mod_eq_of_lt (Nat.or_lt_two_pow hw vb.isLt)
    · rw [BitVec.toNat_xor]; exact Nat.mod_eq_of_lt (Nat.xor_lt_two_pow hw vb.isLt)
    · rw [BitVec.toNat_shiftLeft]
    · rw [BitVec.toNat_ushiftRight]
      exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _) hw)
  | .divPow2 (t := t) a k hk hu =>
    simp only [lowerT, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨ta, ha, rfl⟩ := h
    obtain ⟨va, hva, iha⟩ := lowerT_eval a σ ρ l F ta hF hA ha
    have hw := va.isLt
    have hk2 : 2 ^ k < 2 ^ t.width := Nat.pow_lt_pow_right (by decide) hk
    have hkw : k < 2 ^ t.width := Nat.lt_of_lt_of_le hk (Nat.le_of_lt Nat.lt_two_pow_self)
    refine ⟨va / BitVec.ofNat t.width (2 ^ k), by simp only [evalX, hva, Option.bind_some], ?_⟩
    rw [Term.binary_eval .shr t.width (r := .const k t.width) ρ (lowerT_topPositive a σ ta (Agree.wf hA) ha) trivial]
    simp only [Term.eval, Term.evalBin, iha, BitVec.toNat_mod_cancel, BitVec.toNat_udiv,
      BitVec.toNat_ofNat, Nat.mod_mod, Nat.mod_eq_of_lt hkw, Nat.mod_eq_of_lt hk, Nat.mod_eq_of_lt hk2,
      Nat.shiftRight_eq_div_pow]
    exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hw)
  | .modPow2 (t := t) a k hk hu =>
    simp only [lowerT, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨ta, ha, rfl⟩ := h
    obtain ⟨va, hva, iha⟩ := lowerT_eval a σ ρ l F ta hF hA ha
    have hk2 : 2 ^ k < 2 ^ t.width := Nat.pow_lt_pow_right (by decide) hk
    have hm : 2 ^ k - 1 < 2 ^ t.width := by omega
    refine ⟨va % BitVec.ofNat t.width (2 ^ k), by simp only [evalX, hva, Option.bind_some], ?_⟩
    rw [Term.binary_eval .and t.width (r := .const (2 ^ k - 1) t.width) ρ (lowerT_topPositive a σ ta (Agree.wf hA) ha) trivial]
    simp only [Term.eval, Term.evalBin, iha, BitVec.toNat_mod_cancel, BitVec.toNat_umod,
      BitVec.toNat_ofNat, Nat.mod_mod, Nat.mod_eq_of_lt hm, Nat.mod_eq_of_lt hk2,
      Nat.and_two_pow_sub_one_eq_mod]
    exact Nat.mod_eq_of_lt (Nat.lt_trans (Nat.mod_lt _ (Nat.two_pow_pos k)) hk2)
  | .neg (t := t) a =>
    simp only [lowerT, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨ta, ha, rfl⟩ := h
    obtain ⟨va, hva, iha⟩ := lowerT_eval a σ ρ l F ta hF hA ha
    refine ⟨0 - va, by simp only [evalX, hva, Option.bind_some], ?_⟩
    rw [Term.binary_eval .sub t.width (l := .const 0 t.width) ρ trivial (lowerT_topPositive a σ ta (Agree.wf hA) ha)]
    simp [Term.eval, Term.evalBin, iha]
  | .not (t := t) a =>
    simp only [lowerT, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨ta, ha, rfl⟩ := h
    obtain ⟨va, hva, iha⟩ := lowerT_eval a σ ρ l F ta hF hA ha
    have hx : va.toNat ^^^ mask t.width = (~~~ va).toNat := by
      rw [← BitVec.xor_allOnes, BitVec.toNat_xor, BitVec.toNat_allOnes]; rfl
    refine ⟨~~~ va, by simp only [evalX, hva, Option.bind_some], ?_⟩
    rw [Term.binary_eval .xor t.width (r := .const (mask t.width) t.width) ρ (lowerT_topPositive a σ ta (Agree.wf hA) ha) trivial]
    simp only [Term.eval, Term.evalBin, iha, BitVec.toNat_mod_cancel, mask_mod, hx]
  | .conv (s := s) t a =>
    simp only [lowerT, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨ta, ha, rfl⟩ := h
    obtain ⟨va, hva, iha⟩ := lowerT_eval a σ ρ l F ta hF hA ha
    have hs := s.width_pos
    have hta := lowerT_topPositive a σ ta (Agree.wf hA) ha
    have hwa := lowerT_width a σ ta ha
    refine ⟨convX s t va, by simp only [evalX, hva, Option.bind_some], ?_⟩
    simp only [convX]
    rw [truncate_self _ _ (by split <;> simp)]
    by_cases hlt : s.width < t.width
    · simp only [hlt, if_true]
      unfold extendTerm
      simp only [adaptWidth, hwa, hlt, if_true]
      have hze : (zeroExtend ta t.width).topPositive := zeroExtend_topPositive _ _ t.width_pos hta
      have hlowp : (Term.binary .and t.width (zeroExtend ta t.width) (.const (mask s.width) t.width)).topPositive :=
        Term.binary_topPositive _ _ hze trivial
      have hlow := zeroExtend_masked_eval ta s.width t.width ρ hwa (Nat.le_of_lt hlt)
      rw [iha, BitVec.toNat_mod_cancel] at hlow
      rw [← Term.binary_eval .and t.width (r := .const (mask s.width) t.width) ρ hze trivial] at hlow
      have hxw : va.toNat < 2 ^ t.width :=
        Nat.lt_of_lt_of_le va.isLt (Nat.pow_le_pow_right (by decide) (Nat.le_of_lt hlt))
      by_cases hsig : s.signed = true
      · simp only [hsig, Bool.not_true, Bool.false_eq_true, if_false, if_true]
        have hsh : (t.width - s.width) % 2 ^ t.width % t.width = t.width - s.width := by
          have : t.width - s.width < 2 ^ t.width := Nat.lt_of_le_of_lt (Nat.sub_le _ _) Nat.lt_two_pow_self
          rw [Nat.mod_eq_of_lt this, Nat.mod_eq_of_lt (by omega)]
        have hsh' : (t.width - s.width) % 2 ^ t.width % 2 ^ t.width % t.width = t.width - s.width := by
          rw [Nat.mod_mod, hsh]
        rw [Term.binary_eval .sar t.width (r := .const (t.width - s.width) t.width) ρ
            (Term.binary_topPositive .shl t.width (r := .const (t.width - s.width) t.width) hlowp trivial) trivial,
          Term.eval.eq_3, Term.binary_eval .shl t.width (r := .const (t.width - s.width) t.width) ρ hlowp trivial,
          Term.eval.eq_3, hlow]
        simp only [Term.eval, Term.evalBin, hsh, hsh', Nat.mod_mod]
        rw [← BitVec.toNat_setWidth t.width va, ← BitVec.toNat_shiftLeft, BitVec.ofNat_toNat,
          BitVec.setWidth_eq, sshiftRight_shiftLeft_setWidth _ _ hs (Nat.le_of_lt hlt), BitVec.toNat_mod_cancel]
      · have hsig' : s.signed = false := by simpa using hsig
        simp only [hsig', Bool.not_false, Bool.false_eq_true, if_false, if_true, BitVec.toNat_setWidth, hlow,
          Nat.mod_eq_of_lt hxw]
    · simp only [hlt, if_false]
      rw [truncate_eval _ _ _ t.width_pos (by rw [hwa]; omega) hta, iha, BitVec.toNat_setWidth]
  | .cmp (s := s) op lhs rhs =>
    simp only [lowerT, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨tl, hl, tr, hr, rfl⟩ := h
    obtain ⟨vl, hvl, ihl⟩ := lowerT_eval lhs σ ρ l F tl hF hA hl
    obtain ⟨vr, hvr, ihr⟩ := lowerT_eval rhs σ ρ l F tr hF hA hr
    refine ⟨BitVec.ofBool (cmpX s.signed op vl vr), by simp only [evalX, hvl, hvr, Option.bind_some], ?_⟩
    rw [zeroExtend_self _ _ (truncate_width _ _), truncate_cmpT_eval _ _ ρ (lowerT_width lhs σ tl hl) s.width_pos]
    simp only [Term.eval, ihl, ihr]
    rw [lowerT_width lhs σ tl hl]
    simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq, codeOf_holds]
    cases cmpX s.signed op vl vr <;> simp
  | .ite (t := t) c a b =>
    simp only [lowerT, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨tc, hc, ta, ha, tb, hb, rfl⟩ := h
    obtain ⟨vc, hvc, ihc⟩ := lowerT_eval c σ ρ l F tc hF hA hc
    obtain ⟨va, hva, iha⟩ := lowerT_eval a σ ρ l F ta hF hA ha
    obtain ⟨vb, hvb, ihb⟩ := lowerT_eval b σ ρ l F tb hF hA hb
    have hwa := lowerT_width a σ ta ha
    have hwb := lowerT_width b σ tb hb
    refine ⟨if vc = 1 then va else vb, ?_, ?_⟩
    · simp only [evalX, hvc, Option.bind_some]
      by_cases h1 : vc = 1
      · rw [if_pos h1, if_pos h1, hva]
      · rw [if_neg h1, if_neg h1, hvb]
    · rw [Term.iteT_eval ρ (lowerT_topPositive a σ ta (Agree.wf hA) ha) (lowerT_topPositive b σ tb (Agree.wf hA) hb)
        (by rw [hwb, hwa]), Term.eval.eq_5, hwa]
      have key := BitVec1_ne_zero_iff vc
      by_cases h1 : vc = 1
      · have h' : tc.eval ρ ≠ 0 := by rw [ihc]; exact key.mpr h1
        rw [if_pos h', if_pos h1, iha, BitVec.toNat_mod_cancel]
      · have h' : ¬ tc.eval ρ ≠ 0 := by rw [ihc]; exact fun hne => h1 (key.mp hne)
        rw [if_neg h', if_neg h1, ihb, BitVec.toNat_mod_cancel]
  | .letIn (s := s) (t := t) x v b =>
    simp only [lowerT, Option.bind_eq_some_iff] at h
    obtain ⟨tv, hv, hb⟩ := h
    obtain ⟨vv, hvv, ihv⟩ := lowerT_eval v σ ρ l F tv hF hA hv
    obtain ⟨vb, hvb, ihb⟩ := lowerT_eval b _ ρ _ F T hF
      (Agree.set hA x (lowerT_width v σ tv hv) (lowerT_topPositive v σ tv (Agree.wf hA) hv) ihv) hb
    exact ⟨vb, by simp only [evalX, hvv, Option.bind_some, hvb], ihb⟩
  | .call params ret body args =>
    simp only [lowerT, Option.bind_eq_some_iff] at h
    obtain ⟨σ', hσ', hb⟩ := h
    obtain ⟨l', hl', hA'⟩ := bindArgs_agree args σ ρ l F hF hA _ _ (fun _ => 0) (Agree.empty ρ _) σ' hσ'
    obtain ⟨vb, hvb, ihb⟩ := lowerT_eval body _ ρ _ F T hF hA' hb
    exact ⟨vb, by simp only [evalX, hl', Option.bind_some, hvb], ihb⟩
  | .condSet c armT armF rest =>
    simp only [lowerT, Option.bind_eq_some_iff] at h
    obtain ⟨tc, hc, σT, hT, σF, hFm, hr⟩ := h
    obtain ⟨cv, hcv, ihc⟩ := lowerT_eval c σ ρ l F tc hF hA hc
    obtain ⟨lT, hlT, hAT⟩ := runTerms_agree armT σ ρ l F hF hA σT hT
    obtain ⟨lF, hlF, hAF⟩ := runTerms_agree armF σ ρ l F hF hA σF hFm
    have hM : Agree Γ (mergeScope tc σT σF) ρ (if cv = 1 then lT else lF) := merge_agree tc cv ihc hAT hAF
    obtain ⟨vr, hvr, ihr⟩ := lowerT_eval rest _ ρ _ F T hF hM hr
    refine ⟨vr, ?_, ihr⟩
    simp only [evalX, hcv, Option.bind_some]
    by_cases h1 : cv = 1
    · rw [if_pos h1] at hvr; rw [if_pos h1, hlT, Option.bind_some, hvr]
    · rw [if_neg h1] at hvr; rw [if_neg h1, hlF, Option.bind_some, hvr]
  | .whileLoop c body rest =>
    simp only [lowerT, Option.bind_eq_some_iff] at h
    obtain ⟨σ', hσ', hr⟩ := h
    have hc : ∀ σ₀ l₀ tc, Agree Γ σ₀ ρ l₀ → lowerT σ₀ c = some tc → ∃ cv, evalX c ρ l₀ F = some cv ∧ tc.eval ρ = cv.toNat :=
      fun σ₀ l₀ tc hA₀ h₀ => lowerT_eval c σ₀ ρ l₀ F tc hF hA₀ h₀
    have hb : ∀ σ₀ l₀ σ₁, Agree Γ σ₀ ρ l₀ → runTerms σ₀ body = some σ₁ → ∃ l₁, runVals body ρ l₀ F = some l₁ ∧ Agree Γ σ₁ ρ l₁ :=
      fun σ₀ l₀ σ₁ hA₀ h₀ => runTerms_agree body σ₀ ρ l₀ F hF hA₀ σ₁ h₀
    obtain ⟨l', hl', hA'⟩ := unroll_agree hc hb (loopBudget + 1) F σ l σ' (by omega) hA hσ'
    obtain ⟨vr, hvr, ihr⟩ := lowerT_eval rest _ ρ _ F T hF hA' hr
    exact ⟨vr, by simp only [evalX, hl', Option.bind_some, hvr], ihr⟩
  | .matchInt x arms =>
    simp only [lowerT, Option.bind_eq_some_iff] at h
    obtain ⟨sx, hx, ha⟩ := h
    obtain ⟨vx, hvx, ihx⟩ := lowerT_eval x σ ρ l F sx hF hA hx
    obtain ⟨v, hv, ihv⟩ := armsT_eval arms σ sx ρ l F T hF hA vx (lowerT_width x σ sx hx) ihx ha
    exact ⟨v, by simp only [evalX, hvx, Option.bind_some, hv], ihv⟩
  | .matchSet x arms rest =>
    simp only [lowerT, Option.bind_eq_some_iff] at h
    obtain ⟨sx, hx, σ', h', hr⟩ := h
    obtain ⟨vx, hvx, ihx⟩ := lowerT_eval x σ ρ l F sx hF hA hx
    obtain ⟨l', hl', hA'⟩ := armsST_agree arms σ sx ρ l F hF hA vx (lowerT_width x σ sx hx) ihx σ' h'
    obtain ⟨vr, hvr, ihr⟩ := lowerT_eval rest _ ρ _ F T hF hA' hr
    exact ⟨vr, by simp only [evalX, hvx, Option.bind_some, hl', hvr], ihr⟩
  | .elem s v hv i =>
    simp only [lowerT, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨ti, hi, rfl⟩ := h
    obtain ⟨vi, hvi, ihi⟩ := lowerT_eval i σ ρ l F ti hF hA hi
    have hlt : vi.toNat < 2 ^ 32 := vi.isLt
    refine ⟨BitVec.ofNat s.width (ρ (elemName v vi.toNat)), by simp only [evalX, hvi, Option.bind_some], ?_⟩
    rw [Term.selectT_eval]
    simp only [Term.eval]
    rw [truncate_self ti 32 (by rw [lowerT_width i σ ti hi]; rfl), ihi, Nat.mod_eq_of_lt hlt, BitVec.toNat_ofNat]
  | .len v hv =>
    simp only [lowerT, Option.some.injEq] at h
    subst h
    exact ⟨BitVec.ofNat 32 (ρ (lenName v)), by simp only [evalX], (BitVec.toNat_ofNat _ _).symm⟩
termination_by structural e
/-- Running statements keeps the scope agreeing. -/
theorem runTerms_agree {P : Params} {S : Spans} {Γ : Locals} (st : Stmts P S Γ) :
    ∀ (σ : Scope) (ρ : Env) (l : Vals) (F : Nat), loopBudget < F → Agree Γ σ ρ l → ∀ σ', runTerms σ st = some σ' →
      ∃ l', runVals st ρ l F = some l' ∧ Agree Γ σ' ρ l' := by
  intro σ ρ l F hF hA σ' h
  match st with
  | .nil =>
    simp only [runTerms, Option.some.injEq] at h
    subst h
    exact ⟨l, by simp only [runVals], hA⟩
  | .assign x hx e rest =>
    simp only [runTerms, Option.bind_eq_some_iff] at h
    obtain ⟨te, he, hr⟩ := h
    obtain ⟨ve, hve, ihe⟩ := lowerT_eval e σ ρ l F te hF hA he
    have hA' := Agree.set hA x (lowerT_width e σ te he) (lowerT_topPositive e σ te (Agree.wf hA) he) ihe
    rw [Locals.set_same hx] at hA'
    obtain ⟨l', hl', hA''⟩ := runTerms_agree rest _ ρ _ F hF hA' σ' hr
    exact ⟨l', by simp only [runVals, hve, Option.bind_some, hl'], hA''⟩
  | .cond c armT armF rest =>
    simp only [runTerms, Option.bind_eq_some_iff] at h
    obtain ⟨tc, hc, σT, hT, σF, hFm, hr⟩ := h
    obtain ⟨cv, hcv, ihc⟩ := lowerT_eval c σ ρ l F tc hF hA hc
    obtain ⟨lT, hlT, hAT⟩ := runTerms_agree armT σ ρ l F hF hA σT hT
    obtain ⟨lF, hlF, hAF⟩ := runTerms_agree armF σ ρ l F hF hA σF hFm
    have hM : Agree Γ (mergeScope tc σT σF) ρ (if cv = 1 then lT else lF) := merge_agree tc cv ihc hAT hAF
    obtain ⟨l', hl', hA'⟩ := runTerms_agree rest _ ρ _ F hF hM σ' hr
    refine ⟨l', ?_, hA'⟩
    simp only [runVals, hcv, Option.bind_some]
    by_cases h1 : cv = 1
    · rw [if_pos h1] at hl'; rw [if_pos h1, hlT, Option.bind_some, hl']
    · rw [if_neg h1] at hl'; rw [if_neg h1, hlF, Option.bind_some, hl']
  | .loop c body rest =>
    simp only [runTerms, Option.bind_eq_some_iff] at h
    obtain ⟨σ₁, hσ₁, hr⟩ := h
    have hc : ∀ σ₀ l₀ tc, Agree Γ σ₀ ρ l₀ → lowerT σ₀ c = some tc → ∃ cv, evalX c ρ l₀ F = some cv ∧ tc.eval ρ = cv.toNat :=
      fun σ₀ l₀ tc hA₀ h₀ => lowerT_eval c σ₀ ρ l₀ F tc hF hA₀ h₀
    have hb : ∀ σ₀ l₀ σ₂, Agree Γ σ₀ ρ l₀ → runTerms σ₀ body = some σ₂ → ∃ l₂, runVals body ρ l₀ F = some l₂ ∧ Agree Γ σ₂ ρ l₂ :=
      fun σ₀ l₀ σ₂ hA₀ h₀ => runTerms_agree body σ₀ ρ l₀ F hF hA₀ σ₂ h₀
    obtain ⟨l₁, hl₁, hA₁⟩ := unroll_agree hc hb (loopBudget + 1) F σ l σ₁ (by omega) hA hσ₁
    obtain ⟨l', hl', hA'⟩ := runTerms_agree rest _ ρ _ F hF hA₁ σ' hr
    exact ⟨l', by simp only [runVals, hl₁, Option.bind_some, hl'], hA'⟩
  | .matchS x arms rest =>
    simp only [runTerms, Option.bind_eq_some_iff] at h
    obtain ⟨sx, hx, σ₁, h₁, hr⟩ := h
    obtain ⟨vx, hvx, ihx⟩ := lowerT_eval x σ ρ l F sx hF hA hx
    obtain ⟨l₁, hl₁, hA₁⟩ := armsST_agree arms σ sx ρ l F hF hA vx (lowerT_width x σ sx hx) ihx σ₁ h₁
    obtain ⟨l', hl', hA'⟩ := runTerms_agree rest _ ρ _ F hF hA₁ σ' hr
    exact ⟨l', by simp only [runVals, hvx, Option.bind_some, hl₁, hl'], hA'⟩
termination_by structural st
/-- A value-position match's arms agree with the if-chain. -/
theorem armsT_eval {P : Params} {S : Spans} {Γ : Locals} {s t : Ty} (arms : Arms P S Γ s t) :
    ∀ (σ : Scope) (sx : Term) (ρ : Env) (l : Vals) (F : Nat) (T : Term), loopBudget < F → Agree Γ σ ρ l →
      ∀ vx : BitVec s.width, sx.width = s.width → sx.eval ρ = vx.toNat → armsT σ sx arms = some T →
        ∃ v, armsX vx arms ρ l F = some v ∧ T.eval ρ = v.toNat := by
  intro σ sx ρ l F T hF hA vx hw hx h
  match arms with
  | .fallback e =>
    obtain ⟨v, hv, ihv⟩ := lowerT_eval e σ ρ l F T hF hA h
    exact ⟨v, by simp only [armsX, hv], ihv⟩
  | .case k e rest =>
    simp only [armsT, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨te, he, tr, hr, rfl⟩ := h
    obtain ⟨ve, hve, ihe⟩ := lowerT_eval e σ ρ l F te hF hA he
    obtain ⟨vr, hvr, ihr⟩ := armsT_eval rest σ sx ρ l F tr hF hA vx hw hx hr
    have hte := lowerT_topPositive e σ te (Agree.wf hA) he
    have htr := armsT_topPositive rest σ sx tr (Agree.wf hA) hr
    have hwe := lowerT_width e σ te he
    have hwr := armsT_width rest σ sx tr hr
    have hcond := caseCond_eval sx s.width k vx ρ hw s.width_pos hx
    refine ⟨if vx = k then ve else vr, ?_, ?_⟩
    · simp only [armsX]
      by_cases h1 : vx = k
      · rw [if_pos h1, if_pos h1, hve]
      · rw [if_neg h1, if_neg h1, hvr]
    · rw [Term.selectArm_eval ρ hte htr (by rw [hwr, hwe]), Term.eval.eq_5, hwe]
      by_cases h1 : vx = k
      · have h' : (caseCond sx s.width k.toNat).eval ρ ≠ 0 := by rw [hcond, if_pos h1]; decide
        rw [if_pos h', if_pos h1, ihe, BitVec.toNat_mod_cancel]
      · have h' : ¬ (caseCond sx s.width k.toNat).eval ρ ≠ 0 := by rw [hcond, if_neg h1]; decide
        rw [if_neg h', if_neg h1, ihr, BitVec.toNat_mod_cancel]
termination_by structural arms
/-- A statement-position match's arms agree with the taken arm. -/
theorem armsST_agree {P : Params} {S : Spans} {Γ : Locals} {s : Ty} (arms : ArmsS P S Γ s) :
    ∀ (σ : Scope) (sx : Term) (ρ : Env) (l : Vals) (F : Nat), loopBudget < F → Agree Γ σ ρ l →
      ∀ vx : BitVec s.width, sx.width = s.width → sx.eval ρ = vx.toNat → ∀ σ', armsST σ sx arms = some σ' →
        ∃ l', armsVals vx arms ρ l F = some l' ∧ Agree Γ σ' ρ l' := by
  intro σ sx ρ l F hF hA vx hw hx σ' h
  match arms with
  | .fallback st =>
    obtain ⟨l', hl', hA'⟩ := runTerms_agree st σ ρ l F hF hA σ' h
    exact ⟨l', by simp only [armsVals, hl'], hA'⟩
  | .case k st rest =>
    simp only [armsST, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨σk, hk, σr, hr, rfl⟩ := h
    obtain ⟨lk, hlk, hAk⟩ := runTerms_agree st σ ρ l F hF hA σk hk
    obtain ⟨lr, hlr, hAr⟩ := armsST_agree rest σ sx ρ l F hF hA vx hw hx σr hr
    have hcond := caseCond_eval sx s.width k vx ρ hw s.width_pos hx
    have hM := merge_agree (caseCond sx s.width k.toNat) (if vx = k then 1 else 0)
      (by rw [hcond]; by_cases h1 : vx = k <;> simp [h1]) hAk hAr
    refine ⟨if vx = k then lk else lr, ?_, ?_⟩
    · simp only [armsVals]
      by_cases h1 : vx = k
      · rw [if_pos h1, if_pos h1, hlk]
      · rw [if_neg h1, if_neg h1, hlr]
    · by_cases h1 : vx = k
      · simpa [h1] using hM
      · simpa [h1] using hM
termination_by structural arms
/-- Binding a call's arguments keeps the callee's scope agreeing: each
parameter's term has the parameter's width and evaluates to the argument's
value. -/
theorem bindArgs_agree {P : Params} {S : Spans} {Γ : Locals} {ps : List (String × Ty)} (args : Args P S Γ ps) :
    ∀ (σ : Scope) (ρ : Env) (l : Vals) (F : Nat), loopBudget < F → Agree Γ σ ρ l →
      ∀ (Γ0 : Locals) (acc : Scope) (l0 : Vals), Agree Γ0 acc ρ l0 → ∀ σ', bindTerms σ args acc = some σ' →
        ∃ l', bindVals args ρ l l0 F = some l' ∧ Agree (bindTypes Γ0 ps) σ' ρ l' := by
  intro σ ρ l F hF hA Γ0 acc l0 h0 σ' h
  match args with
  | .nil =>
    simp only [bindTerms, Option.some.injEq] at h
    subst h
    exact ⟨l0, by simp only [bindVals], h0⟩
  | .cons (x := x) a rest =>
    simp only [bindTerms, Option.bind_eq_some_iff] at h
    obtain ⟨ta, ha, hr⟩ := h
    obtain ⟨va, hva, iha⟩ := lowerT_eval a σ ρ l F ta hF hA ha
    obtain ⟨l', hl', hA'⟩ := bindArgs_agree rest σ ρ l F hF hA _ _ _
      (Agree.set h0 x (lowerT_width a σ ta ha) (lowerT_topPositive a σ ta (Agree.wf hA) ha) iha) σ' hr
    exact ⟨l', by simp only [bindVals, hva, Option.bind_some, hl'], hA'⟩
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
  | .select n _ i => n ++ "[" ++ i.render ++ "]"

/-- Parameters from a list; the empty local scope and term scope. -/
def ps (l : List (String × Ty)) : Params := fun x => (l.find? (fun p => p.1 = x)).map (·.2)
abbrev Γ0 : Locals := fun _ => none
abbrev σ0 : Scope := fun _ => none
def sp (l : List (String × Ty)) : Spans := fun x => (l.find? (fun p => p.1 = x)).map (·.2)
abbrev sp0 : Spans := fun _ => none
/-- An expression over parameters `P` and spans `S` at a function's entry. -/
abbrev X (P : Params) (S : Spans) (t : Ty) := Expr P S Γ0 t
/-- The render of an expression's lowering at a function's entry. -/
def lowered? {P : Params} {S : Spans} {t : Ty} (e : X P S t) : Option String := (lowerT σ0 e).map Term.render

/-- `(a, b: u32) -> u32 = a + b` -/
example : lowered? ((.arith .add (.var .u32 "a" (by decide)) (.var .u32 "b" (by decide)) : X (ps [("a", .u32), ("b", .u32)]) sp0 .u32)) = some "(a add b)" := by decide
/-- `(a, b: u32) -> u32 = a - b` -/
example : lowered? ((.arith .sub (.var .u32 "a" (by decide)) (.var .u32 "b" (by decide)) : X (ps [("a", .u32), ("b", .u32)]) sp0 .u32)) = some "(a sub b)" := by decide
/-- `(a: u32) -> u32 = a * 3` -/
example : lowered? ((.arith .mul (.var .u32 "a" (by decide)) (.lit .u32 3) : X (ps [("a", .u32)]) sp0 .u32)) = some "(a mul 3)" := by decide
/-- `(a: u32) -> u32 = a / 8` -/
example : lowered? ((.divPow2 (.var .u32 "a" (by decide)) 3 (by decide) rfl : X (ps [("a", .u32)]) sp0 .u32)) = some "(a shr 3)" := by decide
/-- `(a: u32) -> u32 = a % 8` -/
example : lowered? ((.modPow2 (.var .u32 "a" (by decide)) 3 (by decide) rfl : X (ps [("a", .u32)]) sp0 .u32)) = some "(a and 7)" := by decide
/-- `(a: u32) -> u32 = -a` -/
example : lowered? ((.neg (.var .u32 "a" (by decide)) : X (ps [("a", .u32)]) sp0 .u32)) = some "(0 sub a)" := by decide
/-- `(a: u32) -> u32 = ^a` -/
example : lowered? ((.not (.var .u32 "a" (by decide)) : X (ps [("a", .u32)]) sp0 .u32)) = some "(a xor 4294967295)" := by decide
/-- `(a, b: u32) -> u32 = (a << 3) | (b >> 5)` -/
example : lowered? ((.bit .or (.bit .shl (.var .u32 "a" (by decide)) (.lit .u32 3) rfl) (.bit .shr (.var .u32 "b" (by decide)) (.lit .u32 5) rfl) rfl : X (ps [("a", .u32), ("b", .u32)]) sp0 .u32))
    = some "((a shl 3) or (b shr 5))" := by decide
/-- `(a, b: u32) -> u32 = (a & b) ^ b` -/
example : lowered? ((.bit .xor (.bit .and (.var .u32 "a" (by decide)) (.var .u32 "b" (by decide)) rfl) (.var .u32 "b" (by decide)) rfl : X (ps [("a", .u32), ("b", .u32)]) sp0 .u32))
    = some "((a and b) xor b)" := by decide
/-- `(a: u8) -> u32 = u32(a)` -/
example : lowered? ((.conv .u32 (.var .u8 "a" (by decide)) : X (ps [("a", .u8)]) sp0 .u32)) = some "(a and 255)" := by decide
/-- `(a: i8) -> i32 = i32(a)` -/
example : lowered? ((.conv .i32 (.var .i8 "a" (by decide)) : X (ps [("a", .i8)]) sp0 .i32)) = some "(((a and 255) shl 24) sar 24)" := by decide
/-- `(a: i32) -> i64 = i64(a) + 1` -/
example : lowered? ((.arith .add (.conv .i64 (.var .i32 "a" (by decide))) (.lit .i64 1) : X (ps [("a", .i32)]) sp0 .i64))
    = some "((((a and 4294967295) shl 32) sar 32) add 1)" := by decide
/-- `(a: u32) -> u8 = u8_trunc_u32(a)` — a re-widthed parameter prints as itself. -/
example : lowered? ((.conv .u8 (.var .u32 "a" (by decide)) : X (ps [("a", .u32)]) sp0 .u8)) = some "a" := by decide
/-- `(a, b: u16) -> u32 = u32(a) * u32(b)` -/
example : lowered? ((.arith .mul (.conv .u32 (.var .u16 "a" (by decide))) (.conv .u32 (.var .u16 "b" (by decide))) : X (ps [("a", .u16), ("b", .u16)]) sp0 .u32))
    = some "((a and 65535) mul (b and 65535))" := by decide
/-- `(a, b: u32) -> Bool = a < b` and the other five unsigned comparisons -/
example : lowered? ((.cmp .lt (.var .u32 "a" (by decide)) (.var .u32 "b" (by decide)) : X (ps [("a", .u32), ("b", .u32)]) sp0 .bool)) = some "(a lo b)" := by decide
example : lowered? ((.cmp .le (.var .u32 "a" (by decide)) (.var .u32 "b" (by decide)) : X (ps [("a", .u32), ("b", .u32)]) sp0 .bool)) = some "(a ls b)" := by decide
example : lowered? ((.cmp .gt (.var .u32 "a" (by decide)) (.var .u32 "b" (by decide)) : X (ps [("a", .u32), ("b", .u32)]) sp0 .bool)) = some "(a hi b)" := by decide
example : lowered? ((.cmp .ge (.var .u32 "a" (by decide)) (.var .u32 "b" (by decide)) : X (ps [("a", .u32), ("b", .u32)]) sp0 .bool)) = some "(a hs b)" := by decide
example : lowered? ((.cmp .eq (.var .u32 "a" (by decide)) (.var .u32 "b" (by decide)) : X (ps [("a", .u32), ("b", .u32)]) sp0 .bool)) = some "(a eq b)" := by decide
example : lowered? ((.cmp .ne (.var .u32 "a" (by decide)) (.var .u32 "b" (by decide)) : X (ps [("a", .u32), ("b", .u32)]) sp0 .bool)) = some "(a ne b)" := by decide
/-- `(a, b: i32) -> Bool = a < b` and the other three signed orders -/
example : lowered? ((.cmp .lt (.var .i32 "a" (by decide)) (.var .i32 "b" (by decide)) : X (ps [("a", .i32), ("b", .i32)]) sp0 .bool)) = some "(a lt b)" := by decide
example : lowered? ((.cmp .le (.var .i32 "a" (by decide)) (.var .i32 "b" (by decide)) : X (ps [("a", .i32), ("b", .i32)]) sp0 .bool)) = some "(a le b)" := by decide
example : lowered? ((.cmp .gt (.var .i32 "a" (by decide)) (.var .i32 "b" (by decide)) : X (ps [("a", .i32), ("b", .i32)]) sp0 .bool)) = some "(a gt b)" := by decide
example : lowered? ((.cmp .ge (.var .i32 "a" (by decide)) (.var .i32 "b" (by decide)) : X (ps [("a", .i32), ("b", .i32)]) sp0 .bool)) = some "(a ge b)" := by decide
/-- `(a, b, c: u32) -> Bool = a < b && b < c` -/
example : lowered? ((.bit .and (.cmp .lt (.var .u32 "a" (by decide)) (.var .u32 "b" (by decide))) (.cmp .lt (.var .u32 "b" (by decide)) (.var .u32 "c" (by decide))) rfl : X (ps [("a", .u32), ("b", .u32), ("c", .u32)]) sp0 .bool))
    = some "((a lo b) and (b lo c))" := by decide
/-- `(a, b: u32) -> Bool = a < b || a == b` -/
example : lowered? ((.bit .or (.cmp .lt (.var .u32 "a" (by decide)) (.var .u32 "b" (by decide))) (.cmp .eq (.var .u32 "a" (by decide)) (.var .u32 "b" (by decide))) rfl : X (ps [("a", .u32), ("b", .u32)]) sp0 .bool))
    = some "((a lo b) or (a eq b))" := by decide
/-- `(a, b: u32) -> Bool = !(a < b)` -/
example : lowered? ((.not (.cmp .lt (.var .u32 "a" (by decide)) (.var .u32 "b" (by decide))) : X (ps [("a", .u32), ("b", .u32)]) sp0 .bool)) = some "((a lo b) xor 1)" := by decide
/-- `(a, b: u32) -> u32 = a < b ? a | b` -/
example : lowered? ((.ite (.cmp .lt (.var .u32 "a" (by decide)) (.var .u32 "b" (by decide))) (.var .u32 "a" (by decide)) (.var .u32 "b" (by decide)) : X (ps [("a", .u32), ("b", .u32)]) sp0 .u32))
    = some "((a lo b) ? a : b)" := by decide
/-- `(a, b: i64) -> i64 = a < b ? b - a | a - b` -/
example : lowered? ((.ite (.cmp .lt (.var .i64 "a" (by decide)) (.var .i64 "b" (by decide))) (.arith .sub (.var .i64 "b" (by decide)) (.var .i64 "a" (by decide))) (.arith .sub (.var .i64 "a" (by decide)) (.var .i64 "b" (by decide))) : X (ps [("a", .i64), ("b", .i64)]) sp0 .i64))
    = some "((a lt b) ? (b sub a) : (a sub b))" := by decide

/-! Locals and calls: a local is substituted, a call is inlined, so the
renders are the terms the source would have without them. -/

/-- `(a, b: u32) -> u32 = { y: u32 = a + b; y * y }` -/
example : lowered? ((.letIn "y" (.arith .add (.var .u32 "a" (by decide)) (.var .u32 "b" (by decide)))
    (.arith .mul (.var .u32 "y" (by decide)) (.var .u32 "y" (by decide))) : X (ps [("a", .u32), ("b", .u32)]) sp0 .u32))
    = some "((a add b) mul (a add b))" := by decide
/-- `(a: u32) -> u32 = { y: u32 = a; y = y + 1; y * 2 }` — a rebinding replaces the term. -/
example : lowered? ((.letIn "y" (.var .u32 "a" (by decide))
    (.letIn "y" (.arith .add (.var .u32 "y" (by decide)) (.lit .u32 1))
      (.arith .mul (.var .u32 "y" (by decide)) (.lit .u32 2))) : X (ps [("a", .u32)]) sp0 .u32))
    = some "((a add 1) mul 2)" := by decide
/-- `(a: u32) -> u32 = { y: u8 = u8_trunc_u32(a); u32(y) }` — a narrow local read at its own width. -/
example : lowered? ((.letIn "y" (.conv .u8 (.var .u32 "a" (by decide)))
    (.conv .u32 (.var .u8 "y" (by decide))) : X (ps [("a", .u32)]) sp0 .u32))
    = some "(a and 255)" := by decide
/-- `g: (x: u32) -> u32 = x * x`; `f: (a: u32) -> u32 = g(a + 1)` -/
example : lowered? ((.call [("x", .u32)] .u32
    (.arith .mul (.var .u32 "x" (by decide)) (.var .u32 "x" (by decide)))
    (.cons (.arith .add (.var .u32 "a" (by decide)) (.lit .u32 1)) .nil) : X (ps [("a", .u32)]) sp0 .u32))
    = some "((a add 1) mul (a add 1))" := by decide
/-- `h: (x, y: u32) -> u32 = { d: u32 = x - y; d & 255 }`; `f: (a, b: u32) -> u32 = h(b, a)` -/
example : lowered? ((.call [("x", .u32), ("y", .u32)] .u32
    (.letIn "d" (.arith .sub (.var .u32 "x" (by decide)) (.var .u32 "y" (by decide)))
      (.bit .and (.var .u32 "d" (by decide)) (.lit .u32 255) rfl))
    (.cons (.var .u32 "b" (by decide)) (.cons (.var .u32 "a" (by decide)) .nil)) : X (ps [("a", .u32), ("b", .u32)]) sp0 .u32))
    = some "((b sub a) and 255)" := by decide

/-- `(a, b: u32) -> u32 = { m: u32 = a; a < b ? { m = b } | { }; m * 2 }` -/
example : lowered? ((.letIn "m" (.var .u32 "a" (by decide))
    (.condSet (.cmp .lt (.var .u32 "a" (by decide)) (.var .u32 "b" (by decide)))
      (.assign "m" (by decide) (.var .u32 "b" (by decide)) .nil) .nil
      (.arith .mul (.var .u32 "m" (by decide)) (.lit .u32 2))) : X (ps [("a", .u32), ("b", .u32)]) sp0 .u32))
    = some "(((a lo b) ? b : a) mul 2)" := by decide
/-- `(a, b: u32) -> u32 = { x: u32 = a; y: u32 = b; a < b ? { x = b; y = a } | { x = x + 1 }; x - y }` -/
example : lowered? ((.letIn "x" (.var .u32 "a" (by decide)) (.letIn "y" (.var .u32 "b" (by decide))
    (.condSet (.cmp .lt (.var .u32 "a" (by decide)) (.var .u32 "b" (by decide)))
      (.assign "x" (by decide) (.var .u32 "b" (by decide)) (.assign "y" (by decide) (.var .u32 "a" (by decide)) .nil))
      (.assign "x" (by decide) (.arith .add (.var .u32 "x" (by decide)) (.lit .u32 1)) .nil)
      (.arith .sub (.var .u32 "x" (by decide)) (.var .u32 "y" (by decide))))) : X (ps [("a", .u32), ("b", .u32)]) sp0 .u32))
    = some "(((a lo b) ? b : (a add 1)) sub ((a lo b) ? a : b))" := by decide

/-- `(a, b: u32) -> u32 = { m: u32 = a; a < b ? { m = b } | { }; m * 2 }` -/
example : lowered? ((.letIn "m" (.var .u32 "a" (by decide))
    (.condSet (.cmp .lt (.var .u32 "a" (by decide)) (.var .u32 "b" (by decide)))
      (.assign "m" (by decide) (.var .u32 "b" (by decide)) .nil) .nil
      (.arith .mul (.var .u32 "m" (by decide)) (.lit .u32 2))) : X (ps [("a", .u32), ("b", .u32)]) sp0 .u32))
    = some "(((a lo b) ? b : a) mul 2)" := by decide
/-- `(a, b: u32) -> u32 = { x: u32 = a; y: u32 = b; a < b ? { x = b; y = a } | { x = x + 1 }; x - y }` -/
example : lowered? ((.letIn "x" (.var .u32 "a" (by decide)) (.letIn "y" (.var .u32 "b" (by decide))
    (.condSet (.cmp .lt (.var .u32 "a" (by decide)) (.var .u32 "b" (by decide)))
      (.assign "x" (by decide) (.var .u32 "b" (by decide)) (.assign "y" (by decide) (.var .u32 "a" (by decide)) .nil))
      (.assign "x" (by decide) (.arith .add (.var .u32 "x" (by decide)) (.lit .u32 1)) .nil)
      (.arith .sub (.var .u32 "x" (by decide)) (.var .u32 "y" (by decide))))) : X (ps [("a", .u32), ("b", .u32)]) sp0 .u32))
    = some "(((a lo b) ? b : (a add 1)) sub ((a lo b) ? a : b))" := by decide

/-- `(v: []u32, i: u32) -> u32 = v[i]` -/
example : lowered? ((.elem .u32 "v" (by decide) (.var .u32 "i" (by decide)) : X (ps [("i", .u32)]) (sp [("v", .u32)]) .u32))
    = some "v[i]" := by decide
/-- `(v: []u32, i: u32) -> u32 = v[i + 1] * v[0]` — a constant index is the element parameter, the same name. -/
example : lowered? ((.arith .mul (.elem .u32 "v" (by decide) (.arith .add (.var .u32 "i" (by decide)) (.lit .u32 1)))
    (.elem .u32 "v" (by decide) (.lit .u32 0)) : X (ps [("i", .u32)]) (sp [("v", .u32)]) .u32))
    = some "(v[(i add 1)] mul v[0])" := by decide
/-- `(b: []u8, i: u32) -> u32 = u32(b[i])` — a select is not re-widthed the way a parameter is:
`zeroExtend` masks it to its own width, and `extendTerm` masks again. -/
example : lowered? ((.conv .u32 (.elem .u8 "b" (by decide) (.var .u32 "i" (by decide))) : X (ps [("i", .u32)]) (sp [("b", .u8)]) .u32))
    = some "((b[i] and 255) and 255)" := by decide
/-- `(v: []u32, i: u32) -> Bool = i < len(v)` -/
example : lowered? ((.cmp .lt (.var .u32 "i" (by decide)) (.len (s := .u32) "v" (by decide)) : X (ps [("i", .u32)]) (sp [("v", .u32)]) .bool))
    = some "(i lo len(v))" := by decide

/-! Folding: constant subterms fold as `binaryTerm`, `cmpTerm` and `iteTerm`
fold them, so the renders are the folded terms. -/

/-- `(a: u32) -> u32 = a + 2 * 3` -/
example : lowered? ((.arith .add (.var .u32 "a" (by decide)) (.arith .mul (.lit .u32 2) (.lit .u32 3)) : X (ps [("a", .u32)]) sp0 .u32))
    = some "(a add 6)" := by decide
/-- `(a: u32) -> u32 = a + 0` -/
example : lowered? ((.arith .add (.var .u32 "a" (by decide)) (.lit .u32 0) : X (ps [("a", .u32)]) sp0 .u32))
    = some "a" := by decide
/-- `(a, b: u32) -> u32 = 2 < 3 ? a | b` — a constant condition picks its arm. -/
example : lowered? ((.ite (.cmp .lt (.lit .u32 2) (.lit .u32 3)) (.var .u32 "a" (by decide)) (.var .u32 "b" (by decide)) : X (ps [("a", .u32), ("b", .u32)]) sp0 .u32))
    = some "a" := by decide

/-! Loops: `lowerWhile` unrolls while the folded condition is a non-zero
constant, so a counted loop lowers to its unrolled body. -/

/-- `(n: u32) -> u32 = { s: u32 = 0; i: u32 = 0; while i < 3 { s = s + n; i = i + 1 }; s }` -/
example : lowered? ((.letIn "s" (.lit .u32 0) (.letIn "i" (.lit .u32 0)
    (.whileLoop (.cmp .lt (.var .u32 "i" (by decide)) (.lit .u32 3))
      (.assign "s" (by decide) (.arith .add (.var .u32 "s" (by decide)) (.var .u32 "n" (by decide)))
        (.assign "i" (by decide) (.arith .add (.var .u32 "i" (by decide)) (.lit .u32 1)) .nil))
      (.var .u32 "s" (by decide)))) : X (ps [("n", .u32)]) sp0 .u32)) = some "((n add n) add n)" := by decide
/-- `(n: u32) -> u32 = { s: u32 = 0; i: u32 = 0; while i < 4 { i % 2 == 0 ? { s = s + n } | { }; i = i + 1 }; s }` -/
example : lowered? ((.letIn "s" (.lit .u32 0) (.letIn "i" (.lit .u32 0)
    (.whileLoop (.cmp .lt (.var .u32 "i" (by decide)) (.lit .u32 4))
      (.cond (.cmp .eq (.modPow2 (.var .u32 "i" (by decide)) 1 (by decide) rfl) (.lit .u32 0))
        (.assign "s" (by decide) (.arith .add (.var .u32 "s" (by decide)) (.var .u32 "n" (by decide))) .nil) .nil
        (.assign "i" (by decide) (.arith .add (.var .u32 "i" (by decide)) (.lit .u32 1)) .nil))
      (.var .u32 "s" (by decide)))) : X (ps [("n", .u32)]) sp0 .u32)) = some "(n add n)" := by decide
/-- `(n: u32) -> u32 = { i: u32 = 0; while i < n { i = i + 1 }; i }` — a data-dependent loop is outside the subset. -/
example : lowered? ((.letIn "i" (.lit .u32 0)
    (.whileLoop (.cmp .lt (.var .u32 "i" (by decide)) (.var .u32 "n" (by decide)))
      (.assign "i" (by decide) (.arith .add (.var .u32 "i" (by decide)) (.lit .u32 1)) .nil)
      (.var .u32 "i" (by decide))) : X (ps [("n", .u32)]) sp0 .u32)) = none := by decide

/-! Integer-constant matches: an if-chain of equality selects, the first
case outermost, the wildcard arm the fallback. -/

/-- `(op, a, b: u32) -> u32 = op ? | 0 => a | 1 => b | _ => a + b` -/
example : lowered? ((.matchInt (.var .u32 "op" (by decide))
    (.case 0 (.var .u32 "a" (by decide)) (.case 1 (.var .u32 "b" (by decide))
      (.fallback (.arith .add (.var .u32 "a" (by decide)) (.var .u32 "b" (by decide)))))) : X (ps [("op", .u32), ("a", .u32), ("b", .u32)]) sp0 .u32))
    = some "((op eq 0) ? a : ((op eq 1) ? b : (a add b)))" := by decide
/-- `(op, a: u32) -> u32 = { r: u32 = a; op ? | 0 => { r = a + 1 } | 1 => { r = a * 2 } | _ => { }; r }` -/
example : lowered? ((.letIn "r" (.var .u32 "a" (by decide))
    (.matchSet (.var .u32 "op" (by decide))
      (.case 0 (.assign "r" (by decide) (.arith .add (.var .u32 "a" (by decide)) (.lit .u32 1)) .nil)
        (.case 1 (.assign "r" (by decide) (.arith .mul (.var .u32 "a" (by decide)) (.lit .u32 2)) .nil)
          (.fallback .nil)))
      (.var .u32 "r" (by decide))) : X (ps [("op", .u32), ("a", .u32)]) sp0 .u32))
    = some "((op eq 0) ? (a add 1) : ((op eq 1) ? (a mul 2) : a))" := by decide

end Oak.LoweringRefinement
