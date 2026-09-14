import Oak.AssemblerSemantics
import Oak.IntegerDivision

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

/-- Division and remainder by any divisor (`20-types.md` §11.1): a zero
divisor traps (the extraction yields no value), `MIN / -1` is `MIN` and
`MIN % -1` is `0`. -/
inductive DivOp
  | div | rem
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

/-- An owned array is its `n` element leaves in scope, named by `nm` — `x[k]`
for the array local `x` (`elemName x`), `r.h[k]` for the array field `h`
of the record `r`, `a[k].x` for the field `x` of the record elements of
`a` (the verifier's `oakValue` tree, each leaf named as `paramAggregate`
names it; the extraction's `Array` holds the same values indexed). -/
def bindLeaves (Γ : Locals) (nm : Nat → String) (e : Ty) : Nat → Locals
  | 0 => Γ
  | k + 1 => (bindLeaves Γ nm e k).set (nm k) e

/-- The `n` leaves `nm 0`…`nm (n-1)` of element type `e` are in scope. -/
def ArrIn (Γ : Locals) (nm : Nat → String) (e : Ty) (n : Nat) : Prop := ∀ k, k < n → Γ (nm k) = some e

instance (Γ : Locals) (nm : Nat → String) (e : Ty) (n : Nat) : Decidable (ArrIn Γ nm e n) :=
  inferInstanceAs (Decidable (∀ k, k < n → Γ (nm k) = some e))

/-- An array literal's elements as named fields: `nm k` for each `k < n`. -/
def arrayFields (nm : Nat → String) (e : Ty) (n : Nat) : List (String × Ty) := (List.range n).map fun k => (nm k, e)

/-- Names bound in order under a naming (`id` for a callee's parameters, the
field-leaf naming for a record's fields; a later duplicate wins, as
`bound[param] = …` does). -/
def bindTypes (nm : String → String) (Γ : Locals) : List (String × Ty) → Locals
  | [] => Γ
  | (x, s) :: ps => bindTypes nm (Γ.set (nm x) s) ps

/-- The verifier's name for field `f` of record `r` (`paramAggregate`'s
`prefix + "." + name`): a record is its scalar field leaves, each a local
under that name, as an owned array is its element leaves. -/
def fieldName (r f : String) : String := r ++ "." ++ f

/-- A borrowed span: the callee's span parameter `s` (`[]e`, `[*]e`) of `n`
elements, and the caller's leaves it borrows (`span(&a)`: `elemName "a"`;
a span passed on: the caller's own span leaves). `enterCall` binds the
callee's `s` to a copy of the owner's array and, for a writable span,
writes the callee's final leaves back on return. -/
structure Borrow where
  s : String
  e : Ty
  n : Nat
  nm : Nat → String

/-- The borrows' callee-side leaves `s[k]` in scope. -/
def bindBorrows (Γ : Locals) : List Borrow → Locals
  | [] => Γ
  | b :: bs => bindBorrows (bindLeaves Γ (elemName b.s) b.e b.n) bs

/-- The callee's scope at entry: its parameters bound to the arguments,
its body's locals (zero until assigned: a declaration's initializer is the
first assignment), its span parameters' leaves. -/
def calleeScope (params locals : List (String × Ty)) (bs : List Borrow) : Locals :=
  bindBorrows (bindTypes id (bindTypes id (fun _ => none) params) locals) bs

/-- Every borrow's caller-side leaves are in scope with the borrow's type. -/
def borrowsIn (Γ : Locals) (bs : List Borrow) : Bool := bs.all fun b => decide (ArrIn Γ b.nm b.e b.n)

/-- The callee-side view of the borrows: the leaves `s[k]`. -/
def calleeSide (bs : List Borrow) : List Borrow := bs.map fun b => { b with nm := elemName b.s }

/-- The fresh symbol standing for a loop-carried local's value on an
iteration of data-dependent loop `idx` (`loopEvent.freshName`:
`loop<index>.<var>`). -/
def loopName (idx : Nat) (x : String) : String := "loop" ++ toString idx ++ "." ++ x

/-- The loop-carried locals are locals of the stated types. -/
def CarriedIn (Γ : Locals) (carried : List (String × Ty)) : Prop := ∀ p, p ∈ carried → Γ p.1 = some p.2

instance (Γ : Locals) (carried : List (String × Ty)) : Decidable (CarriedIn Γ carried) :=
  inferInstanceAs (Decidable (∀ p, p ∈ carried → Γ p.1 = some p.2))

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
`len v h` its `len(v)`; `arrDecl nm e n hn b` declares an owned array of
`n` elements (zero-initialized, as `zeroValue` and `Array.replicate` both
say) for the block `b`, `arrLit nm e n hn items b` one from a literal,
`arrGet e n nm hn h i` reads its element `i` and `arrSetE nm h hn i v
rest` writes it — an owned array is its element leaves under the names
the verifier gives them (`nm`: `x[k]` for a local, `r.h[k]` for a record's
array field, `a[k].x` for a field of an array's record elements, so a
nested aggregate is the same leaves under longer names), both readers see
the same cells, and both trap outside the range (`none`); `recDecl r fs fields
b` declares the record local `r: R = R{ f₁: e₁, … }` whose scalar fields
`fs` are given in the type's order, for the block `b` — a record is its
field leaves `r.f`, so a field read is the variable `r.f` and a field
write its rebinding, for a local as for a record parameter
(`paramAggregate`); a tagged union is the record of its `tag` leaf and its
payload leaves, a variant match the constant match on the tag; `callX
params locals bs hb hc stmts results args rest` is a call whose callee
borrows the caller's arrays through span parameters (`enterCall`) and
whose results — a scalar, or the leaves of a record the callee builds
(`inlineCallValue`) — are bound in the caller under `rs` for `rest`, the
borrowed leaves written back first; `Stmts.callS` is the same in statement
position, its results assigned to existing locals; `whileEvent idx c body
rest` is a data-dependent loop — one whose condition does not fold to a
constant — summarized as `loopEvent` summarizes it: the carried locals
(those the body assigns) stand as the fresh symbols `loop<idx>.x` after
the loop, and the condition and body over those symbols are the event's
one-iteration semantics; `Stmts.loopEvent` the same in statement
position. -/
inductive Expr (P : Params) (S : Spans) : Locals → Ty → Type
  | var {Γ : Locals} (t : Ty) (x : String) (h : resolve P Γ x = some t) : Expr P S Γ t
  | lit {Γ : Locals} (t : Ty) (v : BitVec t.width) : Expr P S Γ t
  | arith {Γ : Locals} (op : ArithOp) {t : Ty} (a b : Expr P S Γ t) : Expr P S Γ t
  | bit {Γ : Locals} (op : BitOp) {t : Ty} (a b : Expr P S Γ t) (h : t.signed = false) : Expr P S Γ t
  | divPow2 {Γ : Locals} {t : Ty} (a : Expr P S Γ t) (k : Nat) (hk : k < t.width) (hu : t.signed = false) : Expr P S Γ t
  | modPow2 {Γ : Locals} {t : Ty} (a : Expr P S Γ t) (k : Nat) (hk : k < t.width) (hu : t.signed = false) : Expr P S Γ t
  | divRem {Γ : Locals} {t : Ty} (op : DivOp) (a b : Expr P S Γ t) : Expr P S Γ t
  | neg {Γ : Locals} {t : Ty} (a : Expr P S Γ t) : Expr P S Γ t
  | not {Γ : Locals} {t : Ty} (a : Expr P S Γ t) : Expr P S Γ t
  | conv {Γ : Locals} {s : Ty} (t : Ty) (a : Expr P S Γ s) : Expr P S Γ t
  | cmp {Γ : Locals} {s : Ty} (op : CmpOp) (l r : Expr P S Γ s) : Expr P S Γ .bool
  | ite {Γ : Locals} {t : Ty} (c : Expr P S Γ .bool) (a b : Expr P S Γ t) : Expr P S Γ t
  | letIn {Γ : Locals} {s t : Ty} (x : String) (v : Expr P S Γ s) (b : Expr P S (Γ.set x s) t) : Expr P S Γ t
  | call {Γ : Locals} (params : List (String × Ty)) (ret : Ty)
      (body : Expr P S (bindTypes id (fun _ => none) params) ret) (args : Args P S Γ params) : Expr P S Γ ret
  | recDecl {Γ : Locals} {t : Ty} (r : String) (fs : List (String × Ty)) (fields : Args P S Γ fs)
      (b : Expr P S (bindTypes (fieldName r) Γ fs) t) : Expr P S Γ t
  | whileEvent {Γ : Locals} {t : Ty} (idx : Nat) (c : Expr P S Γ .bool) (body : Stmts P S Γ) (rest : Expr P S Γ t) : Expr P S Γ t
  | callX {Γ : Locals} {t : Ty} (params locals : List (String × Ty)) (bs : List Borrow)
      (hb : borrowsIn Γ bs = true) (hc : borrowsIn (calleeScope params locals bs) (calleeSide bs) = true)
      {rs : List (String × Ty)}
      (stmts : Stmts P S (calleeScope params locals bs)) (results : Args P S (calleeScope params locals bs) rs)
      (args : Args P S Γ params) (rest : Expr P S (bindTypes id Γ rs) t) : Expr P S Γ t
  | condSet {Γ : Locals} {t : Ty} (c : Expr P S Γ .bool) (armT armF : Stmts P S Γ) (rest : Expr P S Γ t) : Expr P S Γ t
  | whileLoop {Γ : Locals} {t : Ty} (c : Expr P S Γ .bool) (body : Stmts P S Γ) (rest : Expr P S Γ t) : Expr P S Γ t
  | matchInt {Γ : Locals} {s t : Ty} (x : Expr P S Γ s) (arms : Arms P S Γ s t) : Expr P S Γ t
  | matchSet {Γ : Locals} {s t : Ty} (x : Expr P S Γ s) (arms : ArmsS P S Γ s) (rest : Expr P S Γ t) : Expr P S Γ t
  | elem {Γ : Locals} (s : Ty) (v : String) (h : S v = some s) (i : Expr P S Γ .u32) : Expr P S Γ s
  | len {Γ : Locals} {s : Ty} (v : String) (h : S v = some s) : Expr P S Γ .u32
  | arrDecl {Γ : Locals} {t : Ty} (nm : Nat → String) (e : Ty) (n : Nat) (hn : 0 < n) (b : Expr P S (bindLeaves Γ nm e n) t) : Expr P S Γ t
  | arrLit {Γ : Locals} {t : Ty} (nm : Nat → String) (e : Ty) (n : Nat) (hn : 0 < n) (items : Args P S Γ (arrayFields nm e n))
      (b : Expr P S (bindLeaves Γ nm e n) t) : Expr P S Γ t
  | arrGet {Γ : Locals} (e : Ty) (n : Nat) (nm : Nat → String) (hn : 0 < n ∧ n < 2 ^ 32) (h : ArrIn Γ nm e n) (i : Expr P S Γ .u32) : Expr P S Γ e
  | arrSetE {Γ : Locals} {t e : Ty} {n : Nat} (nm : Nat → String) (h : ArrIn Γ nm e n) (hn : n < 2 ^ 32) (i : Expr P S Γ .u32) (v : Expr P S Γ e) (rest : Expr P S Γ t) : Expr P S Γ t
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
  | arrSet {Γ : Locals} {e : Ty} {n : Nat} (nm : Nat → String) (h : ArrIn Γ nm e n) (hn : n < 2 ^ 32) (i : Expr P S Γ .u32) (v : Expr P S Γ e) (rest : Stmts P S Γ) : Stmts P S Γ
  | loopEvent {Γ : Locals} (idx : Nat) (c : Expr P S Γ .bool) (body : Stmts P S Γ) (rest : Stmts P S Γ) : Stmts P S Γ
  | callS {Γ : Locals} (params locals : List (String × Ty)) (bs : List Borrow)
      (hb : borrowsIn Γ bs = true) (hc : borrowsIn (calleeScope params locals bs) (calleeSide bs) = true)
      {rs : List (String × Ty)} (hrs : bindTypes id Γ rs = Γ)
      (stmts : Stmts P S (calleeScope params locals bs)) (results : Args P S (calleeScope params locals bs) rs)
      (args : Args P S Γ params) (rest : Stmts P S Γ) : Stmts P S Γ
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

mutual
/-- The names a statement list assigns (`assignedLocals`): locals, array
leaves written, a call's results and the leaves its borrows write back. -/
def Stmts.assigned {P : Params} {S : Spans} : {Γ : Locals} → Stmts P S Γ → List String
  | _, .nil => []
  | _, .assign x _ _ rest => x :: rest.assigned
  | _, .cond _ armT armF rest => armT.assigned ++ armF.assigned ++ rest.assigned
  | _, .loop _ body rest => body.assigned ++ rest.assigned
  | _, .matchS _ arms rest => arms.assigned ++ rest.assigned
  | _, .arrSet (n := n) nm _ _ _ _ rest => (List.range n).map nm ++ rest.assigned
  | _, .loopEvent _ _ body rest => body.assigned ++ rest.assigned
  | _, .callS (rs := rs) _ _ bs _ _ _ _ _ _ rest =>
    rs.map Prod.fst ++ (bs.flatMap fun b => (List.range b.n).map b.nm) ++ rest.assigned
def ArmsS.assigned {P : Params} {S : Spans} : {Γ : Locals} → {s : Ty} → ArmsS P S Γ s → List String
  | _, _, .fallback st => st.assigned
  | _, _, .case _ st rest => st.assigned ++ rest.assigned
end

/-- `loopEvent`'s carried locals: the locals the body assigns, with their
types (a local declared inside the body is the body's own in the Go; the
model pre-declares it, so it is carried too — its fresh symbol is read by
nothing after the loop). -/
def carriedOf {P : Params} {S : Spans} {Γ : Locals} (body : Stmts P S Γ) : List (String × Ty) :=
  body.assigned.filterMap fun y => (Γ y).map fun t => (y, t)

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

/-- Division at the type's signedness, on a nonzero divisor: `UIntN`'s `/`
and `%`, `IntN`'s truncating `sdiv` and `srem`. -/
def divX (signed : Bool) (op : DivOp) {w : Nat} (x y : BitVec w) : BitVec w :=
  match op with
  | .div => if signed then x.sdiv y else x / y
  | .rem => if signed then x.srem y else x % y

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

/-- The fresh symbols denote the exit values: `ρ (loop<idx>.x)`, read at
the local's width as the verifier reads a parameter term, is `l' x` for
every carried local. The model's reading of a summarized loop is defined
only for assignments that interpret the symbols this way (`none`
otherwise), so the theorem speaks about exactly those. -/
def freshDenote (ρ : Env) (idx : Nat) (carried : List (String × Ty)) (l' : Vals) : Bool :=
  carried.all fun p => ρ (loopName idx p.1) % 2 ^ p.2.width == l' p.1

/-- A callee's locals before their first assignment. -/
def zeroVals (l : Vals) : List (String × Ty) → Vals
  | [] => l
  | (x, _) :: rest => zeroVals (l.set x 0) rest

/-- Element values copied leaf by leaf from one naming to another. -/
def copyVals (src : Vals) (nmS : Nat → String) (dst : Vals) (nmD : Nat → String) : Nat → Vals
  | 0 => dst
  | k + 1 => (copyVals src nmS dst nmD k).set (nmD k) (src (nmS k))

/-- The borrowed arrays' values into the callee (`s[k] := a[k]`). -/
def copyInVals (l lc : Vals) : List Borrow → Vals
  | [] => lc
  | b :: bs => copyInVals l (copyVals l b.nm lc (elemName b.s) b.n) bs

/-- The callee's final span leaves back to the caller (`a[k] := s[k]`, the
extraction's rebinding of the span owners a call returns). -/
def copyOutVals (lf l : Vals) : List Borrow → Vals
  | [] => l
  | b :: bs => copyOutVals lf (copyVals lf (elemName b.s) l b.nm b.n) bs

/-- A declared array's zero elements (`Array.replicate n 0`). -/
def zeroLeaves (l : Vals) (nm : Nat → String) : Nat → Vals
  | 0 => l
  | k + 1 => (zeroLeaves l nm k).set (nm k) 0

/-- `setIfInBounds` on the leaves: element `k` takes the value when `k` is
the index, its own value otherwise (leaf by leaf, as the verifier writes,
so the two readers are compared cell by cell). -/
def writeLeaves (l : Vals) (nm : Nat → String) (i v : Nat) : Nat → Vals
  | 0 => l
  | k + 1 => (writeLeaves l nm i v k).set (nm k) (if i = k then v else l (nm k))

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
fuel`, the callee's own `def`); a data-dependent loop is `loopX` too,
under assignments whose fresh symbols denote the exit values
(`freshDenote`); a statement-level conditional rebinds the
variables its arms assign to the taken arm's values (`let (vars) ← if c
then do A; pure (vars) else do B; pure (vars)`), the untouched ones being
equal on both sides; a loop is `loopX`; an integer-constant match is the
if-chain `if x == k₁ then … else …` in value and statement position; an
owned array's element read or write is the `Array` cell in range and a
trap (`none`) outside it — Oak's semantics, where the extraction's own
`getD`/`setIfInBounds` reads zero and drops the write (`95-extraction.md`
§3, a modeling choice the seam does not adopt); a span element `v[i]` is the
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
  | _, t, .divRem op a b, ρ, l, F => (evalX a ρ l F).bind fun x => (evalX b ρ l F).bind fun y =>
      if y = 0 then none else some (divX t.signed op x y)
  | _, _, .neg a, ρ, l, F => (evalX a ρ l F).bind fun x => some (0 - x)
  | _, _, .not a, ρ, l, F => (evalX a ρ l F).bind fun x => some (~~~ x)
  | _, t, .conv (s := s) _ a, ρ, l, F => (evalX a ρ l F).bind fun x => some (convX s t x)
  | _, _, .cmp (s := s) op lhs rhs, ρ, l, F =>
    (evalX lhs ρ l F).bind fun x => (evalX rhs ρ l F).bind fun y => some (BitVec.ofBool (cmpX s.signed op x y))
  | _, _, .ite c a b, ρ, l, F => (evalX c ρ l F).bind fun cv => if cv = 1 then evalX a ρ l F else evalX b ρ l F
  | _, _, .letIn x v b, ρ, l, F => (evalX v ρ l F).bind fun x' => evalX b ρ (l.set x x'.toNat) F
  | _, _, .call _ _ body args, ρ, l, F => (bindVals id args ρ l (fun _ => 0) F).bind fun l' => evalX body ρ l' F
  | _, _, .recDecl r _ fields b, ρ, l, F => (bindVals (fieldName r) fields ρ l l F).bind fun l' => evalX b ρ l' F
  | _, _, .whileEvent idx c body rest, ρ, l, F =>
    (loopX (fun l₀ => evalX c ρ l₀ F) (fun l₀ => runVals body ρ l₀ F) F l).bind fun l' =>
      if freshDenote ρ idx (carriedOf body) l' then evalX rest ρ l' F else none
  | _, _, .callX params locals bs _ _ stmts results args rest, ρ, l, F =>
    (bindVals id args ρ l (fun _ => 0) F).bind fun lp =>
    (runVals stmts ρ (copyInVals l (zeroVals lp locals) bs) F).bind fun lf =>
    (bindVals id results ρ lf (copyOutVals lf l bs) F).bind fun l' => evalX rest ρ l' F
  | _, _, .condSet c armT armF rest, ρ, l, F =>
    (evalX c ρ l F).bind fun cv => (if cv = 1 then runVals armT ρ l F else runVals armF ρ l F).bind fun l' => evalX rest ρ l' F
  | _, _, .whileLoop c body rest, ρ, l, F =>
    (loopX (fun l₀ => evalX c ρ l₀ F) (fun l₀ => runVals body ρ l₀ F) F l).bind fun l' => evalX rest ρ l' F
  | _, _, .matchInt x arms, ρ, l, F => (evalX x ρ l F).bind fun vx => armsX vx arms ρ l F
  | _, _, .matchSet x arms rest, ρ, l, F =>
    (evalX x ρ l F).bind fun vx => (armsVals vx arms ρ l F).bind fun l' => evalX rest ρ l' F
  | _, s, .elem _ v _ i, ρ, l, F => (evalX i ρ l F).bind fun k => some (BitVec.ofNat s.width (ρ (elemName v k.toNat)))
  | _, _, .len v _, ρ, _, _ => some (BitVec.ofNat 32 (ρ (lenName v)))
  | _, _, .arrDecl nm e n _ b, ρ, l, F => evalX b ρ (zeroLeaves l nm n) F
  | _, _, .arrLit nm e n _ items b, ρ, l, F => (bindVals id items ρ l l F).bind fun l' => evalX b ρ l' F
  | _, e, .arrGet _ n nm _ _ i, ρ, l, F =>
    (evalX i ρ l F).bind fun k => if k.toNat < n then some (BitVec.ofNat e.width (l (nm k.toNat))) else none
  | _, _, .arrSetE (n := n) nm _ _ i v rest, ρ, l, F =>
    (evalX i ρ l F).bind fun k => (evalX v ρ l F).bind fun vv =>
      if k.toNat < n then evalX rest ρ (writeLeaves l nm k.toNat vv.toNat n) F else none
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
  | _, .arrSet (n := n) nm _ _ i v rest, ρ, l, F =>
    (evalX i ρ l F).bind fun k => (evalX v ρ l F).bind fun vv =>
      if k.toNat < n then runVals rest ρ (writeLeaves l nm k.toNat vv.toNat n) F else none
  | _, .loopEvent idx c body rest, ρ, l, F =>
    (loopX (fun l₀ => evalX c ρ l₀ F) (fun l₀ => runVals body ρ l₀ F) F l).bind fun l' =>
      if freshDenote ρ idx (carriedOf body) l' then runVals rest ρ l' F else none
  | _, .callS params locals bs _ _ _ stmts results args rest, ρ, l, F =>
    (bindVals id args ρ l (fun _ => 0) F).bind fun lp =>
    (runVals stmts ρ (copyInVals l (zeroVals lp locals) bs) F).bind fun lf =>
    (bindVals id results ρ lf (copyOutVals lf l bs) F).bind fun l' => runVals rest ρ l' F
/-- A value-position match: `if x == k₁ then e₁ else if … else e`. -/
def armsX {P : Params} {S : Spans} : {Γ : Locals} → {s t : Ty} → BitVec s.width → Arms P S Γ s t → Env → Vals → Nat → Option (BitVec t.width)
  | _, _, _, _, .fallback e, ρ, l, F => evalX e ρ l F
  | _, _, _, vx, .case k e rest, ρ, l, F => if vx = k then evalX e ρ l F else armsX vx rest ρ l F
/-- A statement-position match: the taken arm's statements. -/
def armsVals {P : Params} {S : Spans} : {Γ : Locals} → {s : Ty} → BitVec s.width → ArmsS P S Γ s → Env → Vals → Nat → Option Vals
  | _, _, _, .fallback st, ρ, l, F => runVals st ρ l F
  | _, _, vx, .case k st rest, ρ, l, F => if vx = k then runVals st ρ l F else armsVals vx rest ρ l F
/-- The callee's values (a record literal's field values): each argument
evaluated in the caller's scope and bound under its name, in order. -/
def bindVals {P : Params} {S : Spans} (nm : String → String) : {Γ : Locals} → {ps : List (String × Ty)} → Args P S Γ ps → Env → Vals → Vals → Nat → Option Vals
  | _, _, .nil, _, _, acc, _ => some acc
  | _, _, .cons (x := x) a rest, ρ, l, acc, F => (evalX a ρ l F).bind fun x' => bindVals nm rest ρ l (acc.set (nm x) x'.toNat) F
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

/-- The integer quotients the verifier keeps as uninterpreted operations
(`floatTerm("udiv"/"sdiv", …)`, docs/spec/94-assembler.md §8, the
thirty-first increment): shared by every side that divides the same
operands, evaluated as the machine's total division. -/
inductive UOp
  | udiv | sdiv
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
  | uop (op : UOp) (w : Nat) (l r : Term)
  deriving DecidableEq

def Term.width : Term → Nat
  | .param _ w => w
  | .const _ w => w
  | .bin _ w _ _ => w
  | .cmp _ w _ _ => w
  | .ite w _ _ _ => w
  | .select _ w _ => w
  | .uop _ w _ _ => w

@[simp] theorem Term.width_param (n : String) (w : Nat) : (Term.param n w).width = w := rfl
@[simp] theorem Term.width_const (v w : Nat) : (Term.const v w).width = w := rfl
@[simp] theorem Term.width_bin (op : TOp) (w : Nat) (l r : Term) : (Term.bin op w l r).width = w := rfl
@[simp] theorem Term.width_cmp (c : Cond) (w : Nat) (l r : Term) : (Term.cmp c w l r).width = w := rfl
@[simp] theorem Term.width_ite (w : Nat) (c l r : Term) : (Term.ite w c l r).width = w := rfl
@[simp] theorem Term.width_select (n : String) (w : Nat) (i : Term) : (Term.select n w i).width = w := rfl
@[simp] theorem Term.width_uop (op : UOp) (w : Nat) (l r : Term) : (Term.uop op w l r).width = w := rfl

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

/-- The quotient's evaluation (`floatEval` for `udiv`/`sdiv`,
asm/floats_ops.go): the operands masked to the width; a zero divisor
yields 0 (the AArch64 result); `sdiv` is the truncating `BitVec.sdiv`,
whose `MIN / -1` is `MIN` — Go's `-a` wrapped. -/
def Term.evalU (op : UOp) (w : Nat) (a b : Nat) : Nat :=
  match op with
  | .udiv => (if b = 0 then 0 else a / b) % 2 ^ w
  | .sdiv => (if b = 0 then 0 else ((BitVec.ofNat w a).sdiv (BitVec.ofNat w b)).toNat) % 2 ^ w

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
  | .uop op w l r, ρ => Term.evalU op w (l.eval ρ % 2 ^ w) (r.eval ρ % 2 ^ w)

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

/-- The verifier's division: the quotient the uninterpreted `udiv`/`sdiv`
of the operands at their width, the remainder `a - (a / b) * b` (the
machines' definition, `Oak.IntegerDivision`); the lowering then widens by
the type's signedness as it does every result (`extendTerm`), here at the
type's own width. -/
def divT (signed : Bool) (op : DivOp) (w : Nat) (l r : Term) : Term :=
  let q := Term.uop (if signed then .sdiv else .udiv) w l r
  match op with
  | .div => q
  | .rem => Term.binary .sub w l (Term.binary .mul w q r)

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

/-- A declared array's zero elements (`zeroValue`: `constTerm(0, width)`
per leaf). -/
def zeroTerms (σ : Scope) (nm : Nat → String) (w : Nat) : Nat → Scope
  | 0 => σ
  | k + 1 => (zeroTerms σ nm w k).set (nm k) (.const 0 w)

/-- A leaf's term (`elems[k].scalar`); a default the invariant rules out. -/
def leaf (σ : Scope) (nm : Nat → String) (k : Nat) : Term := (σ (nm k)).getD (.const 0 0)

/-- `loopEvent`: each carried local stands as its fresh symbol
(`paramTerm(ev.freshName(name), width)`) — on an iteration and after the
loop. -/
def freshScope (σ : Scope) (idx : Nat) : List (String × Ty) → Scope
  | [] => σ
  | (x, t) :: rest => freshScope (σ.set x (.param (loopName idx x) t.width)) idx rest

/-- A callee's locals before their first assignment (`declareLocal` binds
the initializer's term; the zero here is never read). -/
def zeroLocals (σ : Scope) : List (String × Ty) → Scope
  | [] => σ
  | (x, s) :: rest => zeroLocals (σ.set x (.const 0 s.width)) rest

/-- Element terms copied leaf by leaf (`local.agg.copy()`, `leaves(...)`). -/
def copyLeaves (src : Scope) (nmS : Nat → String) (dst : Scope) (nmD : Nat → String) : Nat → Scope
  | 0 => dst
  | k + 1 => (copyLeaves src nmS dst nmD k).set (nmD k) (leaf src nmS k)

/-- `enterCall`: each borrowed array copied into the callee's span leaves. -/
def copyIn (σ σc : Scope) : List Borrow → Scope
  | [] => σc
  | b :: bs => copyIn σ (copyLeaves σ b.nm σc (elemName b.s) b.n) bs

/-- `enterCall`'s restore: the callee's final span leaves written back to
the owners (every leaf, as `leaves(final.agg, b.owner, …)` copies them). -/
def copyOut (σf σ : Scope) : List Borrow → Scope
  | [] => σ
  | b :: bs => copyOut σf (copyLeaves σf (elemName b.s) σ b.nm b.n) bs

/-- `elementUnderIndex`: the last element, then from the second-to-last
down `mergeValues(cmpTerm("eq", index, k), elems[k], out)`, so the first
element's select is outermost. `readArr σ ti x k rem` is the read from
element `k` with `rem` elements after it. -/
def readArr (σ : Scope) (ti : Term) (nm : Nat → String) : Nat → Nat → Term
  | k, 0 => leaf σ nm k
  | k, rem + 1 => Term.selectArm (caseCond ti 32 k) (leaf σ nm k) (readArr σ ti nm (k + 1) rem)

/-- `assignUnderIndex`: the value lowered once, every element `k` taking it
under `index == k` (`iteTerm(truncate(cond, 1), value, elems[k])`); a
literal index folds the conditions and leaves exactly one element
replaced, as `placeOf` does directly. -/
def writeArr (σ : Scope) (ti tv : Term) (nm : Nat → String) : Nat → Scope
  | 0 => σ
  | k + 1 => (writeArr σ ti tv nm k).set (nm k) (Term.iteT (caseCond ti 32 k) tv (leaf σ nm k))

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
(`enterCall`, `inlineCall`); a call that borrows arrays through span
parameters copies the owners' leaves into the callee's span leaves, runs
the callee's statements, writes the span leaves back and binds the results
— the scalar result, or the leaves of the record `inlineCallValue` builds
— in the caller (`enterCall`'s `bound`, `borrows` and restore); a record local is declared as its field
leaves from the literal (`declareLocal`, `aggregateValue`), read and
written as the scalar locals they are (`readPlace`, `assignPlace`); a
statement-level conditional runs each arm
on the locals before it and, for every local an arm assigned, selects
between the arms' terms by the condition (`lowerConditionalStatement`:
`iteTerm(truncate(cond, 1), afterTrue, afterFalse)`); a loop unrolls while
its lowered condition folds to a non-zero constant (`lowerWhile`); a
data-dependent loop is summarized (`loopEvent`): the carried locals take
fresh symbols, the condition and the body are lowered over them — the
event's `cond` and `next`, which `verifyLoops` matches against the asm
side's — and the code after the loop reads the symbols; an
integer-constant match compares the scrutinee with each literal
(`matchArms`) and selects arm by arm into the fallback (`selectMatch`,
`lowerMatchStatement`); an owned array is declared as its zero leaves
(`zeroValue`) or its literal's elements (`aggregateValue`'s `ArrayLiteral`,
each element at the element type), read through `elementUnderIndex` and
written through `assignUnderIndex`, the index at width 32 — the verifier's
`elems`, each leaf under the name the seam gives it; a span
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
  | σ, _, t, .divRem op a b => (lowerT σ a).bind fun l => (lowerT σ b).bind fun r =>
      some (extendTerm (divT t.signed op t.width l r) t.width t.width t.signed)
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
  | σ, _, _, .call _ _ body args => (bindTerms id σ args (fun _ => none)).bind fun σ' => lowerT σ' body
  | σ, _, _, .recDecl r _ fields b => (bindTerms (fieldName r) σ fields σ).bind fun σ' => lowerT σ' b
  | σ, _, _, .whileEvent idx c body rest =>
    (lowerT (freshScope σ idx (carriedOf body)) c).bind fun _ =>
    (runTerms (freshScope σ idx (carriedOf body)) body).bind fun _ =>
    lowerT (freshScope σ idx (carriedOf body)) rest
  | σ, _, _, .callX params locals bs _ _ stmts results args rest =>
    (bindTerms id σ args (fun _ => none)).bind fun σp =>
    (runTerms (copyIn σ (zeroLocals σp locals) bs) stmts).bind fun σf =>
    (bindTerms id σf results (copyOut σf σ bs)).bind fun σ' => lowerT σ' rest
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
  | σ, _, _, .arrDecl nm e n _ b => lowerT (zeroTerms σ nm e.width n) b
  | σ, _, _, .arrLit nm e n _ items b => (bindTerms id σ items σ).bind fun σ' => lowerT σ' b
  | σ, _, e, .arrGet _ n nm _ _ i => (lowerT σ i).bind fun ti => some (adaptWidth (readArr σ ti nm 0 (n - 1)) e.width)
  | σ, _, _, .arrSetE (n := n) nm _ _ i v rest =>
    (lowerT σ i).bind fun ti => (lowerT σ v).bind fun tv => lowerT (writeArr σ ti tv nm n) rest
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
  | σ, _, .arrSet (n := n) nm _ _ i v rest =>
    (lowerT σ i).bind fun ti => (lowerT σ v).bind fun tv => runTerms (writeArr σ ti tv nm n) rest
  | σ, _, .loopEvent idx c body rest =>
    (lowerT (freshScope σ idx (carriedOf body)) c).bind fun _ =>
    (runTerms (freshScope σ idx (carriedOf body)) body).bind fun _ =>
    runTerms (freshScope σ idx (carriedOf body)) rest
  | σ, _, .callS params locals bs _ _ _ stmts results args rest =>
    (bindTerms id σ args (fun _ => none)).bind fun σp =>
    (runTerms (copyIn σ (zeroLocals σp locals) bs) stmts).bind fun σf =>
    (bindTerms id σf results (copyOut σf σ bs)).bind fun σ' => runTerms σ' rest
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
/-- `enterCall`'s `bound`, and `aggregateValue`'s record literal: each
argument lowered in the caller's scope at its width and bound under its
name, in order (a record's fields in the type's order, each leaf `r.f`). -/
def bindTerms {P : Params} {S : Spans} (nm : String → String) (σ : Scope) : {Γ : Locals} → {ps : List (String × Ty)} → Args P S Γ ps → Scope → Option Scope
  | _, _, .nil, acc => some acc
  | _, _, .cons (x := x) a rest, acc => (lowerT σ a).bind fun ta => bindTerms nm σ rest (acc.set (nm x) ta)
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
  | .divRem _ a b =>
    simp only [lowerT, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨l, -, r, -, rfl⟩ := h
    exact extendTerm_width _ _ _ _
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
  | .recDecl r fs fields b =>
    simp only [lowerT, Option.bind_eq_some_iff] at h
    obtain ⟨σ', -, hb⟩ := h
    exact lowerT_width b _ _ hb
  | .callX params locals bs hb hc stmts results args rest =>
    simp only [lowerT, Option.bind_eq_some_iff] at h
    obtain ⟨σp, -, σf, -, σ', -, hr⟩ := h
    exact lowerT_width rest _ _ hr
  | .whileEvent idx c body rest =>
    simp only [lowerT, Option.bind_eq_some_iff] at h
    obtain ⟨tc, -, σb, -, hr⟩ := h
    exact lowerT_width rest _ _ hr
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
  | .arrDecl nm e n hn b => exact lowerT_width b _ _ h
  | .arrLit nm e n hn items b =>
    simp only [lowerT, Option.bind_eq_some_iff] at h
    obtain ⟨σ', -, hb⟩ := h
    exact lowerT_width b _ _ hb
  | .arrGet e n nm hn hin i =>
    simp only [lowerT, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨ti, -, rfl⟩ := h
    exact adaptWidth_width _ _
  | .arrSetE nm hin hn32 i v rest =>
    simp only [lowerT, Option.bind_eq_some_iff] at h
    obtain ⟨ti, -, tv, -, hr⟩ := h
    exact lowerT_width rest _ _ hr
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

theorem Term.evalU_lt (op : UOp) (w a b : Nat) : Term.evalU op w a b < 2 ^ w := by
  cases op <;> simp only [Term.evalU] <;> exact Nat.mod_lt _ (Nat.two_pow_pos w)

theorem Term.uop_topPositive (op : UOp) (w : Nat) (l r : Term) : (Term.uop op w l r).topPositive := trivial

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
  | uop op w l r => exact Term.evalU_lt _ _ _ _

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
  | uop op w₀ l r =>
    simp only [truncate, Term.width_uop] at heq ⊢
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
  | uop op w₀ l r =>
    simp only [Term.width_uop] at heq hle hlt hm hself
    simp only [zeroExtend, Term.width_uop, heq, ite_false, Term.eval, Term.evalBin, hm, hlt, and_mask_of_le _ _ _ hle, Nat.mod_mod]
    exact hself _

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

/-- The signed remainder is the dividend less the truncated quotient times
the divisor at every width (`Oak.IntegerDivision.srem_eq_sub_sdiv_mul_8`
decides it at the byte width): through the integers, where `tmod` is
`a - b * tdiv a b` and lies strictly inside the signed range. -/
theorem srem_eq_sub_sdiv_mul {w : Nat} (x y : BitVec w) : x.srem y = x - x.sdiv y * y := by
  cases w with
  | zero => simp [BitVec.eq_nil x]
  | succ w' =>
    apply BitVec.toInt_inj.mp
    rw [BitVec.toInt_srem, BitVec.toInt_sub, BitVec.toInt_mul, BitVec.toInt_sdiv,
      Int.bmod_mul_bmod, Int.sub_bmod_bmod,
      show x.toInt - x.toInt.tdiv y.toInt * y.toInt = x.toInt.tmod y.toInt from by rw [Int.tmod_def, Int.mul_comm]]
    symm
    have hx1 := BitVec.toInt_lt (x := x)
    have hx2 := BitVec.le_toInt x
    have hy1 := BitVec.toInt_lt (x := y)
    have hy2 := BitVec.le_toInt y
    have habs := Int.natAbs_tmod x.toInt y.toInt
    have hpow : (2 : Nat) ^ (w' + 1) = 2 * 2 ^ w' := by rw [Nat.pow_succ, Nat.mul_comm]
    have hpow' : (2 : Int) ^ (w' + 1 - 1) = ((2 ^ w' : Nat) : Int) := by simp
    rw [hpow] at *
    rw [hpow'] at hx1 hx2 hy1 hy2
    -- `tmod` lies strictly inside the signed range: below the divisor's
    -- magnitude, or the dividend itself when the divisor is zero.
    apply Int.bmod_eq_of_le
    · generalize (2 ^ w' : Nat) = k at *
      by_cases hy : y.toInt = 0
      · rw [hy, Int.tmod_zero]; omega
      · have hlt : (x.toInt.tmod y.toInt).natAbs < y.toInt.natAbs := by
          rw [habs]; exact Nat.mod_lt _ (Int.natAbs_pos.mpr hy)
        omega
    · generalize (2 ^ w' : Nat) = k at *
      by_cases hy : y.toInt = 0
      · rw [hy, Int.tmod_zero]; omega
      · have hlt : (x.toInt.tmod y.toInt).natAbs < y.toInt.natAbs := by
          rw [habs]; exact Nat.mod_lt _ (Int.natAbs_pos.mpr hy)
        omega

/-- Extending a term from its own width to itself is the identity on its
value: the mask keeps every bit, the shifts by zero move none. -/
theorem extendTerm_self_eval (t : Term) (w : Nat) (signed : Bool) (ρ : Env) (hw : t.width = w) (hp : t.topPositive) (hpos : 0 < w) :
    (extendTerm t w w signed).eval ρ = t.eval ρ % 2 ^ w := by
  have hlt := Term.eval_lt t ρ hp
  rw [hw] at hlt
  have hadapt : adaptWidth t w = t := by
    simp only [adaptWidth, hw, Nat.lt_irrefl, if_false]
    exact truncate_self t w hw
  have hlow : (Term.binary .and w (adaptWidth t w) (.const (mask w) w)).eval ρ = t.eval ρ % 2 ^ w := by
    rw [hadapt, Term.binary_eval .and w (r := .const (mask w) w) ρ hp trivial]
    simp only [Term.eval, Term.evalBin, mask_mod]
    rw [and_mask_of_le _ _ _ (Nat.le_refl w), Nat.mod_mod]
  have hlowp : (Term.binary .and w (adaptWidth t w) (.const (mask w) w)).topPositive :=
    Term.binary_topPositive _ _ (adaptWidth_topPositive t w hpos hp) trivial
  unfold extendTerm
  cases signed
  · simpa using hlow
  · simp only [Bool.not_true, Bool.false_eq_true, if_false, Nat.sub_self]
    rw [Term.binary_eval .sar w (r := .const 0 w) ρ (Term.binary_topPositive .shl w (r := .const 0 w) hlowp trivial) trivial,
      Term.eval.eq_3, Term.binary_eval .shl w (r := .const 0 w) ρ hlowp trivial, Term.eval.eq_3, hlow]
    simp only [Term.eval, Term.evalBin, Nat.zero_mod, Nat.shiftLeft_zero, Nat.mod_mod, BitVec.sshiftRight_zero,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]

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

theorem leaf_topPositive {σ : Scope} (hσ : σ.wf) (nm : Nat → String) (k : Nat) : (leaf σ nm k).topPositive := by
  unfold leaf
  cases h : σ (nm k) with
  | none => trivial
  | some term => exact hσ _ term h

theorem readArr_topPositive {σ : Scope} (hσ : σ.wf) (ti : Term) (nm : Nat → String) :
    ∀ k rem, (readArr σ ti nm k rem).topPositive := by
  intro k rem
  induction rem generalizing k with
  | zero => exact leaf_topPositive hσ nm k
  | succ rem ih => exact Term.selectArm_topPositive (leaf_topPositive hσ nm k) (ih (k + 1))

theorem zeroTerms_wf {σ : Scope} (hσ : σ.wf) (nm : Nat → String) (w : Nat) : ∀ n, (zeroTerms σ nm w n).wf := by
  intro n
  induction n with
  | zero => exact hσ
  | succ n ih => exact Scope.wf_set ih trivial

theorem writeArr_wf {σ : Scope} (hσ : σ.wf) {ti tv : Term} (htv : tv.topPositive) (nm : Nat → String) : ∀ n, (writeArr σ ti tv nm n).wf := by
  intro n
  induction n with
  | zero => exact hσ
  | succ n ih => exact Scope.wf_set ih (Term.iteT_topPositive htv (leaf_topPositive hσ nm n))

theorem freshScope_wf {σ : Scope} (hσ : σ.wf) (idx : Nat) : ∀ carried, (freshScope σ idx carried).wf := by
  intro carried
  induction carried generalizing σ with
  | nil => exact hσ
  | cons p rest ih => obtain ⟨x, t⟩ := p; exact ih (Scope.wf_set hσ trivial)

theorem zeroLocals_wf {σ : Scope} (hσ : σ.wf) : ∀ ls : List (String × Ty), (zeroLocals σ ls).wf := by
  intro ls
  induction ls generalizing σ with
  | nil => exact hσ
  | cons p rest ih => obtain ⟨x, t⟩ := p; exact ih (Scope.wf_set hσ trivial)

theorem copyLeaves_wf {src dst : Scope} (hs : src.wf) (hd : dst.wf) (nmS nmD : Nat → String) :
    ∀ n, (copyLeaves src nmS dst nmD n).wf := by
  intro n
  induction n with
  | zero => exact hd
  | succ n ih => exact Scope.wf_set ih (leaf_topPositive hs nmS n)

theorem copyIn_wf {σ : Scope} (hσ : σ.wf) : ∀ (bs : List Borrow) (σc : Scope), σc.wf → (copyIn σ σc bs).wf := by
  intro bs
  induction bs with
  | nil => intro σc hc; exact hc
  | cons b bs ih => intro σc hc; exact ih _ (copyLeaves_wf hσ hc _ _ _)

theorem copyOut_wf {σf : Scope} (hf : σf.wf) : ∀ (bs : List Borrow) (σ : Scope), σ.wf → (copyOut σf σ bs).wf := by
  intro bs
  induction bs with
  | nil => intro σ hσ; exact hσ
  | cons b bs ih => intro σ hσ; exact ih _ (copyLeaves_wf hf hσ _ _ _)

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
  | .divRem (t := t) op a b =>
    simp only [lowerT, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨l, hl, r, hr, rfl⟩ := h
    apply extendTerm_topPositive _ _ _ _ t.width_pos
    cases op
    · trivial
    · exact Term.binary_topPositive _ _ (lowerT_topPositive a σ l hσ hl)
        (Term.binary_topPositive _ _ (Term.uop_topPositive _ _ _ _) (lowerT_topPositive b σ r hσ hr))
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
    exact lowerT_topPositive body _ T (bindTerms_wf args id σ _ σ' hσ Scope.wf_empty hσ') hb
  | .recDecl r fs fields b =>
    simp only [lowerT, Option.bind_eq_some_iff] at h
    obtain ⟨σ', hσ', hb⟩ := h
    exact lowerT_topPositive b _ T (bindTerms_wf fields (fieldName r) σ _ σ' hσ hσ hσ') hb
  | .callX params locals bs hb hc stmts results args rest =>
    simp only [lowerT, Option.bind_eq_some_iff] at h
    obtain ⟨σp, hp, σf, hf, σ', hres, hr⟩ := h
    have hwp := bindTerms_wf args id σ _ σp hσ Scope.wf_empty hp
    have hwf := runTerms_wf stmts _ σf (copyIn_wf hσ bs _ (zeroLocals_wf hwp locals)) hf
    exact lowerT_topPositive rest _ T (bindTerms_wf results id σf _ σ' hwf (copyOut_wf hwf bs σ hσ) hres) hr
  | .whileEvent idx c body rest =>
    simp only [lowerT, Option.bind_eq_some_iff] at h
    obtain ⟨tc, -, σb, -, hr⟩ := h
    exact lowerT_topPositive rest _ T (freshScope_wf hσ idx _) hr
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
  | .arrDecl nm e n hn b => exact lowerT_topPositive b _ T (zeroTerms_wf hσ nm e.width n) h
  | .arrLit nm e n hn items b =>
    simp only [lowerT, Option.bind_eq_some_iff] at h
    obtain ⟨σ', hσ', hb⟩ := h
    exact lowerT_topPositive b _ T (bindTerms_wf items id σ _ σ' hσ hσ hσ') hb
  | .arrGet e n nm hn hin i =>
    simp only [lowerT, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨ti, -, rfl⟩ := h
    exact adaptWidth_topPositive _ _ e.width_pos (readArr_topPositive hσ ti nm 0 (n - 1))
  | .arrSetE nm hin hn32 i v rest =>
    simp only [lowerT, Option.bind_eq_some_iff] at h
    obtain ⟨ti, -, tv, hv, hr⟩ := h
    exact lowerT_topPositive rest _ T (writeArr_wf hσ (lowerT_topPositive v σ tv hσ hv) nm _) hr
termination_by structural e
theorem bindTerms_wf {P : Params} {S : Spans} {Γ : Locals} {ps : List (String × Ty)} (args : Args P S Γ ps) :
    ∀ (nm : String → String) (σ acc σ' : Scope), σ.wf → acc.wf → bindTerms nm σ args acc = some σ' → σ'.wf := by
  intro nm σ acc σ' hσ hacc h
  match args with
  | .nil => simp only [bindTerms, Option.some.injEq] at h; subst h; exact hacc
  | .cons a rest =>
    simp only [bindTerms, Option.bind_eq_some_iff] at h
    obtain ⟨ta, ha, hr⟩ := h
    exact bindTerms_wf rest nm σ _ σ' hσ (Scope.wf_set hacc (lowerT_topPositive a σ ta hσ ha)) hr
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
  | .arrSet nm hin hn32 i v rest =>
    simp only [runTerms, Option.bind_eq_some_iff] at h
    obtain ⟨ti, -, tv, hv, hr⟩ := h
    exact runTerms_wf rest _ σ' (writeArr_wf hσ (lowerT_topPositive v σ tv hσ hv) nm _) hr
  | .callS params locals bs hb hc hrs stmts results args rest =>
    simp only [runTerms, Option.bind_eq_some_iff] at h
    obtain ⟨σp, hp, σf, hf, σ₁, hres, hr⟩ := h
    have hwp := bindTerms_wf args id σ _ σp hσ Scope.wf_empty hp
    have hwf := runTerms_wf stmts _ σf (copyIn_wf hσ bs _ (zeroLocals_wf hwp locals)) hf
    exact runTerms_wf rest _ σ' (bindTerms_wf results id σf _ σ₁ hwf (copyOut_wf hwf bs σ hσ) hres) hr
  | .loopEvent idx c body rest =>
    simp only [runTerms, Option.bind_eq_some_iff] at h
    obtain ⟨tc, -, σb, -, hr⟩ := h
    exact runTerms_wf rest _ σ' (freshScope_wf hσ idx _) hr
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

theorem Locals.set_same {Γ : Locals} {x : String} {s : Ty} (h : Γ x = some s) : Γ.set x s = Γ := by
  funext y
  unfold Locals.set
  split
  · rename_i heq; subst heq; exact h.symm
  · rfl

/-- A scope is typed by the locals: a name that is not a local has no
term; a local's term has the local's width and is well formed. -/
def Typed (Γ : Locals) (σ : Scope) : Prop :=
  (∀ x, Γ x = none → σ x = none) ∧
  (∀ x t, Γ x = some t → ∃ term, σ x = some term ∧ term.width = t.width ∧ term.topPositive)

/-- A scope's two readings agree: typed, and each local's term evaluates
to the local's `let`-bound value. -/
def Agree (Γ : Locals) (σ : Scope) (ρ : Env) (l : Vals) : Prop :=
  Typed Γ σ ∧ ∀ x t term, Γ x = some t → σ x = some term → term.eval ρ = l x

theorem Typed.wf {Γ : Locals} {σ : Scope} (h : Typed Γ σ) : σ.wf := by
  intro x term hx
  cases hΓ : Γ x with
  | none => rw [h.1 x hΓ] at hx; cases hx
  | some t =>
    obtain ⟨term', hσ, _, hp⟩ := h.2 x t hΓ
    rw [hσ] at hx; cases hx; exact hp

theorem Agree.wf {Γ : Locals} {σ : Scope} {ρ : Env} {l : Vals} (h : Agree Γ σ ρ l) : σ.wf := h.1.wf

theorem Typed.empty : Typed (fun _ => none) (fun _ => none) :=
  ⟨fun _ _ => rfl, fun _ _ h => by cases h⟩

theorem Agree.empty (ρ : Env) (l : Vals) : Agree (fun _ => none) (fun _ => none) ρ l :=
  ⟨Typed.empty, fun _ _ _ h => by cases h⟩

theorem Typed.set {Γ : Locals} {σ : Scope} (h : Typed Γ σ) (x : String) {s : Ty} {term : Term}
    (hw : term.width = s.width) (hp : term.topPositive) : Typed (Γ.set x s) (σ.set x term) := by
  constructor
  · intro y hy
    unfold Locals.set at hy; unfold Scope.set
    split at hy
    · cases hy
    · rename_i hne; rw [if_neg hne]; exact h.1 y hy
  · intro y t hy
    unfold Locals.set at hy; unfold Scope.set
    split at hy
    · rename_i heq; cases hy; exact ⟨term, by rw [if_pos heq], hw, hp⟩
    · rename_i hne
      obtain ⟨term', hσ, hw', hp'⟩ := h.2 y t hy
      exact ⟨term', by rw [if_neg hne]; exact hσ, hw', hp'⟩

theorem Agree.set {Γ : Locals} {σ : Scope} {ρ : Env} {l : Vals} (h : Agree Γ σ ρ l) (x : String) {s : Ty} {term : Term} {v : Nat}
    (hw : term.width = s.width) (hp : term.topPositive) (hv : term.eval ρ = v) :
    Agree (Γ.set x s) (σ.set x term) ρ (l.set x v) := by
  refine ⟨h.1.set x hw hp, ?_⟩
  intro y t term' hy hσ
  unfold Locals.set at hy; unfold Scope.set at hσ; unfold Vals.set
  split at hy
  · rename_i heq; rw [if_pos heq] at hσ; cases hσ; rw [if_pos heq]; exact hv
  · rename_i hne; rw [if_neg hne] at hσ; rw [if_neg hne]; exact h.2 y t term' hy hσ

/-- The value a typed scope's local evaluates to is below its width. -/
theorem Agree.value_lt {Γ : Locals} {σ : Scope} {ρ : Env} {l : Vals} (h : Agree Γ σ ρ l) {x : String} {t : Ty}
    (hx : Γ x = some t) : l x < 2 ^ t.width := by
  obtain ⟨term, hσ, hw, hp⟩ := h.1.2 x t hx
  rw [← h.2 x t term hx hσ, ← hw]
  exact Term.eval_lt term ρ hp

/-! ### Merges -/

theorem mergeScope_typed {Γ : Locals} {c : Term} {σT σF : Scope} (hT : Typed Γ σT) (hF : Typed Γ σF) :
    Typed Γ (mergeScope c σT σF) := by
  constructor
  · intro y hy
    unfold mergeScope
    rw [hT.1 y hy, hF.1 y hy]
  · intro y t hy
    obtain ⟨a, haσ, haw, hap⟩ := hT.2 y t hy
    obtain ⟨b, hbσ, hbw, hbp⟩ := hF.2 y t hy
    unfold mergeScope
    rw [haσ, hbσ]
    exact ⟨Term.selectArm c a b, rfl, by rw [Term.selectArm_width (hbw.trans haw.symm), haw], Term.selectArm_topPositive hap hbp⟩

/-- A merge under a true condition agrees with the true arm. -/
theorem merge_agree_left {Γ : Locals} {σT σF : Scope} {ρ : Env} {lT : Vals} (c : Term) (hc : c.eval ρ ≠ 0)
    (hT : Agree Γ σT ρ lT) (hF : Typed Γ σF) : Agree Γ (mergeScope c σT σF) ρ lT := by
  refine ⟨mergeScope_typed hT.1 hF, ?_⟩
  intro y t term hy hσ
  obtain ⟨a, haσ, haw, hap⟩ := hT.1.2 y t hy
  obtain ⟨b, hbσ, hbw, hbp⟩ := hF.2 y t hy
  unfold mergeScope at hσ
  rw [haσ, hbσ] at hσ
  cases hσ
  rw [Term.selectArm_eval ρ hap hbp (hbw.trans haw.symm), Term.eval.eq_5, if_pos hc,
    Nat.mod_eq_of_lt (Term.eval_lt a ρ hap)]
  exact hT.2 y t a hy haσ

/-- A merge under a false condition agrees with the false arm. -/
theorem merge_agree_right {Γ : Locals} {σT σF : Scope} {ρ : Env} {lF : Vals} (c : Term) (hc : c.eval ρ = 0)
    (hT : Typed Γ σT) (hF : Agree Γ σF ρ lF) : Agree Γ (mergeScope c σT σF) ρ lF := by
  refine ⟨mergeScope_typed hT hF.1, ?_⟩
  intro y t term hy hσ
  obtain ⟨a, haσ, haw, hap⟩ := hT.2 y t hy
  obtain ⟨b, hbσ, hbw, hbp⟩ := hF.1.2 y t hy
  unfold mergeScope at hσ
  rw [haσ, hbσ] at hσ
  cases hσ
  have hba : b.width = a.width := hbw.trans haw.symm
  rw [Term.selectArm_eval ρ hap hbp hba, Term.eval.eq_5, if_neg (fun h => h hc), ← hba,
    Nat.mod_eq_of_lt (Term.eval_lt b ρ hbp)]
  exact hF.2 y t b hy hbσ

/-! ### Arrays -/

theorem bindTypes_append (nm : String → String) (Γ : Locals) (ps qs : List (String × Ty)) :
    bindTypes nm Γ (ps ++ qs) = bindTypes nm (bindTypes nm Γ ps) qs := by
  induction ps generalizing Γ with
  | nil => rfl
  | cons p ps ih =>
    obtain ⟨x, s⟩ := p
    simp only [List.cons_append, bindTypes]
    exact ih _

theorem arrIn_bindLeaves (Γ : Locals) (nm : Nat → String) (e : Ty) (n : Nat) : ArrIn (bindLeaves Γ nm e n) nm e n := by
  intro k hk
  induction n with
  | zero => exact absurd hk (Nat.not_lt_zero k)
  | succ n ih =>
    show Locals.set (bindLeaves Γ nm e n) (nm n) e (nm k) = some e
    unfold Locals.set
    split
    · rfl
    · rename_i hne
      have hkn : k ≠ n := fun h => hne (by rw [h])
      exact ih (by omega)

/-- An array literal binds the same leaves the declaration does. -/
theorem bindTypes_arrayFields (Γ : Locals) (nm : Nat → String) (e : Ty) : ∀ n, bindTypes id Γ (arrayFields nm e n) = bindLeaves Γ nm e n := by
  intro n
  induction n generalizing Γ with
  | zero => rfl
  | succ n ih =>
    unfold arrayFields
    rw [List.range_succ, List.map_append, bindTypes_append]
    show bindTypes id (bindTypes id Γ (arrayFields nm e n)) [(nm n, e)] = bindLeaves Γ nm e (n + 1)
    rw [ih Γ]
    rfl

theorem zeroTerms_agree {Γ : Locals} {σ : Scope} {ρ : Env} {l : Vals} (h : Agree Γ σ ρ l) (nm : Nat → String) (e : Ty) :
    ∀ n, Agree (bindLeaves Γ nm e n) (zeroTerms σ nm e.width n) ρ (zeroLeaves l nm n) := by
  intro n
  induction n with
  | zero => exact h
  | succ n ih => exact ih.set (nm n) rfl trivial (by simp [Term.eval])

/-- A leaf of an array in scope: its term and its width. -/
theorem leaf_spec {Γ : Locals} {σ : Scope} {ρ : Env} {l : Vals} (h : Agree Γ σ ρ l) {nm : Nat → String} {e : Ty} {n : Nat}
    (hin : ArrIn Γ nm e n) {k : Nat} (hk : k < n) :
    (leaf σ nm k).width = e.width ∧ (leaf σ nm k).topPositive ∧ (leaf σ nm k).eval ρ = l (nm k) := by
  obtain ⟨term, hσ, hw, hp⟩ := h.1.2 _ e (hin k hk)
  have hl : leaf σ nm k = term := by unfold leaf; rw [hσ]; rfl
  rw [hl]
  exact ⟨hw, hp, h.2 _ e term (hin k hk) hσ⟩

theorem caseCond_eval_nat (sx : Term) (ρ : Env) (k : Nat) (vi : BitVec 32) (hw : sx.width = 32)
    (hx : sx.eval ρ = vi.toNat) (hk : k < 2 ^ 32) : (caseCond sx 32 k).eval ρ = if vi.toNat = k then 1 else 0 := by
  have := caseCond_eval sx 32 (BitVec.ofNat 32 k) vi ρ hw (by decide) hx
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk] at this
  rw [this]
  by_cases h : vi.toNat = k
  · rw [if_pos (BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk]; exact h)), if_pos h]
  · rw [if_neg (fun heq => h (by rw [heq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk])), if_neg h]

theorem readArr_width {Γ : Locals} {σ : Scope} {ρ : Env} {l : Vals} (h : Agree Γ σ ρ l) {nm : Nat → String} {e : Ty} {n : Nat}
    (hin : ArrIn Γ nm e n) (ti : Term) : ∀ k rem, k + rem < n → (readArr σ ti nm k rem).width = e.width := by
  intro k rem
  induction rem generalizing k with
  | zero => intro hk; exact (leaf_spec h hin (by omega)).1
  | succ rem ih =>
    intro hk
    simp only [readArr]
    rw [Term.selectArm_width (by rw [ih (k + 1) (by omega), (leaf_spec h hin (by omega : k < n)).1]), (leaf_spec h hin (by omega : k < n)).1]

/-- Reading at a symbolic index in range is the element there. -/
theorem readArr_eval {Γ : Locals} {σ : Scope} {ρ : Env} {l : Vals} (h : Agree Γ σ ρ l) {nm : Nat → String} {e : Ty} {n : Nat}
    (hin : ArrIn Γ nm e n) (hn32 : n < 2 ^ 32) (ti : Term) (vi : BitVec 32) (hw : ti.width = 32) (hti : ti.eval ρ = vi.toNat) :
    ∀ k rem, k + rem < n → k ≤ vi.toNat → vi.toNat ≤ k + rem → (readArr σ ti nm k rem).eval ρ = l (nm vi.toNat) := by
  intro k rem
  induction rem generalizing k with
  | zero =>
    intro hk hlo hhi
    have hk' : vi.toNat = k := by omega
    rw [hk']
    exact (leaf_spec h hin (by omega)).2.2
  | succ rem ih =>
    intro hk hlo hhi
    have hkn : k < n := by omega
    obtain ⟨hlw, hlp, hlv⟩ := leaf_spec h hin hkn
    have hrw := readArr_width h hin ti (k + 1) rem (by omega)
    have hrp := readArr_topPositive (Agree.wf h) ti nm (k + 1) rem
    simp only [readArr]
    rw [Term.selectArm_eval ρ hlp hrp (hrw.trans hlw.symm), Term.eval.eq_5,
      caseCond_eval_nat ti ρ k vi hw hti (by omega)]
    by_cases hvk : vi.toNat = k
    · rw [if_pos hvk, if_pos (by decide), Nat.mod_eq_of_lt (Term.eval_lt _ ρ hlp), hlv, hvk]
    · rw [if_neg hvk, if_neg (by decide), show (leaf σ nm k).width = (readArr σ ti nm (k + 1) rem).width from hlw.trans hrw.symm,
        Nat.mod_eq_of_lt (Term.eval_lt _ ρ hrp)]
      exact ih (k + 1) (by omega) (by omega) (by omega)

/-- Writing at a symbolic index in range agrees leaf by leaf. -/
theorem writeArr_agree {Γ : Locals} {σ : Scope} {ρ : Env} {l : Vals} (h : Agree Γ σ ρ l) {nm : Nat → String} {e : Ty} {n : Nat}
    (hin : ArrIn Γ nm e n) {ti tv : Term} (vi : BitVec 32) (hw : ti.width = 32) (hti : ti.eval ρ = vi.toNat)
    (htw : tv.width = e.width) (htp : tv.topPositive) (vv : BitVec e.width) (htv : tv.eval ρ = vv.toNat) (hn : n < 2 ^ 32) :
    ∀ m, m ≤ n → Agree Γ (writeArr σ ti tv nm m) ρ (writeLeaves l nm vi.toNat vv.toNat m) := by
  intro m
  induction m with
  | zero => intro _; exact h
  | succ m ih =>
    intro hm
    obtain ⟨hlw, hlp, hlv⟩ := leaf_spec h hin (by omega : m < n)
    have hA := ih (by omega)
    have hΓ : Γ.set (nm m) e = Γ := Locals.set_same (hin m (by omega))
    have := hA.set (nm m) (s := e) (term := Term.iteT (caseCond ti 32 m) tv (leaf σ nm m))
      (v := if vi.toNat = m then vv.toNat else l (nm m))
      (by rw [Term.iteT_width (hlw.trans htw.symm), htw]) (Term.iteT_topPositive htp hlp) ?_
    · rw [hΓ] at this
      exact this
    · rw [Term.iteT_eval ρ htp hlp (hlw.trans htw.symm), Term.eval.eq_5, caseCond_eval_nat ti ρ m vi hw hti (by omega)]
      by_cases hvm : vi.toNat = m
      · rw [if_pos hvm, if_pos (by decide), Nat.mod_eq_of_lt (Term.eval_lt _ ρ htp), htv, if_pos hvm]
      · rw [if_neg hvm, if_neg (by decide), show tv.width = (leaf σ nm m).width from htw.trans hlw.symm,
          Nat.mod_eq_of_lt (Term.eval_lt _ ρ hlp), hlv, if_neg hvm]

theorem writeArr_typed {Γ : Locals} {σ : Scope} (h : Typed Γ σ) {nm : Nat → String} {e : Ty} {n : Nat} (hin : ArrIn Γ nm e n)
    {ti tv : Term} (htw : tv.width = e.width) (htp : tv.topPositive) : ∀ m, m ≤ n → Typed Γ (writeArr σ ti tv nm m) := by
  intro m
  induction m with
  | zero => intro _; exact h
  | succ m ih =>
    intro hm
    obtain ⟨term, hσ, hlw, hlp⟩ := h.2 _ e (hin m (by omega))
    have hl : leaf σ nm m = term := by unfold leaf; rw [hσ]; rfl
    have hΓ : Γ.set (nm m) e = Γ := Locals.set_same (hin m (by omega))
    have := (ih (by omega)).set (nm m) (s := e) (term := Term.iteT (caseCond ti 32 m) tv (leaf σ nm m))
      (by rw [hl, Term.iteT_width (hlw.trans htw.symm), htw]) (by rw [hl]; exact Term.iteT_topPositive htp hlp)
    rw [hΓ] at this
    exact this

theorem zeroTerms_typed {Γ : Locals} {σ : Scope} (h : Typed Γ σ) (nm : Nat → String) (e : Ty) :
    ∀ n, Typed (bindLeaves Γ nm e n) (zeroTerms σ nm e.width n) := by
  intro n
  induction n with
  | zero => exact h
  | succ n ih => exact ih.set (nm n) rfl trivial

/-! ### Calls: the callee's scope and the write-back -/

theorem bindLeaves_same {Γ : Locals} {nm : Nat → String} {e : Ty} : ∀ n, ArrIn Γ nm e n → bindLeaves Γ nm e n = Γ := by
  intro n hin
  induction n with
  | zero => rfl
  | succ n ih =>
    show (bindLeaves Γ nm e n).set (nm n) e = Γ
    rw [ih (fun k hk => hin k (by omega)), Locals.set_same (hin n (by omega))]

theorem borrowsIn_cons {Γ : Locals} {b : Borrow} {bs : List Borrow} (h : borrowsIn Γ (b :: bs) = true) :
    ArrIn Γ b.nm b.e b.n ∧ borrowsIn Γ bs = true := by
  simpa only [borrowsIn, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] using h

theorem leaf_typed {Γ : Locals} {σ : Scope} (h : Typed Γ σ) {nm : Nat → String} {e : Ty} {n : Nat}
    (hin : ArrIn Γ nm e n) {k : Nat} (hk : k < n) : (leaf σ nm k).width = e.width ∧ (leaf σ nm k).topPositive := by
  obtain ⟨term, hσ, hw, hp⟩ := h.2 _ e (hin k hk)
  have hl : leaf σ nm k = term := by unfold leaf; rw [hσ]; rfl
  rw [hl]
  exact ⟨hw, hp⟩

theorem zeroLocals_typed {Γ : Locals} {σ : Scope} (h : Typed Γ σ) : ∀ ls, Typed (bindTypes id Γ ls) (zeroLocals σ ls) := by
  intro ls
  induction ls generalizing Γ σ with
  | nil => exact h
  | cons p rest ih => obtain ⟨x, t⟩ := p; exact ih (h.set x rfl trivial)

theorem zeroLocals_agree {Γ : Locals} {σ : Scope} {ρ : Env} {l : Vals} (h : Agree Γ σ ρ l) :
    ∀ ls, Agree (bindTypes id Γ ls) (zeroLocals σ ls) ρ (zeroVals l ls) := by
  intro ls
  induction ls generalizing Γ σ l with
  | nil => exact h
  | cons p rest ih => obtain ⟨x, t⟩ := p; exact ih (h.set x rfl trivial (by simp [Term.eval]))

theorem copyLeaves_typed {Γs Γd : Locals} {σs σd : Scope} (hs : Typed Γs σs) {nmS : Nat → String} {e : Ty} {n : Nat}
    (hin : ArrIn Γs nmS e n) (hd : Typed Γd σd) (nmD : Nat → String) :
    ∀ m, m ≤ n → Typed (bindLeaves Γd nmD e m) (copyLeaves σs nmS σd nmD m) := by
  intro m
  induction m with
  | zero => intro _; exact hd
  | succ m ih =>
    intro hm
    obtain ⟨hw, hp⟩ := leaf_typed hs hin (by omega : m < n)
    exact (ih (by omega)).set (nmD m) hw hp

theorem copyLeaves_agree {Γs Γd : Locals} {σs σd : Scope} {ρ : Env} {ls ld : Vals} (hs : Agree Γs σs ρ ls)
    {nmS : Nat → String} {e : Ty} {n : Nat} (hin : ArrIn Γs nmS e n) (hd : Agree Γd σd ρ ld) (nmD : Nat → String) :
    ∀ m, m ≤ n → Agree (bindLeaves Γd nmD e m) (copyLeaves σs nmS σd nmD m) ρ (copyVals ls nmS ld nmD m) := by
  intro m
  induction m with
  | zero => intro _; exact hd
  | succ m ih =>
    intro hm
    obtain ⟨hw, hp, hv⟩ := leaf_spec hs hin (by omega : m < n)
    exact (ih (by omega)).set (nmD m) hw hp hv

theorem copyIn_typed {Γ : Locals} {σ : Scope} (h : Typed Γ σ) :
    ∀ (bs : List Borrow), borrowsIn Γ bs = true → ∀ {Γc : Locals} {σc : Scope}, Typed Γc σc → Typed (bindBorrows Γc bs) (copyIn σ σc bs) := by
  intro bs
  induction bs with
  | nil => intro _ Γc σc hc; exact hc
  | cons b bs ih =>
    intro hb Γc σc hc
    obtain ⟨hin, hrest⟩ := borrowsIn_cons hb
    exact ih hrest (copyLeaves_typed h hin hc _ b.n (Nat.le_refl _))

theorem copyIn_agree {Γ : Locals} {σ : Scope} {ρ : Env} {l : Vals} (h : Agree Γ σ ρ l) :
    ∀ (bs : List Borrow), borrowsIn Γ bs = true → ∀ {Γc : Locals} {σc : Scope} {lc : Vals}, Agree Γc σc ρ lc →
      Agree (bindBorrows Γc bs) (copyIn σ σc bs) ρ (copyInVals l lc bs) := by
  intro bs
  induction bs with
  | nil => intro _ Γc σc lc hc; exact hc
  | cons b bs ih =>
    intro hb Γc σc lc hc
    obtain ⟨hin, hrest⟩ := borrowsIn_cons hb
    exact ih hrest (copyLeaves_agree h hin hc _ b.n (Nat.le_refl _))

theorem copyOut_typed {Γf : Locals} {σf : Scope} (hf : Typed Γf σf) :
    ∀ (bs : List Borrow), borrowsIn Γf (calleeSide bs) = true → ∀ {Γ : Locals} {σ : Scope}, Typed Γ σ → borrowsIn Γ bs = true →
      Typed Γ (copyOut σf σ bs) := by
  intro bs
  induction bs with
  | nil => intro _ Γ σ hσ _; exact hσ
  | cons b bs ih =>
    intro hc Γ σ hσ hb
    obtain ⟨hcin, hcrest⟩ := borrowsIn_cons (by simpa only [calleeSide, List.map_cons] using hc)
    obtain ⟨hin, hrest⟩ := borrowsIn_cons hb
    have := copyLeaves_typed hf hcin hσ b.nm b.n (Nat.le_refl _)
    rw [bindLeaves_same b.n hin] at this
    exact ih hcrest this hrest

theorem copyOut_agree {Γf : Locals} {σf : Scope} {ρ : Env} {lf : Vals} (hf : Agree Γf σf ρ lf) :
    ∀ (bs : List Borrow), borrowsIn Γf (calleeSide bs) = true → ∀ {Γ : Locals} {σ : Scope} {l : Vals}, Agree Γ σ ρ l →
      borrowsIn Γ bs = true → Agree Γ (copyOut σf σ bs) ρ (copyOutVals lf l bs) := by
  intro bs
  induction bs with
  | nil => intro _ Γ σ l hσ _; exact hσ
  | cons b bs ih =>
    intro hc Γ σ l hσ hb
    obtain ⟨hcin, hcrest⟩ := borrowsIn_cons (by simpa only [calleeSide, List.map_cons] using hc)
    obtain ⟨hin, hrest⟩ := borrowsIn_cons hb
    have := copyLeaves_agree hf hcin hσ b.nm b.n (Nat.le_refl _)
    rw [bindLeaves_same b.n hin] at this
    exact ih hcrest this hrest

/-! ### Loops -/

theorem unroll_typed {Γ : Locals} {cond : Scope → Option Term} {body : Scope → Option Scope}
    (hb : ∀ σ σ', Typed Γ σ → body σ = some σ' → Typed Γ σ') :
    ∀ n σ σ', Typed Γ σ → unroll cond body n σ = some σ' → Typed Γ σ' := by
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

/-- Unrolling agrees with the fuel-indexed loop whenever both run: while
the folded condition is a non-zero constant the extraction's condition is
`1` and both run the body; a zero constant is `0` and both stop. -/
theorem unroll_agree {Γ : Locals} {ρ : Env} {condT : Scope → Option Term} {bodyT : Scope → Option Scope}
    {condX : Vals → Option (BitVec 1)} {bodyX : Vals → Option Vals}
    (hc : ∀ σ l tc cv, Agree Γ σ ρ l → condT σ = some tc → condX l = some cv → tc.eval ρ = cv.toNat)
    (hb : ∀ σ l σ' l', Agree Γ σ ρ l → bodyT σ = some σ' → bodyX l = some l' → Agree Γ σ' ρ l') :
    ∀ n F σ l σ' l', Agree Γ σ ρ l → unroll condT bodyT n σ = some σ' → loopX condX bodyX F l = some l' →
      Agree Γ σ' ρ l' := by
  intro n
  induction n with
  | zero => intro F σ l σ' l' _ h; simp [unroll] at h
  | succ n ih =>
    intro F σ l σ' l' hA h hX
    cases F with
    | zero => simp [loopX] at hX
    | succ F' =>
    simp only [unroll, Option.bind_eq_some_iff] at h
    obtain ⟨tc, htc, h⟩ := h
    simp only [loopX, Option.bind_eq_some_iff] at hX
    obtain ⟨cv, hcv, hX⟩ := hX
    have heq := hc σ l tc cv hA htc hcv
    split at h
    · rename_i v w
      simp only [Term.eval] at heq
      split at h
      · rename_i hz
        simp only [Option.some.injEq] at h
        subst h
        have hcv0 : cv.toNat = 0 := by rw [← heq, hz]
        have hne : cv ≠ 1 := fun h1 => (BitVec1_ne_zero_iff cv).mpr h1 hcv0
        rw [if_neg hne, Option.some.injEq] at hX
        subst hX
        exact hA
      · rename_i hnz
        have h1 : cv = 1 := (BitVec1_ne_zero_iff cv).mp (by rw [← heq]; exact hnz)
        rw [if_pos h1] at hX
        simp only [Option.bind_eq_some_iff] at h hX
        obtain ⟨σ₁, hσ₁, hrest⟩ := h
        obtain ⟨l₁, hl₁, hXrest⟩ := hX
        exact ih F' σ₁ l₁ σ' l' (hb σ l σ₁ l₁ hA hσ₁ hl₁) hrest hXrest
    · simp at h

theorem bindTerms_typed {P : Params} {S : Spans} {Γ : Locals} {ps : List (String × Ty)} (args : Args P S Γ ps) :
    ∀ (nm : String → String) (σ : Scope), σ.wf → ∀ (Γ0 : Locals) (acc σ' : Scope), Typed Γ0 acc →
      bindTerms nm σ args acc = some σ' → Typed (bindTypes nm Γ0 ps) σ' := by
  intro nm σ hσ Γ0 acc σ' h0 h
  match args with
  | .nil => simp only [bindTerms, Option.some.injEq] at h; subst h; exact h0
  | .cons (x := x) a rest =>
    simp only [bindTerms, Option.bind_eq_some_iff] at h
    obtain ⟨ta, ha, hr⟩ := h
    exact bindTerms_typed rest nm σ hσ _ _ σ' (h0.set (nm x) (lowerT_width a σ ta ha) (lowerT_topPositive a σ ta hσ ha)) hr
termination_by structural args

/-! ### Data-dependent loops: the fresh symbols -/

theorem freshScope_not_mem (σ : Scope) (idx : Nat) : ∀ (carried : List (String × Ty)) (y : String),
    (∀ p, p ∈ carried → p.1 ≠ y) → freshScope σ idx carried y = σ y := by
  intro carried
  induction carried generalizing σ with
  | nil => intro y _; rfl
  | cons p rest ih =>
    intro y hy
    obtain ⟨x, t⟩ := p
    simp only [freshScope]
    rw [ih _ y (fun q hq => hy q (List.mem_cons_of_mem _ hq))]
    unfold Scope.set
    rw [if_neg (Ne.symm (hy (x, t) (List.mem_cons_self)))]

theorem freshScope_mem {Γ : Locals} (σ : Scope) (idx : Nat) : ∀ (carried : List (String × Ty)), CarriedIn Γ carried →
    ∀ (y : String) (t : Ty), Γ y = some t → (∃ p, p ∈ carried ∧ p.1 = y) →
      freshScope σ idx carried y = some (.param (loopName idx y) t.width) := by
  intro carried
  induction carried generalizing σ with
  | nil => intro _ y t _ h; obtain ⟨p, hp, -⟩ := h; cases hp
  | cons p rest ih =>
    intro hc y t hy hmem
    obtain ⟨x, s⟩ := p
    simp only [freshScope]
    by_cases hin : ∃ q, q ∈ rest ∧ q.1 = y
    · exact ih _ (fun q hq => hc q (List.mem_cons_of_mem _ hq)) y t hy hin
    · rw [freshScope_not_mem _ _ rest y (fun q hq hqy => hin ⟨q, hq, hqy⟩)]
      obtain ⟨q, hq, hqy⟩ := hmem
      rcases List.mem_cons.mp hq with rfl | hq'
      · simp only at hqy
        subst hqy
        have hs : Γ x = some s := hc (x, s) List.mem_cons_self
        rw [hs] at hy
        cases hy
        unfold Scope.set
        rw [if_pos rfl]
      · exact absurd ⟨q, hq', hqy⟩ hin

theorem freshScope_typed {Γ : Locals} {σ : Scope} (h : Typed Γ σ) (idx : Nat) {carried : List (String × Ty)} (hc : CarriedIn Γ carried) :
    Typed Γ (freshScope σ idx carried) := by
  constructor
  · intro y hy
    rw [freshScope_not_mem σ idx carried y (fun p hp hpy => by rw [← hpy, hc p hp] at hy; cases hy)]
    exact h.1 y hy
  · intro y t hy
    by_cases hin : ∃ p, p ∈ carried ∧ p.1 = y
    · exact ⟨_, freshScope_mem σ idx carried hc y t hy hin, rfl, trivial⟩
    · rw [freshScope_not_mem σ idx carried y (fun p hp hpy => hin ⟨p, hp, hpy⟩)]
      exact h.2 y t hy

theorem freshDenote_sound {ρ : Env} {idx : Nat} {carried : List (String × Ty)} {l' : Vals} (h : freshDenote ρ idx carried l' = true) :
    ∀ p, p ∈ carried → ρ (loopName idx p.1) % 2 ^ p.2.width = l' p.1 := by
  intro p hp
  unfold freshDenote at h
  rw [List.all_eq_true] at h
  exact beq_iff_eq.mp (h p hp)

theorem carriedOf_in {P : Params} {S : Spans} {Γ : Locals} (body : Stmts P S Γ) : CarriedIn Γ (carriedOf body) := by
  intro p hp
  unfold carriedOf at hp
  rw [List.mem_filterMap] at hp
  obtain ⟨y, -, hy⟩ := hp
  cases hΓ : Γ y with
  | none => rw [hΓ] at hy; cases hy
  | some t => rw [hΓ] at hy; simp only [Option.map_some, Option.some.injEq] at hy; subst hy; exact hΓ

/-- A name the body assigns is carried (it is a local, by the statements'
side conditions). -/
theorem carriedOf_covers {P : Params} {S : Spans} {Γ : Locals} (body : Stmts P S Γ) {y : String} (hy : y ∈ body.assigned)
    {t : Ty} (hΓ : Γ y = some t) : (y, t) ∈ carriedOf body := by
  unfold carriedOf
  rw [List.mem_filterMap]
  exact ⟨y, hy, by rw [hΓ]; rfl⟩

theorem bindTypes_not_mem (nm : String → String) (Γ : Locals) : ∀ (ps : List (String × Ty)) (y : String),
    (∀ p, p ∈ ps → nm p.1 ≠ y) → bindTypes nm Γ ps y = Γ y := by
  intro ps
  induction ps generalizing Γ with
  | nil => intro y _; rfl
  | cons q rest ih =>
    intro y hy
    obtain ⟨x, s⟩ := q
    simp only [bindTypes]
    rw [ih _ y (fun p hp => hy p (List.mem_cons_of_mem _ hp))]
    unfold Locals.set
    rw [if_neg (Ne.symm (hy (x, s) List.mem_cons_self))]

/-- A name a statement list assigns is a local, by the statements' side
conditions. -/
theorem bindTypes_mem_some (nm : String → String) (Γ : Locals) : ∀ (ps : List (String × Ty)) (p : String × Ty), p ∈ ps →
    ∃ t, bindTypes nm Γ ps (nm p.1) = some t := by
  intro ps
  induction ps generalizing Γ with
  | nil => intro p hp; cases hp
  | cons q rest ih =>
    intro p hp
    obtain ⟨x, s⟩ := q
    simp only [bindTypes]
    rcases List.mem_cons.mp hp with rfl | hp'
    · by_cases hin : ∃ q', q' ∈ rest ∧ nm q'.1 = nm x
      · obtain ⟨q', hq', hq'y⟩ := hin
        obtain ⟨t, ht⟩ := ih _ q' hq'
        exact ⟨t, by rw [← hq'y]; exact ht⟩
      · refine ⟨s, ?_⟩
        rw [bindTypes_not_mem nm _ rest (nm x) (fun q' hq' hq'y => hin ⟨q', hq', hq'y⟩)]
        unfold Locals.set
        rw [if_pos rfl]
    · exact ih _ p hp'

mutual
theorem assigned_local {P : Params} {S : Spans} {Γ : Locals} (st : Stmts P S Γ) : ∀ {y : String}, y ∈ st.assigned → ∃ t, Γ y = some t := by
  intro y hy
  match st with
  | .nil => simp [Stmts.assigned] at hy
  | .assign x hx e rest =>
    simp only [Stmts.assigned, List.mem_cons] at hy
    rcases hy with rfl | hy
    · exact ⟨_, hx⟩
    · exact assigned_local rest hy
  | .cond c armT armF rest =>
    simp only [Stmts.assigned, List.mem_append] at hy
    rcases hy with (hy | hy) | hy
    · exact assigned_local armT hy
    · exact assigned_local armF hy
    · exact assigned_local rest hy
  | .loop c body rest =>
    simp only [Stmts.assigned, List.mem_append] at hy
    rcases hy with hy | hy
    · exact assigned_local body hy
    · exact assigned_local rest hy
  | .matchS x arms rest =>
    simp only [Stmts.assigned, List.mem_append] at hy
    rcases hy with hy | hy
    · exact armsAssigned_local arms hy
    · exact assigned_local rest hy
  | .arrSet (e := e) (n := n) nm hin hn32 i v rest =>
    simp only [Stmts.assigned, List.mem_append] at hy
    rcases hy with hy | hy
    · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hy
      exact ⟨e, hin k (List.mem_range.mp hk)⟩
    · exact assigned_local rest hy
  | .loopEvent idx c body rest =>
    simp only [Stmts.assigned, List.mem_append] at hy
    rcases hy with hy | hy
    · exact assigned_local body hy
    · exact assigned_local rest hy
  | .callS (rs := rs) params locals bs hb hc hrs stmts results args rest =>
    simp only [Stmts.assigned, List.mem_append] at hy
    rcases hy with (hy | hy) | hy
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hy
      obtain ⟨t, ht⟩ := bindTypes_mem_some id Γ rs p hp
      rw [hrs] at ht
      exact ⟨t, ht⟩
    · obtain ⟨b, hb', hk⟩ := List.mem_flatMap.mp hy
      obtain ⟨k, hk', rfl⟩ := List.mem_map.mp hk
      have hin : ArrIn Γ b.nm b.e b.n := by
        unfold borrowsIn at hb
        rw [List.all_eq_true] at hb
        exact decide_eq_true_eq.mp (hb b hb')
      exact ⟨b.e, hin k (List.mem_range.mp hk')⟩
    · exact assigned_local rest hy
termination_by structural st
theorem armsAssigned_local {P : Params} {S : Spans} {Γ : Locals} {s : Ty} (arms : ArmsS P S Γ s) : ∀ {y : String}, y ∈ arms.assigned → ∃ t, Γ y = some t := by
  intro y hy
  match arms with
  | .fallback st => exact assigned_local st hy
  | .case k st rest =>
    simp only [ArmsS.assigned, List.mem_append] at hy
    rcases hy with hy | hy
    · exact assigned_local st hy
    · exact armsAssigned_local rest hy
termination_by structural arms
end

/-- A name outside the carried locals is one the body does not assign. -/
theorem not_carried_not_assigned {P : Params} {S : Spans} {Γ : Locals} (body : Stmts P S Γ) {y : String}
    (h : ∀ p, p ∈ carriedOf body → p.1 ≠ y) : y ∉ body.assigned := by
  intro hy
  obtain ⟨t, ht⟩ := assigned_local body hy
  exact h (y, t) (carriedOf_covers body hy ht) rfl

/-- After a summarized loop the scope agrees with the exit values: a
carried local is its fresh symbol, which denotes its exit value; any other
local is untouched by the body and keeps its value. -/
theorem freshScope_agree {Γ : Locals} {σ : Scope} {ρ : Env} {l l' : Vals} (h : Agree Γ σ ρ l) (idx : Nat)
    {carried : List (String × Ty)} (hc : CarriedIn Γ carried) (hd : ∀ p, p ∈ carried → ρ (loopName idx p.1) % 2 ^ p.2.width = l' p.1)
    (hout : ∀ y, (∀ p, p ∈ carried → p.1 ≠ y) → l' y = l y) : Agree Γ (freshScope σ idx carried) ρ l' := by
  refine ⟨freshScope_typed h.1 idx hc, ?_⟩
  intro y t term hy hσ
  by_cases hin : ∃ p, p ∈ carried ∧ p.1 = y
  · rw [freshScope_mem σ idx carried hc y t hy hin] at hσ
    cases hσ
    obtain ⟨⟨py, pt⟩, hp, hpy⟩ := hin
    simp only at hpy
    subst hpy
    have hpt : pt = t := by
      have := hc (py, pt) hp
      simp only at this
      rw [this] at hy
      exact Option.some.inj hy
    subst hpt
    simp only [Term.eval]
    exact hd (py, pt) hp
  · have hn : ∀ p, p ∈ carried → p.1 ≠ y := fun p hp hpy => hin ⟨p, hp, hpy⟩
    rw [freshScope_not_mem σ idx carried y hn] at hσ
    rw [hout y hn]
    exact h.2 y t term hy hσ

/-! ### Names a statement list leaves alone -/

theorem loopX_unassigned {cond : Vals → Option (BitVec 1)} {body : Vals → Option Vals} {y : String}
    (hb : ∀ l l', body l = some l' → l' y = l y) :
    ∀ n l l', loopX cond body n l = some l' → l' y = l y := by
  intro n
  induction n with
  | zero => intro l l' h; simp [loopX] at h
  | succ n ih =>
    intro l l' h
    simp only [loopX, Option.bind_eq_some_iff] at h
    obtain ⟨cv, -, h⟩ := h
    split at h
    · simp only [Option.bind_eq_some_iff] at h
      obtain ⟨l₁, h1, h2⟩ := h
      rw [ih l₁ l' h2, hb l l₁ h1]
    · simp only [Option.some.injEq] at h; subst h; rfl

theorem writeLeaves_unassigned (l : Vals) (nm : Nat → String) (i v : Nat) {y : String} :
    ∀ n, (∀ k, k < n → nm k ≠ y) → writeLeaves l nm i v n y = l y := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro hn
    simp only [writeLeaves]
    unfold Vals.set
    rw [if_neg (Ne.symm (hn n (Nat.lt_succ_self n)))]
    exact ih (fun k hk => hn k (Nat.lt_succ_of_lt hk))

theorem copyVals_unassigned (src : Vals) (nmS : Nat → String) (dst : Vals) (nmD : Nat → String) {y : String} :
    ∀ n, (∀ k, k < n → nmD k ≠ y) → copyVals src nmS dst nmD n y = dst y := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro hn
    simp only [copyVals]
    unfold Vals.set
    rw [if_neg (Ne.symm (hn n (Nat.lt_succ_self n)))]
    exact ih (fun k hk => hn k (Nat.lt_succ_of_lt hk))

theorem copyOutVals_unassigned (lf : Vals) {y : String} :
    ∀ (bs : List Borrow) (l : Vals), (∀ b, b ∈ bs → ∀ k, k < b.n → b.nm k ≠ y) → copyOutVals lf l bs y = l y := by
  intro bs
  induction bs with
  | nil => intro l _; rfl
  | cons b bs ih =>
    intro l hb
    simp only [copyOutVals]
    rw [ih _ (fun b' hb' => hb b' (List.mem_cons_of_mem _ hb')),
      copyVals_unassigned lf (elemName b.s) l b.nm b.n (hb b List.mem_cons_self)]

theorem bindVals_unassigned {P : Params} {S : Spans} {Γ : Locals} {ps : List (String × Ty)} (args : Args P S Γ ps) (nm : String → String) :
    ∀ (ρ : Env) (l acc l' : Vals) (F : Nat) {y : String}, (∀ p, p ∈ ps → nm p.1 ≠ y) →
      bindVals nm args ρ l acc F = some l' → l' y = acc y := by
  intro ρ l acc l' F y hps h
  match args with
  | .nil => simp only [bindVals, Option.some.injEq] at h; subst h; rfl
  | .cons (x := x) (s := s) a rest =>
    simp only [bindVals, Option.bind_eq_some_iff] at h
    obtain ⟨va, -, hr⟩ := h
    rw [bindVals_unassigned rest nm ρ l _ l' F (fun p hp => hps p (List.mem_cons_of_mem _ hp)) hr]
    unfold Vals.set
    rw [if_neg (Ne.symm (hps (x, s) List.mem_cons_self))]
termination_by structural args

mutual
/-- A name a statement list does not assign keeps its value. -/
theorem runVals_unassigned {P : Params} {S : Spans} {Γ : Locals} (st : Stmts P S Γ) :
    ∀ (ρ : Env) (l l' : Vals) (F : Nat) {y : String}, y ∉ st.assigned → runVals st ρ l F = some l' → l' y = l y := by
  intro ρ l l' F y hy hv
  match st with
  | .nil => simp only [runVals, Option.some.injEq] at hv; subst hv; rfl
  | .assign x hx e rest =>
    simp only [Stmts.assigned, List.mem_cons, not_or] at hy
    simp only [runVals, Option.bind_eq_some_iff] at hv
    obtain ⟨ve, -, hvr⟩ := hv
    rw [runVals_unassigned rest ρ _ l' F hy.2 hvr]
    unfold Vals.set
    rw [if_neg hy.1]
  | .cond c armT armF rest =>
    simp only [Stmts.assigned, List.mem_append, not_or] at hy
    simp only [runVals, Option.bind_eq_some_iff] at hv
    obtain ⟨cv, -, l₁, h₁, hvr⟩ := hv
    rw [runVals_unassigned rest ρ _ l' F hy.2 hvr]
    split at h₁
    · exact runVals_unassigned armT ρ l l₁ F hy.1.1 h₁
    · exact runVals_unassigned armF ρ l l₁ F hy.1.2 h₁
  | .loop c body rest =>
    simp only [Stmts.assigned, List.mem_append, not_or] at hy
    simp only [runVals, Option.bind_eq_some_iff] at hv
    obtain ⟨l₁, hl₁, hvr⟩ := hv
    rw [runVals_unassigned rest ρ _ l' F hy.2 hvr]
    exact loopX_unassigned (fun l₀ l₂ h₀ => runVals_unassigned body ρ l₀ l₂ F hy.1 h₀) _ l l₁ hl₁
  | .matchS x arms rest =>
    simp only [Stmts.assigned, List.mem_append, not_or] at hy
    simp only [runVals, Option.bind_eq_some_iff] at hv
    obtain ⟨vx, -, l₁, hl₁, hvr⟩ := hv
    rw [runVals_unassigned rest ρ _ l' F hy.2 hvr]
    exact armsVals_unassigned arms ρ l l₁ F vx hy.1 hl₁
  | .arrSet (n := n) nm hin hn32 i v rest =>
    simp only [Stmts.assigned, List.mem_append, not_or] at hy
    simp only [runVals, Option.bind_eq_some_iff] at hv
    obtain ⟨vi, -, vv, -, hv⟩ := hv
    split at hv
    · rw [runVals_unassigned rest ρ _ l' F hy.2 hv]
      exact writeLeaves_unassigned l nm _ _ n (fun k hk hk' => hy.1 (List.mem_map.mpr ⟨k, List.mem_range.mpr hk, hk'⟩))
    · cases hv
  | .loopEvent idx c body rest =>
    simp only [Stmts.assigned, List.mem_append, not_or] at hy
    simp only [runVals, Option.bind_eq_some_iff] at hv
    obtain ⟨l₁, hl₁, hv⟩ := hv
    split at hv
    · rw [runVals_unassigned rest ρ _ l' F hy.2 hv]
      exact loopX_unassigned (fun l₀ l₂ h₀ => runVals_unassigned body ρ l₀ l₂ F hy.1 h₀) _ l l₁ hl₁
    · cases hv
  | .callS (rs := rs) params locals bs hb hc hrs stmts results args rest =>
    simp only [Stmts.assigned, List.mem_append, not_or] at hy
    simp only [runVals, Option.bind_eq_some_iff] at hv
    obtain ⟨lp, -, lf, -, l₁, hl₁, hvr⟩ := hv
    rw [runVals_unassigned rest ρ _ l' F hy.2 hvr,
      bindVals_unassigned results id ρ lf _ l₁ F (fun p hp hpy => hy.1.1 (List.mem_map.mpr ⟨p, hp, hpy⟩)) hl₁]
    exact copyOutVals_unassigned lf bs l (fun b hb' k hk hk' => hy.1.2 (List.mem_flatMap.mpr ⟨b, hb', List.mem_map.mpr ⟨k, List.mem_range.mpr hk, hk'⟩⟩))
termination_by structural st
theorem armsVals_unassigned {P : Params} {S : Spans} {Γ : Locals} {s : Ty} (arms : ArmsS P S Γ s) :
    ∀ (ρ : Env) (l l' : Vals) (F : Nat) (vx : BitVec s.width) {y : String}, y ∉ arms.assigned →
      armsVals vx arms ρ l F = some l' → l' y = l y := by
  intro ρ l l' F vx y hy hv
  match arms with
  | .fallback st => exact runVals_unassigned st ρ l l' F hy hv
  | .case k st rest =>
    simp only [ArmsS.assigned, List.mem_append, not_or] at hy
    simp only [armsVals] at hv
    split at hv
    · exact runVals_unassigned st ρ l l' F hy.1 hv
    · exact armsVals_unassigned rest ρ l l' F vx hy.2 hv
termination_by structural arms
end

/-! ### Statements keep scopes typed -/

mutual
theorem runTerms_typed {P : Params} {S : Spans} {Γ : Locals} (st : Stmts P S Γ) :
    ∀ (σ σ' : Scope), Typed Γ σ → runTerms σ st = some σ' → Typed Γ σ' := by
  intro σ σ' hσ h
  match st with
  | .nil => simp only [runTerms, Option.some.injEq] at h; subst h; exact hσ
  | .assign x hx e rest =>
    simp only [runTerms, Option.bind_eq_some_iff] at h
    obtain ⟨te, he, hr⟩ := h
    have := hσ.set x (lowerT_width e σ te he) (lowerT_topPositive e σ te hσ.wf he)
    rw [Locals.set_same hx] at this
    exact runTerms_typed rest _ σ' this hr
  | .cond c armT armF rest =>
    simp only [runTerms, Option.bind_eq_some_iff] at h
    obtain ⟨tc, -, σT, hT, σF, hF, hr⟩ := h
    exact runTerms_typed rest _ σ' (mergeScope_typed (runTerms_typed armT σ σT hσ hT) (runTerms_typed armF σ σF hσ hF)) hr
  | .loop c body rest =>
    simp only [runTerms, Option.bind_eq_some_iff] at h
    obtain ⟨σ₁, hσ₁, hr⟩ := h
    exact runTerms_typed rest _ σ' (unroll_typed (fun σ₀ σ₂ h₀ h₂ => runTerms_typed body σ₀ σ₂ h₀ h₂) _ σ σ₁ hσ hσ₁) hr
  | .matchS x arms rest =>
    simp only [runTerms, Option.bind_eq_some_iff] at h
    obtain ⟨sx, -, σ₁, h₁, hr⟩ := h
    exact runTerms_typed rest _ σ' (armsST_typed arms σ sx σ₁ hσ h₁) hr
  | .arrSet nm hin hn32 i v rest =>
    simp only [runTerms, Option.bind_eq_some_iff] at h
    obtain ⟨ti, -, tv, hv, hr⟩ := h
    exact runTerms_typed rest _ σ' (writeArr_typed hσ hin (lowerT_width v σ tv hv) (lowerT_topPositive v σ tv hσ.wf hv) _ (Nat.le_refl _)) hr
  | .loopEvent idx c body rest =>
    simp only [runTerms, Option.bind_eq_some_iff] at h
    obtain ⟨tc, -, σb, -, hr⟩ := h
    exact runTerms_typed rest _ σ' (freshScope_typed hσ idx (carriedOf_in body)) hr
  | .callS params locals bs hb hc hrs stmts results args rest =>
    simp only [runTerms, Option.bind_eq_some_iff] at h
    obtain ⟨σp, hp, σf, hf, σ₁, hres, hr⟩ := h
    have htp := bindTerms_typed args id σ hσ.wf _ _ σp Typed.empty hp
    have htf := runTerms_typed stmts _ σf (copyIn_typed hσ bs hb (zeroLocals_typed htp locals)) hf
    have ht₁ := bindTerms_typed results id σf htf.wf _ _ σ₁ (copyOut_typed htf bs hc hσ hb) hres
    rw [hrs] at ht₁
    exact runTerms_typed rest _ σ' ht₁ hr
termination_by structural st
theorem armsST_typed {P : Params} {S : Spans} {Γ : Locals} {s : Ty} (arms : ArmsS P S Γ s) :
    ∀ (σ : Scope) (sx : Term) (σ' : Scope), Typed Γ σ → armsST σ sx arms = some σ' → Typed Γ σ' := by
  intro σ sx σ' hσ h
  match arms with
  | .fallback st => exact runTerms_typed st σ σ' hσ h
  | .case k st rest =>
    simp only [armsST, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨σk, hk, σr, hr, rfl⟩ := h
    exact mergeScope_typed (runTerms_typed st σ σk hσ hk) (armsST_typed rest σ sx σr hσ hr)
termination_by structural arms
end


/-! ### The theorem -/

mutual
/-- The verifier's lowering and the extraction's reading agree wherever
both run: whatever the lowering admits (`some T`) and the extraction
computes (`some v`, under any fuel), the term evaluates to the value.
Where the extraction traps (`none`: an index out of range, a fuel run
out) the lowering carries the verifier's trap obligation instead, which
`oak prove` discharges separately. The seam of
`126-verification-chain.md` §4, closed for expressions, locals, calls,
statement-level conditionals, constant matches, span elements, counted
loops and owned arrays. -/
theorem lowerT_eval {P : Params} {S : Spans} {Γ : Locals} {t : Ty} (e : Expr P S Γ t) :
    ∀ (σ : Scope) (ρ : Env) (l : Vals) (F : Nat) (T : Term) (v : BitVec t.width),
      Agree Γ σ ρ l → lowerT σ e = some T → evalX e ρ l F = some v → T.eval ρ = v.toNat := by
  intro σ ρ l F T v hA h hv
  revert v
  match e with
  | .var t x h' =>
    intro v hv
    simp only [lowerT, Option.some.injEq] at h
    simp only [evalX, Option.some.injEq] at hv
    subst h hv
    simp only [varX]
    cases hΓ : Γ x with
    | none =>
      rw [hA.1.1 x hΓ]
      simp [Term.eval]
    | some t' =>
      have ht : t' = t := by simp [resolve, hΓ] at h'; exact h'
      subst ht
      obtain ⟨term, hσ, hw, hp⟩ := hA.1.2 x t' hΓ
      have hv := hA.2 x t' term hΓ hσ
      rw [hσ]
      simp only [adaptWidth, hw, Nat.lt_irrefl, if_false, truncate_self term _ hw, hv, BitVec.toNat_ofNat]
      rw [← hv, Nat.mod_eq_of_lt (hw ▸ Term.eval_lt term ρ hp)]
  | .lit t w =>
    intro v hv
    simp only [lowerT, Option.some.injEq] at h
    simp only [evalX, Option.some.injEq] at hv
    subst h hv
    simp [Term.eval]
  | .arith (t := t) op a b =>
    intro v hv
    simp only [lowerT, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨ta, ha, tb, hb, rfl⟩ := h
    simp only [evalX, Option.bind_eq_some_iff, Option.some.injEq] at hv
    obtain ⟨va, hva, vb, hvb, rfl⟩ := hv
    have iha := lowerT_eval a σ ρ l F ta va hA ha hva
    have ihb := lowerT_eval b σ ρ l F tb vb hA hb hvb
    rw [Term.binary_eval _ _ ρ (lowerT_topPositive a σ ta (Agree.wf hA) ha) (lowerT_topPositive b σ tb (Agree.wf hA) hb)]
    cases op <;> simp [arithX, arithTOp, Term.eval, Term.evalBin, iha, ihb, Nat.add_comm]
  | .bit (t := t) op a b hs =>
    intro v hv
    simp only [lowerT, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨ta, ha, tb, hb, rfl⟩ := h
    simp only [evalX, Option.bind_eq_some_iff, Option.some.injEq] at hv
    obtain ⟨va, hva, vb, hvb, rfl⟩ := hv
    have iha := lowerT_eval a σ ρ l F ta va hA ha hva
    have ihb := lowerT_eval b σ ρ l F tb vb hA hb hvb
    have hw := va.isLt
    rw [Term.binary_eval _ _ ρ (lowerT_topPositive a σ ta (Agree.wf hA) ha) (lowerT_topPositive b σ tb (Agree.wf hA) hb)]
    cases op <;> simp only [bitX, bitTOp, Term.eval, Term.evalBin, iha, ihb, BitVec.toNat_mod_cancel]
    · rw [BitVec.toNat_and]; exact Nat.mod_eq_of_lt (Nat.and_lt_two_pow _ vb.isLt)
    · rw [BitVec.toNat_or]; exact Nat.mod_eq_of_lt (Nat.or_lt_two_pow hw vb.isLt)
    · rw [BitVec.toNat_xor]; exact Nat.mod_eq_of_lt (Nat.xor_lt_two_pow hw vb.isLt)
    · rw [BitVec.toNat_shiftLeft]
    · rw [BitVec.toNat_ushiftRight]
      exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _) hw)
  | .divPow2 (t := t) a k hk hu =>
    intro v hv
    simp only [lowerT, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨ta, ha, rfl⟩ := h
    simp only [evalX, Option.bind_eq_some_iff, Option.some.injEq] at hv
    obtain ⟨va, hva, rfl⟩ := hv
    have iha := lowerT_eval a σ ρ l F ta va hA ha hva
    have hw := va.isLt
    have hk2 : 2 ^ k < 2 ^ t.width := Nat.pow_lt_pow_right (by decide) hk
    have hkw : k < 2 ^ t.width := Nat.lt_of_lt_of_le hk (Nat.le_of_lt Nat.lt_two_pow_self)
    rw [Term.binary_eval .shr t.width (r := .const k t.width) ρ (lowerT_topPositive a σ ta (Agree.wf hA) ha) trivial]
    simp only [Term.eval, Term.evalBin, iha, BitVec.toNat_mod_cancel, BitVec.toNat_udiv,
      BitVec.toNat_ofNat, Nat.mod_mod, Nat.mod_eq_of_lt hkw, Nat.mod_eq_of_lt hk, Nat.mod_eq_of_lt hk2,
      Nat.shiftRight_eq_div_pow]
    exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hw)
  | .modPow2 (t := t) a k hk hu =>
    intro v hv
    simp only [lowerT, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨ta, ha, rfl⟩ := h
    simp only [evalX, Option.bind_eq_some_iff, Option.some.injEq] at hv
    obtain ⟨va, hva, rfl⟩ := hv
    have iha := lowerT_eval a σ ρ l F ta va hA ha hva
    have hk2 : 2 ^ k < 2 ^ t.width := Nat.pow_lt_pow_right (by decide) hk
    have hm : 2 ^ k - 1 < 2 ^ t.width := by omega
    rw [Term.binary_eval .and t.width (r := .const (2 ^ k - 1) t.width) ρ (lowerT_topPositive a σ ta (Agree.wf hA) ha) trivial]
    simp only [Term.eval, Term.evalBin, iha, BitVec.toNat_mod_cancel, BitVec.toNat_umod,
      BitVec.toNat_ofNat, Nat.mod_mod, Nat.mod_eq_of_lt hm, Nat.mod_eq_of_lt hk2,
      Nat.and_two_pow_sub_one_eq_mod]
    exact Nat.mod_eq_of_lt (Nat.lt_trans (Nat.mod_lt _ (Nat.two_pow_pos k)) hk2)
  | .divRem (t := t) op a b =>
    intro v hv
    simp only [lowerT, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨ta, ha, tb, hb, rfl⟩ := h
    simp only [evalX, Option.bind_eq_some_iff] at hv
    obtain ⟨va, hva, vb, hvb, hv⟩ := hv
    have iha := lowerT_eval a σ ρ l F ta va hA ha hva
    have ihb := lowerT_eval b σ ρ l F tb vb hA hb hvb
    have hta := lowerT_topPositive a σ ta (Agree.wf hA) ha
    have htb := lowerT_topPositive b σ tb (Agree.wf hA) hb
    have hwa := lowerT_width a σ ta ha
    -- The extraction has a value only on a nonzero divisor.
    by_cases hz : vb = 0
    · simp [hz] at hv
    simp only [hz, if_false, Option.some.injEq] at hv
    subst hv
    have hnz : vb.toNat ≠ 0 := fun h0 => hz (BitVec.eq_of_toNat_eq (by simpa using h0))
    -- The quotient term evaluates to the quotient.
    have hq : (Term.uop (if t.signed then .sdiv else .udiv) t.width ta tb).eval ρ = (divX t.signed .div va vb).toNat := by
      cases hs : t.signed <;>
        simp only [Term.eval, Term.evalU, divX, hs, Bool.false_eq_true, if_false, if_true, iha, ihb,
          BitVec.toNat_mod_cancel, hnz, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      · rw [BitVec.toNat_udiv]; exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) va.isLt)
    -- The division term at the type's width, before the identity extension.
    have hd : (divT t.signed op t.width ta tb).eval ρ = (divX t.signed op va vb).toNat := by
      cases op
      · exact hq
      · simp only [divT]
        rw [Term.binary_eval .sub t.width ρ hta (Term.binary_topPositive .mul t.width (Term.uop_topPositive _ _ _ _) htb),
          Term.eval.eq_3, Term.binary_eval .mul t.width ρ (Term.uop_topPositive _ _ _ _) htb, Term.eval.eq_3, hq, iha, ihb]
        simp only [Term.evalBin, BitVec.toNat_mod_cancel, Term.width_uop]
        cases hs : t.signed <;> simp only [divX, hs, Bool.false_eq_true, if_false, if_true]
        · rw [Oak.IntegerDivision.umod_eq_sub_udiv_mul va vb, BitVec.toNat_sub, BitVec.toNat_mul, Nat.mod_mod]
          exact congrArg (· % 2 ^ t.width) (Nat.add_comm _ _)
        · rw [srem_eq_sub_sdiv_mul va vb, BitVec.toNat_sub, BitVec.toNat_mul, Nat.mod_mod]
          exact congrArg (· % 2 ^ t.width) (Nat.add_comm _ _)
    have hdw : (divT t.signed op t.width ta tb).width = t.width := by
      cases op <;> simp [divT, Term.binary_width]
    have hdp : (divT t.signed op t.width ta tb).topPositive := by
      cases op
      · trivial
      · exact Term.binary_topPositive _ _ hta (Term.binary_topPositive _ _ (Term.uop_topPositive _ _ _ _) htb)
    rw [extendTerm_self_eval _ _ _ ρ hdw hdp t.width_pos, hd, BitVec.toNat_mod_cancel]
  | .neg (t := t) a =>
    intro v hv
    simp only [lowerT, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨ta, ha, rfl⟩ := h
    simp only [evalX, Option.bind_eq_some_iff, Option.some.injEq] at hv
    obtain ⟨va, hva, rfl⟩ := hv
    have iha := lowerT_eval a σ ρ l F ta va hA ha hva
    rw [Term.binary_eval .sub t.width (l := .const 0 t.width) ρ trivial (lowerT_topPositive a σ ta (Agree.wf hA) ha)]
    simp [Term.eval, Term.evalBin, iha]
  | .not (t := t) a =>
    intro v hv
    simp only [lowerT, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨ta, ha, rfl⟩ := h
    simp only [evalX, Option.bind_eq_some_iff, Option.some.injEq] at hv
    obtain ⟨va, hva, rfl⟩ := hv
    have iha := lowerT_eval a σ ρ l F ta va hA ha hva
    have hx : va.toNat ^^^ mask t.width = (~~~ va).toNat := by
      rw [← BitVec.xor_allOnes, BitVec.toNat_xor, BitVec.toNat_allOnes]; rfl
    rw [Term.binary_eval .xor t.width (r := .const (mask t.width) t.width) ρ (lowerT_topPositive a σ ta (Agree.wf hA) ha) trivial]
    simp only [Term.eval, Term.evalBin, iha, BitVec.toNat_mod_cancel, mask_mod, hx]
  | .conv (s := s) t a =>
    intro v hv
    simp only [lowerT, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨ta, ha, rfl⟩ := h
    simp only [evalX, Option.bind_eq_some_iff, Option.some.injEq] at hv
    obtain ⟨va, hva, rfl⟩ := hv
    have iha := lowerT_eval a σ ρ l F ta va hA ha hva
    have hs := s.width_pos
    have hta := lowerT_topPositive a σ ta (Agree.wf hA) ha
    have hwa := lowerT_width a σ ta ha
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
    intro v hv
    simp only [lowerT, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨tl, hl, tr, hr, rfl⟩ := h
    simp only [evalX, Option.bind_eq_some_iff] at hv
    obtain ⟨vl, hvl, vr, hvr, hv⟩ := hv
    cases hv
    have ihl := lowerT_eval lhs σ ρ l F tl vl hA hl hvl
    have ihr := lowerT_eval rhs σ ρ l F tr vr hA hr hvr
    rw [zeroExtend_self _ _ (truncate_width _ _), truncate_cmpT_eval _ _ ρ (lowerT_width lhs σ tl hl) s.width_pos]
    simp only [Term.eval, ihl, ihr]
    rw [lowerT_width lhs σ tl hl]
    simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq, codeOf_holds]
    cases cmpX s.signed op vl vr <;> simp
  | .ite (t := t) c a b =>
    intro v hv
    simp only [lowerT, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨tc, hc, ta, ha, tb, hb, rfl⟩ := h
    simp only [evalX, Option.bind_eq_some_iff] at hv
    obtain ⟨vc, hvc, hv⟩ := hv
    have ihc := lowerT_eval c σ ρ l F tc vc hA hc hvc
    have hwa := lowerT_width a σ ta ha
    have hwb := lowerT_width b σ tb hb
    have hpa := lowerT_topPositive a σ ta (Agree.wf hA) ha
    have hpb := lowerT_topPositive b σ tb (Agree.wf hA) hb
    rw [Term.iteT_eval ρ hpa hpb (by rw [hwb, hwa]), Term.eval.eq_5, hwa]
    have key := BitVec1_ne_zero_iff vc
    split at hv
    · rename_i h1
      have h' : tc.eval ρ ≠ 0 := by rw [ihc]; exact key.mpr h1
      rw [if_pos h', lowerT_eval a σ ρ l F ta v hA ha hv, BitVec.toNat_mod_cancel]
    · rename_i h1
      have h' : ¬ tc.eval ρ ≠ 0 := by rw [ihc]; exact fun hne => h1 (key.mp hne)
      rw [if_neg h', lowerT_eval b σ ρ l F tb v hA hb hv, BitVec.toNat_mod_cancel]
  | .letIn (s := s) (t := t) x w b =>
    intro v hv
    simp only [lowerT, Option.bind_eq_some_iff] at h
    obtain ⟨tv, hw', hb⟩ := h
    simp only [evalX, Option.bind_eq_some_iff] at hv
    obtain ⟨vv, hvv, hvb⟩ := hv
    have ihv := lowerT_eval w σ ρ l F tv vv hA hw' hvv
    exact lowerT_eval b _ ρ _ F T v (Agree.set hA x (lowerT_width w σ tv hw') (lowerT_topPositive w σ tv (Agree.wf hA) hw') ihv) hb hvb
  | .call params ret body args =>
    intro v hv
    simp only [lowerT, Option.bind_eq_some_iff] at h
    obtain ⟨σ', hσ', hb⟩ := h
    simp only [evalX, Option.bind_eq_some_iff] at hv
    obtain ⟨l', hl', hvb⟩ := hv
    exact lowerT_eval body _ ρ _ F T v (bindArgs_agree args id σ ρ l F hA _ _ (fun _ => 0) (Agree.empty ρ _) σ' l' hσ' hl') hb hvb
  | .recDecl r fs fields b =>
    intro v hv
    simp only [lowerT, Option.bind_eq_some_iff] at h
    obtain ⟨σ', hσ', hb⟩ := h
    simp only [evalX, Option.bind_eq_some_iff] at hv
    obtain ⟨l', hl', hvb⟩ := hv
    exact lowerT_eval b _ ρ _ F T v (bindArgs_agree fields (fieldName r) σ ρ l F hA _ _ l hA σ' l' hσ' hl') hb hvb
  | .whileEvent idx c body rest =>
    intro v hv
    simp only [lowerT, Option.bind_eq_some_iff] at h
    obtain ⟨tc, -, σb, -, hr⟩ := h
    simp only [evalX, Option.bind_eq_some_iff] at hv
    obtain ⟨l', hl', hv⟩ := hv
    split at hv
    · rename_i hden
      have hA' := freshScope_agree hA idx (carriedOf_in body) (freshDenote_sound hden)
        (fun y hy => loopX_unassigned (fun l₀ l₂ h₀ => runVals_unassigned body ρ l₀ l₂ F (not_carried_not_assigned body hy) h₀) _ l l' hl')
      exact lowerT_eval rest _ ρ _ F T v hA' hr hv
    · cases hv
  | .callX params locals bs hb hc stmts results args rest =>
    intro v hv
    simp only [lowerT, Option.bind_eq_some_iff] at h
    obtain ⟨σp, hp, σf, hf, σ', hres, hr⟩ := h
    simp only [evalX, Option.bind_eq_some_iff] at hv
    obtain ⟨lp, hlp, lf, hlf, l', hlres, hvr⟩ := hv
    have hAp := bindArgs_agree args id σ ρ l F hA _ _ (fun _ => 0) (Agree.empty ρ _) σp lp hp hlp
    have hAc := copyIn_agree hA bs hb (zeroLocals_agree hAp locals)
    have hAf := runTerms_agree stmts _ ρ _ F σf lf hAc hf hlf
    have hAo := copyOut_agree hAf bs hc hA hb
    have hA' := bindArgs_agree results id _ ρ _ F hAf _ _ _ hAo σ' l' hres hlres
    exact lowerT_eval rest _ ρ _ F T v hA' hr hvr
  | .condSet c armT armF rest =>
    intro v hv
    simp only [lowerT, Option.bind_eq_some_iff] at h
    obtain ⟨tc, hc, σT, hT, σF, hFm, hr⟩ := h
    simp only [evalX, Option.bind_eq_some_iff] at hv
    obtain ⟨cv, hcv, l₁, hl₁, hvr⟩ := hv
    have ihc := lowerT_eval c σ ρ l F tc cv hA hc hcv
    have key := BitVec1_ne_zero_iff cv
    have hTt := runTerms_typed armT σ σT hA.1 hT
    have hFt := runTerms_typed armF σ σF hA.1 hFm
    split at hl₁
    · rename_i h1
      have hM := merge_agree_left tc (by rw [ihc]; exact key.mpr h1) (runTerms_agree armT σ ρ l F σT l₁ hA hT hl₁) hFt
      exact lowerT_eval rest _ ρ _ F T v hM hr hvr
    · rename_i h1
      have hz : tc.eval ρ = 0 := by
        rw [ihc]
        have hne : ¬ cv.toNat ≠ 0 := fun hne => h1 (key.mp hne)
        omega
      have hM := merge_agree_right tc hz hTt (runTerms_agree armF σ ρ l F σF l₁ hA hFm hl₁)
      exact lowerT_eval rest _ ρ _ F T v hM hr hvr
  | .whileLoop c body rest =>
    intro v hv
    simp only [lowerT, Option.bind_eq_some_iff] at h
    obtain ⟨σ', hσ', hr⟩ := h
    simp only [evalX, Option.bind_eq_some_iff] at hv
    obtain ⟨l', hl', hvr⟩ := hv
    have hc : ∀ σ₀ l₀ tc cv, Agree Γ σ₀ ρ l₀ → lowerT σ₀ c = some tc → evalX c ρ l₀ F = some cv → tc.eval ρ = cv.toNat :=
      fun σ₀ l₀ tc cv hA₀ h₀ hv₀ => lowerT_eval c σ₀ ρ l₀ F tc cv hA₀ h₀ hv₀
    have hb : ∀ σ₀ l₀ σ₁ l₁, Agree Γ σ₀ ρ l₀ → runTerms σ₀ body = some σ₁ → runVals body ρ l₀ F = some l₁ → Agree Γ σ₁ ρ l₁ :=
      fun σ₀ l₀ σ₁ l₁ hA₀ h₀ hv₀ => runTerms_agree body σ₀ ρ l₀ F σ₁ l₁ hA₀ h₀ hv₀
    exact lowerT_eval rest _ ρ _ F T v (unroll_agree hc hb (loopBudget + 1) F σ l σ' l' hA hσ' hl') hr hvr
  | .matchInt x arms =>
    intro v hv
    simp only [lowerT, Option.bind_eq_some_iff] at h
    obtain ⟨sx, hx, ha⟩ := h
    simp only [evalX, Option.bind_eq_some_iff] at hv
    obtain ⟨vx, hvx, hva⟩ := hv
    have ihx := lowerT_eval x σ ρ l F sx vx hA hx hvx
    exact armsT_eval arms σ sx ρ l F T vx v hA (lowerT_width x σ sx hx) ihx ha hva
  | .matchSet x arms rest =>
    intro v hv
    simp only [lowerT, Option.bind_eq_some_iff] at h
    obtain ⟨sx, hx, σ', h', hr⟩ := h
    simp only [evalX, Option.bind_eq_some_iff] at hv
    obtain ⟨vx, hvx, l', hl', hvr⟩ := hv
    have ihx := lowerT_eval x σ ρ l F sx vx hA hx hvx
    exact lowerT_eval rest _ ρ _ F T v (armsST_agree arms σ sx ρ l F vx σ' l' hA (lowerT_width x σ sx hx) ihx h' hl') hr hvr
  | .elem s w hw i =>
    intro v hv
    simp only [lowerT, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨ti, hi, rfl⟩ := h
    simp only [evalX, Option.bind_eq_some_iff, Option.some.injEq] at hv
    obtain ⟨vi, hvi, rfl⟩ := hv
    have ihi := lowerT_eval i σ ρ l F ti vi hA hi hvi
    have hlt : vi.toNat < 2 ^ 32 := vi.isLt
    rw [Term.selectT_eval]
    simp only [Term.eval]
    rw [truncate_self ti 32 (by rw [lowerT_width i σ ti hi]; rfl), ihi, Nat.mod_eq_of_lt hlt, BitVec.toNat_ofNat]
  | .len w hw =>
    intro v hv
    simp only [lowerT, Option.some.injEq] at h
    simp only [evalX] at hv
    subst h
    cases hv
    exact (BitVec.toNat_ofNat _ _).symm
  | .arrDecl nm e n hn b =>
    intro v hv
    exact lowerT_eval b _ ρ _ F T v (zeroTerms_agree hA nm e n) h hv
  | .arrLit nm e n hn items b =>
    intro v hv
    simp only [lowerT, Option.bind_eq_some_iff] at h
    obtain ⟨σ', hσ', hb⟩ := h
    simp only [evalX, Option.bind_eq_some_iff] at hv
    obtain ⟨l', hl', hvb⟩ := hv
    have hA' := bindArgs_agree items id σ ρ l F hA _ _ l hA σ' l' hσ' hl'
    rw [bindTypes_arrayFields] at hA'
    exact lowerT_eval b _ ρ _ F T v hA' hb hvb
  | .arrGet e n nm hn hin i =>
    intro v hv
    obtain ⟨hn0, hn32⟩ := hn
    simp only [lowerT, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨ti, hi, rfl⟩ := h
    simp only [evalX, Option.bind_eq_some_iff] at hv
    obtain ⟨vi, hvi, hv⟩ := hv
    by_cases hlt : vi.toNat < n
    · rw [if_pos hlt, Option.some.injEq] at hv
      subst hv
      have ihi := lowerT_eval i σ ρ l F ti vi hA hi hvi
      have hwi := lowerT_width i σ ti hi
      have hlast : 0 + (n - 1) < n := by rw [Nat.zero_add]; exact Nat.sub_one_lt (Nat.pos_iff_ne_zero.mp hn0)
      have hrw := readArr_width hA hin ti 0 (n - 1) hlast
      have hread := readArr_eval hA hin hn32 ti vi hwi ihi 0 (n - 1) hlast (Nat.zero_le _)
        (by rw [Nat.zero_add]; exact Nat.le_sub_one_of_lt hlt)
      rw [adaptWidth, if_neg (by rw [hrw]; exact Nat.lt_irrefl _), truncate_self _ _ hrw, hread, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (hA.value_lt (hin vi.toNat hlt))]
      rfl
    · rw [if_neg hlt] at hv; cases hv
  | .arrSetE (e := e) (n := n) nm hin hn32 i w rest =>
    intro v hv
    simp only [lowerT, Option.bind_eq_some_iff] at h
    obtain ⟨ti, hi, tv, htv, hr⟩ := h
    simp only [evalX, Option.bind_eq_some_iff] at hv
    obtain ⟨vi, hvi, vv, hvv, hv⟩ := hv
    split at hv
    · rename_i hlt
      have ihi := lowerT_eval i σ ρ l F ti vi hA hi hvi
      have ihv := lowerT_eval w σ ρ l F tv vv hA htv hvv
      exact lowerT_eval rest _ ρ _ F T v
        (writeArr_agree hA hin vi (lowerT_width i σ ti hi) ihi (lowerT_width w σ tv htv) (lowerT_topPositive w σ tv (Agree.wf hA) htv) vv ihv hn32 n (Nat.le_refl n)) hr hv
    · cases hv
termination_by structural e
/-- Running statements keeps the scope agreeing. -/
theorem runTerms_agree {P : Params} {S : Spans} {Γ : Locals} (st : Stmts P S Γ) :
    ∀ (σ : Scope) (ρ : Env) (l : Vals) (F : Nat) (σ' : Scope) (l' : Vals), Agree Γ σ ρ l →
      runTerms σ st = some σ' → runVals st ρ l F = some l' → Agree Γ σ' ρ l' := by
  intro σ ρ l F σ' l' hA h hv
  match st with
  | .nil =>
    simp only [runTerms, Option.some.injEq] at h
    simp only [runVals, Option.some.injEq] at hv
    subst h hv
    exact hA
  | .assign x hx e rest =>
    simp only [runTerms, Option.bind_eq_some_iff] at h
    obtain ⟨te, he, hr⟩ := h
    simp only [runVals, Option.bind_eq_some_iff] at hv
    obtain ⟨ve, hve, hvr⟩ := hv
    have ihe := lowerT_eval e σ ρ l F te ve hA he hve
    have hA' := Agree.set hA x (lowerT_width e σ te he) (lowerT_topPositive e σ te (Agree.wf hA) he) ihe
    rw [Locals.set_same hx] at hA'
    exact runTerms_agree rest _ ρ _ F σ' l' hA' hr hvr
  | .cond c armT armF rest =>
    simp only [runTerms, Option.bind_eq_some_iff] at h
    obtain ⟨tc, hc, σT, hT, σF, hFm, hr⟩ := h
    simp only [runVals, Option.bind_eq_some_iff] at hv
    obtain ⟨cv, hcv, l₁, hl₁, hvr⟩ := hv
    have ihc := lowerT_eval c σ ρ l F tc cv hA hc hcv
    have key := BitVec1_ne_zero_iff cv
    have hTt := runTerms_typed armT σ σT hA.1 hT
    have hFt := runTerms_typed armF σ σF hA.1 hFm
    split at hl₁
    · rename_i h1
      have hM := merge_agree_left tc (by rw [ihc]; exact key.mpr h1) (runTerms_agree armT σ ρ l F σT l₁ hA hT hl₁) hFt
      exact runTerms_agree rest _ ρ _ F σ' l' hM hr hvr
    · rename_i h1
      have hz : tc.eval ρ = 0 := by
        rw [ihc]
        have hne : ¬ cv.toNat ≠ 0 := fun hne => h1 (key.mp hne)
        omega
      have hM := merge_agree_right tc hz hTt (runTerms_agree armF σ ρ l F σF l₁ hA hFm hl₁)
      exact runTerms_agree rest _ ρ _ F σ' l' hM hr hvr
  | .loop c body rest =>
    simp only [runTerms, Option.bind_eq_some_iff] at h
    obtain ⟨σ₁, hσ₁, hr⟩ := h
    simp only [runVals, Option.bind_eq_some_iff] at hv
    obtain ⟨l₁, hl₁, hvr⟩ := hv
    have hc : ∀ σ₀ l₀ tc cv, Agree Γ σ₀ ρ l₀ → lowerT σ₀ c = some tc → evalX c ρ l₀ F = some cv → tc.eval ρ = cv.toNat :=
      fun σ₀ l₀ tc cv hA₀ h₀ hv₀ => lowerT_eval c σ₀ ρ l₀ F tc cv hA₀ h₀ hv₀
    have hb : ∀ σ₀ l₀ σ₂ l₂, Agree Γ σ₀ ρ l₀ → runTerms σ₀ body = some σ₂ → runVals body ρ l₀ F = some l₂ → Agree Γ σ₂ ρ l₂ :=
      fun σ₀ l₀ σ₂ l₂ hA₀ h₀ hv₀ => runTerms_agree body σ₀ ρ l₀ F σ₂ l₂ hA₀ h₀ hv₀
    exact runTerms_agree rest _ ρ _ F σ' l' (unroll_agree hc hb (loopBudget + 1) F σ l σ₁ l₁ hA hσ₁ hl₁) hr hvr
  | .matchS x arms rest =>
    simp only [runTerms, Option.bind_eq_some_iff] at h
    obtain ⟨sx, hx, σ₁, h₁, hr⟩ := h
    simp only [runVals, Option.bind_eq_some_iff] at hv
    obtain ⟨vx, hvx, l₁, hl₁, hvr⟩ := hv
    have ihx := lowerT_eval x σ ρ l F sx vx hA hx hvx
    exact runTerms_agree rest _ ρ _ F σ' l' (armsST_agree arms σ sx ρ l F vx σ₁ l₁ hA (lowerT_width x σ sx hx) ihx h₁ hl₁) hr hvr
  | .arrSet (e := e) (n := n) nm hin hn32 i w rest =>
    simp only [runTerms, Option.bind_eq_some_iff] at h
    obtain ⟨ti, hi, tv, htv, hr⟩ := h
    simp only [runVals, Option.bind_eq_some_iff] at hv
    obtain ⟨vi, hvi, vv, hvv, hv⟩ := hv
    split at hv
    · rename_i hlt
      have ihi := lowerT_eval i σ ρ l F ti vi hA hi hvi
      have ihv := lowerT_eval w σ ρ l F tv vv hA htv hvv
      exact runTerms_agree rest _ ρ _ F σ' l'
        (writeArr_agree hA hin vi (lowerT_width i σ ti hi) ihi (lowerT_width w σ tv htv) (lowerT_topPositive w σ tv (Agree.wf hA) htv) vv ihv hn32 n (Nat.le_refl n)) hr hv
    · cases hv
  | .loopEvent idx c body rest =>
    simp only [runTerms, Option.bind_eq_some_iff] at h
    obtain ⟨tc, -, σb, -, hr⟩ := h
    simp only [runVals, Option.bind_eq_some_iff] at hv
    obtain ⟨l₁, hl₁, hv⟩ := hv
    split at hv
    · rename_i hden
      have hA₁ := freshScope_agree hA idx (carriedOf_in body) (freshDenote_sound hden)
        (fun y hy => loopX_unassigned (fun l₀ l₂ h₀ => runVals_unassigned body ρ l₀ l₂ F (not_carried_not_assigned body hy) h₀) _ l l₁ hl₁)
      exact runTerms_agree rest _ ρ _ F σ' l' hA₁ hr hv
    · cases hv
  | .callS params locals bs hb hc hrs stmts results args rest =>
    simp only [runTerms, Option.bind_eq_some_iff] at h
    obtain ⟨σp, hp, σf, hf, σ₁, hres, hr⟩ := h
    simp only [runVals, Option.bind_eq_some_iff] at hv
    obtain ⟨lp, hlp, lf, hlf, l₁, hlres, hvr⟩ := hv
    have hAp := bindArgs_agree args id σ ρ l F hA _ _ (fun _ => 0) (Agree.empty ρ _) σp lp hp hlp
    have hAc := copyIn_agree hA bs hb (zeroLocals_agree hAp locals)
    have hAf := runTerms_agree stmts _ ρ _ F σf lf hAc hf hlf
    have hAo := copyOut_agree hAf bs hc hA hb
    have hA₁ := bindArgs_agree results id _ ρ _ F hAf _ _ _ hAo σ₁ l₁ hres hlres
    rw [hrs] at hA₁
    exact runTerms_agree rest _ ρ _ F σ' l' hA₁ hr hvr
termination_by structural st
/-- A value-position match's arms agree with the if-chain. -/
theorem armsT_eval {P : Params} {S : Spans} {Γ : Locals} {s t : Ty} (arms : Arms P S Γ s t) :
    ∀ (σ : Scope) (sx : Term) (ρ : Env) (l : Vals) (F : Nat) (T : Term) (vx : BitVec s.width) (v : BitVec t.width),
      Agree Γ σ ρ l → sx.width = s.width → sx.eval ρ = vx.toNat → armsT σ sx arms = some T →
        armsX vx arms ρ l F = some v → T.eval ρ = v.toNat := by
  intro σ sx ρ l F T vx v hA hw hx h hv
  match arms with
  | .fallback e => exact lowerT_eval e σ ρ l F T v hA h hv
  | .case k e rest =>
    simp only [armsT, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨te, he, tr, hr, rfl⟩ := h
    simp only [armsX] at hv
    have hte := lowerT_topPositive e σ te (Agree.wf hA) he
    have htr := armsT_topPositive rest σ sx tr (Agree.wf hA) hr
    have hwe := lowerT_width e σ te he
    have hwr := armsT_width rest σ sx tr hr
    have hcond := caseCond_eval sx s.width k vx ρ hw s.width_pos hx
    rw [Term.selectArm_eval ρ hte htr (by rw [hwr, hwe]), Term.eval.eq_5, hwe]
    split at hv
    · rename_i h1
      have h' : (caseCond sx s.width k.toNat).eval ρ ≠ 0 := by rw [hcond, if_pos h1]; decide
      rw [if_pos h', lowerT_eval e σ ρ l F te v hA he hv, BitVec.toNat_mod_cancel]
    · rename_i h1
      have h' : ¬ (caseCond sx s.width k.toNat).eval ρ ≠ 0 := by rw [hcond, if_neg h1]; decide
      rw [if_neg h', armsT_eval rest σ sx ρ l F tr vx v hA hw hx hr hv, BitVec.toNat_mod_cancel]
termination_by structural arms
/-- A statement-position match's arms agree with the taken arm. -/
theorem armsST_agree {P : Params} {S : Spans} {Γ : Locals} {s : Ty} (arms : ArmsS P S Γ s) :
    ∀ (σ : Scope) (sx : Term) (ρ : Env) (l : Vals) (F : Nat) (vx : BitVec s.width) (σ' : Scope) (l' : Vals),
      Agree Γ σ ρ l → sx.width = s.width → sx.eval ρ = vx.toNat → armsST σ sx arms = some σ' →
        armsVals vx arms ρ l F = some l' → Agree Γ σ' ρ l' := by
  intro σ sx ρ l F vx σ' l' hA hw hx h hv
  match arms with
  | .fallback st => exact runTerms_agree st σ ρ l F σ' l' hA h hv
  | .case k st rest =>
    simp only [armsST, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨σk, hk, σr, hr, rfl⟩ := h
    simp only [armsVals] at hv
    have hcond := caseCond_eval sx s.width k vx ρ hw s.width_pos hx
    have hkt := runTerms_typed st σ σk hA.1 hk
    have hrt := armsST_typed rest σ sx σr hA.1 hr
    split at hv
    · rename_i h1
      exact merge_agree_left _ (by rw [hcond, if_pos h1]; decide) (runTerms_agree st σ ρ l F σk l' hA hk hv) hrt
    · rename_i h1
      exact merge_agree_right _ (by rw [hcond, if_neg h1]) hkt (armsST_agree rest σ sx ρ l F vx σr l' hA hw hx hr hv)
termination_by structural arms
/-- Binding a call's arguments keeps the callee's scope agreeing: each
parameter's term has the parameter's width and evaluates to the argument's
value. -/
theorem bindArgs_agree {P : Params} {S : Spans} {Γ : Locals} {ps : List (String × Ty)} (args : Args P S Γ ps) :
    ∀ (nm : String → String) (σ : Scope) (ρ : Env) (l : Vals) (F : Nat), Agree Γ σ ρ l →
      ∀ (Γ0 : Locals) (acc : Scope) (l0 : Vals), Agree Γ0 acc ρ l0 → ∀ (σ' : Scope) (l' : Vals),
        bindTerms nm σ args acc = some σ' → bindVals nm args ρ l l0 F = some l' → Agree (bindTypes nm Γ0 ps) σ' ρ l' := by
  intro nm σ ρ l F hA Γ0 acc l0 h0 σ' l' h hv
  match args with
  | .nil =>
    simp only [bindTerms, Option.some.injEq] at h
    simp only [bindVals, Option.some.injEq] at hv
    subst h hv
    exact h0
  | .cons (x := x) a rest =>
    simp only [bindTerms, Option.bind_eq_some_iff] at h
    obtain ⟨ta, ha, hr⟩ := h
    simp only [bindVals, Option.bind_eq_some_iff] at hv
    obtain ⟨va, hva, hvr⟩ := hv
    have iha := lowerT_eval a σ ρ l F ta va hA ha hva
    exact bindArgs_agree rest nm σ ρ l F hA _ _ _
      (Agree.set h0 (nm x) (lowerT_width a σ ta ha) (lowerT_topPositive a σ ta (Agree.wf hA) ha) iha) σ' l' hr hvr
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

def UOp.render : UOp → String
  | .udiv => "udiv" | .sdiv => "sdiv"

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
  | .uop op w l r => op.render ++ toString w ++ "(" ++ l.render ++ ", " ++ r.render ++ ")"

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
example : lowered? ((.divRem .div (.var .u32 "a" (by decide)) (.var .u32 "b" (by decide)) : X (ps [("a", .u32), ("b", .u32)]) sp0 .u32)) = some "(udiv32(a, b) and 4294967295)" := by decide
example : lowered? ((.divRem .rem (.var .u32 "a" (by decide)) (.var .u32 "b" (by decide)) : X (ps [("a", .u32), ("b", .u32)]) sp0 .u32)) = some "((a sub (udiv32(a, b) mul b)) and 4294967295)" := by decide
example : lowered? ((.divRem .div (.var .i32 "a" (by decide)) (.var .i32 "b" (by decide)) : X (ps [("a", .i32), ("b", .i32)]) sp0 .i32)) = some "(((sdiv32(a, b) and 4294967295) shl 0) sar 0)" := by decide
example : lowered? ((.divRem .rem (.var .i8 "a" (by decide)) (.var .i8 "b" (by decide)) : X (ps [("a", .i8), ("b", .i8)]) sp0 .i8)) = some "((((a sub (sdiv8(a, b) mul b)) and 255) shl 0) sar 0)" := by decide
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

/-! Owned arrays: an array local is its element leaves `x[k]`; a read at a
symbolic index selects element by element, a write selects at every
element, and literal indices fold both to the one element. -/

/-- `(i, v: u32) -> u32 = { a: [3]u32; a[0] = v; a[1] = v + 1; a[2] = v * 2; a[i] }` -/
example : lowered? ((.arrDecl (elemName "a") .u32 3 (by decide)
    (.arrSetE (n := 3) (elemName "a") (by decide) (by decide) (.lit .u32 0) (.var .u32 "v" (by decide))
    (.arrSetE (n := 3) (elemName "a") (by decide) (by decide) (.lit .u32 1) (.arith .add (.var .u32 "v" (by decide)) (.lit .u32 1))
    (.arrSetE (n := 3) (elemName "a") (by decide) (by decide) (.lit .u32 2) (.arith .mul (.var .u32 "v" (by decide)) (.lit .u32 2))
    (.arrGet .u32 3 (elemName "a") (by decide) (by decide) (.var .u32 "i" (by decide)))))) : X (ps [("i", .u32), ("v", .u32)]) sp0 .u32))
    = some "((i eq 0) ? v : ((i eq 1) ? (v add 1) : (v mul 2)))" := by decide
/-- `(i, v: u32) -> u32 = { a: [2]u32; a[i] = v; a[1] }` — a write at a symbolic index selects at every element. -/
example : lowered? ((.arrDecl (elemName "a") .u32 2 (by decide)
    (.arrSetE (n := 2) (elemName "a") (by decide) (by decide) (.var .u32 "i" (by decide)) (.var .u32 "v" (by decide))
    (.arrGet .u32 2 (elemName "a") (by decide) (by decide) (.lit .u32 1))) : X (ps [("i", .u32), ("v", .u32)]) sp0 .u32))
    = some "((i eq 1) ? v : 0)" := by decide

/-! Records: a record is its field leaves `r.f`, a field read the variable,
a field write its rebinding. -/

/-- `P: type = struct { x: u32, y: u32 }`; `(a, b: u32) -> u32 = { p: P = P{ x: a, y: b }; p.x = p.x + 1; p.x * p.y }` -/
example : lowered? ((.recDecl "p" [("x", .u32), ("y", .u32)] (.cons (.var .u32 "a" (by decide)) (.cons (.var .u32 "b" (by decide)) .nil))
    (.letIn "p.x" (.arith .add (.var .u32 "p.x" (by decide)) (.lit .u32 1))
      (.arith .mul (.var .u32 "p.x" (by decide)) (.var .u32 "p.y" (by decide)))) : X (ps [("a", .u32), ("b", .u32)]) sp0 .u32))
    = some "((a add 1) mul b)" := by decide
/-- `(p: P) -> u32 = p.x + p.y` — a record parameter is its field leaves as parameters. -/
example : lowered? ((.arith .add (.var .u32 "p.x" (by decide)) (.var .u32 "p.y" (by decide)) : X (ps [("p.x", .u32), ("p.y", .u32)]) sp0 .u32))
    = some "(p.x add p.y)" := by decide

/-! Sum types need no constructor of their own: a tagged union is its `tag`
leaf (32 bits, the variant's index) and one payload leaf per carrying
variant, `u.tag` and `u.V` (`zeroValue`, `paramAggregate`); a variant is a
record declaration with the tag constant and the payload; a variant match
is the constant match on the tag (`matchArms`: `cmpTerm("eq", tag, index)`)
whose arm binds the payload leaf under the pattern's name (`lo.locals[x] =
payload.scalar`, the alias `letIn x u.V` is). -/

/-- `U: type = A | B: u32`; `(v: u32) -> u32 = { u: U = B(v); u ? | B(x) => x + 1 | A => 0 }` -/
example : lowered? ((.recDecl "u" [("tag", .u32), ("B", .u32)] (.cons (.lit .u32 1) (.cons (.var .u32 "v" (by decide)) .nil))
    (.matchInt (.var .u32 "u.tag" (by decide))
      (.case 1 (.letIn "x" (.var .u32 "u.B" (by decide)) (.arith .add (.var .u32 "x" (by decide)) (.lit .u32 1)))
        (.fallback (.lit .u32 0)))) : X (ps [("v", .u32)]) sp0 .u32))
    = some "(v add 1)" := by decide
/-- `(u: U) -> u32 = u ? | B(x) => x + 1 | A => 0` — a union parameter is its tag and payload leaves. -/
example : lowered? ((.matchInt (.var .u32 "u.tag" (by decide))
      (.case 1 (.letIn "x" (.var .u32 "u.B" (by decide)) (.arith .add (.var .u32 "x" (by decide)) (.lit .u32 1)))
        (.fallback (.lit .u32 0))) : X (ps [("u.tag", .u32), ("u.B", .u32)]) sp0 .u32))
    = some "((u.tag eq 1) ? (u.B add 1) : 0)" := by decide

/-! Nested aggregates and array literals: a record's array field is the
leaves `r.h[k]`, an array's record elements the leaves `a[k].x`; a literal
binds its elements in order. -/

/-- `(v, i: u32) -> u32 = { a: [3]u32 = [v, 5, v + 1]; a[i] }` -/
example : lowered? ((.arrLit (elemName "a") .u32 3 (by decide)
    (.cons (.var .u32 "v" (by decide)) (.cons (.lit .u32 5) (.cons (.arith .add (.var .u32 "v" (by decide)) (.lit .u32 1)) .nil)))
    (.arrGet .u32 3 (elemName "a") (by decide) (by decide) (.var .u32 "i" (by decide))) : X (ps [("v", .u32), ("i", .u32)]) sp0 .u32))
    = some "((i eq 0) ? v : ((i eq 1) ? 5 : (v add 1)))" := by decide
/-- `R: type = struct { h: [2]u32, n: u32 }`; `(i, v: u32) -> u32 = { r: R = R { h: [v, v + 1], n: 3 }; r.h[i] + r.n }` -/
example : lowered? ((.arrLit (elemName "r.h") .u32 2 (by decide)
    (.cons (.var .u32 "v" (by decide)) (.cons (.arith .add (.var .u32 "v" (by decide)) (.lit .u32 1)) .nil))
    (.recDecl "r" [("n", .u32)] (.cons (.lit .u32 3) .nil)
      (.arith .add (.arrGet .u32 2 (elemName "r.h") (by decide) (by decide) (.var .u32 "i" (by decide))) (.var .u32 "r.n" (by decide))))
    : X (ps [("i", .u32), ("v", .u32)]) sp0 .u32))
    = some "(((i eq 0) ? v : (v add 1)) add 3)" := by decide
/-- `P: type = struct { x: u32, y: u32 }`; `(i, v: u32) -> u32 = { a: [2]P = [P { x: v, y: 1 }, P { x: v + 1, y: 2 }]; a[i].x }` -/
example : lowered? ((.arrLit (fun k => fieldName (elemName "a" k) "x") .u32 2 (by decide)
    (.cons (.var .u32 "v" (by decide)) (.cons (.arith .add (.var .u32 "v" (by decide)) (.lit .u32 1)) .nil))
    (.arrLit (fun k => fieldName (elemName "a" k) "y") .u32 2 (by decide)
      (.cons (.lit .u32 1) (.cons (.lit .u32 2) .nil))
      (.arrGet .u32 2 (fun k => fieldName (elemName "a" k) "x") (by decide) (by decide) (.var .u32 "i" (by decide))))
    : X (ps [("i", .u32), ("v", .u32)]) sp0 .u32))
    = some "((i eq 0) ? v : (v add 1))" := by decide
/-- Locals from a list. -/
def ls (l : List (String × Ty)) : Locals := fun x => (l.find? (fun p => p.1 = x)).map (·.2)
/-- An aggregate parameter is an aggregate local whose leaves are parameter
terms (`bindAggregateParams`): the scope binds each leaf to `paramTerm`. -/
def paramLeaves (l : List (String × Ty)) : Scope := fun x => (l.find? (fun p => p.1 = x)).map fun p => Term.param p.1 p.2.width
/-- `(r: R, i: u32) -> u32 = r.h[i]` — a record parameter's array field is its leaves `r.h[k]`, parameter terms. -/
example : ((lowerT (paramLeaves [("r.h[0]", .u32), ("r.h[1]", .u32), ("r.n", .u32)])
    (.arrGet .u32 2 (elemName "r.h") (by decide) (by decide) (.var .u32 "i" (by decide))
      : Expr (ps [("i", .u32)]) sp0 (ls [("r.h[0]", .u32), ("r.h[1]", .u32), ("r.n", .u32)]) .u32)).map Term.render)
    = some "((i eq 0) ? r.h[0] : r.h[1])" := by decide

/-! Calls that borrow and calls that return records: the callee's span
leaves are copies of the owner's, written back on return; a record result
is bound leaf by leaf. -/

/-- `g: (s: [*]u32, v: u32) -> u32 = { s[1] = v; s[0] + s[1] }`;
`f: (v: u32) -> u32 = { a: [2]u32; a[0] = v; r: u32 = g(span(&a), v + 1); r + a[1] }` -/
example : lowered? ((.arrDecl (elemName "a") .u32 2 (by decide)
    (.arrSetE (n := 2) (elemName "a") (by decide) (by decide) (.lit .u32 0) (.var .u32 "v" (by decide))
    (.callX [("v", .u32)] [] [⟨"s", .u32, 2, elemName "a"⟩] (by decide) (by decide) (rs := [("r", .u32)])
      (.arrSet (n := 2) (elemName "s") (by decide) (by decide) (.lit .u32 1) (.var .u32 "v" (by decide)) .nil)
      (.cons (.arith .add (.arrGet .u32 2 (elemName "s") (by decide) (by decide) (.lit .u32 0))
        (.arrGet .u32 2 (elemName "s") (by decide) (by decide) (.lit .u32 1))) .nil)
      (.cons (.arith .add (.var .u32 "v" (by decide)) (.lit .u32 1)) .nil)
      (.arith .add (.var .u32 "r" (by decide)) (.arrGet .u32 2 (elemName "a") (by decide) (by decide) (.lit .u32 1)))))
    : X (ps [("v", .u32)]) sp0 .u32))
    = some "((v add (v add 1)) add (v add 1))" := by decide
/-- `shift: (p: P, dx: u32) -> P = P { x: p.x + dx, y: p.y }`;
`f: (a, b: u32) -> u32 = { p: P = P { x: a, y: b }; q: P = shift(p, 1); q.x * q.y }` -/
example : lowered? ((.recDecl "p" [("x", .u32), ("y", .u32)] (.cons (.var .u32 "a" (by decide)) (.cons (.var .u32 "b" (by decide)) .nil))
    (.callX [("p.x", .u32), ("p.y", .u32), ("dx", .u32)] [] [] (by decide) (by decide) (rs := [("q.x", .u32), ("q.y", .u32)])
      .nil
      (.cons (.arith .add (.var .u32 "p.x" (by decide)) (.var .u32 "dx" (by decide))) (.cons (.var .u32 "p.y" (by decide)) .nil))
      (.cons (.var .u32 "p.x" (by decide)) (.cons (.var .u32 "p.y" (by decide)) (.cons (.lit .u32 1) .nil)))
      (.arith .mul (.var .u32 "q.x" (by decide)) (.var .u32 "q.y" (by decide)))) : X (ps [("a", .u32), ("b", .u32)]) sp0 .u32))
    = some "((a add 1) mul b)" := by decide

/-! A local declared inside a loop body or an arm (`lowerLoopBody`,
`lowerArm`: `declareLocal` each time through) binds the initializer's term,
exactly as an assignment to a local declared before does, so the model
pre-declares it — the terms every later read sees are the same. -/

/-- `(n: u32) -> u32 = { s: u32 = 0; i: u32 = 0; while i < 2 { d: u32 = n * 2; s = s + d; i = i + 1 }; s }` -/
example : lowered? ((.letIn "s" (.lit .u32 0) (.letIn "i" (.lit .u32 0) (.letIn "d" (.lit .u32 0)
    (.whileLoop (.cmp .lt (.var .u32 "i" (by decide)) (.lit .u32 2))
      (.assign "d" (by decide) (.arith .mul (.var .u32 "n" (by decide)) (.lit .u32 2))
        (.assign "s" (by decide) (.arith .add (.var .u32 "s" (by decide)) (.var .u32 "d" (by decide)))
          (.assign "i" (by decide) (.arith .add (.var .u32 "i" (by decide)) (.lit .u32 1)) .nil)))
      (.var .u32 "s" (by decide))))) : X (ps [("n", .u32)]) sp0 .u32))
    = some "((n mul 2) add (n mul 2))" := by decide
/-- `(a, b: u32) -> u32 = { r: u32 = a; a < b ? { t: u32 = b - a; r = t } | { }; r }` -/
example : lowered? ((.letIn "r" (.var .u32 "a" (by decide)) (.letIn "t" (.lit .u32 0)
    (.condSet (.cmp .lt (.var .u32 "a" (by decide)) (.var .u32 "b" (by decide)))
      (.assign "t" (by decide) (.arith .sub (.var .u32 "b" (by decide)) (.var .u32 "a" (by decide)))
        (.assign "r" (by decide) (.var .u32 "t" (by decide)) .nil)) .nil
      (.var .u32 "r" (by decide)))) : X (ps [("a", .u32), ("b", .u32)]) sp0 .u32))
    = some "((a lo b) ? (b sub a) : a)" := by decide

/-! Data-dependent loops: the carried locals stand as the fresh symbols
`loop<idx>.<var>` after the loop, and the code after it reads them. -/

/-- `(n: u32) -> u32 = { s: u32 = 0; i: u32 = 0; while i < n { s = s + i; i = i + 1 }; s + i }` -/
example : lowered? ((.letIn "s" (.lit .u32 0) (.letIn "i" (.lit .u32 0)
    (.whileEvent 1 (.cmp .lt (.var .u32 "i" (by decide)) (.var .u32 "n" (by decide)))
      (.assign "s" (by decide) (.arith .add (.var .u32 "s" (by decide)) (.var .u32 "i" (by decide)))
        (.assign "i" (by decide) (.arith .add (.var .u32 "i" (by decide)) (.lit .u32 1)) .nil))
      (.arith .add (.var .u32 "s" (by decide)) (.var .u32 "i" (by decide))))) : X (ps [("n", .u32)]) sp0 .u32))
    = some "(loop1.s add loop1.i)" := by decide
/-- The same loop, only `s` read after it. -/
example : lowered? ((.letIn "s" (.lit .u32 0) (.letIn "i" (.lit .u32 0)
    (.whileEvent 1 (.cmp .lt (.var .u32 "i" (by decide)) (.var .u32 "n" (by decide)))
      (.assign "s" (by decide) (.arith .add (.var .u32 "s" (by decide)) (.var .u32 "i" (by decide)))
        (.assign "i" (by decide) (.arith .add (.var .u32 "i" (by decide)) (.lit .u32 1)) .nil))
      (.arith .mul (.var .u32 "s" (by decide)) (.lit .u32 2)))) : X (ps [("n", .u32)]) sp0 .u32))
    = some "(loop1.s mul 2)" := by decide

end Oak.LoweringRefinement
