import Oak.FloatOps

/-!
# The first floating-point source/lowering refinement

`Oak.LoweringRefinement` relates the extraction and verifier lowerings for the
shared integer and aggregate language.  This module starts the corresponding
floating-point seam with the binary32 operations emitted by
`oak build -lean-floats bits`: `+`, `-`, `*`, `/`, `fma`, and the six
comparisons.

For addition, subtraction, multiplication, and fused multiply-add, the source
side uses the exact `Oak.FloatOps` carriers, modulo their documented
canonical-NaN reading of Lean's `Float32`. Division uses Lean's `Float32`
division, the same semantic primitive the extraction emits; its refinement
establishes operation identity and operand order, not a new bit-level proof of
division rounding. The verifier side has the operation names used by
`asm/floats_lowering.go` and `asm/floats_ops.go`: `fadd`, `fsub`, `fmul`,
`fdiv`, and ternary `fma`, each at width 32. The Go render test in
`asm/lowering_refinement_test.go` pins production lowering to the `lowerF`
shapes below.

The second increment adds literals after decimal parsing has rounded them to
binary32 bits, plus straight-line local declarations and rebindings.  The
third adds the total sign operations: negation, absolute value, and copysign,
under that same result-level NaN quotient. Payload-observing bitcasts are not
part of this theorem. The fourth adds IEEE equality and ordering: NaNs are
unordered and the two signed zeros are equal. The comparison leaves compose
through pure Boolean literals, negation, conjunction, and disjunction. The
fifth increment closes arbitrarily nested value-position conditionals over
those guards and straight-line float leaves. The sixth closes pure calls over
ordered arguments. The seventh closes statement-position conditionals over
any finite sequence of scalar `f32` bindings: both arms start from the same
scope, execute assignments in order, and merge every written name.
The eighth adds operation-preserving binary32 division throughout that existing
pure control-flow and call surface.
The ninth adds the extraction's exact `Oak.FloatOps.fma32` carrier and the
verifier's ordered ternary `fma` application throughout the same surface.
The tenth adds the explicit widening `f64(e)` for every straight-line `f32`
expression already covered: the extraction and verifier models both apply
`Float32.toFloat` to the same binary32 value, and the verifier shape retains
the width-changing `fcvt` node. This is operation identity and operand
composition, not an independent proof of IEEE widening, the Go evaluator, or
an ISA instruction. The eleventh adds a deliberately separate binary64 FMA
family with already-rounded literal bits and straight-line locals. Extraction
and verifier terms both retain one ordered `Oak.FloatOps.fma64` application.
This is carrier identity, operation identity, and operand order; it is not an
independent proof of the FMA implementation, IEEE rounding, exception modes,
NaN payloads, Go evaluation, or an ISA instruction. The twelfth admits the
existing widening family as leaves of that binary64 FMA tree, so a widened
binary32 expression composes with binary64 parameters, literals, FMA, and pure
binary64 locals without erasing its `fcvt` node. The binary32 leaf still starts
in its own initial parameter scope; arbitrary mixed-width statement sequencing
is not claimed. Decimal parsing itself, all other conversions, spans,
nested/effectful statement control flow, borrowing/recursive/effectful calls,
other binary64 arithmetic, and SIMD remain outside this theorem.
-/

namespace Oak.FloatLoweringRefinement

/-- The binary32 operations in this refinement. Addition, subtraction, and
multiplication use the bit-exact carriers in `Oak.FloatOps`; division is the
shared Lean `Float32` primitive. -/
inductive SourceOp
  | add
  | sub
  | mul
  | div
  deriving DecidableEq, Repr

/-- The corresponding `termFloat` operation names in the verifier. -/
inductive VerifierOp
  | fadd
  | fsub
  | fmul
  | fdiv
  deriving DecidableEq, Repr

/-- Exact unary operations on a binary32 bit pattern. -/
inductive SourceUnaryOp
  | neg
  | abs
  deriving DecidableEq, Repr

/-- The bit operations emitted by the verifier lowering. -/
inductive VerifierUnaryOp
  | xorSign
  | clearSign
  deriving DecidableEq, Repr

/-- IEEE comparison operations in the source syntax. -/
inductive SourceCompareOp
  | eq
  | ne
  | lt
  | le
  | gt
  | ge
  deriving DecidableEq, Repr

/-- The corresponding predicates built by the verifier's `floatCompare`. -/
inductive VerifierCompareOp
  | eq
  | ne
  | lt
  | le
  | gt
  | ge
  deriving DecidableEq, Repr

/-- The spelling map in `oakLowering.lower` for binary32 arithmetic. -/
def lowerOp : SourceOp → VerifierOp
  | .add => .fadd
  | .sub => .fsub
  | .mul => .fmul
  | .div => .fdiv

/-- The spelling map for unary sign operations. -/
def lowerUnaryOp : SourceUnaryOp → VerifierUnaryOp
  | .neg => .xorSign
  | .abs => .clearSign

def lowerCompareOp : SourceCompareOp → VerifierCompareOp
  | .eq => .eq
  | .ne => .ne
  | .lt => .lt
  | .le => .le
  | .gt => .gt
  | .ge => .ge

/-- The extraction's `-lean-floats bits` reading of the four operations. -/
def SourceOp.eval : SourceOp → Float32 → Float32 → Float32
  | .add => Oak.FloatOps.add32
  | .sub => Oak.FloatOps.sub32
  | .mul => Oak.FloatOps.mul32
  | .div => fun a b => a / b

/-- The formal reading of the verifier's `termFloat` names.  The verifier
treats a non-constant application as uninterpreted when deciding equality;
this evaluator gives that shared application its Oak binary32 meaning. -/
def VerifierOp.eval : VerifierOp → Float32 → Float32 → Float32
  | .fadd => Oak.FloatOps.add32
  | .fsub => Oak.FloatOps.sub32
  | .fmul => Oak.FloatOps.mul32
  | .fdiv => fun a b => a / b

/-- The extraction's bit-level reading of binary32 sign operations. -/
def SourceUnaryOp.eval : SourceUnaryOp → Float32 → Float32
  | .neg => Oak.FloatOps.neg32
  | .abs => Oak.FloatOps.abs32

/-- The verifier's xor-sign and clear-sign terms have the same reading. -/
def VerifierUnaryOp.eval : VerifierUnaryOp → Float32 → Float32
  | .xorSign => Oak.FloatOps.neg32
  | .clearSign => Oak.FloatOps.abs32

/-- The bit-level comparison carriers used by extraction. -/
def SourceCompareOp.eval : SourceCompareOp → Float32 → Float32 → Bool
  | .eq => Oak.FloatOps.eq32
  | .ne => Oak.FloatOps.ne32
  | .lt => Oak.FloatOps.lt32
  | .le => Oak.FloatOps.le32
  | .gt => Oak.FloatOps.gt32
  | .ge => Oak.FloatOps.ge32

/-- The semantic reading of the verifier's `floatCompare` result. -/
def VerifierCompareOp.eval : VerifierCompareOp → Float32 → Float32 → Bool
  | .eq => Oak.FloatOps.eq32
  | .ne => Oak.FloatOps.ne32
  | .lt => Oak.FloatOps.lt32
  | .le => Oak.FloatOps.le32
  | .gt => Oak.FloatOps.gt32
  | .ge => Oak.FloatOps.ge32

/-- Mapping a source operation to the verifier operation preserves its shared
binary32 meaning. -/
@[simp] theorem lowerOp_eval (op : SourceOp) (a b : Float32) :
    (lowerOp op).eval a b = op.eval a b := by
  cases op <;> rfl

@[simp] theorem lowerUnaryOp_eval (op : SourceUnaryOp) (a : Float32) :
    (lowerUnaryOp op).eval a = op.eval a := by
  cases op <;> rfl

@[simp] theorem lowerCompareOp_eval (op : SourceCompareOp) (a b : Float32) :
    (lowerCompareOp op).eval a b = op.eval a b := by
  cases op <;> rfl

/-- The shared straight-line source subset for this increment. -/
inductive Expr
  | param (name : String)
  | literal (bits : UInt32)
  | binary (op : SourceOp) (left right : Expr)
  | fma (multiplicand multiplier addend : Expr)
  | unary (op : SourceUnaryOp) (operand : Expr)
  | copysign (magnitude sign : Expr)
  /-- A local declaration or rebinding.  The initializer is evaluated in the
  old scope; the body sees the new value. -/
  | letIn (name : String) (value body : Expr)
  deriving Repr

/-- A source parameter environment. -/
abbrev SourceEnv := String → Float32

/-- Rebind one name in the extraction's current scope. -/
def SourceEnv.set (ρ : SourceEnv) (name : String) (value : Float32) : SourceEnv :=
  fun candidate => if candidate = name then value else ρ candidate

/-- The extraction-side interpretation. -/
def Expr.eval : Expr → SourceEnv → Float32
  | .param name, ρ => ρ name
  | .literal bits, _ => Float32.ofBits bits
  | .binary op left right, ρ => op.eval (left.eval ρ) (right.eval ρ)
  | .fma multiplicand multiplier addend, ρ =>
      Oak.FloatOps.fma32
        (multiplicand.eval ρ) (multiplier.eval ρ) (addend.eval ρ)
  | .unary op operand, ρ => op.eval (operand.eval ρ)
  | .copysign magnitude sign, ρ =>
      Oak.FloatOps.copysign32 (magnitude.eval ρ) (sign.eval ρ)
  | .letIn name value body, ρ => body.eval (ρ.set name (value.eval ρ))

/- The mutually recursive verifier value and Boolean terms. `Term.ite` is
the merge produced for a float local assigned in both arms of a statement
conditional; comparison leaves in its guard refer back to float terms. -/
mutual
  inductive Term
    | param (name : String)
    | literal (bits : UInt32)
    | float (op : VerifierOp) (left right : Term)
    | fma (multiplicand multiplier addend : Term)
    | unary (op : VerifierUnaryOp) (operand : Term)
    | copysign (magnitude sign : Term)
    | ite (guard : BoolTerm) (whenTrue whenFalse : Term)
    deriving Repr

  inductive BoolTerm
    | compare (op : VerifierCompareOp) (left right : Term)
    | literal (value : Bool)
    | negate (condition : BoolTerm)
    | conjunction (left right : BoolTerm)
    | disjunction (left right : BoolTerm)
    deriving Repr
end

/-- The verifier's symbolic bindings.  A local maps directly to the term of
its initializer, which is how `declareLocal` and `assignLocal` substitute
straight-line locals in `asm/verify.go`. -/
abbrev TermEnv := String → Term

/-- Rebind one symbolic local. -/
def TermEnv.set (σ : TermEnv) (name : String) (value : Term) : TermEnv :=
  fun candidate => if candidate = name then value else σ candidate

/- The mutually recursive verifier-side interpretation under the same source
parameters. -/
mutual
  def Term.eval : Term → SourceEnv → Float32
    | .param name, ρ => ρ name
    | .literal bits, _ => Float32.ofBits bits
    | .float op left right, ρ => op.eval (left.eval ρ) (right.eval ρ)
    | .fma multiplicand multiplier addend, ρ =>
        Oak.FloatOps.fma32
          (multiplicand.eval ρ) (multiplier.eval ρ) (addend.eval ρ)
    | .unary op operand, ρ => op.eval (operand.eval ρ)
    | .copysign magnitude sign, ρ =>
        Oak.FloatOps.copysign32 (magnitude.eval ρ) (sign.eval ρ)
    | .ite guard whenTrue whenFalse, ρ =>
        bif guard.eval ρ then whenTrue.eval ρ else whenFalse.eval ρ

  def BoolTerm.eval : BoolTerm → SourceEnv → Bool
    | .compare op left right, ρ => op.eval (left.eval ρ) (right.eval ρ)
    | .literal value, _ => value
    | .negate condition, ρ => !condition.eval ρ
    | .conjunction left right, ρ => left.eval ρ && right.eval ρ
    | .disjunction left right, ρ => left.eval ρ || right.eval ρ
end

/-- The float branch of `oakLowering.lower`: operands keep their source order,
each source operation becomes one width-32 `termFloat`, and a local is
substituted by its initializer's already-lowered term. -/
def lowerWith : Expr → TermEnv → Term
  | .param name, σ => σ name
  | .literal bits, _ => .literal bits
  | .binary op left right, σ =>
      .float (lowerOp op) (lowerWith left σ) (lowerWith right σ)
  | .fma multiplicand multiplier addend, σ =>
      .fma (lowerWith multiplicand σ) (lowerWith multiplier σ)
        (lowerWith addend σ)
  | .unary op operand, σ =>
      .unary (lowerUnaryOp op) (lowerWith operand σ)
  | .copysign magnitude sign, σ =>
      .copysign (lowerWith magnitude σ) (lowerWith sign σ)
  | .letIn name value body, σ =>
      lowerWith body (σ.set name (lowerWith value σ))

/-- A symbolic environment agrees with the extraction's current scope when
every bound term evaluates, under the immutable function parameters, to the
scope value of the same name. -/
def Agree (parameters current : SourceEnv) (σ : TermEnv) : Prop :=
  ∀ name, (σ name).eval parameters = current name

private theorem agree_set (parameters current : SourceEnv) (σ : TermEnv)
    (name : String) (value : Float32) (lowered : Term)
    (hσ : Agree parameters current σ)
    (hv : lowered.eval parameters = value) :
    Agree parameters (current.set name value) (σ.set name lowered) := by
  intro candidate
  by_cases h : candidate = name
  · simp [SourceEnv.set, TermEnv.set, h, hv]
  · simp [SourceEnv.set, TermEnv.set, h, hσ candidate]

/-- Generalized refinement invariant used under local bindings. -/
theorem lowerWith_eval (e : Expr) (parameters current : SourceEnv) (σ : TermEnv)
    (hσ : Agree parameters current σ) :
    (lowerWith e σ).eval parameters = e.eval current := by
  induction e generalizing current σ with
  | param name => exact hσ name
  | literal => rfl
  | binary op left right ihLeft ihRight =>
      simp only [lowerWith, Term.eval, Expr.eval]
      rw [ihLeft current σ hσ, ihRight current σ hσ]
      exact lowerOp_eval op (left.eval current) (right.eval current)
  | fma multiplicand multiplier addend ihMultiplicand ihMultiplier ihAddend =>
      simp only [lowerWith, Term.eval, Expr.eval]
      rw [ihMultiplicand current σ hσ, ihMultiplier current σ hσ,
          ihAddend current σ hσ]
  | unary op operand ih =>
      simp only [lowerWith, Term.eval, Expr.eval]
      rw [ih current σ hσ]
      exact lowerUnaryOp_eval op (operand.eval current)
  | copysign magnitude sign ihMagnitude ihSign =>
      simp only [lowerWith, Term.eval, Expr.eval]
      rw [ihMagnitude current σ hσ, ihSign current σ hσ]
  | letIn name value body ihValue ihBody =>
      simp only [lowerWith, Expr.eval]
      exact ihBody
        (current.set name (value.eval current))
        (σ.set name (lowerWith value σ))
        (agree_set parameters current σ name (value.eval current)
          (lowerWith value σ) hσ (ihValue current σ hσ))

/-- The initial symbolic scope maps every name to its parameter term. -/
def parameterTerms : TermEnv := Term.param

@[simp] theorem parameterTerms_agree (ρ : SourceEnv) : Agree ρ ρ parameterTerms := by
  intro name
  rfl

/-- Lower an expression from the function's initial parameter scope. -/
def lowerF (e : Expr) : Term := lowerWith e parameterTerms

/-- **Source-to-verifier seam for exact binary32 arithmetic.**  Every
straight-line expression in the subset has the same value under the
extraction reading and the verifier-term reading, for every parameter
assignment. -/
theorem lowerF_eval (e : Expr) (ρ : SourceEnv) :
    (lowerF e).eval ρ = e.eval ρ := by
  exact lowerWith_eval e ρ ρ parameterTerms (parameterTerms_agree ρ)

/-! ## Carrier-level binary32-to-binary64 widening -/

/-- The extraction-side explicit `f64(e)` over the existing binary32 slice. -/
inductive WidenExpr
  | fromF32 (source : Expr)
  deriving Repr

/-- The verifier's width-changing unary `termFloat("fcvt", 64, source)`.
The source term remains width 32. -/
inductive WidenTerm
  | fcvt (source : Term)
  deriving Repr

/-- Extraction reading: `codegen/lean` emits `Float32.toFloat`. -/
def WidenExpr.eval : WidenExpr → SourceEnv → Float
  | .fromF32 source, ρ => (source.eval ρ).toFloat

/-- Verifier-model reading of the ordered width-changing `fcvt` operation.
This deliberately uses the same carrier as extraction; it does not prove the
production evaluator or an ISA implementation of that carrier. -/
def WidenTerm.eval : WidenTerm → SourceEnv → Float
  | .fcvt source, ρ => (source.eval ρ).toFloat

/-- Lower the operand in its binary32 scope, then retain one widening node. -/
def lowerWidenWith : WidenExpr → TermEnv → WidenTerm
  | .fromF32 source, σ => .fcvt (lowerWith source σ)

theorem lowerWidenWith_eval (widen : WidenExpr)
    (parameters current : SourceEnv) (σ : TermEnv)
    (hσ : Agree parameters current σ) :
    (lowerWidenWith widen σ).eval parameters = widen.eval current := by
  cases widen with
  | fromF32 source =>
      simp only [lowerWidenWith, WidenTerm.eval, WidenExpr.eval]
      rw [lowerWith_eval source parameters current σ hσ]

/-- Closed carrier-level seam for explicit binary32-to-binary64
widening from a function's initial parameter scope. -/
def lowerWiden (widen : WidenExpr) : WidenTerm :=
  lowerWidenWith widen parameterTerms

theorem lowerWiden_eval (widen : WidenExpr) (ρ : SourceEnv) :
    (lowerWiden widen).eval ρ = widen.eval ρ := by
  exact lowerWidenWith_eval widen ρ ρ parameterTerms
    (parameterTerms_agree ρ)

/-! ## A bounded binary64 FMA family -/

/-- The extraction-side binary64 FMA slice. Literals enter only after the
frontend has rounded them to binary64 bits; locals are pure substitutions. -/
inductive F64Expr
  | param (name : String)
  | literal (bits : UInt64)
  | widened (source : WidenExpr)
  | fma (multiplicand multiplier addend : F64Expr)
  | letIn (name : String) (value body : F64Expr)
  deriving Repr

abbrev F64SourceEnv := String → Float

def F64SourceEnv.set (ρ : F64SourceEnv) (name : String)
    (value : Float) : F64SourceEnv :=
  fun candidate => if candidate = name then value else ρ candidate

/-- Extraction reading. The ordered ternary operation is exactly the carrier
emitted by `codegen/lean`; this definition does not independently verify that
carrier's implementation. -/
def F64Expr.eval : F64Expr → F64SourceEnv → SourceEnv → Float
  | .param name, ρ64, _ => ρ64 name
  | .literal bits, _, _ => Float.ofBits bits
  | .widened source, _, ρ32 => source.eval ρ32
  | .fma multiplicand multiplier addend, ρ64, ρ32 =>
      Oak.FloatOps.fma64
        (multiplicand.eval ρ64 ρ32) (multiplier.eval ρ64 ρ32)
        (addend.eval ρ64 ρ32)
  | .letIn name value body, ρ64, ρ32 =>
      body.eval (ρ64.set name (value.eval ρ64 ρ32)) ρ32

/-- The verifier-term fragment corresponding to the bounded source family. -/
inductive F64Term
  | param (name : String)
  | literal (bits : UInt64)
  | widened (source : WidenTerm)
  | fma (multiplicand multiplier addend : F64Term)
  deriving Repr

abbrev F64TermEnv := String → F64Term

def F64TermEnv.set (σ : F64TermEnv) (name : String)
    (value : F64Term) : F64TermEnv :=
  fun candidate => if candidate = name then value else σ candidate

/-- Verifier-model reading of the same ordered `fma64` application. This is
an operation-identity model, not a proof of the Go evaluator or an ISA FMA. -/
def F64Term.eval : F64Term → F64SourceEnv → SourceEnv → Float
  | .param name, ρ64, _ => ρ64 name
  | .literal bits, _, _ => Float.ofBits bits
  | .widened source, _, ρ32 => source.eval ρ32
  | .fma multiplicand multiplier addend, ρ64, ρ32 =>
      Oak.FloatOps.fma64
        (multiplicand.eval ρ64 ρ32) (multiplier.eval ρ64 ρ32)
        (addend.eval ρ64 ρ32)

/-- Preserve one ordered ternary node and substitute pure local bindings. -/
def lowerF64With : F64Expr → F64TermEnv → F64Term
  | .param name, σ => σ name
  | .literal bits, _ => .literal bits
  | .widened source, _ => .widened (lowerWiden source)
  | .fma multiplicand multiplier addend, σ =>
      .fma (lowerF64With multiplicand σ) (lowerF64With multiplier σ)
        (lowerF64With addend σ)
  | .letIn name value body, σ =>
      lowerF64With body (σ.set name (lowerF64With value σ))

def F64Agree (parameters : F64SourceEnv) (ρ32 : SourceEnv)
    (current : F64SourceEnv) (σ : F64TermEnv) : Prop :=
  ∀ name, (σ name).eval parameters ρ32 = current name

private theorem f64Agree_set (parameters : F64SourceEnv) (ρ32 : SourceEnv)
    (current : F64SourceEnv)
    (σ : F64TermEnv) (name : String) (value : Float) (lowered : F64Term)
    (hσ : F64Agree parameters ρ32 current σ)
    (hv : lowered.eval parameters ρ32 = value) :
    F64Agree parameters ρ32 (current.set name value) (σ.set name lowered) := by
  intro candidate
  by_cases h : candidate = name
  · simp [F64SourceEnv.set, F64TermEnv.set, h, hv]
  · simp [F64SourceEnv.set, F64TermEnv.set, h, hσ candidate]

/-- The generalized local-substitution refinement. Both readings apply the
same binary64 carrier in the same operand order. -/
theorem lowerF64With_eval (e : F64Expr)
    (parameters current : F64SourceEnv) (ρ32 : SourceEnv) (σ : F64TermEnv)
    (hσ : F64Agree parameters ρ32 current σ) :
    (lowerF64With e σ).eval parameters ρ32 = e.eval current ρ32 := by
  induction e generalizing current σ with
  | param name => exact hσ name
  | literal => rfl
  | widened source => exact lowerWiden_eval source ρ32
  | fma multiplicand multiplier addend ihMultiplicand ihMultiplier ihAddend =>
      simp only [lowerF64With, F64Term.eval, F64Expr.eval]
      rw [ihMultiplicand current σ hσ, ihMultiplier current σ hσ,
          ihAddend current σ hσ]
  | letIn name value body ihValue ihBody =>
      simp only [lowerF64With, F64Expr.eval]
      exact ihBody
        (current.set name (value.eval current ρ32))
        (σ.set name (lowerF64With value σ))
        (f64Agree_set parameters ρ32 current σ name (value.eval current ρ32)
          (lowerF64With value σ) hσ (ihValue current σ hσ))

def f64ParameterTerms : F64TermEnv := F64Term.param

@[simp] theorem f64ParameterTerms_agree (ρ64 : F64SourceEnv) (ρ32 : SourceEnv) :
    F64Agree ρ64 ρ32 ρ64 f64ParameterTerms := by
  intro name
  rfl

def lowerF64 (e : F64Expr) : F64Term :=
  lowerF64With e f64ParameterTerms

/-- Closed carrier-level source-to-verifier seam for the bounded binary64 FMA
family. It proves operation identity and order, not IEEE implementation
correctness or machine-instruction semantics. -/
theorem lowerF64_eval (e : F64Expr) (ρ64 : F64SourceEnv) (ρ32 : SourceEnv) :
    (lowerF64 e).eval ρ64 ρ32 = e.eval ρ64 ρ32 := by
  exact lowerF64With_eval e ρ64 ρ64 ρ32 f64ParameterTerms
    (f64ParameterTerms_agree ρ64 ρ32)

/-- A Boolean condition over two float expressions. -/
inductive Condition
  | compare (op : SourceCompareOp) (left right : Expr)
  | literal (value : Bool)
  | negate (condition : Condition)
  | conjunction (left right : Condition)
  | disjunction (left right : Condition)
  deriving Repr

def Condition.eval : Condition → SourceEnv → Bool
  | .compare op left right, ρ => op.eval (left.eval ρ) (right.eval ρ)
  | .literal value, _ => value
  | .negate condition, ρ => !condition.eval ρ
  | .conjunction left right, ρ => left.eval ρ && right.eval ρ
  | .disjunction left right, ρ => left.eval ρ || right.eval ρ

def lowerConditionWith : Condition → TermEnv → BoolTerm
  | .compare op left right, σ =>
      .compare (lowerCompareOp op) (lowerWith left σ) (lowerWith right σ)
  | .literal value, _ => .literal value
  | .negate condition, σ => .negate (lowerConditionWith condition σ)
  | .conjunction left right, σ =>
      .conjunction (lowerConditionWith left σ) (lowerConditionWith right σ)
  | .disjunction left right, σ =>
      .disjunction (lowerConditionWith left σ) (lowerConditionWith right σ)

/-- Float comparison lowering preserves the IEEE predicate in every agreeing
scope. The comparison carriers treat every NaN alike, so this result is
independent of Lean's NaN-payload canonicalization. -/
theorem lowerConditionWith_eval (condition : Condition)
    (parameters current : SourceEnv) (σ : TermEnv)
    (hσ : Agree parameters current σ) :
    (lowerConditionWith condition σ).eval parameters = condition.eval current := by
  induction condition generalizing parameters current σ with
  | compare op left right =>
      simp only [lowerConditionWith, BoolTerm.eval, Condition.eval]
      rw [lowerWith_eval left parameters current σ hσ,
          lowerWith_eval right parameters current σ hσ]
      exact lowerCompareOp_eval op (left.eval current) (right.eval current)
  | literal => rfl
  | negate condition ih =>
      simp only [lowerConditionWith, BoolTerm.eval, Condition.eval]
      rw [ih parameters current σ hσ]
  | conjunction left right ihLeft ihRight =>
      simp only [lowerConditionWith, BoolTerm.eval, Condition.eval]
      rw [ihLeft parameters current σ hσ, ihRight parameters current σ hσ]
  | disjunction left right ihLeft ihRight =>
      simp only [lowerConditionWith, BoolTerm.eval, Condition.eval]
      rw [ihLeft parameters current σ hσ, ihRight parameters current σ hσ]

def lowerCondition (condition : Condition) : BoolTerm :=
  lowerConditionWith condition parameterTerms

theorem lowerCondition_eval (condition : Condition) (ρ : SourceEnv) :
    (lowerCondition condition).eval ρ = condition.eval ρ := by
  exact lowerConditionWith_eval condition ρ ρ parameterTerms
    (parameterTerms_agree ρ)

/-- One value-position Bool conditional in the source. Its guard and both
arms may contain any straight-line expression covered above. -/
structure SourceConditional where
  guard : Condition
  whenTrue : Expr
  whenFalse : Expr
  deriving Repr

/-- The verifier's `iteTerm` together with its lowered guard and arms. -/
structure VerifierConditional where
  guard : BoolTerm
  whenTrue : Term
  whenFalse : Term
  deriving Repr

def SourceConditional.eval (branch : SourceConditional) (ρ : SourceEnv) : Float32 :=
  bif branch.guard.eval ρ then branch.whenTrue.eval ρ else branch.whenFalse.eval ρ

def VerifierConditional.eval (branch : VerifierConditional)
    (ρ : SourceEnv) : Float32 :=
  bif branch.guard.eval ρ then branch.whenTrue.eval ρ else branch.whenFalse.eval ρ

/-- The value-position `MatchExpression` path in `oakLowering.lower`: lower
the Bool scrutinee, lower both value arms in the incoming symbolic scope, and
join them with `iteTerm`. -/
def lowerValueConditionalWith (branch : SourceConditional)
    (σ : TermEnv) : VerifierConditional := {
  guard := lowerConditionWith branch.guard σ
  whenTrue := lowerWith branch.whenTrue σ
  whenFalse := lowerWith branch.whenFalse σ
}

/-- The verifier select and the extraction's Lean `if` choose equal float
values in every agreeing scope. -/
theorem lowerValueConditionalWith_eval (branch : SourceConditional)
    (parameters current : SourceEnv) (σ : TermEnv)
    (hσ : Agree parameters current σ) :
    (lowerValueConditionalWith branch σ).eval parameters = branch.eval current := by
  simp only [lowerValueConditionalWith, VerifierConditional.eval,
    SourceConditional.eval]
  rw [lowerConditionWith_eval branch.guard parameters current σ hσ,
      lowerWith_eval branch.whenTrue parameters current σ hσ,
      lowerWith_eval branch.whenFalse parameters current σ hσ]

def lowerValueConditional (branch : SourceConditional) : VerifierConditional :=
  lowerValueConditionalWith branch parameterTerms

theorem lowerValueConditional_eval (branch : SourceConditional) (ρ : SourceEnv) :
    (lowerValueConditional branch).eval ρ = branch.eval ρ := by
  exact lowerValueConditionalWith_eval branch ρ ρ parameterTerms
    (parameterTerms_agree ρ)

/-- Pure float value expressions with arbitrarily nested Bool conditionals.
Each leaf is the straight-line subset and every guard is the pure condition
subset above. -/
inductive FlowExpr
  | leaf (value : Expr)
  | branch (guard : Condition) (whenTrue whenFalse : FlowExpr)
  deriving Repr

/-- The corresponding recursive tree of verifier `iteTerm`s. -/
inductive FlowTerm
  | leaf (value : Term)
  | branch (guard : BoolTerm) (whenTrue whenFalse : FlowTerm)
  deriving Repr

def FlowExpr.eval : FlowExpr → SourceEnv → Float32
  | .leaf value, ρ => value.eval ρ
  | .branch guard whenTrue whenFalse, ρ =>
      bif guard.eval ρ then whenTrue.eval ρ else whenFalse.eval ρ

def FlowTerm.eval : FlowTerm → SourceEnv → Float32
  | .leaf value, ρ => value.eval ρ
  | .branch guard whenTrue whenFalse, ρ =>
      bif guard.eval ρ then whenTrue.eval ρ else whenFalse.eval ρ

def lowerFlowWith : FlowExpr → TermEnv → FlowTerm
  | .leaf value, σ => .leaf (lowerWith value σ)
  | .branch guard whenTrue whenFalse, σ =>
      .branch (lowerConditionWith guard σ)
        (lowerFlowWith whenTrue σ) (lowerFlowWith whenFalse σ)

/-- Every finite nest of pure value conditionals preserves the source value.
This is the recursive form of `lowerValueConditionalWith_eval`. -/
theorem lowerFlowWith_eval (flow : FlowExpr)
    (parameters current : SourceEnv) (σ : TermEnv)
    (hσ : Agree parameters current σ) :
    (lowerFlowWith flow σ).eval parameters = flow.eval current := by
  induction flow generalizing parameters current σ with
  | leaf value => exact lowerWith_eval value parameters current σ hσ
  | branch guard whenTrue whenFalse ihTrue ihFalse =>
      simp only [lowerFlowWith, FlowTerm.eval, FlowExpr.eval]
      rw [lowerConditionWith_eval guard parameters current σ hσ,
          ihTrue parameters current σ hσ,
          ihFalse parameters current σ hσ]

def lowerFlow (flow : FlowExpr) : FlowTerm :=
  lowerFlowWith flow parameterTerms

theorem lowerFlow_eval (flow : FlowExpr) (ρ : SourceEnv) :
    (lowerFlow flow).eval ρ = flow.eval ρ := by
  exact lowerFlowWith_eval flow ρ ρ parameterTerms (parameterTerms_agree ρ)

/-- A sequence of scalar declarations or assignments. Each right-hand side
sees the preceding bindings, matching statement order in an Oak block. -/
abbrev Bindings := List (String × Expr)

def evalBindings : Bindings → SourceEnv → SourceEnv
  | [], current => current
  | (name, value) :: rest, current =>
      evalBindings rest (current.set name (value.eval current))

def lowerBindings : Bindings → TermEnv → TermEnv
  | [], σ => σ
  | (name, value) :: rest, σ =>
      lowerBindings rest (σ.set name (lowerWith value σ))

def bindingNames : Bindings → List String
  | [] => []
  | (name, _) :: rest => name :: bindingNames rest

/-- Sequential scalar bindings preserve the environment agreement invariant. -/
theorem lowerBindings_agree (bindings : Bindings)
    (parameters current : SourceEnv) (σ : TermEnv)
    (hσ : Agree parameters current σ) :
    Agree parameters (evalBindings bindings current) (lowerBindings bindings σ) := by
  induction bindings generalizing current σ with
  | nil => exact hσ
  | cons binding rest ih =>
      rcases binding with ⟨name, value⟩
      exact ih
        (current.set name (value.eval current))
        (σ.set name (lowerWith value σ))
        (agree_set parameters current σ name (value.eval current)
          (lowerWith value σ) hσ
          (lowerWith_eval value parameters current σ hσ))

/-- Rebind exactly the names written by either arm to their selected source
values. Names outside the write set retain their pre-branch values. -/
def selectBindings : List String → Bool → SourceEnv → SourceEnv → SourceEnv → SourceEnv
  | [], _, before, _, _ => before
  | name :: rest, guard, before, afterTrue, afterFalse =>
      selectBindings rest guard
        (before.set name (bif guard then afterTrue name else afterFalse name))
        afterTrue afterFalse

/-- The verifier counterpart of `selectBindings`, matching `mergeLocals`:
every written scalar local becomes an `iteTerm` over the two arm outcomes. -/
def mergeBindings : List String → BoolTerm → TermEnv → TermEnv → TermEnv → TermEnv
  | [], _, before, _, _ => before
  | name :: rest, guard, before, afterTrue, afterFalse =>
      mergeBindings rest guard
        (before.set name (.ite guard (afterTrue name) (afterFalse name)))
        afterTrue afterFalse

private theorem mergeBindings_agree (names : List String)
    (parameters : SourceEnv) (sourceGuard : Bool) (verifierGuard : BoolTerm)
    (before afterTrue afterFalse : SourceEnv)
    (beforeTerms afterTrueTerms afterFalseTerms : TermEnv)
    (hBefore : Agree parameters before beforeTerms)
    (hTrue : Agree parameters afterTrue afterTrueTerms)
    (hFalse : Agree parameters afterFalse afterFalseTerms)
    (hGuard : verifierGuard.eval parameters = sourceGuard) :
    Agree parameters
      (selectBindings names sourceGuard before afterTrue afterFalse)
      (mergeBindings names verifierGuard beforeTerms afterTrueTerms afterFalseTerms) := by
  induction names generalizing before beforeTerms with
  | nil => exact hBefore
  | cons name rest ih =>
      apply ih
      exact agree_set parameters before beforeTerms name
        (bif sourceGuard then afterTrue name else afterFalse name)
        (.ite verifierGuard (afterTrueTerms name) (afterFalseTerms name)) hBefore (by
          simp only [Term.eval]
          rw [hGuard, hTrue name, hFalse name])

/-- A statement-position conditional over any finite number of scalar `f32`
locals. Initializers and both arms execute sequentially; each arm starts from
the same initialized scope, then every name written by either arm is merged. -/
structure ConditionalBlock where
  initializers : Bindings
  guard : Condition
  whenTrue : Bindings
  whenFalse : Bindings
  continuation : Expr
  deriving Repr

def ConditionalBlock.sourceBase (branch : ConditionalBlock)
    (current : SourceEnv) : SourceEnv :=
  evalBindings branch.initializers current

def ConditionalBlock.verifierBase (branch : ConditionalBlock)
    (σ : TermEnv) : TermEnv :=
  lowerBindings branch.initializers σ

def ConditionalBlock.written (branch : ConditionalBlock) : List String :=
  bindingNames branch.whenTrue ++ bindingNames branch.whenFalse

def ConditionalBlock.sourceMerged (branch : ConditionalBlock)
    (current : SourceEnv) : SourceEnv :=
  let before := branch.sourceBase current
  selectBindings branch.written (branch.guard.eval before) before
    (evalBindings branch.whenTrue before)
    (evalBindings branch.whenFalse before)

def ConditionalBlock.verifierMerged (branch : ConditionalBlock)
    (σ : TermEnv) : TermEnv :=
  let before := branch.verifierBase σ
  mergeBindings branch.written (lowerConditionWith branch.guard before) before
    (lowerBindings branch.whenTrue before)
    (lowerBindings branch.whenFalse before)

def ConditionalBlock.eval (branch : ConditionalBlock)
    (current : SourceEnv) : Float32 :=
  branch.continuation.eval (branch.sourceMerged current)

def lowerConditionalBlockWith (branch : ConditionalBlock)
    (σ : TermEnv) : Term :=
  lowerWith branch.continuation (branch.verifierMerged σ)

private theorem conditionalBlockMerged_agree (branch : ConditionalBlock)
    (parameters current : SourceEnv) (σ : TermEnv)
    (hσ : Agree parameters current σ) :
    Agree parameters (branch.sourceMerged current) (branch.verifierMerged σ) := by
  have hBase : Agree parameters (branch.sourceBase current)
      (branch.verifierBase σ) :=
    lowerBindings_agree branch.initializers parameters current σ hσ
  have hTrue : Agree parameters
      (evalBindings branch.whenTrue (branch.sourceBase current))
      (lowerBindings branch.whenTrue (branch.verifierBase σ)) :=
    lowerBindings_agree branch.whenTrue parameters
      (branch.sourceBase current) (branch.verifierBase σ) hBase
  have hFalse : Agree parameters
      (evalBindings branch.whenFalse (branch.sourceBase current))
      (lowerBindings branch.whenFalse (branch.verifierBase σ)) :=
    lowerBindings_agree branch.whenFalse parameters
      (branch.sourceBase current) (branch.verifierBase σ) hBase
  exact mergeBindings_agree branch.written parameters
    (branch.guard.eval (branch.sourceBase current))
    (lowerConditionWith branch.guard (branch.verifierBase σ))
    (branch.sourceBase current)
    (evalBindings branch.whenTrue (branch.sourceBase current))
    (evalBindings branch.whenFalse (branch.sourceBase current))
    (branch.verifierBase σ)
    (lowerBindings branch.whenTrue (branch.verifierBase σ))
    (lowerBindings branch.whenFalse (branch.verifierBase σ)) hBase hTrue hFalse
    (lowerConditionWith_eval branch.guard parameters
      (branch.sourceBase current) (branch.verifierBase σ) hBase)

theorem lowerConditionalBlockWith_eval (branch : ConditionalBlock)
    (parameters current : SourceEnv) (σ : TermEnv)
    (hσ : Agree parameters current σ) :
    (lowerConditionalBlockWith branch σ).eval parameters = branch.eval current := by
  exact lowerWith_eval branch.continuation parameters
    (branch.sourceMerged current) (branch.verifierMerged σ)
    (conditionalBlockMerged_agree branch parameters current σ hσ)

def lowerConditionalBlock (branch : ConditionalBlock) : Term :=
  lowerConditionalBlockWith branch parameterTerms

theorem lowerConditionalBlock_eval (branch : ConditionalBlock) (ρ : SourceEnv) :
    (lowerConditionalBlock branch).eval ρ = branch.eval ρ := by
  exact lowerConditionalBlockWith_eval branch ρ ρ parameterTerms
    (parameterTerms_agree ρ)

/-- The original one-local slice, retained as a compact corollary of the
general finite-binding statement theorem. -/
structure ConditionalAssignment where
  name : String
  initial : Expr
  guard : Condition
  whenTrue : Expr
  whenFalse : Expr
  continuation : Expr
  deriving Repr

def ConditionalAssignment.asBlock (branch : ConditionalAssignment) : ConditionalBlock := {
  initializers := [(branch.name, branch.initial)]
  guard := branch.guard
  whenTrue := [(branch.name, branch.whenTrue)]
  whenFalse := [(branch.name, branch.whenFalse)]
  continuation := branch.continuation
}

def ConditionalAssignment.eval (branch : ConditionalAssignment)
    (current : SourceEnv) : Float32 :=
  branch.asBlock.eval current

def lowerConditionalAssignmentWith (branch : ConditionalAssignment)
    (σ : TermEnv) : Term :=
  lowerConditionalBlockWith branch.asBlock σ

theorem lowerConditionalAssignmentWith_eval (branch : ConditionalAssignment)
    (parameters current : SourceEnv) (σ : TermEnv)
    (hσ : Agree parameters current σ) :
    (lowerConditionalAssignmentWith branch σ).eval parameters = branch.eval current := by
  exact lowerConditionalBlockWith_eval branch.asBlock parameters current σ hσ

def lowerConditionalAssignment (branch : ConditionalAssignment) : Term :=
  lowerConditionalAssignmentWith branch parameterTerms

theorem lowerConditionalAssignment_eval (branch : ConditionalAssignment)
    (ρ : SourceEnv) :
    (lowerConditionalAssignment branch).eval ρ = branch.eval ρ := by
  exact lowerConditionalAssignmentWith_eval branch ρ ρ parameterTerms
    (parameterTerms_agree ρ)

/-- A pure call in this slice: ordered callee parameter names paired with
argument expressions evaluated in the caller, and a straight-line callee body.
Parameter uniqueness is a frontend invariant. -/
structure Call where
  arguments : List (String × Expr)
  body : Expr
  deriving Repr

/-- Unbound names cannot occur in a checked callee. Giving both semantic
readings the same zero default makes that frontend invariant irrelevant to the
refinement proof. -/
def emptySourceEnv : SourceEnv := fun _ => Float32.ofBits 0
def emptyTermEnv : TermEnv := fun _ => .literal 0

@[simp] theorem emptyEnvs_agree (parameters : SourceEnv) :
    Agree parameters emptySourceEnv emptyTermEnv := by
  intro name
  rfl

/-- Bind arguments from left to right. Every argument is evaluated in the
unchanged caller scope, never in the partially built callee scope. -/
def bindSourceArgumentsFrom (caller base : SourceEnv) :
    List (String × Expr) → SourceEnv
  | [] => base
  | (name, argument) :: rest =>
      bindSourceArgumentsFrom caller
        (base.set name (argument.eval caller)) rest

/-- Verifier counterpart: lower every argument in the unchanged caller term
scope and bind its term to the corresponding callee parameter. -/
def bindTermArgumentsFrom (caller : TermEnv) (base : TermEnv) :
    List (String × Expr) → TermEnv
  | [] => base
  | (name, argument) :: rest =>
      bindTermArgumentsFrom caller
        (base.set name (lowerWith argument caller)) rest

theorem bindArgumentsFrom_agree (arguments : List (String × Expr))
    (parameters current baseSource : SourceEnv) (caller baseTerm : TermEnv)
    (hcaller : Agree parameters current caller)
    (hbase : Agree parameters baseSource baseTerm) :
    Agree parameters
      (bindSourceArgumentsFrom current baseSource arguments)
      (bindTermArgumentsFrom caller baseTerm arguments) := by
  induction arguments generalizing baseSource baseTerm with
  | nil => exact hbase
  | cons binding rest ih =>
      rcases binding with ⟨name, argument⟩
      simp only [bindSourceArgumentsFrom, bindTermArgumentsFrom]
      exact ih
        (baseSource.set name (argument.eval current))
        (baseTerm.set name (lowerWith argument caller))
        (agree_set parameters baseSource baseTerm name
          (argument.eval current) (lowerWith argument caller) hbase
          (lowerWith_eval argument parameters current caller hcaller))

def bindSourceArguments (caller : SourceEnv)
    (arguments : List (String × Expr)) : SourceEnv :=
  bindSourceArgumentsFrom caller emptySourceEnv arguments

def bindTermArguments (caller : TermEnv)
    (arguments : List (String × Expr)) : TermEnv :=
  bindTermArgumentsFrom caller emptyTermEnv arguments

theorem bindArguments_agree (arguments : List (String × Expr))
    (parameters current : SourceEnv) (caller : TermEnv)
    (hcaller : Agree parameters current caller) :
    Agree parameters
      (bindSourceArguments current arguments)
      (bindTermArguments caller arguments) := by
  exact bindArgumentsFrom_agree arguments parameters current emptySourceEnv
    caller emptyTermEnv hcaller (emptyEnvs_agree parameters)

def Call.eval (call : Call) (caller : SourceEnv) : Float32 :=
  call.body.eval (bindSourceArguments caller call.arguments)

/-- The pure-f32 portion of `inlineCall`: bind lowered arguments to the
callee's parameters and lower its body in that new symbolic scope. -/
def lowerCallWith (call : Call) (caller : TermEnv) : Term :=
  lowerWith call.body (bindTermArguments caller call.arguments)

theorem lowerCallWith_eval (call : Call) (parameters current : SourceEnv)
    (caller : TermEnv) (hcaller : Agree parameters current caller) :
    (lowerCallWith call caller).eval parameters = call.eval current := by
  exact lowerWith_eval call.body parameters
    (bindSourceArguments current call.arguments)
    (bindTermArguments caller call.arguments)
    (bindArguments_agree call.arguments parameters current caller hcaller)

def lowerCall (call : Call) : Term := lowerCallWith call parameterTerms

theorem lowerCall_eval (call : Call) (ρ : SourceEnv) :
    (lowerCall call).eval ρ = call.eval ρ := by
  exact lowerCallWith_eval call ρ ρ parameterTerms (parameterTerms_agree ρ)

private def a : Expr := .param "a"
private def b : Expr := .param "b"
private def c : Expr := .param "c"
private def a64 : F64Expr := .param "a"
private def b64 : F64Expr := .param "b"
private def c64 : F64Expr := .param "c"
private def x64 : F64Expr := .param "x"
private def y64 : F64Expr := .param "y"

/-- Render pins mirrored by `asm/lowering_refinement_test.go`. -/
example : lowerF (.binary .add a b) = .float .fadd (.param "a") (.param "b") := rfl
example : lowerF (.binary .sub a b) = .float .fsub (.param "a") (.param "b") := rfl
example : lowerF (.binary .mul a b) = .float .fmul (.param "a") (.param "b") := rfl
example : lowerF (.binary .div a b) = .float .fdiv (.param "a") (.param "b") := rfl
example : lowerF (.fma a b c) =
    .fma (.param "a") (.param "b") (.param "c") := rfl
example : lowerWiden (.fromF32 (.binary .add a b)) =
    .fcvt (.float .fadd (.param "a") (.param "b")) := rfl
example : lowerF64 (.fma a64 b64 c64) =
    .fma (.param "a") (.param "b") (.param "c") := rfl
example : lowerF64
    (.fma (.widened (.fromF32 (.binary .add a b))) x64 y64) =
    .fma (.widened (.fcvt (.float .fadd (.param "a") (.param "b"))))
      (.param "x") (.param "y") := rfl
example : lowerF64
    (.letIn "t" (.fma a64 b64 c64)
      (.fma (.param "t") b64 c64)) =
    .fma (.fma (.param "a") (.param "b") (.param "c"))
      (.param "b") (.param "c") := rfl
example : lowerF (.unary .neg a) = .unary .xorSign (.param "a") := rfl
example : lowerF (.unary .abs a) = .unary .clearSign (.param "a") := rfl
example : lowerF (.copysign (.unary .neg a) b) =
    .copysign (.unary .xorSign (.param "a")) (.param "b") := rfl
example : lowerCondition (.compare .eq a b) =
    .compare .eq (.param "a") (.param "b") := rfl
example : lowerCondition (.compare .ne a b) =
    .compare .ne (.param "a") (.param "b") := rfl
example : lowerCondition (.compare .lt a b) =
    .compare .lt (.param "a") (.param "b") := rfl
example : lowerCondition (.compare .le a b) =
    .compare .le (.param "a") (.param "b") := rfl
example : lowerCondition (.compare .gt a b) =
    .compare .gt (.param "a") (.param "b") := rfl
example : lowerCondition (.compare .ge a b) =
    .compare .ge (.param "a") (.param "b") := rfl
example : lowerCondition
    (.disjunction
      (.negate (.compare .lt a b))
      (.conjunction
        (.compare .eq a b)
        (.compare .ne b (.literal 0)))) =
    .disjunction
      (.negate (.compare .lt (.param "a") (.param "b")))
      (.conjunction
        (.compare .eq (.param "a") (.param "b"))
        (.compare .ne (.param "b") (.literal 0))) := rfl
example : lowerValueConditional {
    guard := .compare .lt a b
    whenTrue := .binary .add a (.literal 0x3F800000)
    whenFalse := .binary .mul b (.literal 0x40000000)
  } = {
    guard := .compare .lt (.param "a") (.param "b")
    whenTrue := .float .fadd (.param "a") (.literal 0x3F800000)
    whenFalse := .float .fmul (.param "b") (.literal 0x40000000)
  } := rfl
example : lowerFlow
    (.branch (.compare .lt a b)
      (.branch (.compare .eq a (.literal 0))
        (.leaf (.binary .add a (.literal 0x3F800000)))
        (.leaf (.binary .sub b (.literal 0x3F800000))))
      (.leaf (.binary .mul b (.literal 0x40000000)))) =
    .branch (.compare .lt (.param "a") (.param "b"))
      (.branch (.compare .eq (.param "a") (.literal 0))
        (.leaf (.float .fadd (.param "a") (.literal 0x3F800000)))
        (.leaf (.float .fsub (.param "b") (.literal 0x3F800000))))
      (.leaf (.float .fmul (.param "b") (.literal 0x40000000))) := rfl
example : lowerConditionalAssignment {
    name := "y"
    initial := a
    guard := .compare .lt a b
    whenTrue := .binary .add b (.literal 0x3F800000)
    whenFalse := .binary .mul a (.literal 0x40000000)
    continuation := .binary .sub (.param "y") (.literal 0x40400000)
  } = .float .fsub
    (.ite (.compare .lt (.param "a") (.param "b"))
      (.float .fadd (.param "b") (.literal 0x3F800000))
      (.float .fmul (.param "a") (.literal 0x40000000)))
    (.literal 0x40400000) := rfl
example : lowerConditionalBlock {
    initializers := [("x", a), ("y", b)]
    guard := .compare .lt (.param "x") (.param "y")
    whenTrue := [
      ("x", .binary .add (.param "y") (.literal 0x3F800000)),
      ("y", .binary .mul (.param "x") (.literal 0x40000000))]
    whenFalse := [
      ("x", .binary .sub (.param "x") (.literal 0x3F800000)),
      ("y", .binary .add (.param "y") (.literal 0x40400000))]
    continuation := .binary .sub (.param "x") (.param "y")
  } = .float .fsub
    (.ite (.compare .lt (.param "a") (.param "b"))
      (.float .fadd (.param "b") (.literal 0x3F800000))
      (.float .fsub (.param "a") (.literal 0x3F800000)))
    (.ite (.compare .lt (.param "a") (.param "b"))
      (.float .fmul
        (.float .fadd (.param "b") (.literal 0x3F800000))
        (.literal 0x40000000))
      (.float .fadd (.param "b") (.literal 0x40400000))) := rfl
example : lowerCall {
    arguments := [("x", .binary .add a b), ("y", b)]
    body := .binary .add (.binary .mul (.param "x") (.param "y"))
      (.literal 0x3F800000)
  } = .float .fadd
    (.float .fmul
      (.float .fadd (.param "a") (.param "b"))
      (.param "b"))
    (.literal 0x3F800000) := rfl
example : lowerF (.binary .add (.binary .mul a b) c) =
    .float .fadd (.float .fmul (.param "a") (.param "b")) (.param "c") := rfl
example : lowerF (.binary .add a (.literal 0x3FC00000)) =
    .float .fadd (.param "a") (.literal 0x3FC00000) := rfl
example : lowerF (.letIn "y" (.binary .add a (.literal 0x3FC00000))
    (.binary .mul (.param "y") (.param "y"))) =
    .float .fmul
      (.float .fadd (.param "a") (.literal 0x3FC00000))
      (.float .fadd (.param "a") (.literal 0x3FC00000)) := rfl
example : lowerF (.letIn "y" a
    (.letIn "y" (.binary .add (.param "y") (.literal 0x3F800000))
      (.binary .mul (.param "y") (.literal 0x40000000)))) =
    .float .fmul
      (.float .fadd (.param "a") (.literal 0x3F800000))
      (.literal 0x40000000) := rfl

end Oak.FloatLoweringRefinement
