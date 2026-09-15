import Oak.FloatOps

/-!
# The first floating-point source/lowering refinement

`Oak.LoweringRefinement` relates the extraction and verifier lowerings for the
shared integer and aggregate language.  This module starts the corresponding
floating-point seam with the binary32 operations emitted by
`oak build -lean-floats bits`: `+`, `-`, `*`, and the six comparisons.

The source side uses the exact `Oak.FloatOps` carriers, modulo their documented
canonical-NaN reading of Lean's `Float32`. The verifier side has
the operation names used by `asm/floats_lowering.go` and
`asm/floats_ops.go`: `fadd`, `fsub`, and `fmul`, each at width 32.  The Go
render test in `asm/lowering_refinement_test.go` pins production lowering to
the `lowerF` shapes below.

The second increment adds literals after decimal parsing has rounded them to
binary32 bits, plus straight-line local declarations and rebindings.  The
third adds the total sign operations: negation, absolute value, and copysign,
under that same result-level NaN quotient. Payload-observing bitcasts are not
part of this theorem. The fourth adds IEEE equality and ordering: NaNs are
unordered and the two signed zeros are equal. The comparison leaves compose
through pure Boolean literals, negation, conjunction, and disjunction.
Decimal parsing itself, conversions, spans, control flow, calls, binary64, and
SIMD remain outside this theorem.
-/

namespace Oak.FloatLoweringRefinement

/-- The binary32 operations whose extraction uses the bit-exact carriers in
`Oak.FloatOps`. -/
inductive SourceOp
  | add
  | sub
  | mul
  deriving DecidableEq, Repr

/-- The corresponding `termFloat` operation names in the verifier. -/
inductive VerifierOp
  | fadd
  | fsub
  | fmul
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

/-- The extraction's `-lean-floats bits` reading of the three operations. -/
def SourceOp.eval : SourceOp → Float32 → Float32 → Float32
  | .add => Oak.FloatOps.add32
  | .sub => Oak.FloatOps.sub32
  | .mul => Oak.FloatOps.mul32

/-- The formal reading of the verifier's `termFloat` names.  The verifier
treats a non-constant application as uninterpreted when deciding equality;
this evaluator gives that shared application its Oak binary32 meaning. -/
def VerifierOp.eval : VerifierOp → Float32 → Float32 → Float32
  | .fadd => Oak.FloatOps.add32
  | .fsub => Oak.FloatOps.sub32
  | .fmul => Oak.FloatOps.mul32

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

/-- Mapping a source operation to the verifier operation preserves its exact
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
  | .unary op operand, ρ => op.eval (operand.eval ρ)
  | .copysign magnitude sign, ρ =>
      Oak.FloatOps.copysign32 (magnitude.eval ρ) (sign.eval ρ)
  | .letIn name value body, ρ => body.eval (ρ.set name (value.eval ρ))

/-- The verifier term subset reached by `lowerF`. -/
inductive Term
  | param (name : String)
  | literal (bits : UInt32)
  | float (op : VerifierOp) (left right : Term)
  | unary (op : VerifierUnaryOp) (operand : Term)
  | copysign (magnitude sign : Term)
  deriving Repr

/-- The verifier's symbolic bindings.  A local maps directly to the term of
its initializer, which is how `declareLocal` and `assignLocal` substitute
straight-line locals in `asm/verify.go`. -/
abbrev TermEnv := String → Term

/-- Rebind one symbolic local. -/
def TermEnv.set (σ : TermEnv) (name : String) (value : Term) : TermEnv :=
  fun candidate => if candidate = name then value else σ candidate

/-- The verifier-side interpretation under the same source parameters. -/
def Term.eval : Term → SourceEnv → Float32
  | .param name, ρ => ρ name
  | .literal bits, _ => Float32.ofBits bits
  | .float op left right, ρ => op.eval (left.eval ρ) (right.eval ρ)
  | .unary op operand, ρ => op.eval (operand.eval ρ)
  | .copysign magnitude sign, ρ =>
      Oak.FloatOps.copysign32 (magnitude.eval ρ) (sign.eval ρ)

/-- The float branch of `oakLowering.lower`: operands keep their source order,
each source operation becomes one width-32 `termFloat`, and a local is
substituted by its initializer's already-lowered term. -/
def lowerWith : Expr → TermEnv → Term
  | .param name, σ => σ name
  | .literal bits, _ => .literal bits
  | .binary op left right, σ =>
      .float (lowerOp op) (lowerWith left σ) (lowerWith right σ)
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

/-- A Boolean condition over two float expressions. -/
inductive Condition
  | compare (op : SourceCompareOp) (left right : Expr)
  | literal (value : Bool)
  | negate (condition : Condition)
  | conjunction (left right : Condition)
  | disjunction (left right : Condition)
  deriving Repr

/-- The verifier-side Boolean term produced by `floatCompare`. -/
inductive BoolTerm
  | compare (op : VerifierCompareOp) (left right : Term)
  | literal (value : Bool)
  | negate (condition : BoolTerm)
  | conjunction (left right : BoolTerm)
  | disjunction (left right : BoolTerm)
  deriving Repr

def Condition.eval : Condition → SourceEnv → Bool
  | .compare op left right, ρ => op.eval (left.eval ρ) (right.eval ρ)
  | .literal value, _ => value
  | .negate condition, ρ => !condition.eval ρ
  | .conjunction left right, ρ => left.eval ρ && right.eval ρ
  | .disjunction left right, ρ => left.eval ρ || right.eval ρ

def BoolTerm.eval : BoolTerm → SourceEnv → Bool
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

/-- Render pins mirrored by `asm/lowering_refinement_test.go`. -/
example : lowerF (.binary .add a b) = .float .fadd (.param "a") (.param "b") := rfl
example : lowerF (.binary .sub a b) = .float .fsub (.param "a") (.param "b") := rfl
example : lowerF (.binary .mul a b) = .float .fmul (.param "a") (.param "b") := rfl
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
