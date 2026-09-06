import Oak.RecordShapeRefinement

namespace Oak.GenericConstraintRefinement

open Oak.RecordShape
open Oak.RecordShapeRefinement

/-- Small semantic type language for the concrete generic-call path. Runtime
    representation is deliberately absent: inference and qualified constraints
    operate only on semantic types. -/
inductive Ty where
  | var : Nat → Ty
  | atom : Nat → Ty
  | record : ConcreteShape → Ty
  | unary : Nat → Ty → Ty
  deriving DecidableEq, Repr

/-- Substitute one quantified type variable through a semantic type. This
    mirrors `Substitution.Apply` for the constructors modeled here. -/
def Substitute (variable : Nat) (replacement : Ty) : Ty → Ty
  | .var name => if name = variable then replacement else .var name
  | .atom name => .atom name
  | .record fields => .record fields
  | .unary ctor arg => .unary ctor (Substitute variable replacement arg)

/-- Infer one quantified variable from a parameter pattern and an actual
    argument. Repeated occurrences must infer the same semantic type. -/
def Infer (variable : Nat) : Ty → Ty → Option Ty
  | .var name, actual => if name = variable then some actual else none
  | .atom expected, .atom actual => if expected = actual then none else none
  | .record expected, .record actual => if expected = actual then none else none
  | .unary expectedCtor expectedArg, .unary actualCtor actualArg =>
      if expectedCtor = actualCtor then Infer variable expectedArg actualArg else none
  | _, _ => none

/-- Record-shape constraint discharge for one inferred semantic type. -/
def Discharge (inferred : Ty) (required : ConcreteShape) : Bool :=
  match inferred with
  | .record candidate => SatisfiesBool candidate required
  | _ => false

/-- Successful direct generic invocation: infer `T`, discharge its record-shape
    requirement, then substitute the inferred semantic type into the result. -/
def Invoke
    (variable : Nat)
    (parameter actual result : Ty)
    (required : ConcreteShape) : Option Ty :=
  match Infer variable parameter actual with
  | none => none
  | some inferred =>
      if Discharge inferred required then
        some (Substitute variable inferred result)
      else
        none

/-- A direct `T` parameter infers exactly the actual semantic type. -/
theorem infer_direct (variable : Nat) (actual : Ty) :
    Infer variable (.var variable) actual = some actual := by
  simp [Infer]

/-- A nested unary parameter, such as a view/container of `T`, preserves the
    same inferred semantic binding when constructor identity matches. -/
theorem infer_unary (variable ctor : Nat) (actual : Ty) :
    Infer variable (.unary ctor (.var variable)) (.unary ctor actual) = some actual := by
  simp [Infer]

/-- Substitution of the quantified variable itself yields the inferred type. -/
theorem substitute_direct (variable : Nat) (replacement : Ty) :
    Substitute variable replacement (.var variable) = replacement := by
  simp [Substitute]

/-- Substitution is compositional through the modeled unary constructor. -/
theorem substitute_unary (variable ctor : Nat) (replacement body : Ty) :
    Substitute variable replacement (.unary ctor body) =
      .unary ctor (Substitute variable replacement body) := by
  rfl

/-- Whole direct-call refinement. For well-formed record shapes, the executable
    generic pipeline succeeds exactly when the abstract record-shape relation
    holds, and the returned semantic type is exactly the substituted result. -/
theorem invoke_direct_record_iff
    (variable : Nat)
    (candidate required : ConcreteShape)
    (result : Ty)
    (hcandidate : UniqueNames candidate)
    (hrequired : UniqueNames required) :
    Invoke variable (.var variable) (.record candidate) result required =
        some (Substitute variable (.record candidate) result) ↔
      Satisfies candidate required := by
  simp [Invoke, infer_direct, Discharge,
    satisfiesBool_iff_satisfies candidate required hcandidate hrequired]

/-- The same correspondence holds when `T` is inferred through one semantic
    unary constructor (e.g. a modeled view/container position). -/
theorem invoke_unary_record_iff
    (variable ctor : Nat)
    (candidate required : ConcreteShape)
    (result : Ty)
    (hcandidate : UniqueNames candidate)
    (hrequired : UniqueNames required) :
    Invoke variable
        (.unary ctor (.var variable))
        (.unary ctor (.record candidate))
        result required =
        some (Substitute variable (.record candidate) result) ↔
      Satisfies candidate required := by
  simp [Invoke, infer_unary, Discharge,
    satisfiesBool_iff_satisfies candidate required hcandidate hrequired]

/-- If the abstract shape obligation fails, the direct generic call cannot
    produce a substituted result. -/
theorem invoke_direct_rejects_unsatisfied
    (variable : Nat)
    (candidate required : ConcreteShape)
    (result : Ty)
    (hcandidate : UniqueNames candidate)
    (hrequired : UniqueNames required)
    (hnot : ¬ Satisfies candidate required) :
    Invoke variable (.var variable) (.record candidate) result required = none := by
  have hbool : SatisfiesBool candidate required = false := by
    cases h : SatisfiesBool candidate required with
    | false => rfl
    | true =>
        exfalso
        exact hnot ((satisfiesBool_iff_satisfies candidate required hcandidate hrequired).mp h)
  simp [Invoke, Infer, Discharge, hbool]

end Oak.GenericConstraintRefinement
