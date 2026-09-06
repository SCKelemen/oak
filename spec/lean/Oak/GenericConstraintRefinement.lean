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
def Substitute (v : Nat) (replacement : Ty) : Ty → Ty
  | .var name => if name = v then replacement else .var name
  | .atom name => .atom name
  | .record fields => .record fields
  | .unary ctor arg => .unary ctor (Substitute v replacement arg)

/-- Infer one quantified variable from a parameter pattern and an actual
    argument. -/
def Infer (v : Nat) : Ty → Ty → Option Ty
  | .var name, actual => if name = v then some actual else none
  | .atom _, .atom _ => none
  | .record _, .record _ => none
  | .unary expectedCtor expectedArg, .unary actualCtor actualArg =>
      if expectedCtor = actualCtor then Infer v expectedArg actualArg else none
  | _, _ => none

/-- Record-shape constraint discharge for one inferred semantic type. -/
def Discharge (inferred : Ty) (required : ConcreteShape) : Bool :=
  match inferred with
  | .record candidate => SatisfiesBool candidate required
  | _ => false

/-- Successful generic invocation: infer `T`, discharge its record-shape
    requirement, then substitute the inferred semantic type into the result. -/
def Invoke
    (v : Nat)
    (parameter actual result : Ty)
    (required : ConcreteShape) : Option Ty :=
  match Infer v parameter actual with
  | none => none
  | some inferred =>
      if Discharge inferred required then
        some (Substitute v inferred result)
      else
        none

/-- A direct `T` parameter infers exactly the actual semantic type. -/
theorem infer_direct (v : Nat) (actual : Ty) :
    Infer v (.var v) actual = some actual := by
  simp [Infer]

/-- A nested unary parameter, such as a view/container of `T`, preserves the
    same inferred semantic binding when constructor identity matches. -/
theorem infer_unary (v ctor : Nat) (actual : Ty) :
    Infer v (.unary ctor (.var v)) (.unary ctor actual) = some actual := by
  simp [Infer]

/-- Substitution of the quantified variable itself yields the inferred type. -/
theorem substitute_direct (v : Nat) (replacement : Ty) :
    Substitute v replacement (.var v) = replacement := by
  simp [Substitute]

/-- Substitution is compositional through the modeled unary constructor. -/
theorem substitute_unary (v ctor : Nat) (replacement body : Ty) :
    Substitute v replacement (.unary ctor body) =
      .unary ctor (Substitute v replacement body) := by
  rfl

/-- Whole direct-call refinement. For well-formed record shapes, the executable
    generic pipeline succeeds exactly when the abstract record-shape relation
    holds, and the returned semantic type is exactly the substituted result. -/
theorem invoke_direct_record_iff
    (v : Nat)
    (candidate required : ConcreteShape)
    (result : Ty)
    (hcandidate : UniqueNames candidate)
    (hrequired : UniqueNames required) :
    Invoke v (.var v) (.record candidate) result required =
        some (Substitute v (.record candidate) result) ↔
      Satisfies candidate required := by
  constructor
  · intro hinvoke
    cases hbool : SatisfiesBool candidate required with
    | false =>
        simp [Invoke, Infer, Discharge, hbool] at hinvoke
    | true =>
        exact (satisfiesBool_iff_satisfies candidate required hcandidate hrequired).mp hbool
  · intro hsatisfies
    have hbool : SatisfiesBool candidate required = true :=
      (satisfiesBool_iff_satisfies candidate required hcandidate hrequired).mpr hsatisfies
    simp [Invoke, Infer, Discharge, hbool]

/-- The same correspondence holds when `T` is inferred through one semantic
    unary constructor (e.g. a modeled view/container position). -/
theorem invoke_unary_record_iff
    (v ctor : Nat)
    (candidate required : ConcreteShape)
    (result : Ty)
    (hcandidate : UniqueNames candidate)
    (hrequired : UniqueNames required) :
    Invoke v
        (.unary ctor (.var v))
        (.unary ctor (.record candidate))
        result required =
        some (Substitute v (.record candidate) result) ↔
      Satisfies candidate required := by
  constructor
  · intro hinvoke
    cases hbool : SatisfiesBool candidate required with
    | false =>
        simp [Invoke, Infer, Discharge, hbool] at hinvoke
    | true =>
        exact (satisfiesBool_iff_satisfies candidate required hcandidate hrequired).mp hbool
  · intro hsatisfies
    have hbool : SatisfiesBool candidate required = true :=
      (satisfiesBool_iff_satisfies candidate required hcandidate hrequired).mpr hsatisfies
    simp [Invoke, Infer, Discharge, hbool]

/-- If the abstract shape obligation fails, the direct generic call cannot
    produce a substituted result. -/
theorem invoke_direct_rejects_unsatisfied
    (v : Nat)
    (candidate required : ConcreteShape)
    (result : Ty)
    (hcandidate : UniqueNames candidate)
    (hrequired : UniqueNames required)
    (hnot : ¬ Satisfies candidate required) :
    Invoke v (.var v) (.record candidate) result required = none := by
  have hbool : SatisfiesBool candidate required = false := by
    cases h : SatisfiesBool candidate required with
    | false => rfl
    | true =>
        exfalso
        exact hnot ((satisfiesBool_iff_satisfies candidate required hcandidate hrequired).mp h)
  simp [Invoke, Infer, Discharge, hbool]


end Oak.GenericConstraintRefinement
