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
  | binary : Nat → Ty → Ty → Ty
  deriving DecidableEq, Repr

/-- Substitute one quantified type variable through a semantic type. This
    mirrors `Substitution.Apply` for the constructors modeled here. -/
def Substitute (v : Nat) (replacement : Ty) : Ty → Ty
  | .var name => if name = v then replacement else .var name
  | .atom name => .atom name
  | .record fields => .record fields
  | .unary ctor arg => .unary ctor (Substitute v replacement arg)
  | .binary ctor left right =>
      .binary ctor (Substitute v replacement left) (Substitute v replacement right)

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


/-- Concrete inference bindings. The list representation mirrors an
    incrementally composed checker substitution: the most recent binding is
    searched first, while rebinding an existing variable must agree exactly. -/
abbrev Bindings := List (Nat × Ty)

def Lookup (v : Nat) : Bindings → Option Ty
  | [] => none
  | (name, value) :: rest =>
      if name = v then some value else Lookup v rest

def Bind (v : Nat) (actual : Ty) (bindings : Bindings) : Option Bindings :=
  match Lookup v bindings with
  | none => some ((v, actual) :: bindings)
  | some previous => if previous = actual then some bindings else none

/-- Infer all variables in one parameter/argument equation while threading every
    binding learned by earlier sibling positions. -/
def InferInto : Ty → Ty → Bindings → Option Bindings
  | .var v, actual, bindings => Bind v actual bindings
  | .atom expected, .atom actual, bindings =>
      if expected = actual then some bindings else none
  | .record expected, .record actual, bindings =>
      if expected = actual then some bindings else none
  | .unary expectedCtor expectedArg, .unary actualCtor actualArg, bindings =>
      if expectedCtor = actualCtor then
        InferInto expectedArg actualArg bindings
      else
        none
  | .binary expectedCtor expectedLeft expectedRight,
      .binary actualCtor actualLeft actualRight, bindings =>
      if expectedCtor = actualCtor then
        match InferInto expectedLeft actualLeft bindings with
        | none => none
        | some next => InferInto expectedRight actualRight next
      else
        none
  | _, _, _ => none

/-- Multiple call parameters are solved left-to-right under one accumulated
    substitution. -/
def InferParameters : List (Ty × Ty) → Bindings → Option Bindings
  | [], bindings => some bindings
  | (parameter, actual) :: rest, bindings =>
      match InferInto parameter actual bindings with
      | none => none
      | some next => InferParameters rest next

def SubstituteBindings (bindings : Bindings) : Ty → Ty
  | .var v =>
      match Lookup v bindings with
      | some replacement => replacement
      | none => .var v
  | .atom name => .atom name
  | .record fields => .record fields
  | .unary ctor arg => .unary ctor (SubstituteBindings bindings arg)
  | .binary ctor left right =>
      .binary ctor
        (SubstituteBindings bindings left)
        (SubstituteBindings bindings right)

/-- Distinct quantified variables can be inferred from distinct parameters in
    one call without losing the earlier binding. -/
theorem infer_distinct_parameters
    (v w : Nat) (left right : Ty) (hvw : v ≠ w) :
    InferParameters [(.var v, left), (.var w, right)] [] =
      some [(w, right), (v, left)] := by
  simp [InferParameters, InferInto, Bind, Lookup, hvw, Ne.symm hvw]

/-- Repeated occurrences accept one consistent semantic type. -/
theorem infer_repeated_accepts (v : Nat) (actual : Ty) :
    InferParameters [(.var v, actual), (.var v, actual)] [] =
      some [(v, actual)] := by
  simp [InferParameters, InferInto, Bind, Lookup]

/-- Repeated occurrences reject conflicting semantic types. -/
theorem infer_repeated_rejects
    (v : Nat) (left right : Ty) (hne : left ≠ right) :
    InferParameters [(.var v, left), (.var v, right)] [] = none := by
  simp [InferParameters, InferInto, Bind, Lookup, hne]

/-- Sibling arguments of a generic application share the accumulated
    substitution, so two variables are both recovered. -/
theorem infer_binary_application
    (ctor v w : Nat) (left right : Ty) (hvw : v ≠ w) :
    InferInto
        (.binary ctor (.var v) (.var w))
        (.binary ctor left right)
        [] =
      some [(w, right), (v, left)] := by
  simp [InferInto, Bind, Lookup, hvw, Ne.symm hvw]

/-- A repeated variable inside one generic application cannot acquire two
    incompatible meanings. -/
theorem infer_binary_repeated_rejects
    (ctor v : Nat) (left right : Ty) (hne : left ≠ right) :
    InferInto
        (.binary ctor (.var v) (.var v))
        (.binary ctor left right)
        [] = none := by
  simp [InferInto, Bind, Lookup, hne]

/-- Applying the solved substitution reconstructs the concrete generic result
    for both quantified variables. -/
theorem substitute_binary_bindings
    (ctor v w : Nat) (left right : Ty) (hvw : v ≠ w) :
    SubstituteBindings [(w, right), (v, left)]
        (.binary ctor (.var v) (.var w)) =
      .binary ctor left right := by
  simp [SubstituteBindings, Lookup, hvw, Ne.symm hvw]

end Oak.GenericConstraintRefinement
