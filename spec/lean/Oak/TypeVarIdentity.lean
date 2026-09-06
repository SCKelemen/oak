namespace Oak.TypeVarIdentity

/-- A source name is only a display label. `binder` is the semantic identity of
    one quantified/inference variable. Two variables may print the same name and
    still be distinct binders. -/
structure TypeVar where
  binder : Nat
  name : Nat
  deriving DecidableEq, Repr

inductive Ty where
  | variable : TypeVar → Ty
  | atom : Nat → Ty
  | arrow : Ty → Ty → Ty
  deriving DecidableEq, Repr

/-- A substitution is keyed by binder identity, not by the display name. -/
abbrev Substitution := TypeVar → Option Ty

def empty : Substitution := fun _ => none

def singleton (variable : TypeVar) (replacement : Ty) : Substitution :=
  fun candidate => if candidate = variable then some replacement else none

def apply (sub : Substitution) : Ty → Ty
  | .variable variable =>
      match sub variable with
      | some replacement => replacement
      | none => .variable variable
  | .atom value => .atom value
  | .arrow parameter result => .arrow (apply sub parameter) (apply sub result)

/-- A singleton substitution replaces exactly its own binder. -/
theorem singleton_hits (variable : TypeVar) (replacement : Ty) :
    apply (singleton variable replacement) (.variable variable) = replacement := by
  simp [apply, singleton]

/-- A substitution for one binder cannot affect a distinct binder, even when the
    two variables have the same source-facing name. -/
theorem singleton_misses_distinct_binder (left right : TypeVar) (replacement : Ty)
    (hne : left ≠ right) :
    apply (singleton left replacement) (.variable right) = .variable right := by
  simp [apply, singleton, hne]

/-- Equal display names do not collapse distinct binder identities. -/
theorem same_name_can_be_distinct (left right : TypeVar)
    (sameName : left.name = right.name)
    (differentBinder : left.binder ≠ right.binder) : left ≠ right := by
  intro heq
  apply differentBinder
  exact congrArg TypeVar.binder heq

/-- Combining the previous laws: same-name variables with different binders do
    not cross-substitute. -/
theorem same_name_does_not_alias (left right : TypeVar) (replacement : Ty)
    (sameName : left.name = right.name)
    (differentBinder : left.binder ≠ right.binder) :
    apply (singleton left replacement) (.variable right) = .variable right := by
  apply singleton_misses_distinct_binder
  exact same_name_can_be_distinct left right sameName differentBinder

/-- Repeated occurrences of one binder are substituted consistently. -/
theorem repeated_binder_substitutes_consistently (variable : TypeVar)
    (replacement : Ty) :
    apply (singleton variable replacement)
        (.arrow (.variable variable) (.variable variable)) =
      .arrow replacement replacement := by
  simp [apply, singleton]

end Oak.TypeVarIdentity
