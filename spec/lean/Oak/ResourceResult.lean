import Oak.ResourceFlow
import Oak.ResourceCall

/-!
# Result identities, callable contracts, and the trusted boundary

`docs/spec/50-borrowing.md` §9 lets a resource-returning callable declare what
its result *is* — fresh authority, an alias of one argument, a shared borrow of
some arguments, or a mutable reborrow of them — and holds both sides to the
claim: the body is validated against it (`OAK-B0117`) and the caller reasons
from it. `docs/spec/112-protocols.md` §5 gives the claim a source spelling on
`via` lines and a trusted form, `via unsafe`, under which the body validation is
dropped and the claim is recorded as an assumption.

This file states the laws the checker's body admission and the caller's
classification rely on. It models the *rule* the implementation applies
(`typechecker/resource_flow.go`, `checkResultContract`), not the syntax.
-/

namespace Oak.ResourceResult

open Oak.ResourceFlow (Name ClassId State Usable Aliases consume)
open Oak.ResourceCall (ParameterMode)

/-- Zero-based explicit argument positions of a callable. -/
abbrev Arg := Nat

/-- The result identity a contract declares. -/
inductive Identity where
  | fresh
  | alias (arg : Arg)
  | borrow (origins : List Arg)
  | borrowMut (origins : List Arg)
  deriving DecidableEq, Repr

/-- What the checker knows about the value a body returns on one path: a
parameter's authority (directly or through a local alias), a borrowed result
dependent on some owners with shared or mutable permission, a value that no
other tracked resource reaches (a fresh result, an independent local, a record
literal mentioning no other resource), or a resource of unknown provenance. -/
inductive Provenance where
  | param (arg : Arg)
  | dependent (owners : List Arg) (mutable : Bool)
  | independent
  | unknown
  deriving DecidableEq, Repr

/-- The body admission rule of `OAK-B0117`: does a body returning `p` honor the
declared identity? Fresh may not be a parameter or a dependent; alias must be
exactly the declared parameter; a borrow may return any declared origin, a
dependent whose owners the declaration covers, or an independent value, never
unknown provenance or authority outside the declared origins; a mutable
reborrow additionally rejects a shared dependent (widening). -/
def Admits : Identity -> Provenance -> Prop
  | .fresh, .param _ => False
  | .fresh, .dependent _ _ => False
  | .fresh, .independent => True
  | .fresh, .unknown => True
  | .alias a, .param b => a = b
  | .alias _, _ => False
  | .borrow os, .param a => a ∈ os
  | .borrow os, .dependent owners _ => owners ⊆ os
  | .borrow _, .independent => True
  | .borrow _, .unknown => False
  | .borrowMut os, .param a => a ∈ os
  | .borrowMut os, .dependent owners mutable => owners ⊆ os ∧ mutable = true
  | .borrowMut _, .independent => True
  | .borrowMut _, .unknown => False

/-- Freshness cannot be manufactured by returning a parameter. -/
theorem fresh_rejects_param (a : Arg) : ¬ Admits .fresh (.param a) := by
  simp [Admits]

/-- Nor by returning a borrowed result of any owners. -/
theorem fresh_rejects_dependent (owners : List Arg) (mutable : Bool) :
    ¬ Admits .fresh (.dependent owners mutable) := by
  simp [Admits]

/-- An alias claim is exact: the body returns the declared parameter's
authority and nothing else. -/
theorem alias_exact (a : Arg) (p : Provenance) :
    Admits (.alias a) p ↔ p = .param a := by
  cases p with
  | param b => simp [Admits]; constructor <;> intro h <;> simp_all
  | dependent _ _ => simp [Admits]
  | independent => simp [Admits]
  | unknown => simp [Admits]

/-- A borrow never accepts unknown provenance: the caller would leave the real
owner unprotected. -/
theorem borrow_rejects_unknown (os : List Arg) : ¬ Admits (.borrow os) .unknown := by
  simp [Admits]

theorem borrowMut_rejects_unknown (os : List Arg) : ¬ Admits (.borrowMut os) .unknown := by
  simp [Admits]

/-- Declaring more origins than the body needs is admitted: a borrow only
restricts the caller, so widening the origin set admits every body the smaller
set admitted. This is why "declare more than you need" is safe and "declare
fewer" is the lie `OAK-B0117` catches. -/
theorem borrow_monotone {os os' : List Arg} (hsub : os ⊆ os') (p : Provenance)
    (h : Admits (.borrow os) p) : Admits (.borrow os') p := by
  cases p with
  | param a => exact hsub (by simpa [Admits] using h)
  | dependent owners _ =>
      simp [Admits] at h ⊢
      exact List.Subset.trans h hsub
  | independent => simp [Admits]
  | unknown => simp [Admits] at h

theorem borrowMut_monotone {os os' : List Arg} (hsub : os ⊆ os') (p : Provenance)
    (h : Admits (.borrowMut os) p) : Admits (.borrowMut os') p := by
  cases p with
  | param a => exact hsub (by simpa [Admits] using h)
  | dependent owners mutable =>
      simp [Admits] at h ⊢
      exact ⟨List.Subset.trans h.1 hsub, h.2⟩
  | independent => simp [Admits]
  | unknown => simp [Admits] at h

/-- A body admitted under an alias claim is admitted under any borrow claim
that lists the aliased parameter: the borrow is the more conservative claim. -/
theorem alias_body_is_borrow_body {a : Arg} {os : List Arg} (hmem : a ∈ os)
    (p : Provenance) (h : Admits (.alias a) p) : Admits (.borrow os) p := by
  rw [alias_exact] at h
  subst h
  simpa [Admits] using hmem

/-- A body admitted under a fresh claim with tracked provenance (not unknown)
is admitted under any borrow claim: the primitive that builds a cursor over an
arena has nothing else to return, and declaring the borrow costs it nothing. -/
theorem fresh_tracked_body_is_borrow_body (os : List Arg) (p : Provenance)
    (hknown : p ≠ .unknown) (h : Admits .fresh p) : Admits (.borrow os) p := by
  cases p with
  | param _ => simp [Admits] at h
  | dependent _ _ => simp [Admits] at h
  | independent => simp [Admits]
  | unknown => exact absurd rfl hknown

/-- Narrowing is admitted: every body a mutable-reborrow claim admits, the
shared-borrow claim over the same origins admits too. -/
theorem borrowMut_narrows_to_borrow (os : List Arg) (p : Provenance)
    (h : Admits (.borrowMut os) p) : Admits (.borrow os) p := by
  cases p with
  | param a => simpa [Admits] using h
  | dependent owners mutable =>
      simp [Admits] at h ⊢
      exact h.1
  | independent => simp [Admits]
  | unknown => simp [Admits] at h

/-- Widening is rejected: a shared dependent can never satisfy a mutable
reborrow claim, whatever its owners. -/
theorem widening_rejected (os owners : List Arg) :
    ¬ Admits (.borrowMut os) (.dependent owners false) := by
  simp [Admits]

/-- Admission is decidable, which is what lets the checker implement it as a
function rather than search. -/
instance (c : Identity) (p : Provenance) : Decidable (Admits c p) := by
  cases c <;> cases p <;> simp only [Admits] <;> infer_instance

/-! ## The trusted boundary

`via unsafe` records the declared identity as an assumption: the callable is
admitted whether or not its body satisfies the claim, and everything else about
the call — entry authority, retention, exclusivity, the caller's reasoning — is
unchanged. `Accepted` is the whole body-side judgment; `Admits` is exactly the
part the boundary removes. -/

/-- The body-side judgment of one callable: validated against its claim, or
trusted. -/
def Accepted (trusted : Bool) (c : Identity) (p : Provenance) : Prop :=
  trusted = true ∨ Admits c p

/-- Without the marker, acceptance is validation. -/
theorem untrusted_is_validation (c : Identity) (p : Provenance) :
    Accepted false c p ↔ Admits c p := by
  simp [Accepted]

/-- With the marker, acceptance holds unconditionally: the claim is an
assumption. This theorem is the precise content of the trust boundary. -/
theorem trusted_accepts_any_body (c : Identity) (p : Provenance) :
    Accepted true c p := by
  simp [Accepted]

/-- The marker never rejects a body that validation admits. -/
theorem trusted_extends_validation (trusted : Bool) (c : Identity) (p : Provenance)
    (h : Admits c p) : Accepted trusted c p :=
  Or.inr h

/-! ## The caller's view

The caller classifies a result binding by the declared identity alone. A fresh
result and a borrowed result each start a class of their own (a borrow's
dependency on its owners is tracked beside the class, in the dependent set of
`50-borrowing.md` §9, and is not modeled here); an alias joins the argument's
class. -/

/-- Place the result name `r` of a call into the caller's state, given the
argument names by position and an unused class for fresh authority. -/
def bindResult (s : State) (r : Name) (args : Arg -> Name) (freshClass : ClassId) :
    Identity -> State
  | .alias a => { s with classOf := fun n => if n = r then s.classOf (args a) else s.classOf n }
  | _ => { s with classOf := fun n => if n = r then freshClass else s.classOf n }

/-- An alias result is the argument under a second name. -/
theorem alias_result_aliases_argument (s : State) (r : Name) (args : Arg -> Name)
    (freshClass : ClassId) (a : Arg) (hdistinct : args a ≠ r) :
    Aliases (bindResult s r args freshClass (.alias a)) r (args a) := by
  simp [Aliases, bindResult, hdistinct]

/-- Consuming the aliased argument after the call leaves the result unusable:
the caller does not hold two authorities, it holds one twice. -/
theorem alias_consumed_with_argument (s : State) (r : Name) (args : Arg -> Name)
    (freshClass : ClassId) (a : Arg) (hdistinct : args a ≠ r) :
    ¬ Usable (consume (bindResult s r args freshClass (.alias a)) (args a)) r :=
  Oak.ResourceFlow.consume_invalidates_alias
    (alias_result_aliases_argument s r args freshClass a hdistinct).symm

/-- Consuming the alias result consumes the argument as well. -/
theorem argument_consumed_with_alias (s : State) (r : Name) (args : Arg -> Name)
    (freshClass : ClassId) (a : Arg) (hdistinct : args a ≠ r) :
    ¬ Usable (consume (bindResult s r args freshClass (.alias a)) r) (args a) :=
  Oak.ResourceFlow.consume_invalidates_alias
    (alias_result_aliases_argument s r args freshClass a hdistinct)

/-- A fresh result shares its class with no prior name, so consuming it leaves
every other name exactly as usable as before. `freshClass` must be a class no
existing name occupies — the checker mints one. -/
theorem fresh_result_independent (s : State) (r : Name) (args : Arg -> Name)
    (freshClass : ClassId) (hunused : ∀ n, s.classOf n ≠ freshClass)
    (other : Name) (hother : other ≠ r) :
    Usable (consume (bindResult s r args freshClass .fresh) r) other ↔
      Usable (bindResult s r args freshClass .fresh) other := by
  apply Oak.ResourceFlow.consume_preserves_unrelated
  simp [Aliases, bindResult, hother]
  exact fun h => hunused other h.symm

/-- The caller's classification depends on the declared identity only: the
trusted marker is invisible to it. Stated as a definitional fact so the model
cannot quietly acquire a caller-side dependence on trust. -/
theorem caller_view_ignores_trust (s : State) (r : Name) (args : Arg -> Name)
    (freshClass : ClassId) (c : Identity) (trusted trusted' : Bool) :
    (trusted, bindResult s r args freshClass c).2 =
      (trusted', bindResult s r args freshClass c).2 := by
  rfl

/-! ## Callable contracts: exact agreement

A function-typed parameter may require a callable contract of the values passed
for it (`OAK-B0116`). Agreement is exact after normalization: the same mode (or
absence of one) at every position and the same fresh-return fact. -/

/-- The normalized contract of a function value: one optional mode per
positional parameter and whether it returns fresh authority. -/
structure Contract where
  modes : List (Option ParameterMode)
  returnsFresh : Bool
  deriving DecidableEq, Repr

/-- The permanent effect of calling a value with contract `c` on the argument
names `args`, once call-local checks have passed: each consumed position
consumes its argument; borrowed and unmarked positions change nothing. -/
def commitContract (c : Contract) (args : Nat -> Name) (s : State) : State :=
  go c.modes 0 s
where
  go : List (Option ParameterMode) -> Nat -> State -> State
    | [], _, s => s
    | none :: rest, i, s => go rest (i + 1) s
    | some mode :: rest, i, s => go rest (i + 1) (Oak.ResourceCall.commit true mode s (args i))

/-- Exact agreement makes the caller's reasoning independent of which value
was passed: two agreeing contracts commit the same state. This is the
substitutability law the rule buys, and the reason variance is not admitted
until its own laws are proved. -/
theorem agreeing_contracts_commit_alike (c d : Contract) (h : c = d)
    (args : Nat -> Name) (s : State) :
    commitContract c args s = commitContract d args s := by
  subst h
  rfl

/-- A consuming value does not agree with a borrowed requirement. -/
theorem consuming_disagrees_with_borrowed (rest : List (Option ParameterMode)) (f : Bool) :
    Contract.mk (some .consumed :: rest) f ≠ Contract.mk (some .borrowed :: rest) f := by
  intro h
  cases h

/-- An uncontracted position does not agree with any mode. -/
theorem uncontracted_disagrees_with_mode (m : ParameterMode)
    (rest : List (Option ParameterMode)) (f : Bool) :
    Contract.mk (none :: rest) f ≠ Contract.mk (some m :: rest) f := by
  intro h
  cases h

/-- Exact agreement is not vacuous: substituting a consuming value for a
borrowed requirement would change the caller's state, consuming the argument
the requirement promised to leave live. -/
theorem consuming_substitution_changes_state (args : Nat -> Name) (s : State)
    (hlive : Usable s (args 0)) :
    commitContract (Contract.mk [some .consumed] false) args s ≠
      commitContract (Contract.mk [some .borrowed] false) args s := by
  intro h
  have hconsumed : ¬ Usable (commitContract (Contract.mk [some .consumed] false) args s) (args 0) := by
    simp only [commitContract, commitContract.go, Oak.ResourceCall.commit]
    exact Oak.ResourceFlow.consume_invalidates_self s (args 0)
  rw [h] at hconsumed
  simp only [commitContract, commitContract.go, Oak.ResourceCall.commit] at hconsumed
  exact hconsumed hlive

end Oak.ResourceResult
