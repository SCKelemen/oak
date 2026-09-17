import Oak.Typestate

/-!
# Sealed typestate constructor provenance

This module gives compiler-generated static-protocol handles a stricter
derivation calculus than the explicit-resource compatibility rules in
`Oak.Typestate`. A sealed handle has one root rule: its resource and origin
identities must come from the policy's designated initial constructor. Every
later handle is an alias-preserving legal transition whose target construction
has been validated as nontrusted.

The root premise `mintedBy designated resource origin` is externally supplied.
This module only retains and extracts that premise; it does not establish that
the premise is true. Likewise, `validatedNontrusted` is an external validation
judgement, not a model of a compiler implementation.

Consequently these theorems prove no allocator uniqueness, distinct or
physical backing storage, ordinary-RAM ownership, unforgeability outside these
abstract introduction rules, Go/compiler refinement, memory ordering,
publication safety, or permission to use pair stores or `STP`.
-/

namespace Oak.SealedTypestate

open Oak.Typestate

variable {State Step Constructor Resource Origin : Type}

/-- The sealing policy for one generated static protocol. `mintedBy` records
an externally justified constructor/source fact. `validatedNontrusted` records
that a target literal was checked from the consumed source handle without a
trusted result claim. -/
structure Policy (State Step Constructor Resource Origin : Type) where
  protocol : Protocol State Step
  designated : Constructor
  mintedBy : Constructor → Resource → Origin → Prop
  validatedNontrusted : State → Step → State → Prop

/-- The runtime identity and state represented by a sealed derivation. -/
structure Runtime (State Resource Origin : Type) where
  resource : Resource
  origin : Origin
  state : State
  deriving Repr

/-- Sealed handle derivations. `root` is the only initial-literal rule and
requires the designated constructor's external mint premise. `transition` is
the only target-literal rule: it preserves the resource and origin indices and
requires both protocol legality and nontrusted validation. There are no rules
for uninitialized roots, alternate fresh constructors, or trusted transitions. -/
inductive Handle (Q : Policy State Step Constructor Resource Origin) :
    Resource → Origin → State → Type where
  | root (resource : Resource) (origin : Origin)
      (minted : Q.mintedBy Q.designated resource origin) :
      Handle Q resource origin Q.protocol.initial
  | transition {resource : Resource} {origin : Origin} {source target : State}
      (handle : Handle Q resource origin source) (step : Step)
      (legal : Q.protocol.legal source step target)
      (validated : Q.validatedNontrusted source step target) :
      Handle Q resource origin target

/-- Project the runtime identity/state certified by the derivation's indices. -/
def Handle.run {Q : Policy State Step Constructor Resource Origin}
    {resource : Resource} {origin : Origin} {state : State} :
    Handle Q resource origin state → Runtime State Resource Origin :=
  fun _ => ⟨resource, origin, state⟩

/-- The dynamic resource, origin, and state are exactly the derivation's
static indices. -/
theorem run_correct {Q : Policy State Step Constructor Resource Origin} :
    ∀ {resource : Resource} {origin : Origin} {state : State}
      (handle : Handle Q resource origin state),
      handle.run = ⟨resource, origin, state⟩ := by
  intros
  rfl

/-- In particular, the runtime state never disagrees with the static state. -/
theorem run_state {Q : Policy State Step Constructor Resource Origin}
    {resource : Resource} {origin : Origin} {state : State}
    (handle : Handle Q resource origin state) : handle.run.state = state := by
  rw [run_correct handle]

/-- Every sealed derivation traces back to the externally supplied premise for
the designated constructor and the same resource/origin identities. -/
theorem traces_to_designated
    {Q : Policy State Step Constructor Resource Origin} :
    ∀ {resource : Resource} {origin : Origin} {state : State}
      (_handle : Handle Q resource origin state),
      Q.mintedBy Q.designated resource origin := by
  intro resource origin state handle
  induction handle with
  | root minted => exact minted
  | transition handle step legal validated ih => exact ih

/-- Without the external designated-mint premise, no sealed handle at any
state can be derived. This is not a proof that a real allocator supplied such
a premise; it is only inversion of the abstract rules. -/
theorem no_handle_without_designated_mint
    {Q : Policy State Step Constructor Resource Origin}
    {resource : Resource} {origin : Origin} {state : State}
    (absent : ¬ Q.mintedBy Q.designated resource origin) :
    ¬ Nonempty (Handle Q resource origin state) := by
  intro existsHandle
  rcases existsHandle with ⟨handle⟩
  exact absent (traces_to_designated handle)

/-- A derivation is at the initial state or its last step is a protocol-legal,
nontrusted-validated transition from a handle with the same identities. -/
theorem initial_or_validated_transition
    {Q : Policy State Step Constructor Resource Origin}
    {resource : Resource} {origin : Origin} {state : State}
    (handle : Handle Q resource origin state) :
    state = Q.protocol.initial ∨
      ∃ (source : State) (prior : Handle Q resource origin source) (step : Step)
        (legal : Q.protocol.legal source step state)
        (validated : Q.validatedNontrusted source step state),
        handle = Handle.transition prior step legal validated := by
  cases handle with
  | root => exact Or.inl rfl
  | transition prior step legal validated =>
      exact Or.inr ⟨_, prior, step, legal, validated, rfl⟩

/-- An admitted transition preserves both runtime identities and reaches its
declared target state. -/
theorem transition_preserves_identity
    {Q : Policy State Step Constructor Resource Origin}
    {resource : Resource} {origin : Origin} {source target : State}
    (handle : Handle Q resource origin source) (step : Step)
    (legal : Q.protocol.legal source step target)
    (validated : Q.validatedNontrusted source step target) :
    let next := Handle.transition handle step legal validated
    next.run.resource = handle.run.resource ∧
      next.run.origin = handle.run.origin ∧
      next.run.state = target := by
  simp [Handle.run]

end Oak.SealedTypestate
