/-!
# Oak.Typestate — state-indexed resource handles

`docs/spec/112-protocols.md` section 5a puts a resource protocol's state
into the handle's type: `Segment[Offloaded]` and `Segment[Published]` are
distinct types, a `via` callable takes `Segment[From]` and returns
`Segment[To]`, and a handle may be constructed only in the protocol's
initial state or inside the transition into its state. This module states
the discipline as a small typed calculus over an abstract protocol and
proves what the specification claims of it:

* `run_sound`: the dynamic state of a handle produced by a well-typed
  sequence of transitions is exactly its static index. The type never lies
  about the state.
* `run_legal`: every transition a well-typed sequence applies is legal at
  the state the handle is in. The legality trap of the projected
  `name_next` (`OAK-M0301`'s runtime counterpart) is unreachable from
  well-typed code.
* `construct_initial_or_transition`: the only ways to obtain a handle at
  state `s` are constructing it at the initial state, when `s` is initial,
  or applying a transition into `s`. No other derivation exists, which is
  the content of `OAK-B0121`.

The calculus is deliberately minimal: states are a type `S` with decidable
equality, a protocol is a decidable legality relation over `(from, step,
to)`, and a well-typed derivation is an inductive judgement indexed by the
handle's static state. Representation is not modeled: the phantom index
is erased (`Oak.PhantomRepresentation`).
-/

namespace Oak.Typestate

variable {S : Type} [DecidableEq S] {Step : Type}

/-- A protocol: an initial state and the legal transitions. -/
structure Protocol (S Step : Type) where
  initial : S
  legal : S → Step → S → Prop

/-- The machine state of a handle: which protocol state the resource is in. -/
structure Machine (S : Type) where
  state : S

/-- Well-typed handle derivations, indexed by the handle's static state
`s`. `construct` is admitted only at the initial state; `transition` moves
a handle of static state `a` to static state `b` when the protocol has a
legal `(a, step, b)`. These are the two rules the checker enforces: a
literal outside the initial state and outside the transition into its
state is `OAK-B0121`, and a `via` callable's signature must spell exactly
the line's `From` and `To`. -/
inductive Handle (P : Protocol S Step) : S → Type where
  | construct : Handle P P.initial
  | transition {a b : S} (h : Handle P a) (step : Step) (legal : P.legal a step b) : Handle P b

/-- The dynamic machine state a derivation produces: construction starts
at the initial state, a transition moves to its target. -/
def Handle.run {P : Protocol S Step} : {s : S} → Handle P s → Machine S
  | _, .construct => ⟨P.initial⟩
  | s, .transition _ _ _ => ⟨s⟩

/-- Soundness: the machine state equals the static index, for every
well-typed derivation. -/
theorem run_sound {P : Protocol S Step} : ∀ {s : S} (h : Handle P s), h.run.state = s := by
  intro s h
  cases h with
  | construct => rfl
  | transition h step legal => rfl

/-- Every transition in a well-typed derivation is legal at the state the
handle is actually in, so the legality check of the projected step
function never fails on well-typed code. -/
theorem run_legal {P : Protocol S Step} {a b : S} (h : Handle P a) (step : Step)
    (legal : P.legal a step b) :
    P.legal h.run.state step (Handle.transition h step legal).run.state := by
  rw [run_sound h, run_sound (Handle.transition h step legal)]
  exact legal

/-- Construction outside the initial state is impossible: a handle at a
non-initial state is a transition into that state. -/
theorem construct_initial_or_transition {P : Protocol S Step} {s : S} (h : Handle P s) :
    s = P.initial ∨ ∃ (a : S) (h' : Handle P a) (step : Step) (legal : P.legal a step s),
      h = Handle.transition h' step legal := by
  cases h with
  | construct => exact Or.inl rfl
  | transition h' step legal => exact Or.inr ⟨_, h', step, legal, rfl⟩

/-- A concrete custody protocol, as in the dbs segment lifecycle:
Fresh → Published → Offloaded → Evicted. -/
inductive Custody where
  | fresh | published | offloaded | evicted
  deriving DecidableEq, Repr

inductive CustodyStep where
  | publish | offload | evict
  deriving DecidableEq, Repr

def custody : Protocol Custody CustodyStep :=
  { initial := .fresh,
    legal := fun a step b =>
      (a = .fresh ∧ step = .publish ∧ b = .published) ∨
      (a = .published ∧ step = .offload ∧ b = .offloaded) ∨
      (a = .offloaded ∧ step = .evict ∧ b = .evicted) }

/-- The well-typed chain `evict(offload(publish(fresh)))`, one typed step
at a time: each binding's type is the handle's state. -/
def published : Handle custody .published :=
  .transition .construct .publish (by simp [custody])

def offloaded : Handle custody .offloaded :=
  .transition published .offload (by simp [custody])

def chain : Handle custody .evicted :=
  .transition offloaded .evict (by simp [custody])

example : chain.run.state = .evicted := run_sound chain

/-- `evict` on a `Published` handle has no derivation: the side condition
`custody.legal .published .evict b` is false for every `b`, so no
`Handle custody b` can be formed from a `Handle custody .published` by
`evict`. In Oak this is the type error
`expected Segment_Offloaded, got Segment_Published`. -/
theorem no_evict_from_published (b : Custody) : ¬ custody.legal .published .evict b := by
  intro h
  simp [custody] at h

end Oak.Typestate
