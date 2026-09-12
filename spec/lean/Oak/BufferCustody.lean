import Oak.Typestate

/-!
# Oak.BufferCustody — custody states on foreign buffers

Model of docs/spec/92-ffi.md section 2.8.5 over the typestate calculus of
`Oak.Typestate`. A `Buffer[T, S]` is a handle whose static index is its
custody state: `host` at `c.own`, moved by transition externs
(`submit : host → device`, `complete : device → host`). The rules the
checker enforces are the calculus's: a handle is constructed only at the
initial state (`c.own` yields `Host`), a transition's signature spells its
line (`Buffer[f32, Host] → Buffer[f32, Device]`), and the borrow and
hand-back operations are admitted only at `host`.

* `run_sound` (inherited): the machine state of every well-typed chain is
  its static index, so a `Buffer[f32, Device]` binding really is in device
  custody.
* `no_borrow_in_device`: borrowing is legal only in `host`; there is no
  derivation of a borrow from a device handle.
* `round_trip`: `complete (submit own)` is a `host` handle again — the
  pilot's submit/complete cycle types.
* `no_complete_from_host`, `no_submit_from_device`: the two wrong-way
  transitions have no derivation, which in Oak is the type error
  `expected Buffer[f32, Device], got Buffer[f32, Host]`.
-/

namespace Oak.BufferCustody

open Oak.Typestate

inductive State where
  | host | device
  deriving DecidableEq, Repr

inductive Step where
  | submit | complete
  deriving DecidableEq, Repr

/-- The custody protocol: Host ⇄ Device. -/
def custody : Protocol State Step :=
  { initial := .host,
    legal := fun a step b =>
      (a = .host ∧ step = .submit ∧ b = .device) ∨
      (a = .device ∧ step = .complete ∧ b = .host) }

/-- `c.own` constructs at the initial state. -/
def own : Handle custody .host := .construct

def submitted : Handle custody .device :=
  .transition own .submit (by simp [custody])

/-- The round trip types: the buffer is back in host custody. -/
def round_trip : Handle custody .host :=
  .transition submitted .complete (by simp [custody])

example : round_trip.run.state = .host := run_sound round_trip
example : submitted.run.state = .device := run_sound submitted

/-- The operations admitted at a state: `view`, `span`, and `c.disown` need
host custody; a transition is admitted where its line starts. -/
def CanBorrow : State → Prop
  | .host => True
  | .device => False

/-- **No borrow in device custody.** A handle at `device` admits no borrow. -/
theorem no_borrow_in_device (_h : Handle custody .device) : ¬ CanBorrow .device := by
  intro contra
  exact contra

/-- Every borrow happens at a handle whose machine state is host. -/
theorem borrow_state_is_host {s : State} (h : Handle custody s) (hb : CanBorrow s) :
    h.run.state = .host := by
  rw [run_sound h]
  cases s with
  | host => rfl
  | device => exact absurd hb (by simp [CanBorrow])

/-! ## A record over a handle carries its custody

`Submitted { data: Buffer[f32, Device], device: u32 }` (docs/spec/92-ffi.md
section 2.8.6) is a handle at `device` with a device identity beside it:
the record's field is the handle, so borrowing through the record needs
host custody as borrowing the handle does, and completing through the
record moves the handle out — the record has no handle left to give,
which is why the record binding is dead after `complete(s.data)`. -/

/-- A record holding a handle at custody state `s` and a device identity. -/
structure Tagged (s : State) where
  data : Handle custody s
  device : Nat

/-- Borrowing through the record happens at host custody. -/
theorem tagged_borrow_state_is_host {s : State} (t : Tagged s) (hb : CanBorrow s) :
    t.data.run.state = .host :=
  borrow_state_is_host t.data hb

/-- Completing through the record: the field's handle moves to host. -/
def complete_tagged (t : Tagged .device) : Handle custody .host :=
  .transition t.data .complete (by simp [custody])

example (t : Tagged .device) : (complete_tagged t).run.state = .host := run_sound (complete_tagged t)

theorem no_complete_from_host (b : State) : ¬ custody.legal .host .complete b := by
  intro h
  simp [custody] at h

theorem no_submit_from_device (b : State) : ¬ custody.legal .device .submit b := by
  intro h
  simp [custody] at h

/-- A device handle is a transition into device: it came from a submit of a
host handle, never from construction. -/
theorem device_from_submit (h : Handle custody .device) :
    ∃ (h' : Handle custody .host), h = Handle.transition h' .submit (Or.inl ⟨rfl, rfl, rfl⟩) := by
  cases h with
  | transition h' step legal =>
    rename_i a
    cases a with
    | host =>
      cases step with
      | submit => exact ⟨h', rfl⟩
      | complete => exact absurd legal (no_complete_from_host _)
    | device =>
      cases step with
      | submit => exact absurd legal (no_submit_from_device _)
      | complete => simp [custody] at legal

end Oak.BufferCustody
