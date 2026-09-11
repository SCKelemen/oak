/-!
# Oak.IoPort — the completion-ring IO port

`docs/spec/120-io.md` fixes one port two realizations satisfy: caller-owned
submission and completion rings, link chains, and a contract (§3) about
completion order, reads seeing writes, and durability under an honest
device. This module states the contract over a minimal model and proves
what both `iosim` and `ionative` are held to:

* `chain_cancels_rest`: when a linked request fails, every later request
  in its chain completes `canceled`, and every earlier one completed on
  its own result. A chain that never fails completes every request.
* `fsync_covers`: a completed fsync makes durable every write completed
  before its submission (the honest-device durability contract); nothing
  completed after the fsync was submitted is claimed.
* `read_sees_write`: a read of a range after a completed write to it
  observes the write, whatever else was written elsewhere.

The model is deliberately small: a request is its tag, whether it
succeeds, and its link flag; a chain is executed in order; a file is a
function from offset to byte.
-/

namespace Oak.IoPort

/-- One request of a chain: its tag, whether the device completes it
successfully, and whether the next request depends on it. -/
structure Req where
  tag : Nat
  ok : Bool
  link : Bool
  deriving DecidableEq, Repr

inductive Outcome where
  | done (tag : Nat)
  | failed (tag : Nat)
  | canceled (tag : Nat)
  deriving DecidableEq, Repr

/-- Execute a chain in order. `cancel` says whether an earlier linked
request failed; from then on every request completes canceled. -/
def runChain : Bool → List Req → List Outcome
  | _, [] => []
  | true, r :: rest => .canceled r.tag :: runChain true rest
  | false, r :: rest =>
      if r.ok then .done r.tag :: runChain false rest
      else .failed r.tag :: runChain (r.link) rest

/-- A chain with no failure completes every request `done`. -/
theorem chain_all_ok (c : List Req) (h : ∀ r ∈ c, r.ok = true) :
    runChain false c = c.map (fun r => Outcome.done r.tag) := by
  induction c with
  | nil => rfl
  | cons r rest ih =>
    have hr : r.ok = true := h r (List.mem_cons_self ..)
    simp [runChain, hr, ih (fun q hq => h q (List.mem_cons_of_mem _ hq))]

/-- Once cancellation is in force, the rest of the chain is canceled. -/
theorem chain_canceled_rest (c : List Req) :
    runChain true c = c.map (fun r => Outcome.canceled r.tag) := by
  induction c with
  | nil => rfl
  | cons r rest ih => simp [runChain, ih]

/-- A linked request that fails cancels exactly the remainder of its
chain: the prefix before it runs normally, it completes `failed`, and
every request after it completes `canceled`. -/
theorem chain_cancels_rest (prefix_ suffix : List Req) (r : Req)
    (hprefix : ∀ q ∈ prefix_, q.ok = true) (hfail : r.ok = false) (hlink : r.link = true) :
    runChain false (prefix_ ++ r :: suffix) =
      prefix_.map (fun q => Outcome.done q.tag) ++ Outcome.failed r.tag :: suffix.map (fun q => Outcome.canceled q.tag) := by
  induction prefix_ with
  | nil => simp [runChain, hfail, hlink, chain_canceled_rest]
  | cons q rest ih =>
    have hq : q.ok = true := hprefix q (List.mem_cons_self ..)
    simp [runChain, hq, ih (fun p hp => hprefix p (List.mem_cons_of_mem _ hp))]

/-- Durability: the writes completed before an fsync is submitted become
durable when the fsync completes. `completedBefore` is what the program
observed complete before it submitted the fsync; `durable` is the device's
durable set. -/
def fsyncComplete (completedBefore durable : List Nat) : List Nat :=
  completedBefore ++ durable

theorem fsync_covers (completedBefore durable : List Nat) (w : Nat)
    (hw : w ∈ completedBefore) : w ∈ fsyncComplete completedBefore durable := by
  simp [fsyncComplete, hw]

theorem fsync_keeps (completedBefore durable : List Nat) (w : Nat)
    (hw : w ∈ durable) : w ∈ fsyncComplete completedBefore durable := by
  simp [fsyncComplete, hw]

/-- Nothing becomes durable through an fsync unless it was completed before
the fsync's submission or was durable already. -/
theorem fsync_claims_nothing_else (completedBefore durable : List Nat) (w : Nat)
    (hw : w ∈ fsyncComplete completedBefore durable) : w ∈ completedBefore ∨ w ∈ durable := by
  simpa [fsyncComplete] using hw

/-- A file as a function from offset to byte; a write of `bytes` at `off`
replaces that range. -/
def File := Nat → Nat

def write (f : File) (off : Nat) (bytes : List Nat) : File :=
  fun i => if off ≤ i ∧ i < off + bytes.length then bytes.getD (i - off) (f i) else f i

def readAt (f : File) (off len : Nat) : List Nat :=
  (List.range len).map (fun k => f (off + k))

/-- Reads see writes: reading the written range after the write returns
the written bytes. -/
theorem read_sees_write (f : File) (off : Nat) (bytes : List Nat) :
    readAt (write f off bytes) off bytes.length = bytes := by
  unfold readAt write
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp at h1
    simp [h1, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1]

/-- Writes elsewhere leave a byte alone. -/
theorem write_elsewhere (f : File) (off : Nat) (bytes : List Nat) (i : Nat)
    (h : i < off ∨ off + bytes.length ≤ i) : write f off bytes i = f i := by
  unfold write
  rcases h with h | h
  · simp [Nat.not_le.mpr h]
  · have : ¬ (off ≤ i ∧ i < off + bytes.length) := fun hh => Nat.lt_irrefl _ (Nat.lt_of_lt_of_le hh.2 h)
    simp [this]

end Oak.IoPort
