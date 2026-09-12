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
* The directory (§2, ops 8–13): exclusive `create` fails exactly when the
  name exists and otherwise adds it (`create_excl`); `rename` moves a name
  (`rename_moves`); `unlink` removes it; a directory change is durable
  exactly after `fsyncdir` (`syncdir_makes_durable`) and a crash forgets
  the changes no `fsyncdir` covered (`crash_forgets_unsynced`); `readdir`
  lists exactly the existing names (`readdir_lists_iff`); `truncate` bounds
  what a read can see (`read_bounded_by_size`).

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

/-! ## The directory (docs/spec/120-io.md §2, ops 8–13)

A directory is the list of names that exist; the port keeps two — the one
the process sees and the durable one a crash reverts to — and `fsyncdir`
is the only operation that copies the first to the second. `create`,
`rename` and `unlink` act on the visible list. Names are `Nat`s here; the
realizations spell them as NUL-terminated bytes. -/

/-- Exclusive create: `Exists` when the name is present, else the name is
added. -/
def create (d : List Nat) (n : Nat) : Option (List Nat) :=
  if n ∈ d then none else some (n :: d)

theorem create_excl (d : List Nat) (n : Nat) :
    create d n = none ↔ n ∈ d := by
  unfold create
  by_cases h : n ∈ d <;> simp [h]

theorem create_adds (d : List Nat) (n : Nat) (h : n ∉ d) :
    create d n = some (n :: d) := by
  simp [create, h]

/-- `unlink` removes every occurrence of the name. -/
def unlink (d : List Nat) (n : Nat) : List Nat := d.filter (fun m => m ≠ n)

theorem unlink_removes (d : List Nat) (n : Nat) : n ∉ unlink d n := by
  simp [unlink]

theorem unlink_keeps (d : List Nat) (n m : Nat) (hm : m ∈ d) (hne : m ≠ n) :
    m ∈ unlink d n := by
  simp [unlink, hm, hne]

/-- `rename a b`: `a` must exist; afterwards `b` exists and `a` does not
(unless they are the same name), and an old `b` is replaced. -/
def rename (d : List Nat) (a b : Nat) : Option (List Nat) :=
  if a ∈ d then some (b :: unlink (unlink d a) b) else none

theorem rename_not_found (d : List Nat) (a b : Nat) (h : a ∉ d) : rename d a b = none := by
  simp [rename, h]

theorem rename_moves (d d' : List Nat) (a b : Nat) (hab : a ≠ b)
    (h : rename d a b = some d') : b ∈ d' ∧ a ∉ d' := by
  unfold rename at h
  by_cases ha : a ∈ d
  · simp [ha] at h
    subst h
    refine ⟨List.mem_cons_self .., ?_⟩
    intro hmem
    rcases List.mem_cons.mp hmem with heq | hin
    · exact hab heq
    · exact absurd (List.mem_filter.mp hin).1 (unlink_removes d a)
  · simp [ha] at h

theorem rename_keeps_others (d d' : List Nat) (a b m : Nat)
    (hm : m ∈ d) (hma : m ≠ a) (hmb : m ≠ b) (h : rename d a b = some d') : m ∈ d' := by
  unfold rename at h
  by_cases ha : a ∈ d
  · simp [ha] at h
    subst h
    exact List.mem_cons_of_mem _ (unlink_keeps _ _ _ (unlink_keeps _ _ _ hm hma) hmb)
  · simp [ha] at h

/-- The two directories: visible and durable. -/
structure Dir where
  visible : List Nat
  durable : List Nat

def syncdir (s : Dir) : Dir := { s with durable := s.visible }
def crash (s : Dir) : Dir := { s with visible := s.durable }

/-- **fsyncdir makes the directory durable**: after it, a crash changes
nothing the process can see. -/
theorem syncdir_makes_durable (s : Dir) : (crash (syncdir s)).visible = s.visible := by
  simp [crash, syncdir]

/-- **A crash forgets unsynced changes**: what the process sees after a
crash is exactly what the last fsyncdir made durable — a name created,
renamed or unlinked since is forgotten. -/
theorem crash_forgets_unsynced (s : Dir) : (crash s).visible = s.durable := rfl

theorem crash_forgets_create (s : Dir) (n : Nat) (hn : n ∉ s.durable) (d' : List Nat)
    (h : create s.visible n = some d') :
    n ∉ (crash { s with visible := d' }).visible := by
  simpa [crash] using hn

/-- `readdir` lists the visible names. -/
def readdir (s : Dir) : List Nat := s.visible

theorem readdir_lists_iff (s : Dir) (n : Nat) : n ∈ readdir s ↔ n ∈ s.visible := Iff.rfl

/-- **Truncate bounds reads**: bytes at or past the file's size read as
absent, so a read of `len` bytes at `off` returns at most `size - off`. -/
def readBounded (f : File) (size off len : Nat) : List Nat :=
  readAt f off (min len (size - off))

theorem read_bounded_by_size (f : File) (size off len : Nat) :
    (readBounded f size off len).length ≤ size - off := by
  simp [readBounded, readAt]
  omega

theorem read_bounded_full (f : File) (size off len : Nat) (h : off + len ≤ size) :
    (readBounded f size off len).length = len := by
  simp [readBounded, readAt]
  omega

/-! ## Direct I/O: the sector rule

`open_direct` (op 14, docs/spec/120-io.md §2, §5) bypasses the host's
cache; every later read and write of that file must be whole sectors.
`io_direct_admits` in both realizations decides exactly this predicate
before any system call. -/

/-- A direct request is admitted when the region serves a sector and the
    offset, the length, and the window's base are each a multiple of it. -/
def directAdmits (sector off len base : Nat) : Bool :=
  sector != 0 && off % sector == 0 && len % sector == 0 && base % sector == 0

theorem directAdmits_iff (sector off len base : Nat) :
    directAdmits sector off len base = true ↔
      sector ≠ 0 ∧ off % sector = 0 ∧ len % sector = 0 ∧ base % sector = 0 := by
  simp [directAdmits, and_assoc]

/-- An admitted request ends on a sector boundary too: whole sectors in,
    whole sectors out — nothing the device must read-modify-write. -/
theorem directAdmits_end (sector off len base : Nat)
    (h : directAdmits sector off len base = true) : (off + len) % sector = 0 := by
  have h' := (directAdmits_iff sector off len base).mp h
  obtain ⟨_, hoff, hlen, _⟩ := h'
  rw [Nat.add_mod, hoff, hlen]
  simp

/-- A request that is not a sector multiple in any one of the three places
    is refused: the rule is exactly the conjunction, nothing weaker. -/
theorem directAdmits_refuses_misaligned_offset (sector off len base : Nat)
    (h : off % sector ≠ 0) : directAdmits sector off len base = false := by
  cases hd : directAdmits sector off len base with
  | false => rfl
  | true =>
      exact absurd ((directAdmits_iff sector off len base).mp hd).2.1 h

end Oak.IoPort
