/-!
# Oak.ProtocolQuorum — quorum predicates over protocol data

`docs/spec/112-protocols.md` section 1 admits `count(data.f)`,
`all(data.f)`, `any(data.f)` and `none(data.f)` over a fixed `[N]Bool`
data field (and their two-argument forms over an array of records). The
projection folds the array in a bounded loop; the TLA+ export writes
`Cardinality({k \in 0..N-1 : f[k]})` and the bounded quantifiers. This
module fixes the meaning both gates share, over a Bool vector, and proves
the laws a replication protocol leans on:

* `count_le`: a count never exceeds the array's length.
* `all_iff`, `any_iff`, `none_iff`: the quantifier forms are exactly the
  count comparisons the spec pairs them with (`count = N`, `count > 0`,
  `count = 0`), so a guard may use either spelling.
* `count_set_true_mono`: acknowledging one slot never lowers the count, so
  a quorum once reached stays reached until a slot is cleared — the
  monotonicity a `commit when count(data.acks) >= Q` guard relies on
  (`quorum_stable`).
* `count_set_false_le`: clearing a slot lowers the count by at most one.
-/

namespace Oak.ProtocolQuorum

/-- The fold the projection performs: the number of true slots. -/
def count : List Bool → Nat
  | [] => 0
  | true :: rest => count rest + 1
  | false :: rest => count rest

/-- The folds the projection performs for all/any/none. -/
def all : List Bool → Bool
  | [] => true
  | b :: rest => b && all rest

def any : List Bool → Bool
  | [] => false
  | b :: rest => b || any rest

def none : List Bool → Bool
  | [] => true
  | b :: rest => !b && none rest

theorem count_le (v : List Bool) : count v ≤ v.length := by
  induction v with
  | nil => simp [count]
  | cons b rest ih =>
    cases b <;> simp [count] <;> omega

theorem all_iff (v : List Bool) : all v = true ↔ count v = v.length := by
  induction v with
  | nil => simp [all, count]
  | cons b rest ih =>
    have hle := count_le rest
    cases b
    · simp [all, count]
      try omega
    · simp [all, count]
      try rw [ih]
      try omega

theorem any_iff (v : List Bool) : any v = true ↔ 0 < count v := by
  induction v with
  | nil => simp [any, count]
  | cons b rest ih =>
    cases b
    · simp [any, count]
      exact ih
    · simp [any, count]

theorem none_iff (v : List Bool) : none v = true ↔ count v = 0 := by
  induction v with
  | nil => simp [none, count]
  | cons b rest ih =>
    cases b
    · simp [none, count]
      exact ih
    · simp [none, count]

/-- Acknowledging slot `i` (setting it true). -/
def setTrue (v : List Bool) (i : Nat) : List Bool := v.set i true
def setFalse (v : List Bool) (i : Nat) : List Bool := v.set i false

theorem count_set_true_mono (v : List Bool) (i : Nat) : count v ≤ count (setTrue v i) := by
  unfold setTrue
  induction v generalizing i with
  | nil => simp [count]
  | cons b rest ih =>
    cases i with
    | zero =>
      cases b <;> simp [List.set_cons_zero, count]
    | succ n =>
      have := ih n
      cases b <;> simp [List.set_cons_succ, count] <;> omega

theorem count_set_false_le (v : List Bool) (i : Nat) : count v ≤ count (setFalse v i) + 1 := by
  unfold setFalse
  induction v generalizing i with
  | nil => simp [count]
  | cons b rest ih =>
    cases i with
    | zero =>
      cases b <;> simp [List.set_cons_zero, count]
    | succ n =>
      have := ih n
      cases b <;> simp [List.set_cons_succ, count] <;> omega

/-- A quorum of Q once reached stays reached under acknowledgements. -/
theorem quorum_stable (v : List Bool) (i q : Nat) (h : q ≤ count v) : q ≤ count (setTrue v i) :=
  Nat.le_trans h (count_set_true_mono v i)

end Oak.ProtocolQuorum
