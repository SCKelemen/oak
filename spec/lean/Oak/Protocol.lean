import Std.Tactic.BVDecide

/-!
# Protocol machines: declaration semantics and their lowerings

`docs/spec/112-protocols.md` §2 projects a `protocol` declaration into
`name_legal` and `name_next`; §2a lowers those, for a machine without a data
record, to a dense transition table or to a shift DFA (`90-backend.md` §14).
This file states what the declaration means — the first line whose source
state and symbol match, in declaration order — and proves that both lowerings
compute exactly that, that the illegal sentinel is exactly illegality, that a
sink-based batch run reports illegality no matter where in the batch it
occurred (so the trap may be deferred to the end of the batch), and that the
shift DFA's 6-bit field packing decodes what it stores.

Guards over a payload are resolved before this model applies: the compiler
evaluates each guard for each payload value, and a *symbol* here is a step
together with its payload value. The compile-time evaluator is checked by
differential tests against the interpreter; the model takes the resolved
lines as given.
-/

namespace Oak.Protocol

/-- One resolved transition line: from a source state, on a symbol, to a
target. `S` states and `T` symbols. -/
structure Line (S T : Nat) where
  from_ : Fin S
  sym   : Fin T
  to    : Fin S
  deriving DecidableEq, Repr

/-- A declaration is its lines in declaration order. -/
structure Decl (S T : Nat) where
  lines : List (Line S T)

variable {S T : Nat}

/-- The declared semantics: the first line from this state on this symbol
gives the target; no line means the step is illegal. -/
def next (d : Decl S T) (s : Fin S) (t : Fin T) : Option (Fin S) :=
  (d.lines.find? fun l => l.from_ == s && l.sym == t).map (·.to)

/-- `legal` is exactly "some line applies". -/
def legal (d : Decl S T) (s : Fin S) (t : Fin T) : Bool :=
  (next d s t).isSome

/-! ## The dense table

Entries are naturals so one table type serves every machine; the sentinel is
`S`, a value no state has. -/

/-- The table entry for (state, symbol): the target's index, or the sentinel. -/
def table (d : Decl S T) (s : Fin S) (t : Fin T) : Nat :=
  match next d s t with
  | some s' => s'.val
  | none => S

/-- A table entry below the sentinel is a real target: the lowering's
`return {tag = n}` returns exactly the declared next state. -/
theorem table_target (d : Decl S T) (s : Fin S) (t : Fin T) (s' : Fin S) :
    next d s t = some s' ↔ table d s t = s'.val := by
  unfold table
  constructor
  · intro h; simp [h]
  · intro h
    cases hn : next d s t with
    | none => simp [hn] at h; exact absurd h (Nat.ne_of_gt s'.isLt)
    | some x =>
        simp [hn] at h
        exact congrArg some (Fin.ext h)

/-- The sentinel is exactly illegality: the lowering's `if (n == sentinel)
trap` fires precisely when the declaration has no line. -/
theorem table_sentinel (d : Decl S T) (s : Fin S) (t : Fin T) :
    next d s t = none ↔ table d s t = S := by
  unfold table
  constructor
  · intro h; simp [h]
  · intro h
    cases hn : next d s t with
    | none => rfl
    | some x =>
        simp [hn] at h
        exact absurd h (Nat.ne_of_lt x.isLt)

/-- `legal` and the table agree. -/
theorem legal_iff_table (d : Decl S T) (s : Fin S) (t : Fin T) :
    legal d s t = true ↔ table d s t ≠ S := by
  unfold legal
  constructor
  · intro h hs
    have := (table_sentinel d s t).2 hs
    simp [this] at h
  · intro h
    cases hn : next d s t with
    | none => exact absurd ((table_sentinel d s t).1 hn) h
    | some _ => simp

/-! ## Batch runs and the deferred trap

`run` is the declared meaning of stepping through a symbol list: it stops at
the first illegal step. `runSink` is what the lowering executes: states are
naturals, the sentinel is a state that every symbol maps to itself, and the
check happens once at the end. -/

def run (d : Decl S T) : Fin S → List (Fin T) → Option (Fin S)
  | s, [] => some s
  | s, t :: ts =>
      match next d s t with
      | some s' => run d s' ts
      | none => none

/-- The lowered step over naturals: a real state looks up the table; the
sink stays the sink. -/
def stepSink (d : Decl S T) (n : Nat) (t : Fin T) : Nat :=
  if h : n < S then table d ⟨n, h⟩ t else S

def runSink (d : Decl S T) : Nat → List (Fin T) → Nat
  | n, [] => n
  | n, t :: ts => runSink d (stepSink d n t) ts

/-- The sink absorbs: once illegal, every later step keeps the sink. -/
theorem runSink_sink (d : Decl S T) (ts : List (Fin T)) : runSink d S ts = S := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simp [runSink, stepSink, ih]

/-- The lowered batch computes the declared run: a real state at the end is
the declared final state, and the sink at the end means some step was
illegal. Deferring the check to the end of the batch loses nothing. -/
theorem runSink_correct (d : Decl S T) (s : Fin S) (ts : List (Fin T)) :
    runSink d s.val ts = (match run d s ts with | some s' => s'.val | none => S) := by
  induction ts generalizing s with
  | nil => simp [runSink, run]
  | cons t ts ih =>
      simp only [runSink, run, stepSink, s.isLt, dite_true]
      cases hn : next d s t with
      | some s' =>
          have ht : table d s t = s'.val := (table_target d s t s').1 hn
          simp only [Fin.eta, ht]
          exact ih s'
      | none =>
          have ht : table d s t = S := (table_sentinel d s t).1 hn
          simp only [Fin.eta, ht]
          exact runSink_sink d ts

theorem runSink_legal (d : Decl S T) (s : Fin S) (ts : List (Fin T)) (s' : Fin S) :
    run d s ts = some s' ↔ runSink d s.val ts = s'.val := by
  rw [runSink_correct]
  constructor
  · intro h; simp [h]
  · intro h
    cases hr : run d s ts with
    | none => simp [hr] at h; exact absurd h (Nat.ne_of_gt s'.isLt)
    | some x => simp [hr] at h; exact congrArg some (Fin.ext h)

theorem runSink_illegal (d : Decl S T) (s : Fin S) (ts : List (Fin T)) :
    run d s ts = none ↔ runSink d s.val ts = S := by
  rw [runSink_correct]
  constructor
  · intro h; simp [h]
  · intro h
    cases hr : run d s ts with
    | none => rfl
    | some x => simp [hr] at h; exact absurd h (Nat.ne_of_lt x.isLt)

/-! ## The shift DFA's packing

A shift DFA stores, per symbol, one 64-bit row holding ten 6-bit fields; the
state is the field's bit offset (`6 * state`), and each field holds the next
state's offset, so the step is `(row >>> state) &&& 63` with no multiply on
the critical path. The lowering applies when states plus the sink number at
most ten (offsets up to 54). `unpack_pack` is the packing law: field `i` of
a packed row is what was stored in it, whatever the other fields hold. It
is decided bit-blasted, once per field. -/

/-- Ten 6-bit fields packed into one 64-bit row, field `i` at bit `6 * i`. -/
def packFields (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 : BitVec 6) : BitVec 64 :=
  a0.zeroExtend 64
  ||| (a1.zeroExtend 64 <<< 6)  ||| (a2.zeroExtend 64 <<< 12)
  ||| (a3.zeroExtend 64 <<< 18) ||| (a4.zeroExtend 64 <<< 24)
  ||| (a5.zeroExtend 64 <<< 30) ||| (a6.zeroExtend 64 <<< 36)
  ||| (a7.zeroExtend 64 <<< 42) ||| (a8.zeroExtend 64 <<< 48)
  ||| (a9.zeroExtend 64 <<< 54)

def pack (f : Fin 10 → BitVec 6) : BitVec 64 :=
  packFields (f 0) (f 1) (f 2) (f 3) (f 4) (f 5) (f 6) (f 7) (f 8) (f 9)

/-- Field `i` of a row: shift to it, keep six bits. The lowering computes
`(row >>> offset) &&& 63` with `offset = 6 * state`. -/
def unpack (row : BitVec 64) (i : Nat) : BitVec 6 :=
  (row >>> (6 * i)).truncate 6

theorem unpack_packFields_0 (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 : BitVec 6) :
    unpack (packFields a0 a1 a2 a3 a4 a5 a6 a7 a8 a9) 0 = a0 := by
  unfold unpack packFields; bv_decide
theorem unpack_packFields_1 (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 : BitVec 6) :
    unpack (packFields a0 a1 a2 a3 a4 a5 a6 a7 a8 a9) 1 = a1 := by
  unfold unpack packFields; bv_decide
theorem unpack_packFields_2 (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 : BitVec 6) :
    unpack (packFields a0 a1 a2 a3 a4 a5 a6 a7 a8 a9) 2 = a2 := by
  unfold unpack packFields; bv_decide
theorem unpack_packFields_3 (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 : BitVec 6) :
    unpack (packFields a0 a1 a2 a3 a4 a5 a6 a7 a8 a9) 3 = a3 := by
  unfold unpack packFields; bv_decide
theorem unpack_packFields_4 (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 : BitVec 6) :
    unpack (packFields a0 a1 a2 a3 a4 a5 a6 a7 a8 a9) 4 = a4 := by
  unfold unpack packFields; bv_decide
theorem unpack_packFields_5 (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 : BitVec 6) :
    unpack (packFields a0 a1 a2 a3 a4 a5 a6 a7 a8 a9) 5 = a5 := by
  unfold unpack packFields; bv_decide
theorem unpack_packFields_6 (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 : BitVec 6) :
    unpack (packFields a0 a1 a2 a3 a4 a5 a6 a7 a8 a9) 6 = a6 := by
  unfold unpack packFields; bv_decide
theorem unpack_packFields_7 (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 : BitVec 6) :
    unpack (packFields a0 a1 a2 a3 a4 a5 a6 a7 a8 a9) 7 = a7 := by
  unfold unpack packFields; bv_decide
theorem unpack_packFields_8 (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 : BitVec 6) :
    unpack (packFields a0 a1 a2 a3 a4 a5 a6 a7 a8 a9) 8 = a8 := by
  unfold unpack packFields; bv_decide
theorem unpack_packFields_9 (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 : BitVec 6) :
    unpack (packFields a0 a1 a2 a3 a4 a5 a6 a7 a8 a9) 9 = a9 := by
  unfold unpack packFields; bv_decide

/-- Every field decodes to what was stored, whatever the other fields hold. -/
theorem unpack_pack (f : Fin 10 → BitVec 6) (i : Fin 10) : unpack (pack f) i.val = f i := by
  unfold pack
  match i with
  | ⟨0, _⟩ => exact unpack_packFields_0 _ _ _ _ _ _ _ _ _ _
  | ⟨1, _⟩ => exact unpack_packFields_1 _ _ _ _ _ _ _ _ _ _
  | ⟨2, _⟩ => exact unpack_packFields_2 _ _ _ _ _ _ _ _ _ _
  | ⟨3, _⟩ => exact unpack_packFields_3 _ _ _ _ _ _ _ _ _ _
  | ⟨4, _⟩ => exact unpack_packFields_4 _ _ _ _ _ _ _ _ _ _
  | ⟨5, _⟩ => exact unpack_packFields_5 _ _ _ _ _ _ _ _ _ _
  | ⟨6, _⟩ => exact unpack_packFields_6 _ _ _ _ _ _ _ _ _ _
  | ⟨7, _⟩ => exact unpack_packFields_7 _ _ _ _ _ _ _ _ _ _
  | ⟨8, _⟩ => exact unpack_packFields_8 _ _ _ _ _ _ _ _ _ _
  | ⟨9, _⟩ => exact unpack_packFields_9 _ _ _ _ _ _ _ _ _ _

/-- An offset field `6 * n` fits six bits exactly when `n ≤ 10`; with the
sink as the tenth field, real states number at most nine. -/
theorem offset_fits (n : Nat) : 6 * n < 64 ↔ n ≤ 10 := by omega

end Oak.Protocol
