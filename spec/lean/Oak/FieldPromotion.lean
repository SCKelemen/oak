/-!
# Record fields in registers

The native lane keeps the scalar fields a loop touches of a record local in
callee-saved registers (docs/spec/94-assembler.md §9 "Fields in registers").
A field has two homes, its memory word and its register: a field store
writes the register, a field read is the register, a whole use of the
record flushes (memory takes the register), and a whole write of the record
reloads (the register takes what memory now holds). The theorem: along any
sequence of stores, flushes, and whole writes, reading the register gives
what the memory-resident field — every store going to memory — would hold,
and at a flush the memory holds it too, so a callee or a copy reading the
record whole sees the promoted values.
-/

namespace Oak.FieldPromotion

/-- The two homes of a promoted field. -/
structure Field where
  mem : Nat
  reg : Nat

/-- `r.f = v`: the register only. -/
def storeField (f : Field) (v : Nat) : Field := { f with reg := v }

/-- A whole use of the record: memory takes the register. -/
def flush (f : Field) : Field := { f with mem := f.reg }

/-- A whole write of the record leaving `v` in the field's memory: the
register reloads it. -/
def wholeWrite (_ : Field) (v : Nat) : Field := { mem := v, reg := v }

/-- A field read: the register. -/
def readField (f : Field) : Nat := f.reg

/-- The operations on a promoted field, in program order. -/
inductive Op
  | store (v : Nat)
  | flush
  | whole (v : Nat)

/-- The promoted discipline. -/
def runPromoted (f : Field) : List Op → Field
  | [] => f
  | .store v :: ops => runPromoted (storeField f v) ops
  | .flush :: ops => runPromoted (flush f) ops
  | .whole v :: ops => runPromoted (wholeWrite f v) ops

/-- The memory-resident discipline: the field's one home takes every
store and every whole write; a flush changes nothing. -/
def runResident (m : Nat) : List Op → Nat
  | [] => m
  | .store v :: ops => runResident v ops
  | .flush :: ops => runResident m ops
  | .whole v :: ops => runResident v ops

/-- Reading the register after any sequence of operations is reading the
memory-resident field. -/
theorem promoted_reads (f : Field) (ops : List Op) :
    readField (runPromoted f ops) = runResident f.reg ops := by
  induction ops generalizing f with
  | nil => rfl
  | cons op ops ih =>
    cases op with
    | store v => exact ih (storeField f v)
    | flush => exact ih (flush f)
    | whole v => exact ih (wholeWrite f v)

/-- At a flush, memory holds the register: a whole use reads the promoted
values from the record's memory. -/
theorem flushed_memory (f : Field) (ops : List Op) :
    (flush (runPromoted f ops)).mem = runResident f.reg ops :=
  promoted_reads f ops

/-- After a whole write, the register holds what memory holds. -/
theorem reloaded (f : Field) (v : Nat) : readField (wholeWrite f v) = (wholeWrite f v).mem := rfl

end Oak.FieldPromotion
