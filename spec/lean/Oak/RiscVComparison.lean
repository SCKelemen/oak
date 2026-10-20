import Oak.RiscVControlFlow

/-! Register-resident i64/u64 comparisons, decoded from ordinary RV64 words.
The producer result is composed with the existing terminator certificate.
Narrow canonical representations, allocation, spills and edge copies are
separate obligations. -/
namespace Oak.RiscVComparison
open Oak.RiscVCallExecution Oak.RiscVControlFlow

inductive Compare
  | eq | ne | lt | le | gt | ge
  deriving DecidableEq, Repr

/-- Source comparison on the full signed or unsigned 64-bit value. -/
def predicate (op : Compare) (signed : Bool) (a b : X) : Bool :=
  match op with
  | .eq => a == b
  | .ne => a != b
  | .lt => if signed then a.slt b else a.ult b
  | .le => if signed then a.sle b else a.ule b
  | .gt => if signed then b.slt a else b.ult a
  | .ge => if signed then b.sle a else b.ule a

def bit (b : Bool) : X := if b then 1#64 else 0#64

inductive ALU
  | sub | slt | sltu | sltiuOne | xoriOne
  deriving DecidableEq, Repr
structure Instruction where
  op : ALU
  rd : Reg
  left : Reg
  right : Reg := 0
  deriving DecidableEq, Repr

def Instruction.encode (i : Instruction) : BitVec 32 :=
  let fields := (i.rd.zeroExtend 32 <<< 7) ||| (i.left.zeroExtend 32 <<< 15)
  match i.op with
  | .sub => 0x40000033 ||| fields ||| (i.right.zeroExtend 32 <<< 20)
  | .slt => 0x2033 ||| fields ||| (i.right.zeroExtend 32 <<< 20)
  | .sltu => 0x3033 ||| fields ||| (i.right.zeroExtend 32 <<< 20)
  | .sltiuOne => 0x103013 ||| fields
  | .xoriOne => 0x104013 ||| fields

def Instruction.execute (i : Instruction) (s : State) : State :=
  let a := read s i.left
  let b := read s i.right
  let value := match i.op with
    | .sub => a - b
    | .slt => bit (a.slt b)
    | .sltu => bit (a.ult b)
    | .sltiuOne => bit (a.ult 1#64)
    | .xoriOne => a ^^^ 1#64
  ⟨s.pc + 4, write s i.rd value⟩

/-- Decode the real SUB/SLT/SLTU and the two immediate forms used by the
selector. SNEZ is SLTU rd,x0,rs; SEQZ is SLTIU rd,rs,1. -/
def decode (w : BitVec 32) : Option Instruction :=
  let rd := w.extractLsb' 7 5
  let a := w.extractLsb' 15 5
  let b := w.extractLsb' 20 5
  if w &&& 0xfe00707f = 0x40000033 then some ⟨.sub, rd, a, b⟩
  else if w &&& 0xfe00707f = 0x2033 then some ⟨.slt, rd, a, b⟩
  else if w &&& 0xfe00707f = 0x3033 then some ⟨.sltu, rd, a, b⟩
  else if w &&& 0xfff0707f = 0x103013 then some ⟨.sltiuOne, rd, a, 0⟩
  else if w &&& 0xfff0707f = 0x104013 then some ⟨.xoriOne, rd, a, 0⟩
  else none

def step (w : BitVec 32) (s : State) : Option State :=
  (decode w).map (fun i => i.execute s)
def runALU : List (BitVec 32) → State → Option State
  | [], s => some s
  | w :: rest, s => (step w s).bind (runALU rest)
def execute : List Instruction → State → State
  | [], s => s
  | i :: rest, s => execute rest (i.execute s)

/-- Immediate instruction encodings do not contain a second source register. -/
def Instruction.canonical (i : Instruction) : Prop :=
  i.op = .sltiuOne ∨ i.op = .xoriOne → i.right = 0

theorem decode_encode (i : Instruction) (h : i.canonical) :
    decode i.encode = some i := by
  rcases i with ⟨op, rd, a, b⟩
  cases op <;> simp only [Instruction.canonical] at h
  all_goals try simp only [true_or, or_true, true_implies] at h
  all_goals try subst b
  all_goals dsimp only [decode, Instruction.encode]
  all_goals split <;> (try split) <;> (try split) <;> (try split) <;> (try split)
  all_goals try simp_all only [Option.some.injEq, Instruction.mk.injEq, true_and]
  all_goals try simp only [Reg] at *
  all_goals bv_decide

theorem run_encoded (is : List Instruction) (s : State)
    (h : ∀ i ∈ is, i.canonical) :
    runALU (is.map Instruction.encode) s = some (execute is s) := by
  induction is generalizing s with
  | nil => rfl
  | cons i rest ih =>
    simp only [List.map_cons, runALU, step, decode_encode i (h i (by simp)),
      Option.map_some, Option.bind_some, execute]
    exact ih _ (fun j hj => h j (by simp [hj]))

/-- Exact instruction plans selected by optIRRV64Selector.compare. -/
def plan (op : Compare) (signed : Bool) (rd a b : Reg) : List Instruction :=
  let less := if signed then ALU.slt else ALU.sltu
  match op with
  | .eq => [⟨.sub, rd, a, b⟩, ⟨.sltiuOne, rd, rd, 0⟩]
  | .ne => [⟨.sub, rd, a, b⟩, ⟨.sltu, rd, 0, rd⟩]
  | .lt => [⟨less, rd, a, b⟩]
  | .le => [⟨less, rd, b, a⟩, ⟨.xoriOne, rd, rd, 0⟩]
  | .gt => [⟨less, rd, b, a⟩]
  | .ge => [⟨less, rd, a, b⟩, ⟨.xoriOne, rd, rd, 0⟩]

def result (op : Compare) (signed : Bool) (rd a b : Reg) (s : State) : State :=
  ⟨s.pc + BitVec.ofNat 64 (4 * (plan op signed rd a b).length),
    write s rd (bit (predicate op signed (read s a) (read s b)))⟩

/-- The comparison produces a canonical Boolean and changes no other
nonzero register. x0 is normalized by the architectural write operation. -/
theorem result_value (op : Compare) (signed : Bool) (rd a b : Reg)
    (s : State) (hr : rd ≠ 0#5) :
    read (result op signed rd a b s) rd =
      bit (predicate op signed (read s a) (read s b)) := by
  exact read_write_same s rd hr _

theorem result_preserves (op : Compare) (signed : Bool) (rd a b r : Reg)
    (s : State) (hz : r ≠ 0#5) (hr : r ≠ rd) :
    (result op signed rd a b s).regs r = s.regs r := by
  exact write_other s rd r hz hr _

theorem read_zero (s : State) : read s 0#5 = 0#64 := by simp [Oak.RiscVCallExecution.read]

theorem write_twice (s : State) (rd : Reg) (v v' : X) (pc : X) :
    write ⟨pc, write s rd v⟩ rd v' = write s rd v' := by
  funext r
  by_cases hz : r = 0#5 <;> by_cases hr : r = rd <;> simp [write, hz, hr]

theorem comparison_values (a b : X) :
    bit ((a - b).ult 1#64) = bit (a == b) ∧
    bit ((0#64).ult (a - b)) = bit (a != b) ∧
    (bit (b.slt a) ^^^ 1#64) = bit (a.sle b) ∧
    (bit (b.ult a) ^^^ 1#64) = bit (a.ule b) := by
  unfold bit
  simp only [X] at *
  bv_decide

/-- Valid even when rd aliases either or both operands. -/
theorem execute_plan (op : Compare) (signed : Bool) (rd a b : Reg)
    (s : State) (hr : rd ≠ 0#5) :
    execute (plan op signed rd a b) s = result op signed rd a b s := by
  simp only [Reg] at *
  have hv := comparison_values (read s a) (read s b)
  have hv' := comparison_values (read s b) (read s a)
  cases op <;> cases signed <;>
    simp [plan, execute, Instruction.execute, result, predicate,
      read_write_same _ _ hr, write_twice, read_zero,
      BitVec.add_assoc, hv.1, hv.2.1, hv.2.2.1, hv.2.2.2,
      hv'.2.2.1, hv'.2.2.2] <;>
      first | exact congrArg (write s rd) hv.1 | exact congrArg (write s rd) hv.2.1

def checkProducer (op : Compare) (signed : Bool) (rd a b : Reg)
    (words : List (BitVec 32)) : Bool :=
  rd != 0 && words == (plan op signed rd a b).map Instruction.encode

theorem checked_producer (op : Compare) (signed : Bool) (rd a b : Reg)
    (words : List (BitVec 32)) (h : checkProducer op signed rd a b words = true)
    (s : State) : runALU words s = some (result op signed rd a b s) := by
  simp only [checkProducer, Bool.and_eq_true, bne_iff_ne, beq_iff_eq] at h
  rw [h.2, run_encoded, execute_plan op signed rd a b s h.1]
  intro i hi
  cases op <;> cases signed <;> simp [plan] at hi <;>
    rcases hi with rfl | rfl <;> simp [Instruction.canonical]

/-- Execute the producer, then the certified terminator. -/
def runCompared (producer control : List (BitVec 32)) (s : State) : Option State :=
  (runALU producer s).bind (run control)

theorem checked_comparison_successor
    (op : Compare) (signed : Bool) (rd a b : Reg)
    (producer control : List (BitVec 32))
    (hp : checkProducer op signed rd a b producer = true)
    (s : State) (yes no : Nat) (next : Option Nat) (addr : Nat → X)
    (hc : check yes no next (result op signed rd a b s).pc addr rd control = true) :
    runCompared producer control s = some
      ⟨if predicate op signed (read s a) (read s b) then addr yes else addr no,
        (result op signed rd a b s).regs⟩ := by
  have hr : rd ≠ 0#5 := by
    have h := hp
    simp only [checkProducer, Bool.and_eq_true, bne_iff_ne, beq_iff_eq] at h
    exact h.1
  rw [runCompared, checked_producer op signed rd a b producer hp s, Option.bind_some]
  change run control ⟨(result op signed rd a b s).pc, (result op signed rd a b s).regs⟩ = _
  have hz : (result op signed rd a b s).regs 0#5 = 0#64 := by simp [result, write]
  rw [checked_successor yes no next _ addr rd control hc (result op signed rd a b s).regs hz]
  have hb : boolValue (result op signed rd a b s).regs rd =
      predicate op signed (read s a) (read s b) := by
    simp only [boolValue, result, read_write_same s rd hr]
    cases predicate op signed (read s a) (read s b) <;> decide
  rw [hb]

end Oak.RiscVComparison
