import Oak.WasmAssemblerTotal
import Oak.WasmNumeric

/-! Decoded straight-line Core execution. Stack head is the top; binary
operators pop rhs before lhs. The Core numeric and variable rules are the
reference, not Oak's wrapping signed-division lowering. Structured control,
calls, memory, module validation and instantiation are outside this model. -/
namespace Oak.WasmExecution

inductive Width where
  | w32 | w64
  deriving DecidableEq, Repr

def Width.bits : Width → Nat | .w32 => 32 | .w64 => 64

inductive Value where
  | i32 (bits : BitVec 32)
  | i64 (bits : BitVec 64)
  deriving DecidableEq, Repr

def Value.width : Value → Width | .i32 _ => .w32 | .i64 _ => .w64

def word (w : Width) : BitVec w.bits → Value :=
  match w with | .w32 => .i32 | .w64 => .i64

structure State where
  stack : List Value := []
  locals : Array Value := #[]
  deriving DecidableEq, Repr

inductive Trap where
  | unreachable | divideByZero | integerOverflow
  deriving DecidableEq, Repr

/-- Invalid states and unsupported instructions are not Core runtime traps. -/
inductive Fault where
  | trap (reason : Trap)
  | malformed | unsupported | stackUnderflow | typeMismatch | localOutOfBounds
  deriving DecidableEq, Repr

inductive Binary where
  | add | sub | mul | divS | divU | remS | remU | and | or | xor
  deriving DecidableEq, Repr

inductive Compare where
  | eq | ne | ltS | ltU | gtS | gtU | leS | leU | geS | geU
  deriving DecidableEq, Repr

/-- Unsigned arithmetic uses naturals, signed arithmetic truncates toward zero.
Only signed division traps on MIN / -1; signed remainder returns zero there. -/
def binary (w : Width) (op : Binary) (a b : BitVec w.bits) : Except Fault Value :=
  let result := fun v => Except.ok (word w v)
  match op with
  | .add => result (a + b)
  | .sub => result (a - b)
  | .mul => result (a * b)
  | .and => result (a &&& b)
  | .or => result (a ||| b)
  | .xor => result (a ^^^ b)
  | .divU => if b = 0 then .error (.trap .divideByZero) else result (a / b)
  | .remU => if b = 0 then .error (.trap .divideByZero) else result (a % b)
  | .remS => if b = 0 then .error (.trap .divideByZero)
      else result (BitVec.ofInt w.bits (a.toInt.tmod b.toInt))
  | .divS => if b = 0 then .error (.trap .divideByZero)
      else if a.toInt = -(2 ^ (w.bits - 1) : Int) ∧ b.toInt = -1
      then .error (.trap .integerOverflow)
      else result (BitVec.ofInt w.bits (a.toInt.tdiv b.toInt))

/-- All comparisons, including i64 comparisons, produce an i32 Boolean. -/
def compare (w : Width) (op : Compare) (a b : BitVec w.bits) : Except Fault Value :=
  let yes := match op with
    | .eq => a == b | .ne => a != b
    | .ltS => decide (a.toInt < b.toInt) | .ltU => decide (a.toNat < b.toNat)
    | .gtS => decide (a.toInt > b.toInt) | .gtU => decide (a.toNat > b.toNat)
    | .leS => decide (a.toInt ≤ b.toInt) | .leU => decide (a.toNat ≤ b.toNat)
    | .geS => decide (a.toInt ≥ b.toInt) | .geU => decide (a.toNat ≥ b.toNat)
  .ok (.i32 (if yes then 1 else 0))

inductive Operation where
  | nop | unreachable | drop | eqz32
  | const (width : Width)
  | get | set | tee
  | binary (width : Width) (op : Binary)
  | compare (width : Width) (op : Compare)
  deriving DecidableEq, Repr

/-- This dispatch intentionally excludes all control delimiters and branches. -/
def operation (opcode : UInt8) : Option Operation :=
  match opcode.toNat with
  | 0 => some .unreachable | 1 => some .nop | 26 => some .drop
  | 32 => some .get | 33 => some .set | 34 => some .tee
  | 65 => some (.const .w32) | 66 => some (.const .w64) | 69 => some .eqz32
  | 70 => some (.compare .w32 .eq) | 71 => some (.compare .w32 .ne)
  | 72 => some (.compare .w32 .ltS) | 73 => some (.compare .w32 .ltU)
  | 74 => some (.compare .w32 .gtS) | 75 => some (.compare .w32 .gtU)
  | 76 => some (.compare .w32 .leS) | 77 => some (.compare .w32 .leU)
  | 78 => some (.compare .w32 .geS) | 79 => some (.compare .w32 .geU)
  | 81 => some (.compare .w64 .eq) | 82 => some (.compare .w64 .ne)
  | 83 => some (.compare .w64 .ltS) | 84 => some (.compare .w64 .ltU)
  | 85 => some (.compare .w64 .gtS) | 86 => some (.compare .w64 .gtU)
  | 87 => some (.compare .w64 .leS) | 88 => some (.compare .w64 .leU)
  | 89 => some (.compare .w64 .geS) | 90 => some (.compare .w64 .geU)
  | 106 => some (.binary .w32 .add) | 107 => some (.binary .w32 .sub)
  | 108 => some (.binary .w32 .mul) | 109 => some (.binary .w32 .divS)
  | 110 => some (.binary .w32 .divU) | 111 => some (.binary .w32 .remS)
  | 112 => some (.binary .w32 .remU) | 113 => some (.binary .w32 .and)
  | 114 => some (.binary .w32 .or) | 115 => some (.binary .w32 .xor)
  | 124 => some (.binary .w64 .add) | 125 => some (.binary .w64 .sub)
  | 126 => some (.binary .w64 .mul) | 127 => some (.binary .w64 .divS)
  | 128 => some (.binary .w64 .divU) | 129 => some (.binary .w64 .remS)
  | 130 => some (.binary .w64 .remU) | 131 => some (.binary .w64 .and)
  | 132 => some (.binary .w64 .or) | 133 => some (.binary .w64 .xor)
  | _ => none

theorem straight_line_opcode_count :
    ((List.range 256).filter (fun n => (operation (UInt8.ofNat n)).isSome)).length = 49 := by decide +kernel

/-- Every modeled opcode belongs to the assembler's admitted scalar profile. -/
theorem operation_admitted : ∀ n : Fin 256,
    (operation (UInt8.ofNat n.val)).isSome = true →
      (WasmInstruction.kind (UInt8.ofNat n.val)).isSome = true := by decide +kernel

/-- All nine admitted control/call forms explicitly remain unsupported here. -/
theorem control_unsupported :
    ([2,3,4,5,11,12,13,15,16] : List UInt8).all (fun op => (operation op).isNone) = true := by decide +kernel

/-- Typed binary stack discipline, leaving arbitrary deeper stack values and
all locals unchanged. Mixed widths refuse instead of silently converting. -/
def applyBinary (w : Width) (f : BitVec w.bits → BitVec w.bits → Except Fault Value)
    (s : State) : Except Fault State := do
  let b :: a :: rest := s.stack | .error .stackUnderflow
  let v ← match w, f, a, b with
    | .w32, f, .i32 x, .i32 y => f x y
    | .w64, f, .i64 x, .i64 y => f x y
    | _, _, _, _ => .error .typeMismatch
  .ok { s with stack := v :: rest }

def localWrite (keep : Bool) (index : Nat) (s : State) : Except Fault State := do
  let v :: rest := s.stack | .error .stackUnderflow
  let some old := s.locals[index]? | .error .localOutOfBounds
  if old.width ≠ v.width then .error .typeMismatch
  else .ok ⟨(if keep then v :: rest else rest), s.locals.setIfInBounds index v⟩

def execute (op : Operation) (immediate : Int) (s : State) : Except Fault State :=
  match op with
  | .nop => .ok s
  | .unreachable => .error (.trap .unreachable)
  | .drop => match s.stack with
    | [] => .error .stackUnderflow
    | _ :: rest => .ok { s with stack := rest }
  | .const w => .ok { s with stack := word w (BitVec.ofInt w.bits immediate) :: s.stack }
  | .get => match s.locals[immediate.toNat]? with
    | none => .error .localOutOfBounds
    | some v => .ok { s with stack := v :: s.stack }
  | .set => localWrite false immediate.toNat s
  | .tee => localWrite true immediate.toNat s
  | .eqz32 => match s.stack with
    | [] => .error .stackUnderflow
    | .i32 v :: rest => .ok { s with stack := .i32 (if v = 0 then 1 else 0) :: rest }
    | _ => .error .typeMismatch
  | .binary w op => applyBinary w (binary w op) s
  | .compare w op => applyBinary w (compare w op) s

/-- Token execution checks operand validity before interpreting it. In
particular negative local indices cannot become index zero via Int.toNat. -/
def step (ins : UInt8 × Int) (s : State) : Except Fault State :=
  if (WasmInstruction.encode ins.1 ins.2).isNone then .error .malformed
  else match operation ins.1 with
    | none => .error .unsupported
    | some op => execute op ins.2 s

def run : List (UInt8 × Int) → State → Except Fault State
  | [], s => .ok s
  | ins :: rest, s => do run rest (← step ins s)

/-- Count is a syntactic instruction count, not a control-flow execution fuel.
Decoding is incremental; faults stop before interpreting subsequent bytes. -/
def runBytes : Nat → List UInt8 → State → Except Fault (State × List UInt8)
  | 0, bytes, s => .ok (s, bytes)
  | n + 1, bytes, s =>
    match WasmInstruction.decode bytes with
    | none => .error .malformed
    | some (ins, tail) => do runBytes n tail (← step ins s)

/-- Exact decoded execution correspondence for every accepted byte sequence,
every initial operand/local state and every suffix, including all faults. -/
theorem runBytes_assemble {instructions bytes}
    (h : WasmInstruction.assemble instructions = some bytes) (suffix : List UInt8) (s : State) :
    runBytes instructions.length (bytes ++ suffix) s = (run instructions s).map (fun out => (out, suffix)) := by
  induction instructions generalizing bytes s with
  | nil => simp [WasmInstruction.assemble] at h; subst bytes; rfl
  | cons ins rest ih =>
    obtain ⟨op, v⟩ := ins
    cases he : WasmInstruction.encode op v with
    | none => simp [WasmInstruction.assemble, he] at h
    | some front =>
      cases ht : WasmInstruction.assemble rest with
      | none => simp [WasmInstruction.assemble, he, ht] at h
      | some tail =>
        simp [WasmInstruction.assemble, he, ht] at h
        subst bytes
        simp only [List.length_cons, runBytes, List.append_assoc, WasmInstruction.decode_encode he]
        cases hs : step (op, v) s <;> simp [run, hs, ih ht, bind, Except.bind, Except.map]

/-- The actual extracted assembler's output executes identically to its input
tokens in this model. The untouched destination suffix remains unread on success. -/
theorem assembled_execution (dst out : Array UInt8) (offset : UInt32)
    (plan : Array WasmAssembler.WasmInstruction) (bytes : List UInt8) (fuel : Nat)
    (result : WasmAssembler.WasmAssembly) (s : State)
    (hp : plan.size < 2^32) (hd : dst.size < 2^32)
    (he : WasmAssembler.instructionSequence plan.toList = some bytes)
    (hfit : offset.toNat + bytes.length ≤ dst.size) (hf : plan.size + 11 ≤ fuel)
    (hw : WasmAssembler.wasm_assemble dst offset plan fuel = some (result, out)) :
    runBytes plan.size (out.toList.drop offset.toNat) s =
      (run (plan.toList.map fun ins => (ins.opcode.toUInt8, ins.immediate.toInt)) s).map
        (fun state => (state, dst.toList.drop (offset.toNat + bytes.length))) := by
  rw [WasmAssembler.assemble_admitted_exact _ _ _ _ _ hp hd he hfit hf] at hw
  cases hw
  rw [WasmAssembler.writeBytes_suffix _ _ _ hfit]
  simpa using runBytes_assemble (WasmAssembler.instructionSequence_model he)
    (dst.toList.drop (offset.toNat + bytes.length)) s

/-- Binary operand order and the deeper-stack/local frame are universal. -/
theorem applyBinary_words (w : Width) (f : BitVec w.bits → BitVec w.bits → Except Fault Value)
    (a b : BitVec w.bits) (rest : List Value) (locals : Array Value) :
    applyBinary w f ⟨word w b :: word w a :: rest, locals⟩ =
      (f a b).map (fun v => ⟨v :: rest, locals⟩) := by
  cases w <;> cases hf : f a b <;> simp [applyBinary, word, hf, bind, Except.bind, Except.map]

/-- Comparison Booleans always have Core's i32 representation. -/
theorem compare_boolean (w : Width) (op : Compare) (a b : BitVec w.bits) :
    compare w op a b = .ok (.i32 0) ∨ compare w op a b = .ok (.i32 1) := by
  cases op <;> simp only [compare] <;> split <;> simp

/-- Signed division traps precisely on zero or the signed overflow pair. -/
theorem signed_division_traps (w : Width) (a b : BitVec w.bits) :
    (∃ reason, binary w .divS a b = .error (.trap reason)) ↔
      b = 0 ∨ (a.toInt = -(2 ^ (w.bits - 1) : Int) ∧ b.toInt = -1) := by
  simp [binary]
  split <;> simp_all
  split <;> simp_all

/-- Core's MIN / -1 remainder is zero, not a signed-division overflow trap. -/
theorem signed_remainder_neg_one (w : Width) (a : BitVec w.bits) :
    binary w .remS a (BitVec.ofInt w.bits (-1)) = .ok (word w 0) := by
  cases w <;> simp [binary, Width.bits]

/-- Numeric division agrees with the existing Core division model; this does
not substitute Oak's nontrapping overflow lowering for the Core instruction. -/
theorem core_signed_division_agrees (w : Width) (a b : BitVec w.bits) :
    (binary w .divS a b).toOption =
      (WasmNumeric.coreSignedDiv w.bits a.toInt b.toInt).map (word w) := by
  have hz : b.toInt = 0 ↔ b = 0#w.bits := by
    rw [← BitVec.toInt_zero, BitVec.toInt_inj]
  by_cases h0 : b = 0#w.bits
  · simp [binary, WasmNumeric.coreSignedDiv, h0, Except.toOption]
  · by_cases hv : a.toInt = -(2 ^ (w.bits - 1) : Int) ∧ b.toInt = -1 <;>
      simp [binary, WasmNumeric.coreSignedDiv, hz, h0, hv, Except.toOption]

/-- Successful local.set/tee preserve the local array length and every slot's
value type. No out-of-bounds dropped store can satisfy the success premise. -/
theorem localWrite_preserves_types (keep : Bool) (index : Nat) (s out : State)
    (h : localWrite keep index s = .ok out) :
    out.locals.size = s.locals.size ∧
      ∀ j : Nat, out.locals[j]?.map Value.width = s.locals[j]?.map Value.width := by
  cases hs : s.stack with
  | nil => simp [localWrite, hs] at h
  | cons v rest =>
    cases hg : s.locals[index]? with
    | none => simp [localWrite, hs, hg] at h
    | some old =>
      by_cases ht : old.width = v.width
      · simp [localWrite, hs, hg, ht] at h
        cases h
        constructor
        · simp
        · intro j
          by_cases hj : index = j
          · subst j
            have hi := (Array.getElem?_eq_some_iff.mp hg).1
            rw [Array.getElem?_setIfInBounds_self_of_lt hi, hg]
            simp [ht]
          · simp [Array.getElem?_setIfInBounds_ne hj]
      · simp [localWrite, hs, hg, ht] at h

end Oak.WasmExecution
