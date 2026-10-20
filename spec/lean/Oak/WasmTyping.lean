import Oak.WasmExecution

/-! Reachable straight-line scalar type checking and execution safety. This is
not the full control-polymorphic module validator. Unreachable is checked with
an arbitrary unchanged type stack; it always traps before any successor runs. -/
namespace Oak.WasmTyping
open WasmExecution

/-- Successful execution has the predicted stack and unchanged local types;
the only permitted failure is an explicit Core runtime trap. -/
def Safe (locals : Array Width) (stack : List Width) : Except Fault State → Prop
  | .ok s => s.stack.map Value.width = stack ∧ s.locals.map Value.width = locals
  | .error fault => ∃ reason, fault = .trap reason

def NumericSafe (w : Width) : Except Fault Value → Prop
  | .ok v => v.width = w
  | .error fault => ∃ reason, fault = .trap reason

def checkBinary (input output : Width) : List Width → Option (List Width)
  | b :: a :: rest => if a = input ∧ b = input then some (output :: rest) else none
  | _ => none

def checkWrite (locals : Array Width) (keep : Bool) (index : Nat) : List Width → Option (List Width)
  | v :: rest => do
    let old ← locals[index]?
    if old = v then some (if keep then v :: rest else rest) else none
  | [] => none

def checkOperation (locals : Array Width) (op : Operation) (imm : Int)
    (stack : List Width) : Option (List Width) :=
  match op with
  | .nop | .unreachable => some stack
  | .const w => some (w :: stack)
  | .drop => match stack with | _ :: rest => some rest | [] => none
  | .get => do let w ← locals[imm.toNat]?; some (w :: stack)
  | .set => checkWrite locals false imm.toNat stack
  | .tee => checkWrite locals true imm.toNat stack
  | .eqz32 => match stack with | .w32 :: rest => some (.w32 :: rest) | _ => none
  | .binary w _ => checkBinary w w stack
  | .compare w _ => checkBinary w .w32 stack

/-- Operand validity is checked before converting indices to Nat. -/
def check (locals : Array Width) (ins : UInt8 × Int) (stack : List Width) : Option (List Width) := do
  if (WasmInstruction.encode ins.1 ins.2).isNone then none else do
    let op ← operation ins.1
    checkOperation locals op ins.2 stack

def checkSequence (locals : Array Width) : List (UInt8 × Int) → List Width → Option (List Width)
  | [], stack => some stack
  | ins :: rest, stack => do checkSequence locals rest (← check locals ins stack)

theorem binary_safe (w : Width) (op : Binary) (a b : BitVec w.bits) :
    NumericSafe w (binary w op a b) := by
  cases w <;> cases op <;> simp only [binary]
  all_goals repeat first | split | simp [NumericSafe, word, Value.width]

theorem compare_safe (w : Width) (op : Compare) (a b : BitVec w.bits) :
    NumericSafe .w32 (compare w op a b) := by
  rcases compare_boolean w op a b with h | h <;> simp [h, NumericSafe, Value.width]

/-- Binary validation prevents both underflow and mixed-width execution. -/
theorem applyBinary_safe (input output : Width)
    (f : BitVec input.bits → BitVec input.bits → Except Fault Value)
    (hf : ∀ a b, NumericSafe output (f a b)) (s : State) (expected : List Width)
    (hc : checkBinary input output (s.stack.map Value.width) = some expected) :
    Safe (s.locals.map Value.width) expected (applyBinary input f s) := by
  cases hs : s.stack with
  | nil => simp [checkBinary, hs] at hc
  | cons b rest =>
    cases rest with
    | nil => simp [checkBinary, hs] at hc
    | cons a rest =>
      cases input <;> cases a <;> cases b <;>
        simp [checkBinary, hs, Value.width] at hc
      all_goals subst expected
      all_goals simp only [applyBinary, hs]
      all_goals rename_i a b
      all_goals have ht := hf a b
      all_goals cases hr : f a b <;> simp_all [Safe, NumericSafe, bind, Except.bind]

/-- Existing local-store invariants lift to the entire type array. -/
theorem localWrite_types (keep : Bool) (index : Nat) (s out : State)
    (h : localWrite keep index s = .ok out) :
    out.locals.map Value.width = s.locals.map Value.width := by
  apply Array.ext_getElem?
  intro i
  simpa using (localWrite_preserves_types keep index s out h).2 i

theorem localWrite_safe (keep : Bool) (index : Nat) (s : State) (expected : List Width)
    (hc : checkWrite (s.locals.map Value.width) keep index (s.stack.map Value.width) = some expected) :
    Safe (s.locals.map Value.width) expected (localWrite keep index s) := by
  cases hs : s.stack with
  | nil => simp [checkWrite, hs] at hc
  | cons v rest =>
    cases hg : s.locals[index]? with
    | none => simp [checkWrite, hs, hg] at hc
    | some old =>
      by_cases ht : old.width = v.width
      · simp [checkWrite, hs, hg, ht] at hc
        subst expected
        have hw : localWrite keep index s = .ok ⟨(if keep then v :: rest else rest), s.locals.setIfInBounds index v⟩ := by
          simp [localWrite, hs, hg, ht]
        have hl := localWrite_types keep index s _ hw
        rw [hw]
        cases keep <;> simp_all [Safe]
      · simp [checkWrite, hs, hg, ht] at hc

/-- All 49 modeled scalar forms preserve types or produce a Core trap. -/
theorem execute_safe (op : Operation) (imm : Int) (s : State) (expected : List Width)
    (hc : checkOperation (s.locals.map Value.width) op imm (s.stack.map Value.width) = some expected) :
    Safe (s.locals.map Value.width) expected (execute op imm s) := by
  cases op with
  | nop => simp_all [checkOperation, execute, Safe]
  | unreachable => simp [execute, Safe]
  | const w => cases w <;> simp_all [checkOperation, execute, Safe, word, Value.width]
  | drop => cases hs : s.stack <;> simp_all [checkOperation, execute, Safe]
  | get =>
    cases hg : s.locals[imm.toNat]? <;> simp_all [checkOperation, execute, Safe]
  | set => exact localWrite_safe false imm.toNat s expected hc
  | tee => exact localWrite_safe true imm.toNat s expected hc
  | eqz32 =>
    cases hs : s.stack with
    | nil => simp [checkOperation, hs] at hc
    | cons v rest => cases v <;> simp_all [checkOperation, execute, Safe, Value.width]
  | binary w op => exact applyBinary_safe w w _ (binary_safe w op) s expected hc
  | compare w op => exact applyBinary_safe w .w32 _ (compare_safe w op) s expected hc

/-- Accepted tokens cannot fail with malformed, unsupported, underflow, width,
or local-index diagnostics on a state with the checked types. -/
theorem step_safe (ins : UInt8 × Int) (s : State) (expected : List Width)
    (hc : check (s.locals.map Value.width) ins (s.stack.map Value.width) = some expected) :
    Safe (s.locals.map Value.width) expected (step ins s) := by
  unfold check at hc
  split at hc
  · contradiction
  · rename_i he
    cases ho : operation ins.1 with
    | none => simp [ho] at hc
    | some op =>
      simp [ho] at hc
      simpa [step, he, ho] using execute_safe op ins.2 s expected hc

/-- Safety composes over every accepted straight-line sequence and all states
with its input/local types; no arithmetic-value precondition is required. -/
theorem sequence_safe (locals : Array Width) (instructions : List (UInt8 × Int))
    (s : State) (expected : List Width) (hl : s.locals.map Value.width = locals)
    (hc : checkSequence locals instructions (s.stack.map Value.width) = some expected) :
    Safe locals expected (WasmExecution.run instructions s) := by
  induction instructions generalizing s with
  | nil => simp_all [checkSequence, WasmExecution.run, Safe]
  | cons ins rest ih =>
    cases ht : check locals ins (s.stack.map Value.width) with
    | none => simp [checkSequence, ht] at hc
    | some types =>
      have hs := step_safe ins s types (by simpa [hl] using ht)
      cases hr : step ins s with
      | error fault => simpa [WasmExecution.run, hr, Safe, bind, Except.bind] using hs
      | ok next =>
        simp [hr, Safe] at hs
        simp [checkSequence, ht] at hc
        simpa [WasmExecution.run, hr, bind, Except.bind] using
          ih next (hs.2.trans hl) (by simpa [hs.1] using hc)

/-- Successful outputs have the checked types; every error is a genuine trap. -/
theorem accepted_no_diagnostic (locals : Array Width) (instructions : List (UInt8 × Int))
    (s : State) (expected : List Width) (fault : Fault)
    (hl : s.locals.map Value.width = locals)
    (hc : checkSequence locals instructions (s.stack.map Value.width) = some expected)
    (he : WasmExecution.run instructions s = .error fault) : ∃ reason, fault = .trap reason := by
  have h := sequence_safe locals instructions s expected hl hc
  simpa [he, Safe] using h

/-- Static acceptance also establishes valid instruction encodings. -/
theorem sequence_encodable (locals : Array Width) (instructions : List (UInt8 × Int))
    (stack expected : List Width) (hc : checkSequence locals instructions stack = some expected) :
    ∃ bytes, WasmInstruction.assemble instructions = some bytes := by
  induction instructions generalizing stack expected with
  | nil => exact ⟨[], rfl⟩
  | cons ins rest ih =>
    obtain ⟨op, imm⟩ := ins
    cases he : WasmInstruction.encode op imm with
    | none => simp [checkSequence, check, he] at hc
    | some front =>
      cases ht : check locals (op, imm) stack with
      | none => simp [checkSequence, ht] at hc
      | some next =>
        simp [checkSequence, ht] at hc
        obtain ⟨tail, hr⟩ := ih next expected hc
        exact ⟨front ++ tail, by simp [WasmInstruction.assemble, he, hr]⟩

/-- Safety applies to decoded assembled bytes, not just token execution. The
existing assembler refinement can supply this exact encoding premise. -/
theorem bytes_safe (locals : Array Width) (instructions : List (UInt8 × Int))
    (s : State) (expected : List Width) (bytes suffix : List UInt8)
    (hl : s.locals.map Value.width = locals)
    (hc : checkSequence locals instructions (s.stack.map Value.width) = some expected)
    (he : WasmInstruction.assemble instructions = some bytes) :
    Safe locals expected ((runBytes instructions.length (bytes ++ suffix) s).map Prod.fst) := by
  rw [runBytes_assemble he suffix s]
  have hs := sequence_safe locals instructions s expected hl hc
  cases hr : WasmExecution.run instructions s <;> simpa [hr, Except.map] using hs

end Oak.WasmTyping
