import Oak.WasmModule

/-! All-input nested calls for one exact original-source fixture and the complete
module decoded from its actual compiler output. This uses the internal scalar
execution model, not the independent hand-transcribed Core relations. Source
identity is checked byte-for-byte; no source parser/compiler refinement or new
source grammar is claimed. See docs/spec/91-wasm-call-composition.md. -/
set_option autoImplicit false
namespace Oak.WasmCallComposition
open WasmExecution WasmCalls

/-- The three functions in compiler order. The wrapper writes 99 to its local 2
while the suspended main function must retain a+7 in its own local 2. -/
def difference : Function := ⟨[.w32,.w32], [.w32], [], [(32,0),(32,1),(107,0)]⟩
def reverse : Function := ⟨[.w32,.w32], [.w32], [.w32,.w32],
  [(65,99),(33,2),(32,1),(32,0),(16,0),(33,3),(32,3),(32,2),(106,0),(32,2),(107,0)]⟩
def main : Function := ⟨[.w32,.w32], [.w32], [.w32,.w32],
  [(32,0),(65,7),(106,0),(33,2),(32,0),(32,1),(16,2),(33,3),(32,3),(32,2),(107,0),(32,2),(107,0)]⟩
def functions : Array Function := #[difference,main,reverse]

/-- Mathematical fixture result, with every operation modulo 2^32. The order
b-a is observable: it is not hidden behind a commutative operation. -/
def result (a b : BitVec 32) : BitVec 32 := (b-a)-(a+7)-(a+7)

def activation (f : Function) (a b : BitVec 32) : WasmControl.Machine :=
  ⟨⟨[], ([Value.i32 a,Value.i32 b] ++ f.locals.map zero).toArray⟩, f.body,
    [⟨.function, f.results.reverse, [], [], []⟩]⟩

/-- Both non-leaf activations start with fresh zero locals, an empty operand
stack and their own implicit function label; suspended operands are not locals. -/
theorem fresh_main (a b : BitVec 32) (junk : List Value) :
    activate main ([.i32 b,.i32 a] ++ junk) = .ok (activation main a b) := by
  simpa [activation] using activate_arguments main [.i32 a,.i32 b] junk rfl
    (by decide +kernel) (by decide +kernel)

theorem fresh_reverse (a b : BitVec 32) (junk : List Value) :
    activate reverse ([.i32 b,.i32 a] ++ junk) = .ok (activation reverse a b) := by
  simpa [activation] using activate_arguments reverse [.i32 a,.i32 b] junk rfl
    (by decide +kernel) (by decide +kernel)

/-- Exactly n transitions of the existing call machine, with errors propagated.
No alternative instruction or call semantics is introduced. -/
def advance (table : Array Function) : Nat → Machine → Except Error Machine
  | 0, m => .ok m
  | n+1, m => do advance table n (← tick table m)

/-- The real main body saves its own local 2 before entering reverse. Its
continuation and function label are suspended, not copied into the callee. -/
theorem main_enters_reverse (a b : BitVec 32) :
    advance functions 7 ⟨activation main a b, []⟩ = .ok
      ⟨activation reverse a b,
        [⟨⟨[], #[.i32 a,.i32 b,.i32 (a+7),.i32 0]⟩,
          main.body.drop 7, [⟨.function,[.w32],[],[],[]⟩]⟩]⟩ := by rfl

/-- Nested subtraction returns to ANY suspended caller, not only this fixture.
Its operands, locals, continuation, labels and outer callers are all preserved;
only the result is prepended. The callee's write of 99 cannot leak back. -/
theorem reverse_returns (a b : BitVec 32) (caller : WasmControl.Machine)
    (outer : List WasmControl.Machine) :
    advance functions 18 ⟨activation reverse a b, caller :: outer⟩ =
      .ok ⟨{caller with state := {caller.state with stack := .i32 (b-a) :: caller.state.stack}},outer⟩ := by
  change Except.ok (⟨{caller with state := {caller.state with stack := Value.i32 (((b-a)+99)-99) :: caller.state.stack}},outer⟩ : Machine) = _
  simp only [BitVec.add_sub_cancel]

/-- General external invocation is stable under extra runtime fuel. -/
theorem invoke_more (table : Array Function) {index fuel : Nat} {args : List Value} {out : State}
    (h : invoke table index fuel args = .ok out) (extra : Nat) :
    invoke table index (fuel+extra) args = .ok out := by
  cases hg : table[index]? with
  | none => simp [invoke, hg] at h
  | some f =>
    by_cases ht : args.map Value.width ≠ f.params
    · simp [invoke, hg, ht] at h
    · cases ha : activate f args.reverse with
      | error err => simp [invoke, hg, ht, ha, bind, Except.bind] at h
      | ok active =>
        simp only [invoke, hg, ht, ↓reduceIte, ha, bind, Except.bind] at h ⊢
        exact WasmCalls.run_more table h extra

/-- Every one of the 2^64 input pairs succeeds with exactly the declared result
and the restored main locals, including the surviving a+7 and b-a values. -/
theorem invocation (a b : BitVec 32) (extra : Nat) :
    invoke functions 1 (32+extra) [.i32 a,.i32 b] =
      .ok ⟨[.i32 (result a b)], #[.i32 a,.i32 b,.i32 (a+7),.i32 (b-a)]⟩ := by
  apply invoke_more (fuel := 32)
  change Except.ok (⟨[.i32 (((b-a+99)-99)-(a+7)-(a+7))],
    #[.i32 a,.i32 b,.i32 (a+7),.i32 ((b-a+99)-99)]⟩ : State) = _
  simp only [BitVec.add_sub_cancel, result]

/-- One less step is insufficient, regardless of argument values. Exhaustion
is an explicit model limit, never a claim that the real engine traps. -/
theorem insufficient_fuel (a b : BitVec 32) :
    invoke functions 1 31 [.i32 a,.i32 b] = .error (.control .exhausted) := by rfl

/-- Exact original fixture bytes. This is an identity check for one source,
not an implementation of Oak parsing, typing, lowering or source semantics. -/
def source : String := "difference: (x: u32, y: u32): u32 {\n  temp: u32 = x - y\n  temp\n}\nreverse: (x: u32, y: u32): u32 {\n  keep: u32 = u32(99)\n  result: u32 = difference(y, x)\n  result + keep - keep\n}\nmain: (a: u32, b: u32): u32 {\n  keep: u32 = a + u32(7)\n  result: u32 = reverse(a, b)\n  result - keep - keep\n}\n"
def sourceBytes : List UInt8 := source.toUTF8.data.toList

def module : WasmModule.Module := ⟨functions,
  [⟨"difference".toUTF8.data.toList,0⟩,⟨"main".toUTF8.data.toList,1⟩,
    ⟨"reverse".toUTF8.data.toList,2⟩]⟩

def accepts (original bytes : List UInt8) : Bool :=
  original == sourceBytes && WasmModule.decode bytes == some module

/-- Acceptance binds original source identity and every decoded module field.
The real emitted module is supplied by the regression, not embedded or replaced
by a hand-built module envelope. Legal equivalent padded LEBs remain allowed. -/
theorem accepted_invocation {original bytes : List UInt8}
    (h : accepts original bytes = true) (a b : BitVec 32) (extra : Nat) :
    original = sourceBytes ∧
    WasmModule.decode bytes = some module ∧
    WasmModule.invokeExport bytes "main".toUTF8.data.toList (32+extra) [.i32 a,.i32 b] =
      some (.ok ⟨[.i32 (result a b)], #[.i32 a,.i32 b,.i32 (a+7),.i32 (b-a)]⟩) := by
  obtain ⟨hs,hd⟩ := Bool.and_eq_true_iff.mp h
  have hs' : original = sourceBytes := by simpa using hs
  have hd' : WasmModule.decode bytes = some module := by simpa using hd
  refine ⟨hs',hd',?_⟩
  rw [WasmModule.invoke_decoded hd' (e := ⟨"main".toUTF8.data.toList,1⟩) (by decide +kernel)]
  exact congrArg some (invocation a b extra)

end Oak.WasmCallComposition
