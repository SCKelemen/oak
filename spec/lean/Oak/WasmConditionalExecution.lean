import Oak.WasmModule

/-! All-input execution of the compiler's unsigned conditional/phi-local shape.
This is the internal decoded model, with no independent Core or engine claim. -/
set_option autoImplicit false
namespace Oak.WasmConditionalExecution
open WasmExecution

/-- Unsigned comparison with modular 32-bit subtraction on the selected arm. -/
def result (a b : BitVec 32) : BitVec 32 := if a.toNat < b.toNat then a-b else b-a

/-- Tokens exclude the final function end, as in WasmModule.code. -/
def body : List WasmControl.Token :=
  [(32,0),(32,1),(73,0),(4,64),(32,0),(32,1),(107,0),(33,2),
    (5,0),(32,1),(32,0),(107,0),(33,2),(11,0),(32,2)]
def function : WasmCalls.Function := ⟨[.w32,.w32],[.w32],[.w32],body⟩
def functions : Array WasmCalls.Function := #[function]
def initial (a b : BitVec 32) : WasmCalls.Machine :=
  ⟨⟨⟨[],#[.i32 a,.i32 b,.i32 0]⟩,body,[⟨.function,[.w32],[],[],[]⟩]⟩,[]⟩

def conditional (a b : BitVec 32) (condition : BitVec 32) : WasmCalls.Machine :=
  ⟨⟨⟨[.i32 condition],#[.i32 a,.i32 b,.i32 0]⟩,
    body.drop 3,[⟨.function,[.w32],[],[],[]⟩]⟩,[]⟩

theorem invoke_initial (a b : BitVec 32) (fuel : Nat) :
    WasmCalls.invoke functions 0 fuel [.i32 a,.i32 b] =
      WasmCalls.run functions fuel (initial a b) := by rfl

theorem comparison_prefix (a b : BitVec 32) (fuel : Nat) :
    WasmCalls.run functions (fuel+3) (initial a b) =
      WasmCalls.run functions fuel (conditional a b
        (if decide (a.toNat < b.toNat) then 1 else 0)) := by rfl

theorem true_arm (a b : BitVec 32) :
    WasmCalls.run functions 13 (conditional a b 1) =
      .ok ⟨[.i32 (a-b)],#[.i32 a,.i32 b,.i32 (a-b)]⟩ := by rfl

theorem false_arm (a b : BitVec 32) :
    WasmCalls.run functions 13 (conditional a b 0) =
      .ok ⟨[.i32 (b-a)],#[.i32 a,.i32 b,.i32 (b-a)]⟩ := by rfl

theorem invocation (a b : BitVec 32) :
    WasmCalls.invoke functions 0 16 [.i32 a,.i32 b] =
      .ok ⟨[.i32 (result a b)], #[.i32 a,.i32 b,.i32 (result a b)]⟩ := by
  rw [invoke_initial, comparison_prefix a b 13]
  by_cases h : a.toNat < b.toNat
  · simpa only [result,h,decide_true,↓reduceIte] using true_arm a b
  · simpa only [result,h,decide_false,Bool.false_eq_true,↓reduceIte] using false_arm a b

/-- Successful export execution remains stable at any larger runtime fuel. -/
theorem invocation_more (a b : BitVec 32) (extra : Nat) :
    WasmCalls.invoke functions 0 (16+extra) [.i32 a,.i32 b] =
      .ok ⟨[.i32 (result a b)],#[.i32 a,.i32 b,.i32 (result a b)]⟩ := by
  rw [invoke_initial]
  exact WasmCalls.run_more functions (by simpa only [invoke_initial] using invocation a b) extra

/-- Arguments are consumed in declaration order; junk operands stay suspended.
The callee has a fresh zero phi local and a separate function label. -/
theorem call_entry (caller : WasmControl.Machine) (outer : List WasmControl.Machine)
    (a b : BitVec 32) (junk : List Value)
    (hs : caller.state.stack = [.i32 b,.i32 a] ++ junk) :
    WasmCalls.call functions 0 ⟨caller,outer⟩ = .ok
      ⟨(initial a b).active,{caller with state := {caller.state with stack := junk}} :: outer⟩ := by
  simpa [initial, function, WasmCalls.zero] using WasmCalls.call_arguments functions 0 function caller outer
    [.i32 a,.i32 b] junk rfl (by simpa using hs) rfl (by decide +kernel) (by decide +kernel)

/-- Iterate the existing call machine without introducing instruction semantics. -/
def advance : Nat → WasmCalls.Machine → Except WasmCalls.Error WasmCalls.Machine
  | 0,m => .ok m
  | n+1,m => do advance n (← WasmCalls.tick functions m)

theorem advance_comparison (a b : BitVec 32) (callers : List WasmControl.Machine) (fuel : Nat) :
    advance (fuel+3) ⟨(initial a b).active,callers⟩ =
      advance fuel ⟨(conditional a b (if decide (a.toNat < b.toNat) then 1 else 0)).active,callers⟩ := by rfl

theorem return_true (a b : BitVec 32) (caller : WasmControl.Machine)
    (outer : List WasmControl.Machine) :
    advance 9 ⟨(conditional a b 1).active,caller :: outer⟩ =
      .ok ⟨{caller with state := {caller.state with stack := .i32 (a-b) :: caller.state.stack}},outer⟩ := by rfl

theorem return_false (a b : BitVec 32) (caller : WasmControl.Machine)
    (outer : List WasmControl.Machine) :
    advance 9 ⟨(conditional a b 0).active,caller :: outer⟩ =
      .ok ⟨{caller with state := {caller.state with stack := .i32 (b-a) :: caller.state.stack}},outer⟩ := by rfl

/-- Both branch paths restore any caller's locals, operands, continuation,
labels and outer callers, adding only the chosen result. -/
theorem return_to_caller (a b : BitVec 32) (caller : WasmControl.Machine)
    (outer : List WasmControl.Machine) :
    advance 12 ⟨(initial a b).active,caller :: outer⟩ =
      .ok ⟨{caller with state := {caller.state with stack := .i32 (result a b) :: caller.state.stack}},outer⟩ := by
  rw [advance_comparison a b (caller :: outer) 9]
  by_cases h : a.toNat < b.toNat
  · simpa only [result,h,decide_true,↓reduceIte] using return_true a b caller outer
  · simpa only [result,h,decide_false,Bool.false_eq_true,↓reduceIte] using return_false a b caller outer

/-- Entry and return compose: precisely the two arguments are consumed, the
result is prepended to the suspended suffix, and every caller field is restored. -/
theorem call_composition (caller : WasmControl.Machine) (outer : List WasmControl.Machine)
    (a b : BitVec 32) (junk : List Value)
    (hs : caller.state.stack = [.i32 b,.i32 a] ++ junk) :
    (WasmCalls.call functions 0 ⟨caller,outer⟩).bind (advance 12) =
      .ok ⟨{caller with state := {caller.state with stack := .i32 (result a b) :: junk}},outer⟩ := by
  rw [call_entry caller outer a b junk hs]
  exact return_to_caller a b {caller with state := {caller.state with stack := junk}} outer

end Oak.WasmConditionalExecution
