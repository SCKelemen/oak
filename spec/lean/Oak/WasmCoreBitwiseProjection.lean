import Oak.BitwiseSourceLowering

/-!
# A Core-shaped relational projection, NOT imported external Core semantics

This hand-written projection follows the named rules in WebAssembly/spec at
970c4116e644e2bf7acb39aab8b733db14ccdf28. See
`spec/wasm-core/README.md` for the exact provenance and remaining obligations.
Lean checks the theorems below, not the transcription's fidelity to SpecTec.
In particular this is NOT an independently verified external binary decoder,
Module_ok proof, or full Core instantiation proof. No production flag uses it.

The binary `end` delimiter is removed by expression decoding; it is not an
execution step. Returning a value instead unwraps an administrative label and
call frame. Lists of values/instructions are in Core order (top at the right),
not the top-at-head stack convention of WasmExecution.
-/
set_option autoImplicit false
namespace Oak.WasmCoreBitwiseProjection
open Oak.BitwiseFunction

/-- Independent syntax for the three Core integer binary operators. -/
inductive Binop where
  | and | or | xor
  deriving DecidableEq, Repr

def binop : Op → Binop
  | .and => .and | .or => .or | .xor => .xor

/-- Mathematical implementation of the SpecTec numeric builtins. These are
only DECLARED builtin upstream; correspondence is a documented trust boundary.
i32 is an unsigned bit pattern here; no signed extension or reinterpretation
is performed by AND/OR/XOR. -/
def numeric : Binop → BitVec 32 → BitVec 32 → BitVec 32
  | .and, a, b => a &&& b
  | .or, a, b => a ||| b
  | .xor, a, b => a ^^^ b

theorem numeric_agrees (op : Op) (a b : BitVec 32) :
    numeric (binop op) a b = eval op a b := by cases op <;> rfl

/-- Pointwise bit-string specification of the three primitives, corresponding
by hand transcription to the normative document's ibits/ibits-inverse equations.
This representation removes bit-string ordering from the Boolean operation. -/
def bitMeaning : Binop → Bool → Bool → Bool
  | .and, a, b => a && b
  | .or, a, b => a || b
  | .xor, a, b => Bool.xor a b

def NumericResult (op : Binop) (a b result : BitVec 32) : Prop :=
  ∀ index : Nat, result.getLsbD index =
    bitMeaning op (a.getLsbD index) (b.getLsbD index)

theorem numeric_bits (op : Binop) (a b : BitVec 32) :
    NumericResult op a b (numeric op a b) := by
  intro i
  cases op <;> simp [numeric, bitMeaning]

theorem numeric_unique (op : Binop) (a b result : BitVec 32)
    (h : NumericResult op a b result) : result = numeric op a b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  exact (h i).trans ((numeric_bits op a b i).symm)

/-- A host's signed i32 presentation and u32 presentation preserve the same
bits when explicitly converted back at width 32, including bit 31 set. -/
theorem signed_unsigned_bits (word : BitVec 32) :
    BitVec.ofInt 32 word.toInt = BitVec.ofNat 32 word.toNat := by simp

inductive Instr where
  | const (value : BitVec 32)
  | localGet (index : Nat)
  | binary (op : Binop)
  | label (arity : Nat) (body : List Instr)
  | frame (arity : Nat) (locals : List (BitVec 32)) (body : List Instr)
  | trap
  deriving Repr

def body (op : Op) : List Instr := [.localGet 0, .localGet 1, .binary (binop op)]

/-- All values in this profile have type i32. Nat counts a stack of i32 types.
The local context contains `localCount` initialized i32 locals (SET I32).
This is a restricted typing derivation, not the complete Core validator. -/
inductive Typed (localCount : Nat) : List Instr → Nat → Nat → Prop where
  | nil (n : Nat) : Typed localCount [] n n
  | localGet {i : Nat} {rest : List Instr} {n result : Nat} :
      i < localCount → Typed localCount rest (n+1) result →
      Typed localCount (.localGet i :: rest) n result
  | binary {op : Binop} {rest : List Instr} {n result : Nat} :
      Typed localCount rest (n+1) result →
      Typed localCount (.binary op :: rest) (n+2) result

theorem body_typed (op : Op) : Typed 2 (body op) 0 1 :=
  .localGet (by decide) (.localGet (by decide) (.binary (.nil 1)))

/-- Restricted Core instruction reductions. `valuesBefore` consists only of values;
this is Step/ctxt-instrs specialized to values followed by a selected redex.
No constructor treats a stuck configuration or trap as a returned result. -/
inductive Step : List (BitVec 32) → List Instr → List Instr → Prop where
  | localGet {locals : List (BitVec 32)} (valuesBefore : List (BitVec 32)) (suffix : List Instr) (i : Nat) (v : BitVec 32) :
      locals[i]? = some v →
      Step locals (valuesBefore.map Instr.const ++ .localGet i :: suffix)
        (valuesBefore.map Instr.const ++ .const v :: suffix)
  | binary {locals : List (BitVec 32)} (valuesBefore : List (BitVec 32)) (suffix : List Instr) (op : Binop) (a b : BitVec 32) :
      Step locals (valuesBefore.map Instr.const ++ .const a :: .const b :: .binary op :: suffix)
        (valuesBefore.map Instr.const ++ .const (numeric op a b) :: suffix)
  | labelContext {locals : List (BitVec 32)} {n : Nat} {code next : List Instr} :
      Step locals code next → Step locals [.label n code] [.label n next]
  | labelValues {locals : List (BitVec 32)} (n : Nat) (values : List (BitVec 32)) :
      Step locals [.label n (values.map Instr.const)] (values.map Instr.const)
  | frameContext {locals : List (BitVec 32)} {n : Nat} {inner : List (BitVec 32)} {code next : List Instr} :
      Step inner code next → Step locals [.frame n inner code] [.frame n inner next]
  | frameValues {locals : List (BitVec 32)} (n : Nat) (inner values : List (BitVec 32)) :
      values.length = n →
      Step locals [.frame n inner (values.map Instr.const)] (values.map Instr.const)

inductive Steps (locals : List (BitVec 32)) : List Instr → List Instr → Prop where
  | refl (code : List Instr) : Steps locals code code
  | trans {a b c : List Instr} : Step locals a b → Steps locals b c → Steps locals a c

theorem Steps.label {locals : List (BitVec 32)} {a b : List Instr}
    (h : Steps locals a b) (n : Nat) : Steps locals [.label n a] [.label n b] := by
  induction h with
  | refl _ => exact .refl _
  | trans step _ ih => exact .trans (.labelContext step) ih

theorem Steps.frame {inner : List (BitVec 32)} {a b : List Instr}
    (h : Steps inner a b) (n : Nat) (outer : List (BitVec 32)) :
    Steps outer [.frame n inner a] [.frame n inner b] := by
  induction h with
  | refl _ => exact .refl _
  | trans step _ ih => exact .trans (.frameContext step) ih

theorem Steps.append {locals : List (BitVec 32)} {a b c : List Instr}
    (h : Steps locals a b) (h' : Steps locals b c) : Steps locals a c := by
  induction h with
  | refl _ => exact h'
  | trans step _ ih => exact .trans step (ih h')

/-- Three reductions, for every pair of 32-bit inputs, in Core stack order. -/
theorem body_steps (op : Op) (a b : BitVec 32) :
    Steps [a,b] (body op) [.const (eval op a b)] := by
  rw [← numeric_agrees]
  exact .trans (.localGet [] [.localGet 1, .binary (binop op)] 0 a rfl)
    (.trans (.localGet [a] [.binary (binop op)] 1 b rfl)
      (.trans (.binary [] [] (binop op) a b) (.refl _)))

/-- Administrative configuration AFTER the Core call-ref rule, whose two
parameters become the locals, with no additional locals. The missing full
store/call-ref/Module_ok bridge is not hidden in this definition. -/
def entered (op : Op) (a b : BitVec 32) : List Instr :=
  [.frame 1 [a,b] [.label 1 (body op)]]

theorem entered_returns (op : Op) (a b : BitVec 32) (outer : List (BitVec 32)) :
    Steps outer (entered op a b) [.const (eval op a b)] := by
  have inside := (body_steps op a b).label 1
  have returned : Steps [a,b] [.label 1 (body op)] [.const (eval op a b)] :=
    inside.append (.trans (.labelValues 1 [eval op a b]) (.refl _))
  exact (returned.frame 1 outer).append
    (.trans (.frameValues 1 [a,b] [eval op a b] rfl) (.refl _))

/-- A narrow abstract module: its sole function has type (i32,i32)->i32,
no extra locals, and no imports, memory, globals, tables, start or other code.
The shape is represented by construction, NOT by an external Module_ok proof. -/
structure Profile where
  name : List UInt8
  op : Op
  deriving DecidableEq, Repr

/-- Empty-store singleton allocation/export projection only. Full Core store
allocation and recursive module/type closure are not formalized here. -/
structure Instance where
  functions : List Profile
  exports : List (List UInt8 × Nat)

def instantiate (profile : Profile) : Instance :=
  ⟨[profile], [(profile.name, 0)]⟩

def exported (inst : Instance) (name : List UInt8) : Option Profile := do
  let entry ← inst.exports.find? (fun e => e.1 = name)
  inst.functions[entry.2]?

theorem instantiate_export (profile : Profile) :
    exported (instantiate profile) profile.name = some profile := by
  simp [exported, instantiate]

/-- Preserve the existing complete-byte module checker rather than inventing
another binary parser. The resulting abstract profile is a projection. -/
def project (entry bytes : List UInt8) (op : Op) : Option Profile :=
  if BitwiseModule.acceptsModule .wasm .wasmLocals [32,32] 32 op entry bytes then
    some ⟨entry, op⟩ else none

/-- The projection cannot broaden admission or bypass complete-byte checks. -/
theorem project_exact (entry bytes : List UInt8) (op : Op) :
    project entry bytes op = some ⟨entry,op⟩ ↔
    BitwiseModule.acceptsModule .wasm .wasmLocals [32,32] 32 op entry bytes = true := by
  simp [project]

/-- Successful admission connects actual complete module bytes to both the
existing byte execution and the typed, Core-shaped relational projection.
It does not assert that `project` implements the external binary grammar. -/
theorem admitted_bridge {entry bytes : List UInt8} {op : Op}
    (accepted : BitwiseModule.acceptsModule .wasm .wasmLocals [32,32] 32 op entry bytes = true)
    (a b : BitVec 32) :
    project entry bytes op = some ⟨entry,op⟩ ∧
    exported (instantiate ⟨entry,op⟩) entry = some ⟨entry,op⟩ ∧
    Typed 2 (body op) 0 1 ∧
    Steps [] (entered op a b) [.const (eval op a b)] ∧
    BitwiseModule.invokeModule entry bytes a b = .ok (eval op a b) := by
  exact ⟨by simp [project, accepted], instantiate_export _, body_typed _,
    entered_returns _ _ _ _, BitwiseModule.admitted_module_success accepted a b⟩

/-- The original source bytes and established typed source semantics are
retained when relating source success to the Core-shaped return derivation. -/
theorem accepted_source_bridge {source bytes : BitwiseSource.Bytes} {claim : BitwiseSource.Decl}
    (accepted : BitwiseSource.accepts source claim .wasm .wasmLocals bytes = true)
    (a b : BitVec 32) (fuel : Nat) :
    BitwiseSource.Grammar source claim ∧
    LoweringRefinement.evalX (BitwiseSourceLowering.toExpr claim)
      (BitwiseSourceLowering.inputs a b) (fun _ => 0) fuel = some (eval claim.op a b) ∧
    project claim.name bytes claim.op = some ⟨claim.name,claim.op⟩ ∧
    exported (instantiate ⟨claim.name,claim.op⟩) claim.name = some ⟨claim.name,claim.op⟩ ∧
    Typed 2 (body claim.op) 0 1 ∧
    Steps [] (entered claim.op a b) [.const (eval claim.op a b)] ∧
    BitwiseModule.invokeModule claim.name bytes a b = .ok (eval claim.op a b) := by
  have h := BitwiseSourceLowering.accepted_module_existing accepted a b fuel
  have admitted := (Bool.and_eq_true_iff.mp accepted).2
  exact ⟨h.1, h.2.1, admitted_bridge admitted a b⟩

end Oak.WasmCoreBitwiseProjection
