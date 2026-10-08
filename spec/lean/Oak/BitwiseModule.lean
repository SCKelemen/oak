import Oak.BitwiseFunction

/-! Bounded one-function module loading for the two-u32 bitwise slice.
Every section/payload is exhausted. Imports, start, memory, extra functions,
extra exports, allocated locals, custom sections and trailing bytes refuse.
This independent model is not a refinement of Go or the external Core spec. -/
set_option autoImplicit false
set_option maxRecDepth 8192
namespace Oak.BitwiseModule
open Oak.WasmExecution Oak.BitwiseFunction

private def expectByte (expected : UInt8) : List UInt8 → Option (List UInt8)
  | byte :: rest => if byte = expected then some rest else none
  | [] => none

private def readNat (bytes : List UInt8) : Option (Nat × List UInt8) := do
  let (value, rest) ← WasmLEB.decode 32 false bytes
  if 0 ≤ value then some (value.toNat, rest) else none

private def expectNat (expected : Nat) (bytes : List UInt8) : Option (List UInt8) := do
  let (value, rest) ← readNat bytes
  if value = expected then some rest else none

private def takeBytes (count : Nat) (bytes : List UInt8) :
    Option (List UInt8 × List UInt8) :=
  if count ≤ bytes.length then some (bytes.take count, bytes.drop count) else none

private def readSection (id : UInt8) (bytes : List UInt8) :
    Option (List UInt8 × List UInt8) := do
  let rest ← expectByte id bytes
  let (count, rest) ← readNat rest
  takeBytes count rest

private def finished (bytes : List UInt8) : Option Unit :=
  if bytes = [] then some () else none

structure Loaded where
  exportName : List UInt8
  code : List UInt8
  deriving DecidableEq, Repr

/-- Check all binary fields in order. One (i32,i32)->i32 type, one function at
type index 0, one named export at function index 0, and no additional locals.
The requested export name is nonempty ASCII and at most 256 bytes. -/
def load (entry bytes : List UInt8) : Option Loaded := do
  if entry = [] ∨ 256 < entry.length ∨ ¬entry.all (fun b => b.toNat < 128) then none else do
  let (header, bytes) ← takeBytes 8 bytes
  if header ≠ [0,97,115,109,1,0,0,0] then none else do
  let (types, bytes) ← readSection 1 bytes
  let types ← expectNat 1 types
  let types ← expectByte 96 types
  let types ← expectNat 2 types
  let types ← expectByte 127 types
  let types ← expectByte 127 types
  let types ← expectNat 1 types
  let types ← expectByte 127 types
  finished types
  let (functions, bytes) ← readSection 3 bytes
  let functions ← expectNat 1 functions
  let functions ← expectNat 0 functions
  finished functions
  let (exports, bytes) ← readSection 7 bytes
  let exports ← expectNat 1 exports
  let (nameLength, exports) ← readNat exports
  let (name, exports) ← takeBytes nameLength exports
  if name ≠ entry then none else do
  let exports ← expectByte 0 exports
  let exports ← expectNat 0 exports
  finished exports
  let (codeSection, bytes) ← readSection 10 bytes
  finished bytes
  let codeSection ← expectNat 1 codeSection
  let (bodyLength, codeSection) ← readNat codeSection
  let (body, codeSection) ← takeBytes bodyLength codeSection
  finished codeSection
  let code ← expectNat 0 body
  some ⟨name, code⟩

def acceptsModule (target : Target) (abi : ABI) (parameters : List Nat)
    (result : Nat) (op : Op) (entry bytes : List UInt8) : Bool :=
  match load entry bytes with
  | none => false
  | some loaded => accepts target abi parameters result op loaded.code

/-- Invoke the decoded named entry with its two parameters and zero extra locals. -/
def invokeModule (entry bytes : List UInt8) (left right : BitVec 32) :
    Except Fault (BitVec 32) :=
  match load entry bytes with
  | none => .error .malformed
  | some loaded => invoke 3 loaded.code #[.i32 left, .i32 right]

/-- Names actual module bytes, entry and target profile. Quantifies over every
admitted module (including padded LEB lengths/indices), not just a fixture. -/
theorem admitted_module_success {target : Target} {abi : ABI}
    {parameters : List Nat} {result : Nat} {op : Op} {entry bytes : List UInt8}
    (accepted : acceptsModule target abi parameters result op entry bytes = true)
    (left right : BitVec 32) :
    invokeModule entry bytes left right = .ok (eval op left right) := by
  cases loaded : load entry bytes with
  | none => simp [acceptsModule, loaded] at accepted
  | some module =>
      simp only [acceptsModule, loaded] at accepted
      simp only [invokeModule, loaded]
      exact accepted_execution accepted left right

def entryName : List UInt8 := [98,105,116,119,105,115,101]

/-- Canonical fixture matched separately against actual compiler output. -/
def moduleBytes (op : Op) : List UInt8 :=
  [0,97,115,109,1,0,0,0, 1,7,1,96,2,127,127,1,127,
   3,2,1,0, 7,11,1,7,98,105,116,119,105,115,101,0,0,
   10,9,1,7,0] ++ functionBytes op

theorem canonical_loaded (op : Op) :
    load entryName (moduleBytes op) = some ⟨entryName, functionBytes op⟩ := by
  cases op <;> decide +kernel

theorem canonical_admitted (op : Op) :
    acceptsModule .wasm .wasmLocals [32,32] 32 op entryName (moduleBytes op) = true := by
  cases op <;> decide +kernel

theorem canonical_success (op : Op) (left right : BitVec 32) :
    invokeModule entryName (moduleBytes op) left right = .ok (eval op left right) :=
  admitted_module_success (canonical_admitted op) left right

/-- Lengths are actually decoded: legal padded LEB encodings are admitted
without requiring byte-for-byte equality to the canonical module fixture. -/
theorem padded_type_length_admitted (op : Op) :
    acceptsModule .wasm .wasmLocals [32,32] 32 op entryName
      ((moduleBytes op).take 9 ++ [135,0] ++ (moduleBytes op).drop 10) = true := by
  cases op <;> decide +kernel

/-- Each single-bit mutation of each byte refuses: 360 cases per operator. -/
theorem single_bit_mutations_refused (op : Op) :
    ((List.range (moduleBytes op).length).all fun index =>
      (List.range 8).all fun bit =>
        !(acceptsModule .wasm .wasmLocals [32,32] 32 op entryName
          ((moduleBytes op).set index ((moduleBytes op).getD index 0 ^^^ UInt8.ofNat (2^bit))))) = true := by
  cases op <;> decide +kernel

example : load entryName ((moduleBytes .and).dropLast) = none := by decide +kernel
example : load entryName (moduleBytes .and ++ [0,0]) = none := by decide +kernel
example : load [120] (moduleBytes .and) = none := by decide +kernel
example : acceptsModule .rv64 .native [32,32] 32 .and entryName (moduleBytes .and) = false := by decide +kernel
example : acceptsModule .wasm .wasmLocals [64,32] 32 .and entryName (moduleBytes .and) = false := by decide +kernel
example : acceptsModule .wasm .wasmLocals [32,32] 32 .or entryName (moduleBytes .and) = false := by decide +kernel
example : acceptsModule .wasm .native [32,32] 32 .and entryName (moduleBytes .and) = false := by decide +kernel
example : acceptsModule .arm64 .wasmLocals [32,32] 32 .and entryName (moduleBytes .and) = false := by decide +kernel
example : acceptsModule .wasm .wasmLocals [32,32] 64 .and entryName (moduleBytes .and) = false := by decide +kernel
end Oak.BitwiseModule
