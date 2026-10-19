import Oak.BitwiseSourceLowering
import Oak.NativeBitwiseImage

/-!
# Original source to complete executable images and Wasm

`check` parses the original canonical two-u32 AND/OR/XOR source and derives its
name and operation before checking one complete Wasm module and both complete
ARM64/RV64 ET_EXEC images. No name, operation, address or body is a trusted input.
The named function's actual decoded symbol address selects the flat-loader bytes
supplied to the existing local instruction-body semantics. Alignment, extent,
nonwrapping address and exact successful load are consequences of admission.

This is initialized function invocation, not execution from ELF e_entry/_start,
a physical instruction-fetch/whole-machine model, Linux loading, hardware, or
external ISA refinement. The ARM projection excludes faults and dynamic return
checks. RV64 retains its aligned, mapped, ordinary coherent 96-byte frame premise;
code bytes and data memory remain separate projections with external coherence
and noninterference assumptions. Wasm retains the bounded module interpreter.
The entire images, including startup and nonloaded metadata, are checked bytes,
but startup is not executed here. No whole-language/compiler theorem or new
production authority/API is asserted; the ET_REL object-bundle contract is unchanged.
-/
set_option autoImplicit false
namespace Oak.BitwiseSourceImageParity
open Oak.BitwiseFunction (Op eval)
open Oak.BitwiseSource (Bytes Decl Grammar Means)
open Oak.NativeBitwiseObject (fromUInt8 toUInt8)
open Oak.NativeBitwiseImage (Loaded)

/-- Each field is derived from original-source parsing before artifact checks. -/
def check (source wasm : Bytes) (arm rv : Oak.MinimalELF.Bytes) : Option Decl := do
  let d ← BitwiseSource.parse source
  if BitwiseModule.acceptsModule .wasm .wasmLocals [32,32] 32 d.op d.name wasm &&
      NativeBitwiseImage.accepts .arm64 (fromUInt8 d.name) arm
        (fromUInt8 (AArch64BitwiseFunction.functionBytes d.op)) &&
      NativeBitwiseImage.accepts .rv64 (fromUInt8 d.name) rv
        (RiscVFramedBitwise.functionBytes d.op) then
    some d
  else none

def accepts (source wasm : Bytes) (arm rv : Oak.MinimalELF.Bytes) : Bool :=
  (check source wasm arm rv).isSome

/-- Reassemble independent source/full-artifact checks without reducing concrete
large images again. No boolean check is omitted or replaced by a premise about
execution, compiler correctness or an externally supplied function address. -/
theorem check_of_artifacts {source wasm : Bytes} {arm rv : Oak.MinimalELF.Bytes} {d : Decl}
    (parsed : BitwiseSource.parse source = some d)
    (wasmGood : BitwiseModule.acceptsModule .wasm .wasmLocals [32,32] 32 d.op d.name wasm = true)
    (armGood : NativeBitwiseImage.accepts .arm64 (fromUInt8 d.name) arm
      (fromUInt8 (AArch64BitwiseFunction.functionBytes d.op)) = true)
    (rvGood : NativeBitwiseImage.accepts .rv64 (fromUInt8 d.name) rv
      (RiscVFramedBitwise.functionBytes d.op) = true) :
    check source wasm arm rv = some d := by
  simp [check, parsed, wasmGood, armGood, rvGood]

/-- Checker success retains the parsed declaration and each full-artifact check. -/
theorem check_sound {source wasm : Bytes} {arm rv : Oak.MinimalELF.Bytes} {d : Decl}
    (h : check source wasm arm rv = some d) :
    BitwiseSource.parse source = some d ∧
    BitwiseSource.accepts source d .wasm .wasmLocals wasm = true ∧
    NativeBitwiseImage.accepts .arm64 (fromUInt8 d.name) arm
      (fromUInt8 (AArch64BitwiseFunction.functionBytes d.op)) = true ∧
    NativeBitwiseImage.accepts .rv64 (fromUInt8 d.name) rv
      (RiscVFramedBitwise.functionBytes d.op) = true := by
  unfold check at h
  cases hp : BitwiseSource.parse source with
  | none => simp [hp] at h
  | some parsed =>
      rw [hp] at h
      change (if _ then some parsed else none) = some d at h
      split at h
      next good =>
        cases h
        obtain ⟨both, rvGood⟩ := Bool.and_eq_true_iff.mp good
        obtain ⟨wasmGood, armGood⟩ := Bool.and_eq_true_iff.mp both
        exact ⟨rfl, by simp [BitwiseSource.accepts, hp, wasmGood], armGood, rvGood⟩
      next => simp at h

theorem accepts_iff {source wasm : Bytes} {arm rv : Oak.MinimalELF.Bytes} :
    accepts source wasm arm rv = true ↔ ∃ d, check source wasm arm rv = some d := by
  simp [accepts, Option.isSome_iff_exists]

/-- Unsupported original grammar is rejected regardless of supplied artifacts. -/
theorem refuses_unsupported {source wasm : Bytes} {arm rv : Oak.MinimalELF.Bytes}
    (unsupported : BitwiseSource.parse source = none) :
    check source wasm arm rv = none ∧ accepts source wasm arm rv = false := by
  simp [check, accepts, unsupported]

/-- No source outside the declarative grammar can pass, independently of the
parser's candidate-discovery behavior or any supplied artifact. -/
theorem refuses_outside_grammar {source wasm : Bytes} {arm rv : Oak.MinimalELF.Bytes}
    (outside : ∀ d, ¬ Grammar source d) :
    check source wasm arm rv = none ∧ accepts source wasm arm rv = false := by
  cases hc : check source wasm arm rv with
  | none => simp [accepts, hc]
  | some d => exact (outside d (BitwiseSource.parse_sound (check_sound hc).1)).elim

/-- A declaration cannot be replayed against different original source bytes. -/
theorem refuses_source_replay {source wasm : Bytes} {arm rv : Oak.MinimalELF.Bytes}
    {d : Decl} (changed : source ≠ BitwiseSource.render d) :
    check source wasm arm rv ≠ some d := by
  intro h
  exact changed (BitwiseSource.parse_exact (check_sound h).1)

/-- A failed complete artifact check cannot be bypassed with another declaration. -/
theorem refuses_failed_artifact {source wasm : Bytes}
    {arm rv : Oak.MinimalELF.Bytes} {d : Decl}
    (parsed : BitwiseSource.parse source = some d)
    (bad : BitwiseModule.acceptsModule .wasm .wasmLocals [32,32] 32 d.op d.name wasm = false ∨
      NativeBitwiseImage.accepts .arm64 (fromUInt8 d.name) arm
        (fromUInt8 (AArch64BitwiseFunction.functionBytes d.op)) = false ∨
      NativeBitwiseImage.accepts .rv64 (fromUInt8 d.name) rv
        (RiscVFramedBitwise.functionBytes d.op) = false) :
    check source wasm arm rv = none := by
  unfold check
  rw [parsed]
  rcases bad with bad | bad | bad <;> simp [bad]

/-- Every field is derived from actual complete bytes; the body is the expected
source-derived comparison, never an unchecked replacement for the loaded bytes. -/
structure ImageBinding (machine : Oak.MinimalELF.Machine)
    (name image body : Oak.MinimalELF.Bytes) (loaded : Loaded) : Prop where
  extracted : NativeBitwiseImage.extract machine name image = some loaded
  profile : NativeBitwiseImage.StrictProfile machine name image
  named : NativeBitwiseImage.NamedFunction image (NativeBitwiseObject.oakPrefix ++ name) loaded
  unique : NativeBitwiseImage.UniqueNamedFunction image (NativeBitwiseObject.oakPrefix ++ name)
    (NativeBitwiseImage.symSection machine) loaded.symbolIndex
  body_eq : loaded.body = body
  address_eq : loaded.address = NativeBitwiseImage.bodyAddress machine
  offset_eq : loaded.fileOffset = NativeBitwiseImage.bodyOffset machine
  size_eq : loaded.size = NativeBitwiseImage.bodySize machine
  length_eq : body.length = loaded.size
  bytes_eq : body = Oak.MinimalELF.slice image loaded.fileOffset loaded.size
  admitted : Oak.MinimalELF.admittedBytes machine image loaded.address body = true
  loaded_bytes : Oak.MinimalELF.loadBytes image loaded.address loaded.size = some body
  file_bound : loaded.fileOffset + loaded.size ≤ image.length
  address_bound : loaded.address + loaded.size < 2^64
  aligned : loaded.address % 4 = 0
  nonempty : 0 < loaded.size

/-- The strict decoded-image theorem also supplies alignment and nonempty extent. -/
theorem accepted_image_binding {machine : Oak.MinimalELF.Machine}
    {name image body : Oak.MinimalELF.Bytes}
    (h : NativeBitwiseImage.accepts machine name image body = true) :
    ∃ loaded, ImageBinding machine name image body loaded := by
  obtain ⟨loaded, extracted, profile, named, unique, body_eq, address_eq,
    offset_eq, size_eq, length_eq, bytes_eq, admitted, loaded_bytes,
    file_bound, address_bound⟩ := NativeBitwiseImage.accepted_named_load h
  refine ⟨loaded, ⟨extracted, profile, named, unique, body_eq, address_eq,
    offset_eq, size_eq, length_eq, bytes_eq, admitted, loaded_bytes,
    file_bound, address_bound, ?_, ?_⟩⟩
  · rw [address_eq]
    cases machine <;> rfl
  · rw [size_eq]
    cases machine <;> decide

/-- Original source, derived name/op, and both actual named complete bodies. -/
theorem accepted_source_image_binding {source wasm : Bytes}
    {arm rv : Oak.MinimalELF.Bytes} {d : Decl}
    (h : check source wasm arm rv = some d) :
    BitwiseSource.parse source = some d ∧ source = BitwiseSource.render d ∧
    Grammar source d ∧
    (∃ loaded, ImageBinding .arm64 (fromUInt8 d.name) arm
      (fromUInt8 (AArch64BitwiseFunction.functionBytes d.op)) loaded) ∧
    (∃ loaded, ImageBinding .rv64 (fromUInt8 d.name) rv
      (RiscVFramedBitwise.functionBytes d.op) loaded) := by
  obtain ⟨parsed, _, armGood, rvGood⟩ := check_sound h
  exact ⟨parsed, BitwiseSource.parse_exact parsed, BitwiseSource.parse_sound parsed,
    accepted_image_binding armGood, accepted_image_binding rvGood⟩

/-- Initialize at the actual decoded function symbol, preserving arbitrary caller
register high halves, return address, SP and flags. -/
def armEntry (loaded : Loaded) (s : AArch64BitwiseFunction.State) :
    AArch64BitwiseFunction.State := { s with pc := BitVec.ofNat 64 loaded.address }

def rvEntry (loaded : Loaded) (left right : BitVec 32)
    (caller : BitVec 5 → BitVec 64) (memory : AArch64SpillMemory.Memory) :
    RiscVFramedBitwise.State :=
  RiscVFramedBitwise.entry left right (BitVec.ofNat 64 loaded.address) caller memory

/-- Load the admitted complete body and supply exactly those bytes to the local
ARM semantics. This does not introduce a fetched-instruction hardware model. -/
def armInvoke (image : Oak.MinimalELF.Bytes) (loaded : Loaded)
    (s : AArch64BitwiseFunction.State) : Option AArch64BitwiseFunction.State :=
  (Oak.MinimalELF.loadBytes image loaded.address loaded.size).bind fun bytes =>
    AArch64BitwiseFunction.invoke (toUInt8 bytes) (armEntry loaded s)

/-- The RV body is obtained from the same flat load at the actual symbol PC. -/
def rvInvoke (image : Oak.MinimalELF.Bytes) (loaded : Loaded)
    (left right : BitVec 32) (caller : BitVec 5 → BitVec 64)
    (memory : AArch64SpillMemory.Memory) (mappedRW : Nat → Nat → Bool) :
    Option RiscVFramedBitwise.State :=
  (Oak.MinimalELF.loadBytes image loaded.address loaded.size).bind fun bytes =>
    RiscVFramedBitwise.invoke mappedRW bytes (rvEntry loaded left right caller memory)

/-- Full u32 function result, not a process exit status. -/
def armResult (image : Oak.MinimalELF.Bytes) (loaded : Loaded)
    (s : AArch64BitwiseFunction.State) : Option (BitVec 32) :=
  (armInvoke image loaded s).map (fun after => (after.regs 0#5).truncate 32)

def rvResult (image : Oak.MinimalELF.Bytes) (loaded : Loaded)
    (left right : BitVec 32) (caller : BitVec 5 → BitVec 64)
    (memory : AArch64SpillMemory.Memory) (mappedRW : Nat → Nat → Bool) : Option (BitVec 32) :=
  (rvInvoke image loaded left right caller memory mappedRW).map
    (fun after => (RiscVCallExecution.read after.core 10).truncate 32)

/-- Successful ARM execution is discharged by the existing instruction theorem. -/
theorem bound_arm_success {name image : Oak.MinimalELF.Bytes} {op : Op} {loaded : Loaded}
    (binding : ImageBinding .arm64 name image
      (fromUInt8 (AArch64BitwiseFunction.functionBytes op)) loaded)
    (s : AArch64BitwiseFunction.State) :
    armInvoke image loaded s = some (AArch64BitwiseFunction.returned op (armEntry loaded s)) := by
  unfold armInvoke
  rw [binding.loaded_bytes]
  simp only [Option.bind_some, NativeBitwiseObject.to_fromUInt8]
  exact AArch64BitwiseFunction.function_success op (armEntry loaded s)

/-- Successful RV execution retains the existing frame premise, without an
execution-success or loader-success premise. -/
theorem bound_rv_success {name image : Oak.MinimalELF.Bytes} {op : Op} {loaded : Loaded}
    (binding : ImageBinding .rv64 name image (RiscVFramedBitwise.functionBytes op) loaded)
    (left right : BitVec 32) (caller : BitVec 5 → BitVec 64)
    (memory : AArch64SpillMemory.Memory) (mappedRW : Nat → Nat → Bool)
    (safe : RiscVFramedBitwise.frameSafe mappedRW (rvEntry loaded left right caller memory) = true) :
    rvInvoke image loaded left right caller memory mappedRW =
      some (RiscVFramedBitwise.finalState op (rvEntry loaded left right caller memory)) := by
  unfold rvInvoke
  rw [binding.loaded_bytes]
  exact RiscVFramedBitwise.function_success op _ mappedRW safe

/-- Full successful ARM ABI contract at the decoded symbol address. -/
def ArmContract (image : Oak.MinimalELF.Bytes) (loaded : Loaded) (op : Op)
    (s : AArch64BitwiseFunction.State) (left right : BitVec 32) : Prop :=
    ∃ after, armInvoke image loaded s = some after ∧
      after.regs 0#5 = (eval op left right).zeroExtend 64 ∧
      (∀ r, r ≠ 0#5 → after.regs r = s.regs r) ∧
      after.pc = s.regs 30#5 ∧ after.sp = s.sp ∧ after.nzcv = s.nzcv

/-- Preserve the entire existing ARM return/register contract. -/
theorem bound_arm_contract {name image : Oak.MinimalELF.Bytes} {op : Op} {loaded : Loaded}
    (binding : ImageBinding .arm64 name image
      (fromUInt8 (AArch64BitwiseFunction.functionBytes op)) loaded)
    (s : AArch64BitwiseFunction.State) (left right : BitVec 32)
    (hleft : (s.regs 0#5).extractLsb' 0 32 = left)
    (hright : (s.regs 1#5).extractLsb' 0 32 = right) :
    ArmContract image loaded op s left right := by
  refine ⟨AArch64BitwiseFunction.returned op (armEntry loaded s),
    bound_arm_success binding s,
    AArch64BitwiseFunction.result_u32 op (armEntry loaded s) left right hleft hright,
    ?_, ?_⟩
  · intro r hr
    exact AArch64BitwiseFunction.preserves_other_registers op (armEntry loaded s) r hr
  · exact AArch64BitwiseFunction.return_boundary op (armEntry loaded s)

/-- Full successful RV ABI, return and frame-footprint contract. The input
adapter is the existing LP64D adapter at the decoded symbol address. -/
def RvContract (image : Oak.MinimalELF.Bytes) (loaded : Loaded) (op : Op)
    (left right : BitVec 32) (caller : BitVec 5 → BitVec 64)
    (memory : AArch64SpillMemory.Memory) (mappedRW : Nat → Nat → Bool) : Prop :=
    ∃ after, rvInvoke image loaded left right caller memory mappedRW = some after ∧
      RiscVCallExecution.read after.core 10 = RiscV.widen 32 false (eval op left right) ∧
      (∀ r, r ≠ 0#5 → r ≠ 10#5 →
        after.core.regs r = (rvEntry loaded left right caller memory).core.regs r) ∧
      after.core.regs 2 = (rvEntry loaded left right caller memory).core.regs 2 ∧
      after.core.regs 9 = (rvEntry loaded left right caller memory).core.regs 9 ∧
      after.core.regs 18 = (rvEntry loaded left right caller memory).core.regs 18 ∧
      after.core.pc = RiscVCallExecution.clearLow
        ((rvEntry loaded left right caller memory).core.regs 1) ∧
      after.mem = RiscVFramedBitwise.frameMemory (rvEntry loaded left right caller memory) ∧
      (∀ a, a < RiscVFramedBitwise.frameBase (rvEntry loaded left right caller memory) ∨
          RiscVFramedBitwise.frameBase (rvEntry loaded left right caller memory) + 16 ≤ a →
        after.mem a = memory a)

/-- Preserve the RV sign-extended result, return, registers and exact memory
footprint. Only the sixteen saved bytes in the required 96-byte frame may change. -/
theorem bound_rv_contract {name image : Oak.MinimalELF.Bytes} {op : Op} {loaded : Loaded}
    (binding : ImageBinding .rv64 name image (RiscVFramedBitwise.functionBytes op) loaded)
    (left right : BitVec 32) (caller : BitVec 5 → BitVec 64)
    (memory : AArch64SpillMemory.Memory) (mappedRW : Nat → Nat → Bool)
    (safe : RiscVFramedBitwise.frameSafe mappedRW (rvEntry loaded left right caller memory) = true) :
    RvContract image loaded op left right caller memory mappedRW := by
  let s := rvEntry loaded left right caller memory
  have restored := RiscVFramedBitwise.stack_and_saves_restored op s
  refine ⟨RiscVFramedBitwise.finalState op s,
    bound_rv_success binding left right caller memory mappedRW safe,
    RiscVFramedBitwise.result_register op left right _ caller memory,
    ?_, restored.1, restored.2.1, restored.2.2, rfl, rfl, ?_⟩
  · intro r hzero hresult
    exact RiscVFramedBitwise.preserved_register op s r hzero hresult
  · intro a outside
    exact RiscVFramedBitwise.memory_footprint op s a outside

/-- Every accepted source/module/image tuple has actual decoded named functions
whose full u32 results agree for all input pairs and compatible initialized
caller states. The dependent frame premise names the decoded RV address.
Execution and load success are conclusions, not caller assumptions. Both
complete existing return/register/frame contracts are included explicitly. -/
theorem accepted_all_input_success {source wasm : Bytes}
    {arm rv : Oak.MinimalELF.Bytes} {d : Decl}
    (h : check source wasm arm rv = some d) :
    ∃ armLoaded rvLoaded,
      ImageBinding .arm64 (fromUInt8 d.name) arm
        (fromUInt8 (AArch64BitwiseFunction.functionBytes d.op)) armLoaded ∧
      ImageBinding .rv64 (fromUInt8 d.name) rv
        (RiscVFramedBitwise.functionBytes d.op) rvLoaded ∧
      ∀ (left right : BitVec 32) (fuel : Nat)
        (armState : AArch64BitwiseFunction.State),
        (armState.regs 0#5).extractLsb' 0 32 = left →
        (armState.regs 1#5).extractLsb' 0 32 = right →
        ∀ (caller : BitVec 5 → BitVec 64) (memory : AArch64SpillMemory.Memory)
          (mappedRW : Nat → Nat → Bool),
          RiscVFramedBitwise.frameSafe mappedRW
            (rvEntry rvLoaded left right caller memory) = true →
          Means source d left right (eval d.op left right) ∧
          LoweringRefinement.evalX (BitwiseSourceLowering.toExpr d)
            (BitwiseSourceLowering.inputs left right) (fun _ => 0) fuel =
              some (eval d.op left right) ∧
          BitwiseModule.invokeModule d.name wasm left right = .ok (eval d.op left right) ∧
          armResult arm armLoaded armState = some (eval d.op left right) ∧
          rvResult rv rvLoaded left right caller memory mappedRW = some (eval d.op left right) ∧
          ArmContract arm armLoaded d.op armState left right ∧
          RvContract rv rvLoaded d.op left right caller memory mappedRW := by
  obtain ⟨_, wasmGood, armGood, rvGood⟩ := check_sound h
  obtain ⟨armLoaded, armBinding⟩ := accepted_image_binding armGood
  obtain ⟨rvLoaded, rvBinding⟩ := accepted_image_binding rvGood
  refine ⟨armLoaded, rvLoaded, armBinding, rvBinding, ?_⟩
  intro left right fuel armState armLeft armRight caller memory mappedRW safe
  have sourceResult := BitwiseSource.accepted_source_to_module wasmGood left right
  refine ⟨sourceResult.1, BitwiseSourceLowering.lowering_success d left right fuel,
    sourceResult.2, ?_, ?_,
    bound_arm_contract armBinding armState left right armLeft armRight,
    bound_rv_contract rvBinding left right caller memory mappedRW safe⟩
  · unfold armResult
    rw [bound_arm_success armBinding]
    simp only [Option.map_some]
    rw [AArch64BitwiseFunction.result_u32 d.op
      (armEntry armLoaded armState) left right armLeft armRight]
    simp
  · unfold rvResult rvInvoke
    rw [rvBinding.loaded_bytes]
    exact RiscVFramedBitwise.all_input_result d.op left right
      (BitVec.ofNat 64 rvLoaded.address) caller memory mappedRW safe

end Oak.BitwiseSourceImageParity
