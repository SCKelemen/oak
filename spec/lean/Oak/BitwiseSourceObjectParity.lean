import Oak.BitwiseSourceLowering
import Oak.NativeBitwiseObject

/-!
# Original-source to complete-artifact bitwise parity

`check` consumes the original source, one complete Wasm module, and two complete
ELF64 relocatable objects. It derives the declaration from the source bytes;
there is no caller-provided operation, function name, body, or source-to-term
relation. The parsed name and operation are checked against each actual artifact.
Accepted source bytes must belong to `BitwiseSource.Grammar`, a deliberately
restricted canonical two-u32 AND/OR/XOR declaration. Other syntax refuses.
Artifact checks impose additional constraints, including the Wasm name limit;
no completeness claim for every declaration in that grammar is made.

The native guarantee is conditional on the existing flat section-loading and
instruction semantics. ARM uses the no-fault scalar projection with its stated
ABI inputs. RV64 uses the actual 36-byte framed body and requires the external
96-byte readable/writable, aligned, noninterfering stack-frame premise. The
aligned, non-wrapping code mapping is explicit. Physical instruction fetch,
OS/linker behavior, executable entry, external ISA refinement, whole-language
parser/compiler correctness, and code/data coherence remain outside the claim.
Wasm uses the existing bounded module interpreter, not an external engine/Core
spec refinement. Nothing here grants production verification authority.
-/
set_option autoImplicit false
namespace Oak.BitwiseSourceObjectParity
open Oak.BitwiseFunction (Op eval)
open Oak.BitwiseSource (Bytes Decl Grammar Means)
open Oak.NativeBitwiseObject (fromUInt8 toUInt8 Loaded)

/-- Each field is derived from original-source parsing before artifact checks. -/
def check (source wasm : Bytes) (arm rv : Oak.MinimalELF.Bytes) : Option Decl := do
  let d ← BitwiseSource.parse source
  if BitwiseModule.acceptsModule .wasm .wasmLocals [32,32] 32 d.op d.name wasm &&
      NativeBitwiseObject.accepts .arm64 (fromUInt8 d.name) arm
        (fromUInt8 (AArch64BitwiseFunction.functionBytes d.op)) &&
      NativeBitwiseObject.accepts .rv64 (fromUInt8 d.name) rv
        (RiscVFramedBitwise.functionBytes d.op) then
    some d
  else none

def accepts (source wasm : Bytes) (arm rv : Oak.MinimalELF.Bytes) : Bool :=
  (check source wasm arm rv).isSome

/-- Checker success retains the parsed declaration and each full-artifact check. -/
theorem check_sound {source wasm : Bytes} {arm rv : Oak.MinimalELF.Bytes} {d : Decl}
    (h : check source wasm arm rv = some d) :
    BitwiseSource.parse source = some d ∧
    BitwiseSource.accepts source d .wasm .wasmLocals wasm = true ∧
    NativeBitwiseObject.accepts .arm64 (fromUInt8 d.name) arm
      (fromUInt8 (AArch64BitwiseFunction.functionBytes d.op)) = true ∧
    NativeBitwiseObject.accepts .rv64 (fromUInt8 d.name) rv
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

/-- The named symbol is decoded from the actual complete object; its entire body
and extent are retained, including the checked canonical container profile. -/
def ObjectBinding (machine : Oak.MinimalELF.Machine) (name image body : Oak.MinimalELF.Bytes)
    (loaded : Loaded) : Prop :=
  NativeBitwiseObject.extract machine name image = some loaded ∧
  NativeBitwiseObject.StrictProfile machine name image ∧
  NativeBitwiseObject.NamedFunction image (NativeBitwiseObject.oakPrefix ++ name) loaded ∧
  NativeBitwiseObject.UniqueFunction image (NativeBitwiseObject.symSection machine)
    loaded.symbolIndex ∧
  loaded.body = body ∧ loaded.entry = 0 ∧ loaded.sectionIndex = 1 ∧
  loaded.fileOffset = 64 ∧ loaded.size = NativeBitwiseObject.bodySize machine ∧
  body = Oak.MinimalELF.slice image loaded.fileOffset loaded.size ∧
  loaded.fileOffset + loaded.size ≤ image.length ∧ body.length = loaded.size ∧
  0 < loaded.size

/-- Exact source, parsed name/op, and both actual named whole bodies are bound. -/
theorem accepted_source_object_binding {source wasm : Bytes}
    {arm rv : Oak.MinimalELF.Bytes} {d : Decl}
    (h : check source wasm arm rv = some d) :
    BitwiseSource.parse source = some d ∧ source = BitwiseSource.render d ∧
    Grammar source d ∧
    (∃ loaded, ObjectBinding .arm64 (fromUInt8 d.name) arm
      (fromUInt8 (AArch64BitwiseFunction.functionBytes d.op)) loaded) ∧
    (∃ loaded, ObjectBinding .rv64 (fromUInt8 d.name) rv
      (RiscVFramedBitwise.functionBytes d.op) loaded) := by
  obtain ⟨parsed, _, armGood, rvGood⟩ := check_sound h
  exact ⟨parsed, BitwiseSource.parse_exact parsed, BitwiseSource.parse_sound parsed,
    NativeBitwiseObject.accepted_named_body armGood,
    NativeBitwiseObject.accepted_named_body rvGood⟩

/-- Observe the full u32 result after loading the checked named ARM section. -/
def armResult (image : Oak.MinimalELF.Bytes) (loaded : Loaded) (base : Nat)
    (s : AArch64BitwiseFunction.State) : Option (BitVec 32) :=
  (NativeBitwiseObject.loadBytes image loaded base
    (NativeBitwiseObject.resolvedEntry loaded base) loaded.size).bind fun bytes =>
      (AArch64BitwiseFunction.invoke (toUInt8 bytes)
        { s with pc := BitVec.ofNat 64 base }).map
          (fun after => (after.regs 0#5).truncate 32)

/-- Observe the full u32 result after loading the checked named RV64 section.
The entry adapter includes the LP64D argument convention and actual base PC. -/
def rvResult (image : Oak.MinimalELF.Bytes) (loaded : Loaded) (base : Nat)
    (left right : BitVec 32) (caller : BitVec 5 → BitVec 64)
    (memory : AArch64SpillMemory.Memory) (mappedRW : Nat → Nat → Bool) : Option (BitVec 32) :=
  (NativeBitwiseObject.loadBytes image loaded base
    (NativeBitwiseObject.resolvedEntry loaded base) loaded.size).bind fun bytes =>
      (RiscVFramedBitwise.invoke mappedRW bytes
        (RiscVFramedBitwise.entry left right (BitVec.ofNat 64 base) caller memory)).map
          (fun after => (RiscVCallExecution.read after.core 10).truncate 32)

/-- All input pairs and all compatible caller states have the same source,
typed-expression, Wasm, and loaded native result. Native identity comes from
the full object, and the operation/name come only from original-source parsing. -/
theorem accepted_all_input_success {source wasm : Bytes}
    {arm rv : Oak.MinimalELF.Bytes} {d : Decl}
    (h : check source wasm arm rv = some d)
    (left right : BitVec 32) (fuel : Nat)
    (armBase rvBase : Nat)
    (armAligned : armBase % 4 = 0) (armBounded : armBase + 8 < 2^64)
    (rvAligned : rvBase % 4 = 0) (rvBounded : rvBase + 36 < 2^64)
    (armState : AArch64BitwiseFunction.State)
    (armLeft : (armState.regs 0#5).extractLsb' 0 32 = left)
    (armRight : (armState.regs 1#5).extractLsb' 0 32 = right)
    (caller : BitVec 5 → BitVec 64) (memory : AArch64SpillMemory.Memory)
    (mappedRW : Nat → Nat → Bool)
    (safe : RiscVFramedBitwise.frameSafe mappedRW
      (RiscVFramedBitwise.entry left right (BitVec.ofNat 64 rvBase) caller memory) = true) :
    Means source d left right (eval d.op left right) ∧
    LoweringRefinement.evalX (BitwiseSourceLowering.toExpr d)
      (BitwiseSourceLowering.inputs left right) (fun _ => 0) fuel =
        some (eval d.op left right) ∧
    BitwiseModule.invokeModule d.name wasm left right = .ok (eval d.op left right) ∧
    (∃ loaded, ObjectBinding .arm64 (fromUInt8 d.name) arm
      (fromUInt8 (AArch64BitwiseFunction.functionBytes d.op)) loaded ∧
      NativeBitwiseObject.resolvedEntry loaded armBase = armBase ∧
      armResult arm loaded armBase armState = some (eval d.op left right)) ∧
    (∃ loaded, ObjectBinding .rv64 (fromUInt8 d.name) rv
      (RiscVFramedBitwise.functionBytes d.op) loaded ∧
      NativeBitwiseObject.resolvedEntry loaded rvBase = rvBase ∧
      rvResult rv loaded rvBase left right caller memory mappedRW =
        some (eval d.op left right)) := by
  obtain ⟨_, wasmGood, armGood, rvGood⟩ := check_sound h
  have sourceResult := BitwiseSource.accepted_source_to_module wasmGood left right
  refine ⟨sourceResult.1, BitwiseSourceLowering.lowering_success d left right fuel,
    sourceResult.2, ?_, ?_⟩
  · obtain ⟨loaded, binding⟩ := NativeBitwiseObject.accepted_named_body armGood
    obtain ⟨loaded', hextract, _, entry, bytes⟩ :=
      NativeBitwiseObject.named_load armGood armBase armAligned armBounded
    have same : loaded' = loaded := Option.some.inj (hextract.symm.trans binding.1)
    subst loaded'
    refine ⟨loaded, binding, entry, ?_⟩
    unfold armResult
    rw [bytes]
    simp only [Option.bind_some, NativeBitwiseObject.to_fromUInt8,
      AArch64BitwiseFunction.function_success, Option.map_some]
    rw [AArch64BitwiseFunction.result_u32 d.op
      { armState with pc := BitVec.ofNat 64 armBase } left right armLeft armRight]
    simp
  · obtain ⟨loaded, binding⟩ := NativeBitwiseObject.accepted_named_body rvGood
    obtain ⟨loaded', hextract, _, entry, bytes⟩ :=
      NativeBitwiseObject.named_load rvGood rvBase rvAligned rvBounded
    have same : loaded' = loaded := Option.some.inj (hextract.symm.trans binding.1)
    subst loaded'
    refine ⟨loaded, binding, entry, ?_⟩
    unfold rvResult
    rw [bytes]
    exact RiscVFramedBitwise.all_input_result d.op left right
      (BitVec.ofNat 64 rvBase) caller memory mappedRW safe

end Oak.BitwiseSourceObjectParity
