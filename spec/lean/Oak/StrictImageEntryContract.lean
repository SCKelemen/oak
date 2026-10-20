import Oak.BitwiseSourceImageParity

/-!
# Pure evidence for the existing RV64 ELF-entry admission boundary

These are projections of the original strict source/full-image check, not a
second checker, an alternate artifact profile, or an execution theorem.
`entry_preconditions` is stated directly in the existing parser, framed-byte
and MinimalELF terms used by OakSailEntrySource.acceptsEntry. Stack placement
remains an explicit initial-state choice; no stack, platform, CSR or timer
initialization follows from an ELF file. The external Sail-importing adapter
must be checked in its own single-version kernel before any execution claim.
-/
set_option autoImplicit false
namespace Oak.StrictImageEntryContract
open Oak.MinimalELF (Bytes segment slice admittedBytes loadBytes)
open Oak.NativeBitwiseObject (fromUInt8)
open Oak.NativeBitwiseImage (StrictProfile)

/-- The entry, load range and offsets are decoded from this same strict image. -/
theorem strict_segment {name image : Bytes} (h : StrictProfile .rv64 name image) :
    segment image = ⟨65536, 4096, 65536, 64, 64, 5, 4096⟩ := h.2.1.1

/-- The actual sixteen-byte startup is wholly loaded at this image's e_entry. -/
theorem strict_startup {name image : Bytes} (h : StrictProfile .rv64 name image) :
    admittedBytes .rv64 image (segment image).entry
      (Oak.NativeBitwiseImage.startup .rv64) = true := by
  have ha := Oak.NativeBitwiseImage.profile_admitted h
  have bytes := h.2.2.2.2.2.2.2.2.2.2.1
  apply (Oak.MinimalELF.admitted_body .rv64 _ _ _).mpr
  refine ⟨((Oak.MinimalELF.admitted_iff .rv64 image).mp ha).1,
    ((Oak.MinimalELF.admitted_iff .rv64 image).mp ha).2, ?_⟩
  rw [Oak.MinimalELF.BodyAt, strict_segment h]
  simpa [Oak.NativeBitwiseImage.startup, Oak.NativeBitwiseImage.textOffset,
    Oak.NativeBitwiseImage.stubSize] using bytes

/-- Exactly the eight AUIPC/JALR bytes consumed by the existing entry proof.
They are selected from the admitted full startup, never supplied by a caller. -/
theorem strict_call_prefix {name image : Bytes} (h : StrictProfile .rv64 name image) :
    admittedBytes .rv64 image (segment image).entry
      [0x97, 0, 0, 0, 0xe7, 0x80, 0, 1] = true := by
  obtain ⟨hh, hl, hb⟩ :=
    (Oak.MinimalELF.admitted_body .rv64 _ _ _).mp (strict_startup h)
  have bytes := congrArg (List.take 8) hb.2.2.2.2
  simp only [slice, List.take_take] at bytes
  apply (Oak.MinimalELF.admitted_body .rv64 _ _ _).mpr
  refine ⟨hh, hl, ?_⟩
  rw [Oak.MinimalELF.BodyAt, strict_segment h]
  simpa [Oak.NativeBitwiseImage.startup, slice, strict_segment h] using bytes

/-- Full source identity and decoded function ownership are retained using the
existing ImageBinding, with the added body=e_entry+16 and startup facts. -/
theorem source_entry_binding {source wasm : List UInt8} {arm image : Bytes}
    {d : Oak.BitwiseSource.Decl}
    (checked : Oak.BitwiseSourceImageParity.check source wasm arm image = some d) :
    Oak.BitwiseSource.parse source = some d ∧
    source = Oak.BitwiseSource.render d ∧ Oak.BitwiseSource.Grammar source d ∧
    ∃ loaded, Oak.BitwiseSourceImageParity.ImageBinding .rv64 (fromUInt8 d.name) image
        (Oak.RiscVFramedBitwise.functionBytes d.op) loaded ∧
      segment image = ⟨65536, 4096, 65536, 64, 64, 5, 4096⟩ ∧
      loaded.address = (segment image).entry + 16 ∧
      admittedBytes .rv64 image (segment image).entry
        (Oak.NativeBitwiseImage.startup .rv64) = true ∧
      loadBytes image (segment image).entry 16 =
        some (Oak.NativeBitwiseImage.startup .rv64) := by
  obtain ⟨parsed, rendered, grammar, _, loaded, binding⟩ :=
    Oak.BitwiseSourceImageParity.accepted_source_image_binding checked
  have startup := strict_startup binding.profile
  refine ⟨parsed, rendered, grammar, loaded, binding, strict_segment binding.profile,
    ?_, startup, ?_⟩
  · rw [binding.address_eq, strict_segment binding.profile]
    rfl
  · exact Oak.MinimalELF.admitted_load startup

/-- Direct input facts for the existing Sail entry consumer. The final five
conjuncts are precisely the existing ImageLayout expression, not a new predicate.
The only added premises choose an aligned, low-RAM, disjoint initial stack.
Platform/ABI register/clock premises of the execution theorem remain untouched. -/
theorem entry_preconditions {source wasm : List UInt8} {arm image : Bytes}
    {d : Oak.BitwiseSource.Decl} {sp : Nat}
    (checked : Oak.BitwiseSourceImageParity.check source wasm arm image = some d)
    (stack_lower : 96 ≤ sp) (stack_upper : sp ≤ 0x02000000)
    (stack_aligned : sp % 16 = 0)
    (stack_separate : 65600 ≤ sp - 96 ∨ sp ≤ 65536) :
    Oak.BitwiseSource.parse source = some d ∧
    Oak.RiscVFramedBitwise.accepts .rv64 .lp64d [32, 32] 32 d.op
      (Oak.RiscVFramedBitwise.functionBytes d.op) = true ∧
    admittedBytes .rv64 image ((segment image).entry + 16)
      (Oak.RiscVFramedBitwise.functionBytes d.op) = true ∧
    admittedBytes .rv64 image (segment image).entry
      [0x97, 0, 0, 0, 0xe7, 0x80, 0, 1] = true ∧
    (segment image).vaddr + (segment image).fileSize ≤ 0x02000000 ∧
    96 ≤ sp ∧ sp ≤ 0x02000000 ∧ sp % 16 = 0 ∧
    ((segment image).vaddr + (segment image).fileSize ≤ sp - 96 ∨
      sp ≤ (segment image).vaddr) := by
  obtain ⟨parsed, _, _, loaded, binding, hs, address, _, _⟩ := source_entry_binding checked
  refine ⟨parsed, ?_, ?_, strict_call_prefix binding.profile, ?_,
    stack_lower, stack_upper, stack_aligned, ?_⟩
  · exact (Oak.RiscVFramedBitwise.accepts_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl, rfl, rfl⟩
  · rw [← address]
    exact binding.admitted
  · rw [hs]
    decide
  · simpa only [hs] using stack_separate

/-- Startup and the entire body are disjoint from every byte in the chosen
96-byte frame. This is a numerical consequence of whole-segment separation. -/
theorem entry_stack_disjoint {source wasm : List UInt8} {arm image : Bytes}
    {d : Oak.BitwiseSource.Decl} {sp : Nat}
    (checked : Oak.BitwiseSourceImageParity.check source wasm arm image = some d)
    (stack_lower : 96 ≤ sp)
    (stack_separate : 65600 ≤ sp - 96 ∨ sp ≤ 65536) :
    (∀ i j : Nat, i < 16 → j < 96 → (segment image).entry + i ≠ sp - 96 + j) ∧
    (∀ i j : Nat, i < 36 → j < 96 → (segment image).entry + 16 + i ≠ sp - 96 + j) := by
  obtain ⟨_, _, _, _, _, hs, _⟩ := source_entry_binding checked
  rw [hs]
  constructor <;> intro i j hi hj <;> dsimp <;> omega

/-- The load range and selected initial frame cannot wrap a 64-bit address. -/
theorem entry_bounds {source wasm : List UInt8} {arm image : Bytes}
    {d : Oak.BitwiseSource.Decl} {sp : Nat}
    (checked : Oak.BitwiseSourceImageParity.check source wasm arm image = some d)
    (stack_lower : 96 ≤ sp) (stack_upper : sp ≤ 0x02000000) :
    (segment image).fileOffset + (segment image).fileSize ≤ image.length ∧
    (segment image).vaddr + (segment image).fileSize < 2^64 ∧
    (segment image).entry % 4 = 0 ∧
    (segment image).entry + 16 + 36 < 2^64 ∧
    sp - 96 + 96 = sp ∧ sp < 2^64 := by
  obtain ⟨_, _, _, loaded, binding, hs, _⟩ := source_entry_binding checked
  have layout := ((Oak.MinimalELF.admitted_body .rv64 _ _ _).mp binding.admitted).2.1
  refine ⟨layout.2.2.2.2.2.2.2.1, ?_⟩
  rw [hs]
  dsimp
  omega

end Oak.StrictImageEntryContract
