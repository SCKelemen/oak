import Oak.NativeBitwiseEnvelopeTotal

/-! Kernel-only controls for outer refusals, real short-circuit termination,
startup inversion, wrong extents, capacity failure, and zero fuel. -/
set_option autoImplicit false
set_option maxRecDepth 16384
namespace Oak.BitwiseELFProducer.TotalControls
open Oak.NativeBitwiseEnvelope
open Oak.MinimalELF (Machine)

theorem unsupported_arch (dst text name : Array UInt8) (arch : UInt32) (fuel : Nat)
    (h1 : arch ≠ 1) (h2 : arch ≠ 2) :
    native_bitwise_elf_image dst text arch name fuel = some (0, dst) := by
  apply image_refuses_outer
  simp [h1,h2]

theorem empty_name (dst text : Array UInt8) (arch : UInt32) (fuel : Nat) :
    native_bitwise_elf_image dst text arch #[] fuel = some (0, dst) := by
  apply image_refuses_outer
  simp

theorem oversized_name (dst text : Array UInt8) (arch : UInt32) (fuel : Nat) :
    native_bitwise_elf_image dst text arch (Array.replicate 257 65) fuel = some (0, dst) := by
  apply image_refuses_outer
  have h : decide ((257 : UInt32) ≤ 256) = false := by decide +kernel
  change (((arch == 1 || arch == 2) && decide ((257 : UInt32) > 0)) &&
    decide ((257 : UInt32) ≤ 256)) = false
  rw [h, Bool.and_false]

theorem maximal_ascii_name :
    native_bitwise_elf_image.loop1 (Array.replicate 256 127) true 0 257 = some (true,256) := by
  apply name_scan_exact _ 257 (by decide) _ (by decide)
  intro b hb
  simp only [Array.toList_replicate, List.mem_replicate] at hb
  rcases hb with ⟨_,rfl⟩
  decide

/-- Invalid bytes are detected before reaching the end, and the increment is real. -/
theorem first_invalid_byte :
    native_bitwise_elf_image.loop1 #[0,65,65] true 0 4 = some (false,1) := by decide +kernel

theorem last_invalid_byte :
    native_bitwise_elf_image.loop1 #[65,65,128] true 0 4 = some (false,3) := by decide +kernel

theorem initial_false_short_circuit :
    native_bitwise_elf_image.loop1 #[65,65,65] false 0 1 = some (false,0) := by decide +kernel

theorem zero_scan_fuel (name : Array UInt8) (ok : Bool) (i : UInt32) :
    native_bitwise_elf_image.loop1 name ok i 0 = none := rfl

/-- The full writer's byte refusal preserves an arbitrary caller buffer. -/
theorem zero_name_byte (dst text : Array UInt8) (arch : UInt32) (fuel : Nat)
    (hd : dst.size < 2^32) (ht : text.size < 2^32) (hf : 4929 ≤ fuel) :
    native_bitwise_elf_image dst text arch #[0] fuel = some (0,dst) := by
  apply image_refusal_exact dst text #[0] arch fuel hd ht (by decide) hf
  rintro ⟨m,_,he⟩
  have hb := he.1.2.2 0 (by simp)
  exact (by decide : ¬(0 < (0 : UInt8))) hb.1

/-- Reject all wrong text lengths before startup reads, without an assumed prefix. -/
theorem wrong_text_extent (m : Machine) (dst text name : Array UInt8) (fuel : Nat)
    (hd : dst.size < 2^32) (ht : text.size < 2^32) (hn : name.size < 2^32)
    (hf : 4929 ≤ fuel) (hlen : text.size ≠ Oak.NativeBitwiseImage.textSize m) :
    native_bitwise_elf_image dst text (archTag m) name fuel = some (0,dst) := by
  rw [image_total_machine m dst text name fuel hd ht hn hf]
  have he : ¬Eligible m dst text name := by intro he; exact hlen he.2.1
  rw [if_neg he]

/-- Full in-range byte extents with a false startup are still refused. -/
theorem zero_startup (m : Machine) (dst name : Array UInt8) (fuel : Nat)
    (hd : dst.size < 2^32) (hn : name.size < 2^32) (hf : 4929 ≤ fuel) :
    native_bitwise_elf_image dst (Array.replicate (Oak.NativeBitwiseImage.textSize m) 0)
      (archTag m) name fuel = some (0,dst) := by
  have ht : (Array.replicate (Oak.NativeBitwiseImage.textSize m) (0 : UInt8)).size < 2^32 := by
    cases m <;> decide
  rw [image_total_machine m dst _ name fuel hd ht hn hf]
  have hp : ¬StartupValid m (Array.replicate (Oak.NativeBitwiseImage.textSize m) 0) := by
    cases m <;> decide +kernel
  have he : ¬Eligible m dst (Array.replicate (Oak.NativeBitwiseImage.textSize m) 0) name := by
    intro he; exact hp he.2.2.1
  rw [if_neg he]

theorem short_capacity (m : Machine) (dst text name : Array UInt8) (fuel : Nat)
    (hd : dst.size < 2^32) (ht : text.size < 2^32) (hn : name.size < 2^32)
    (hf : 4929 ≤ fuel) (hcap : ¬Capacity m dst name) :
    native_bitwise_elf_image dst text (archTag m) name fuel = some (0,dst) := by
  rw [image_total_machine m dst text name fuel hd ht hn hf]
  have he : ¬Eligible m dst text name := by intro he; exact hcap he.2.2.2
  rw [if_neg he]

end Oak.BitwiseELFProducer.TotalControls
