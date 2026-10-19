import Oak.LRATNativeRefinement

/-! RV64 call transfer into the pinned native guards. The caller's a0/a1/a2
values are preserved by the decoded AUIPC/JALR pair; the guard returns the
extracted predicate of those values to the call's continuation. Production
ELF tests bind the call words and destination to preflight guard symbols.
Argument preparation, memory/fetch/traps and whole-caller execution are not
modeled here. -/
set_option autoImplicit false
namespace Oak.LRATRV64GuardCalls
open Oak.RiscVCallExecution
open Oak.LRATNativeGuards
open Oak.LRATRV64Bytes (bit)

def enter (words : BitVec 32 × BitVec 32) (s : State) : Option State := do
  let first ← wide words.1 s
  wide words.2 first

theorem enter_eq (words : BitVec 32 × BitVec 32) (s : State)
    (shape : Oak.RV64Relocation.pairMatches true words.1 words.2 = true)
    (link : words.1.extractLsb' 7 5 = 1#5) :
    enter words s = some (executePatched true 1 words s) := by
  unfold enter
  rw [wide_pair true words.1 words.2 s shape, link]
  rfl

theorem enter_arguments (words : BitVec 32 × BitVec 32) (s : State) :
    read (executePatched true 1 words s) 10 = read s 10 ∧
    read (executePatched true 1 words s) 11 = read s 11 ∧
    read (executePatched true 1 words s) 12 = read s 12 := by
  simp [executePatched, pair, auipc, jalr, Oak.RiscVCallExecution.read, write]

private theorem bind_map {α β γ : Type} (f : α → Option β) (g : β → γ)
    (entry : Option α) (s : α) (value : γ)
    (he : entry = some s) (hf : (f s).map g = some value) :
    (entry.bind f).map g = some value := by
  rw [he]
  exact hf

namespace RV64
open Oak.LRATRV64Bytes

private theorem decoded_pc (bytes : List (BitVec 8)) (code : List (BitVec 32))
    (s : State) (v : X) (hd : decodeWords bytes = some code)
    (hr : (run code s).map State.pc = some v) :
    (executeBytes bytes s).map State.pc = some v := by
  unfold executeBytes
  simp only [hd, Option.bind_some]
  exact hr

def fitsCall (words : BitVec 32 × BitVec 32) (s : State) : Option State :=
  (enter words s).bind (executeBytes fitsBytes)

theorem fits_result (words : BitVec 32 × BitVec 32) (s : State)
    (shape : Oak.RV64Relocation.pairMatches true words.1 words.2 = true)
    (link : words.1.extractLsb' 7 5 = 1#5) :
    (fitsCall words s).map (fun out => read out 10) =
      some (bit (rvFits (read s 10) (read s 11) (read s 12))) := by
  have h := fits_bytes_result (executePatched true 1 words s)
  obtain ⟨ha, hb, hc⟩ := enter_arguments words s
  simp only [ha, hb, hc] at h
  exact bind_map _ _ _ _ _ (enter_eq words s shape link) h

theorem fits_return (words : BitVec 32 × BitVec 32) (s : State)
    (shape : Oak.RV64Relocation.pairMatches true words.1 words.2 = true)
    (link : words.1.extractLsb' 7 5 = 1#5) :
    (fitsCall words s).map State.pc = some (clearLow (s.pc + 8)) := by
  have h := decoded_pc fitsBytes fitsWords (executePatched true 1 words s)
    _ decode_fits (Oak.LRATRV64Bytes.fits_return (executePatched true 1 words s))
  have hl : (executePatched true 1 words s).regs 1 = s.pc + 8 :=
    pair_link s 1 (by decide) _ _
  simp only [Oak.RiscVCallExecution.read, hl] at h
  exact bind_map _ _ _ _ _ (enter_eq words s shape link) h

def allocCall (words : BitVec 32 × BitVec 32) (s : State) : Option State :=
  (enter words s).bind (executeBytes allocBytes)

theorem alloc_result (words : BitVec 32 × BitVec 32) (s : State)
    (shape : Oak.RV64Relocation.pairMatches true words.1 words.2 = true)
    (link : words.1.extractLsb' 7 5 = 1#5) :
    (allocCall words s).map (fun out => read out 10) =
      some (bit (rvAlloc (read s 10))) := by
  have h := alloc_bytes_result (executePatched true 1 words s)
  have ha := (enter_arguments words s).1
  simp only [ha] at h
  exact bind_map _ _ _ _ _ (enter_eq words s shape link) h

theorem alloc_return (words : BitVec 32 × BitVec 32) (s : State)
    (shape : Oak.RV64Relocation.pairMatches true words.1 words.2 = true)
    (link : words.1.extractLsb' 7 5 = 1#5) :
    (allocCall words s).map State.pc = some (clearLow (s.pc + 8)) := by
  have h := decoded_pc allocBytes allocWords (executePatched true 1 words s)
    _ decode_alloc (Oak.LRATRV64Bytes.alloc_return (executePatched true 1 words s))
  have hl : (executePatched true 1 words s).regs 1 = s.pc + 8 :=
    pair_link s 1 (by decide) _ _
  simp only [Oak.RiscVCallExecution.read, hl] at h
  exact bind_map _ _ _ _ _ (enter_eq words s shape link) h

/-- Complete extracted Boolean contract, including rejected inputs. -/
theorem fits_refines (words : BitVec 32 × BitVec 32) (s : State) (fuel : Nat)
    (shape : Oak.RV64Relocation.pairMatches true words.1 words.2 = true)
    (link : words.1.extractLsb' 7 5 = 1#5) :
    (fitsCall words s).map (fun out => read out 10) =
      (Oak.LRATBounds.lrat_fits (UInt32.ofBitVec ((read s 10).truncate 32)) (UInt32.ofBitVec ((read s 11).truncate 32)) (UInt32.ofBitVec ((read s 12).truncate 32)) fuel).map bit := by
  exact (fits_result words s shape link).trans (by
    rw [rv_fits_width]
    rfl)

/-- Complete extracted Boolean contract, including rejected inputs. -/
theorem alloc_refines (words : BitVec 32 × BitVec 32) (s : State) (fuel : Nat)
    (shape : Oak.RV64Relocation.pairMatches true words.1 words.2 = true)
    (link : words.1.extractLsb' 7 5 = 1#5) :
    (allocCall words s).map (fun out => read out 10) =
      (Oak.LRATBounds.lrat_alloc_fits (UInt32.ofBitVec ((read s 10).truncate 32)) fuel).map bit := by
  exact (alloc_result words s shape link).trans (by
    rw [rv_alloc_width]
    rfl)

end RV64

namespace RV64Compressed
open Oak.LRATRV64Compressed

private theorem decoded_pc (bytes : List (BitVec 8)) (code : List (Instruction))
    (s : State) (v : X) (hd : decode bytes = some code)
    (hr : (run code s).map State.pc = some v) :
    (executeBytes bytes s).map State.pc = some v := by
  unfold executeBytes
  simp only [hd, Option.bind_some]
  exact hr

def fitsCall (words : BitVec 32 × BitVec 32) (s : State) : Option State :=
  (enter words s).bind (executeBytes fitsBytes)

theorem fits_result (words : BitVec 32 × BitVec 32) (s : State)
    (shape : Oak.RV64Relocation.pairMatches true words.1 words.2 = true)
    (link : words.1.extractLsb' 7 5 = 1#5) :
    (fitsCall words s).map (fun out => read out 10) =
      some (bit (rvFits (read s 10) (read s 11) (read s 12))) := by
  have h := fits_bytes_result (executePatched true 1 words s)
  obtain ⟨ha, hb, hc⟩ := enter_arguments words s
  simp only [ha, hb, hc] at h
  exact bind_map _ _ _ _ _ (enter_eq words s shape link) h

theorem fits_return (words : BitVec 32 × BitVec 32) (s : State)
    (shape : Oak.RV64Relocation.pairMatches true words.1 words.2 = true)
    (link : words.1.extractLsb' 7 5 = 1#5) :
    (fitsCall words s).map State.pc = some (clearLow (s.pc + 8)) := by
  have h := decoded_pc fitsBytes fitsCode (executePatched true 1 words s)
    _ decode_fits (Oak.LRATRV64Compressed.fits_return (executePatched true 1 words s))
  have hl : (executePatched true 1 words s).regs 1 = s.pc + 8 :=
    pair_link s 1 (by decide) _ _
  simp only [Oak.RiscVCallExecution.read, hl] at h
  exact bind_map _ _ _ _ _ (enter_eq words s shape link) h

def allocCall (words : BitVec 32 × BitVec 32) (s : State) : Option State :=
  (enter words s).bind (executeBytes allocBytes)

theorem alloc_result (words : BitVec 32 × BitVec 32) (s : State)
    (shape : Oak.RV64Relocation.pairMatches true words.1 words.2 = true)
    (link : words.1.extractLsb' 7 5 = 1#5) :
    (allocCall words s).map (fun out => read out 10) =
      some (bit (rvAlloc (read s 10))) := by
  have h := alloc_bytes_result (executePatched true 1 words s)
  have ha := (enter_arguments words s).1
  simp only [ha] at h
  exact bind_map _ _ _ _ _ (enter_eq words s shape link) h

theorem alloc_return (words : BitVec 32 × BitVec 32) (s : State)
    (shape : Oak.RV64Relocation.pairMatches true words.1 words.2 = true)
    (link : words.1.extractLsb' 7 5 = 1#5) :
    (allocCall words s).map State.pc = some (clearLow (s.pc + 8)) := by
  have h := decoded_pc allocBytes allocCode (executePatched true 1 words s)
    _ decode_alloc (Oak.LRATRV64Compressed.alloc_return (executePatched true 1 words s))
  have hl : (executePatched true 1 words s).regs 1 = s.pc + 8 :=
    pair_link s 1 (by decide) _ _
  simp only [Oak.RiscVCallExecution.read, hl] at h
  exact bind_map _ _ _ _ _ (enter_eq words s shape link) h

/-- Complete extracted Boolean contract, including rejected inputs. -/
theorem fits_refines (words : BitVec 32 × BitVec 32) (s : State) (fuel : Nat)
    (shape : Oak.RV64Relocation.pairMatches true words.1 words.2 = true)
    (link : words.1.extractLsb' 7 5 = 1#5) :
    (fitsCall words s).map (fun out => read out 10) =
      (Oak.LRATBounds.lrat_fits (UInt32.ofBitVec ((read s 10).truncate 32)) (UInt32.ofBitVec ((read s 11).truncate 32)) (UInt32.ofBitVec ((read s 12).truncate 32)) fuel).map bit := by
  exact (fits_result words s shape link).trans (by
    rw [rv_fits_width]
    rfl)

/-- Complete extracted Boolean contract, including rejected inputs. -/
theorem alloc_refines (words : BitVec 32 × BitVec 32) (s : State) (fuel : Nat)
    (shape : Oak.RV64Relocation.pairMatches true words.1 words.2 = true)
    (link : words.1.extractLsb' 7 5 = 1#5) :
    (allocCall words s).map (fun out => read out 10) =
      (Oak.LRATBounds.lrat_alloc_fits (UInt32.ofBitVec ((read s 10).truncate 32)) fuel).map bit := by
  exact (alloc_result words s shape link).trans (by
    rw [rv_alloc_width]
    rfl)

end RV64Compressed

end Oak.LRATRV64GuardCalls
