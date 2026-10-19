import Oak.LRATNativeRefinement
import Oak.ObjectRelocation

/-! Ordinary BL call transfer into the pinned ARM64 guard bodies in the
no-fault scalar projection. Argument-producing loads, caller control flow,
fetch, alignment/translation faults and complete Sail execution are excluded. -/
set_option autoImplicit false
namespace Oak.LRATARM64GuardCalls
open Oak.LRATARM64Bytes
open Oak.AArch64BitwiseFunction (readW)

/-- BL writes X30 with the sequential continuation and preserves arguments,
SP and flags. The signed imm26 byte displacement reuses relocation decoding. -/
def transfer (word : BitVec 32) (s : State) : State :=
  { s with pc := s.pc + BitVec.ofInt 64 (Oak.ObjectRelocation.decodeBranch26 word)
           regs := fun r => if r = 30#5 then s.pc + 4 else s.regs r }

def enter (word : BitVec 32) (s : State) : Option State :=
  if word &&& 0xfc000000#32 = 0x94000000#32 then some (transfer word s) else none

theorem enter_eq (word : BitVec 32) (s : State)
    (shape : word &&& 0xfc000000#32 = 0x94000000#32) :
    enter word s = some (transfer word s) := by simp [enter, shape]

theorem transfer_arguments (word : BitVec 32) (s : State) :
    readW (transfer word s).regs 0 = readW s.regs 0 ∧
    readW (transfer word s).regs 1 = readW s.regs 1 ∧
    readW (transfer word s).regs 2 = readW s.regs 2 := by
  simp [transfer, readW]

private theorem bind_map {α β γ : Type} (f : α → Option β) (g : β → γ)
    (entry : Option α) (s : α) (value : γ)
    (he : entry = some s) (hf : (f s).map g = some value) :
    (entry.bind f).map g = some value := by
  rw [he]
  exact hf

private theorem decoded_map {α : Type} (bytes : List (BitVec 8))
    (words : List (BitVec 32)) (s : State) (g : State → α) (v : α)
    (hd : Oak.LRATRV64Bytes.decodeWords bytes = some words)
    (hr : (run words s).map g = some v) :
    (executeBytes bytes s).map g = some v := by
  unfold executeBytes
  simp only [hd, Option.bind_some]
  exact hr

def fitsCall (word : BitVec 32) (s : State) : Option State :=
  (enter word s).bind (executeBytes fitsBytes)

theorem fits_result (word : BitVec 32) (s : State)
    (shape : word &&& 0xfc000000#32 = 0x94000000#32) :
    (fitsCall word s).map (fun out => out.regs 0) =
      some (bit (Oak.LRATNativeGuards.armFits (readW s.regs 0) (readW s.regs 1) (readW s.regs 2))) := by
  have h := fits_bytes_result (transfer word s)
  simp only [(transfer_arguments word s).1, (transfer_arguments word s).2.1,
    (transfer_arguments word s).2.2] at h
  exact bind_map _ _ _ _ _ (enter_eq word s shape) h

theorem fits_return (word : BitVec 32) (s : State)
    (shape : word &&& 0xfc000000#32 = 0x94000000#32) :
    (fitsCall word s).map State.pc = some (s.pc + 4) := by
  have h := decoded_map fitsBytes fitsWords (transfer word s) State.pc _
    decode_fits (Oak.LRATARM64Bytes.fits_return (transfer word s))
  simp only [transfer] at h
  exact bind_map _ _ _ _ _ (enter_eq word s shape) h

theorem fits_sp (word : BitVec 32) (s : State)
    (shape : word &&& 0xfc000000#32 = 0x94000000#32) :
    (fitsCall word s).map State.sp = some s.sp := by
  exact bind_map _ _ _ _ _ (enter_eq word s shape)
    (decoded_map fitsBytes fitsWords (transfer word s) State.sp _
      decode_fits (Oak.LRATARM64Bytes.fits_sp (transfer word s)))

theorem fits_refines (word : BitVec 32) (s : State) (fuel : Nat)
    (shape : word &&& 0xfc000000#32 = 0x94000000#32) :
    (fitsCall word s).map (fun out => out.regs 0) =
      (Oak.LRATBounds.lrat_fits (UInt32.ofBitVec (readW s.regs 0)) (UInt32.ofBitVec (readW s.regs 1)) (UInt32.ofBitVec (readW s.regs 2)) fuel).map bit :=
  fits_result word s shape

def allocCall (word : BitVec 32) (s : State) : Option State :=
  (enter word s).bind (executeBytes allocBytes)

theorem alloc_result (word : BitVec 32) (s : State)
    (shape : word &&& 0xfc000000#32 = 0x94000000#32) :
    (allocCall word s).map (fun out => out.regs 0) =
      some (bit (Oak.LRATNativeGuards.armAlloc (readW s.regs 0))) := by
  have h := alloc_bytes_result (transfer word s)
  simp only [(transfer_arguments word s).1] at h
  exact bind_map _ _ _ _ _ (enter_eq word s shape) h

theorem alloc_return (word : BitVec 32) (s : State)
    (shape : word &&& 0xfc000000#32 = 0x94000000#32) :
    (allocCall word s).map State.pc = some (s.pc + 4) := by
  have h := decoded_map allocBytes allocWords (transfer word s) State.pc _
    decode_alloc (Oak.LRATARM64Bytes.alloc_return (transfer word s))
  simp only [transfer] at h
  exact bind_map _ _ _ _ _ (enter_eq word s shape) h

theorem alloc_sp (word : BitVec 32) (s : State)
    (shape : word &&& 0xfc000000#32 = 0x94000000#32) :
    (allocCall word s).map State.sp = some s.sp := by
  exact bind_map _ _ _ _ _ (enter_eq word s shape)
    (decoded_map allocBytes allocWords (transfer word s) State.sp _
      decode_alloc (Oak.LRATARM64Bytes.alloc_sp (transfer word s)))

theorem alloc_refines (word : BitVec 32) (s : State) (fuel : Nat)
    (shape : word &&& 0xfc000000#32 = 0x94000000#32) :
    (allocCall word s).map (fun out => out.regs 0) =
      (Oak.LRATBounds.lrat_alloc_fits (UInt32.ofBitVec (readW s.regs 0)) fuel).map bit :=
  alloc_result word s shape

end Oak.LRATARM64GuardCalls
