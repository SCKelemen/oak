import Oak.MinimalELF
import OakSailFetchedFrame

/-! An explicit flat image loader into the pinned sequential Sail byte map.
This is a specification of loading, not a verification of firmware or an OS.
The checked single RX segment supplies both bytes and the installed code PMA.
A separate RW, non-executable 96-byte stack is chosen by the invocation. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
noncomputable section
namespace OakSailImageLoad
open LeanRV64D LeanRV64D.Functions
open OakSailBridge.BitwiseDecoded OakSailFetchedCode
open Oak.MinimalELF

/-- Copy all supplied bytes at natural addresses. Only RAM changes. -/
def copyBytes (s : State) (base : Nat) : Bytes → State
  | [] => s
  | b :: bs => setByte (copyBytes s (base + 1) bs) base b

@[simp] theorem copyBytes_regs (s : State) (base : Nat) (bytes : Bytes) :
    (copyBytes s base bytes).regs = s.regs := by
  induction bytes generalizing base with
  | nil => rfl
  | cons b bs ih => exact ih (base + 1)

theorem copyBytes_at (s : State) (base : Nat) (bytes : Bytes) :
    BytesAt (copyBytes s base bytes) base bytes := by
  induction bytes generalizing base with
  | nil => intro i; exact Fin.elim0 i
  | cons b bs ih =>
    intro i
    cases i with
    | mk i hi =>
      cases i with
      | zero => simp [copyBytes, setByte, Std.ExtHashMap.getElem?_insert]
      | succ i =>
        have hi' : i < bs.length := by simpa using hi
        have h := ih (base+1) ⟨i, hi'⟩
        simpa [copyBytes, setByte, Std.ExtHashMap.getElem?_insert, Nat.add_assoc,
          Nat.add_comm, Nat.add_left_comm] using h

theorem copyBytes_other (s : State) (base query : Nat) (bytes : Bytes)
    (h : query < base ∨ base + bytes.length ≤ query) :
    (copyBytes s base bytes).mem.get? query = s.mem.get? query := by
  induction bytes generalizing base with
  | nil => rfl
  | cons b bs ih =>
    have hne : base ≠ query := by simp only [List.length_cons] at h; omega
    have ht : query < base + 1 ∨ base + 1 + bs.length ≤ query := by
      simp only [List.length_cons] at h; omega
    simpa [copyBytes, setByte, Std.ExtHashMap.getElem?_insert, hne] using ih (base+1) ht

/-- The two regions have independent RX/RW attributes; stack execution is off. -/
def imageRegion (image : Bytes) : PMA_Region :=
  { base := BitVec.ofNat 64 (segment image).vaddr,
    size := BitVec.ofNat 64 (segment image).fileSize,
    attributes := { (default : PMA) with readable := true, writable := false, executable := true },
    include_in_device_tree := false }

def stackRegion (sp : Nat) : PMA_Region :=
  { base := BitVec.ofNat 64 (sp - 96), size := 96#64,
    attributes := { (default : PMA) with readable := true, writable := true, executable := false },
    include_in_device_tree := false }

def imageRegions (image : Bytes) (sp : Nat) : List PMA_Region :=
  [imageRegion image, stackRegion sp]

/-- Whole-segment loading and explicit PMA installation. This operation does
not initialize registers, CSRs, clocks, PC, or invoke an ELF entry point. -/
def installImage (s : State) (image : Bytes) (sp : Nat) : State :=
  setRegister (copyBytes s (segment image).vaddr
    (slice image (segment image).fileOffset (segment image).fileSize))
    Register.pma_regions (imageRegions image sp)

/-- Numeric, decidable placement constraints, independent of memory contents
and execution outcomes. The entire code segment and stack frame are disjoint. -/
def ImageLayout (image : Bytes) (sp : Nat) : Prop :=
  (segment image).vaddr + (segment image).fileSize ≤ 0x02000000 ∧
  96 ≤ sp ∧ sp ≤ 0x02000000 ∧ sp % 16 = 0 ∧
  ((segment image).vaddr + (segment image).fileSize ≤ sp - 96 ∨
    sp ≤ (segment image).vaddr)
instance (image : Bytes) (sp : Nat) : Decidable (ImageLayout image sp) :=
  inferInstanceAs (Decidable (_ ∧ _))

def acceptsImage (image : Bytes) (address sp : Nat) (body : Bytes) : Bool :=
  admittedBytes .rv64 image address body && decide (ImageLayout image sp)

theorem acceptsImage_iff (image : Bytes) (address sp : Nat) (body : Bytes) :
    acceptsImage image address sp body = true ↔
      admittedBytes .rv64 image address body = true ∧ ImageLayout image sp := by
  simp [acceptsImage]

/-- A checked loader interface. Invalid file, placement, or stack profiles do
not modify state and return no loaded state. The copy is an explicit flat
loader specification, not the behavior of an unverified host loader. -/
def checkedLoad (s : State) (image : Bytes) (address sp : Nat) (body : Bytes) : Option State :=
  if acceptsImage image address sp body then some (installImage s image sp) else none

theorem checkedLoad_success (s : State) (image : Bytes) (address sp : Nat) (body : Bytes)
    (h : acceptsImage image address sp body = true) :
    checkedLoad s image address sp body = some (installImage s image sp) := by
  simp [checkedLoad, h]

theorem checkedLoad_reject (s : State) (image : Bytes) (address sp : Nat) (body : Bytes)
    (h : acceptsImage image address sp body = false) :
    checkedLoad s image address sp body = none := by
  simp [checkedLoad, h]

/-- Every file-backed byte of the segment is copied, including startup and
padding outside the particular function body checked by admission. -/
theorem loaded_segment (s : State) (image : Bytes) (sp : Nat) :
    BytesAt (installImage s image sp) (segment image).vaddr
      (slice image (segment image).fileOffset (segment image).fileSize) :=
  copyBytes_at s _ _

theorem loaded_body (s : State) (image : Bytes) (address sp : Nat) (body : Bytes)
    (h : admittedBytes .rv64 image address body = true) :
    BytesAt (installImage s image sp) address body := by
  obtain ⟨_, hl, hb⟩ := (admitted_body .rv64 image address body).mp h
  rcases hl with ⟨_, _, _, _, _, _, _, hf, _, _⟩
  rcases hb with ⟨_, _, hlow, hhigh, heq⟩
  intro i
  have hi := i.isLt
  have hlen : (slice image (segment image).fileOffset (segment image).fileSize).length =
      (segment image).fileSize := by simp [slice, List.length_take, List.length_drop]; omega
  have hoff : address - (segment image).vaddr + i.val <
      (slice image (segment image).fileOffset (segment image).fileSize).length := by
    rw [hlen]; omega
  have hc := copyBytes_at s (segment image).vaddr
    (slice image (segment image).fileOffset (segment image).fileSize)
    ⟨address - (segment image).vaddr + i.val, hoff⟩
  have haddr : (segment image).vaddr + (address - (segment image).vaddr + i.val) =
      address + i.val := by omega
  have hbbyte := congrArg (fun xs : Bytes => xs[i.val]?) heq
  have hfi : (segment image).fileOffset + (address - (segment image).vaddr) + i.val <
      image.length := by omega
  simp only [slice, List.getElem?_take, hi, decide_true, ite_true, List.getElem?_drop,
    List.getElem?_eq_getElem hfi, List.getElem?_eq_getElem hi] at hbbyte
  have hidx : (segment image).fileOffset + (address - (segment image).vaddr + i.val) =
      (segment image).fileOffset + (address - (segment image).vaddr) + i.val := by omega
  simp only [haddr, slice, List.getElem_take, List.getElem_drop, hidx] at hc
  exact hc.trans hbbyte

theorem loaded_memory_other (s : State) (image : Bytes) (sp query : Nat)
    (h : query < (segment image).vaddr ∨
      (segment image).vaddr + (segment image).fileSize ≤ query) :
    (installImage s image sp).mem.get? query = s.mem.get? query := by
  apply copyBytes_other
  have hlen : (slice image (segment image).fileOffset (segment image).fileSize).length ≤
      (segment image).fileSize := by simp only [slice, List.length_take]; exact Nat.min_le_left _ _
  omega

@[simp] theorem loaded_register_other (s : State) (image : Bytes) (sp : Nat)
    (r : Register) (h : r ≠ Register.pma_regions) :
    (installImage s image sp).regs.get? r = s.regs.get? r := by
  simp [installImage, setRegister, Std.ExtDHashMap.get?_insert, Ne.symm h]

theorem loaded_regions (s : State) (image : Bytes) (sp : Nat) :
    (installImage s image sp).regs.get? Register.pma_regions = some (imageRegions image sp) := by
  simp [installImage, setRegister, Std.ExtDHashMap.get?_insert]

theorem range_contained (a width b n : Nat) (ha : b ≤ a) (hab : a + width ≤ b + n)
    (hb : b+n < 2^64) :
    range_subset (BitVec.ofNat 64 a) (BitVec.ofNat 64 width)
      (BitVec.ofNat 64 b) (BitVec.ofNat 64 n) = true := by
  have hb' : b < 2^64 := by omega
  have hn : n < 2^64 := by omega
  have ha' : a < 2^64 := by omega
  have hw : width < 2^64 := by omega
  have haend : a + width < 2^64 := by omega
  have hbend : b ≤ a + width := by omega
  have hdiff : a - b < 2^64 := by omega
  have hdiffend : a + width - b < 2^64 := by omega
  simp only [range_subset, ← BitVec.ofNat_add,
    BitVec.ofNat_sub_ofNat_of_le _ _ hb' ha,
    BitVec.ofNat_sub_ofNat_of_le _ _ hb' hbend,
    BitVec.ofNat_sub_ofNat_of_le _ _ hb' (Nat.le_add_right b n),
    Nat.add_sub_cancel_left, zopz0zIzJ_u, Sail.BitVec.toNatInt,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hdiff,
    Nat.mod_eq_of_lt hdiffend]
  simp
  omega

theorem aligned_paddr (addr : BitVec 64) (width : Nat) (h : addr.toNat % width = 0) :
    is_aligned_paddr (.Physaddr addr) width = true := by
  simp [is_aligned_paddr, Sail.BitVec.toNatInt, ← Int.ofNat_tmod, h]
theorem range_disjoint (a width b n : Nat) (hwidth : 0 < width)
    (ha : a+width < 2^64) (hb : b+n < 2^64)
    (hsep : a+width ≤ b ∨ b+n ≤ a) :
    range_subset (BitVec.ofNat 64 a) (BitVec.ofNat 64 width)
      (BitVec.ofNat 64 b) (BitVec.ofNat 64 n) = false := by
  have hb' : b < 2^64 := by omega
  have hn : n < 2^64 := by omega
  have ha' : a < 2^64 := by omega
  have hw : width < 2^64 := by omega
  simp only [range_subset, ← BitVec.ofNat_add,
    BitVec.ofNat_sub_ofNat_of_le _ _ hb' (Nat.le_add_right b n),
    Nat.add_sub_cancel_left, zopz0zIzJ_u, Sail.BitVec.toNatInt,
    BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn,
    Nat.mod_eq_of_lt ha', Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb']
  simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not, Int.not_le]
  simp only [Int.ofNat_eq_natCast]
  omega

theorem image_region_matches (image : Bytes) (sp address : Nat)
    (h : (segment image).vaddr ≤ address)
    (he : address + 4 ≤ (segment image).vaddr + (segment image).fileSize)
    (hb : (segment image).vaddr + (segment image).fileSize < 2^64) :
    matching_pma_region (imageRegions image sp) (.Physaddr (BitVec.ofNat 64 address)) 4 =
      some (imageRegion image) := by
  have hr := range_contained address 4 (segment image).vaddr (segment image).fileSize h he hb
  simp [matching_pma_region, matching_pma_region_bits_range, imageRegions, imageRegion,
    zero_extend, Sail.BitVec.zeroExtend, bits_of_physaddr, to_bits, Sail.get_slice_int, hr]


theorem stack_region_matches (image : Bytes) (sp address : Nat)
    (hl : ImageLayout image sp) (h : sp - 96 ≤ address) (he : address + 8 ≤ sp) :
    matching_pma_region (imageRegions image sp) (.Physaddr (BitVec.ofNat 64 address)) 8 =
      some (stackRegion sp) := by
  rcases hl with ⟨hcode, hsp, hspend, _, hsep⟩
  have hr := range_contained address 8 (sp-96) 96 h (by omega) (by omega)
  have hn := range_disjoint address 8 (segment image).vaddr (segment image).fileSize
    (by omega) (by omega) (by omega) (by omega)
  simp [matching_pma_region, matching_pma_region_bits_range, imageRegions, imageRegion,
    stackRegion, zero_extend, Sail.BitVec.zeroExtend, bits_of_physaddr, to_bits,
    Sail.get_slice_int, hr, hn]

theorem frame_code (s : State) (image : Bytes) (address sp : Nat) (op : Oak.BitwiseFunction.Op)
    (h : acceptsImage image address sp (Oak.RiscVFramedBitwise.functionBytes op) = true) :
    FrameCodeAt (installImage s image sp) (BitVec.ofNat 64 address) op := by
  have ha := (acceptsImage_iff _ _ _ _).mp h
  have hb := (admitted_body .rv64 _ _ _).mp ha.1
  have hlen : (Oak.RiscVFramedBitwise.functionBytes op).length = 36 := by cases op <;> rfl
  have hbound := (admitted_bounds ha.1).2
  rw [hlen] at hbound
  have haddr : address < 2^64 := by omega
  simp only [FrameCodeAt, BitVec.toNat_ofNat, Nat.mod_eq_of_lt haddr]
  exact ⟨loaded_body s image address sp _ ha.1, hb.2.2.2.1, by omega⟩

theorem executable_frame (image : Bytes) (address sp : Nat) (op : Oak.BitwiseFunction.Op)
    (h : acceptsImage image address sp (Oak.RiscVFramedBitwise.functionBytes op) = true)
    (i : Fin 9) :
    ExecutableRegion (imageRegions image sp) (codePC (BitVec.ofNat 64 address) i)
      (imageRegion image) ∧ LowCodeRAM (codePC (BitVec.ofNat 64 address) i) := by
  have ha := (acceptsImage_iff _ _ _ _).mp h
  obtain ⟨_, hl, hb⟩ := (admitted_body .rv64 _ _ _).mp ha.1
  have hlen : (Oak.RiscVFramedBitwise.functionBytes op).length = 36 := by cases op <;> rfl
  rcases hb with ⟨_, halign, hlow, hhigh, _⟩
  rw [hlen] at hhigh
  have hcode := ha.2.1
  have hi := i.isLt
  have haddr : address < 2^64 := by omega
  have hpc : codePC (BitVec.ofNat 64 address) i = BitVec.ofNat 64 (address + 4 * i.val) := by
    simp only [codePC, BitVec.ofNat_add]
  have hpcBound : address + 4 * i.val < 2^64 := by omega
  rw [hpc]
  constructor
  · refine ⟨image_region_matches image sp (address+4 * i.val) (by omega) (by omega) (by omega), rfl, ?_⟩
    apply aligned_paddr
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hpcBound]
    omega
  · unfold LowCodeRAM
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hpcBound]
    omega

theorem stack_bits (image : Bytes) (sp : Nat) (h : ImageLayout image sp) :
    BitVec.ofNat 64 sp - 96#64 = BitVec.ofNat 64 (sp-96) ∧
    BitVec.ofNat 64 sp - 96#64 + 8#64 = BitVec.ofNat 64 (sp-96+8) := by
  have hs := h.2.1
  have heq := BitVec.ofNat_sub_ofNat_of_le (w := 64) sp 96 (by decide) hs
  exact ⟨heq, by rw [heq]; simp only [BitVec.ofNat_add]⟩

theorem stack_access (image : Bytes) (sp : Nat) (h : ImageLayout image sp) :
    OakSailFramedComposition.FrameAccess (imageRegions image sp) (BitVec.ofNat 64 sp)
      (stackRegion sp) (stackRegion sp) := by
  have hsp := h.2.1
  have hend := h.2.2.1
  have halign := h.2.2.2.1
  have hs : sp < 2^64 := by omega
  have hb : sp-96 < 2^64 := by omega
  have hn : sp-96+8 < 2^64 := by omega
  have heq := stack_bits image sp h
  constructor
  · simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hs] using hsp
  · simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hs] using halign
  · rw [heq.1]
    refine ⟨stack_region_matches image sp (sp-96) h (by omega) (by omega), rfl, rfl, ?_⟩
    apply aligned_paddr
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb]
    omega
  · rw [heq.2]
    refine ⟨stack_region_matches image sp (sp-96+8) h (by omega) (by omega), rfl, rfl, ?_⟩
    apply aligned_paddr
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]
    omega
  · rw [heq.1]
    unfold LowRAM
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb]
    omega
  · rw [heq.2]
    unfold LowRAM
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]
    omega

theorem code_stack_disjoint (image : Bytes) (address sp : Nat) (op : Oak.BitwiseFunction.Op)
    (h : acceptsImage image address sp (Oak.RiscVFramedBitwise.functionBytes op) = true) :
    CodeStackDisjoint (BitVec.ofNat 64 address) (BitVec.ofNat 64 sp - 96#64) := by
  have ha := (acceptsImage_iff _ _ _ _).mp h
  obtain ⟨_, _, hb⟩ := (admitted_body .rv64 _ _ _).mp ha.1
  have hlen : (Oak.RiscVFramedBitwise.functionBytes op).length = 36 := by cases op <;> rfl
  rcases hb with ⟨_, _, hlow, hhigh, _⟩
  rw [hlen] at hhigh
  rcases ha.2 with ⟨hcode, hsp, hend, halign, hsep⟩
  have hl : ImageLayout image sp := ⟨hcode, hsp, hend, halign, hsep⟩
  have heq := stack_bits image sp hl
  have hc : address < 2^64 := by omega
  have hs : sp-96 < 2^64 := by omega
  have hn : sp-96+8 < 2^64 := by omega
  unfold CodeStackDisjoint
  rw [heq.2, heq.1]
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hc,
    Nat.mod_eq_of_lt hs, Nat.mod_eq_of_lt hn]
  omega

theorem copyBytes_nonregister_state (s : State) (base : Nat) (bytes : Bytes) :
    (copyBytes s base bytes).cycleCount = s.cycleCount ∧
    (copyBytes s base bytes).sailOutput = s.sailOutput ∧
    (copyBytes s base bytes).choiceState = s.choiceState ∧
    (copyBytes s base bytes).tags = s.tags := by
  induction bytes generalizing base with
  | nil => exact ⟨rfl, rfl, rfl, rfl⟩
  | cons b bs ih => exact ih (base+1)

theorem loaded_nonregister_state (s : State) (image : Bytes) (sp : Nat) :
    (installImage s image sp).cycleCount = s.cycleCount ∧
    (installImage s image sp).sailOutput = s.sailOutput ∧
    (installImage s image sp).choiceState = s.choiceState ∧
    (installImage s image sp).tags = s.tags :=
  copyBytes_nonregister_state s _ _

theorem loaded_memoryConfig (s : State) (image : Bytes) (sp : Nat)
    (previous : List PMA_Region) (h : MemoryConfig s previous) :
    MemoryConfig (installImage s image sp) (imageRegions image sp) := by
  rcases h with ⟨h1,h2,h3,h4,h5,h6,h7⟩
  constructor
  · simpa using h1
  · simpa using h2
  · simpa using h3
  · exact loaded_regions s image sp
  · simpa using h5
  · simpa using h6
  · simpa using h7

end OakSailImageLoad
