import OakSailBridge.FramedMemoryExecution

/-! The actual Sail virtual-memory path for an aligned eight-byte stack
access in Machine/Bare mode. Conditional composition lemmas keep their
physical-memory premise explicit; the final frame proof must discharge it
with the concrete physical-memory and byte-primitive results. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
noncomputable section
namespace OakSailBridge.BitwiseDecoded
open LeanRV64D LeanRV64D.Functions Sail Sail.ConcurrencyInterfaceV1

theorem stack_addr_load_run (s : State) (sp offset : BitVec 64)
    (hx : s.regs.get? Register.x2 = some sp)
    (hp : s.regs.get? Register.cur_privilege = some Privilege.Machine)
    (hm : s.regs.get? Register.mstatus = some (0#64))
    (hc : s.regs.get? Register.mseccfg = some (0#64)) :
    (get_transformed_data_addr (.Regidx 2) offset (.Load .Data) 8).run s =
      .ok (.Ext_DataAddr_OK (.Virtaddr (sp + offset))) s := by
  unfold get_transformed_data_addr ext_data_get_addr
  simp only [read_x2, bind_assoc, pure_bind]
  rw [bind_run_ok _ _ (read_register s Register.x2 sp hx)]
  rw [bind_run_ok _ _ (transform_load_run s (sp + offset) hp hm hc)]
  rfl

theorem stack_addr_store_run (s : State) (sp offset : BitVec 64)
    (hx : s.regs.get? Register.x2 = some sp)
    (hp : s.regs.get? Register.cur_privilege = some Privilege.Machine)
    (hm : s.regs.get? Register.mstatus = some (0#64))
    (hc : s.regs.get? Register.mseccfg = some (0#64)) :
    (get_transformed_data_addr (.Regidx 2) offset (.Store .Data) 8).run s =
      .ok (.Ext_DataAddr_OK (.Virtaddr (sp + offset))) s := by
  unfold get_transformed_data_addr ext_data_get_addr
  simp only [read_x2, bind_assoc, pure_bind]
  rw [bind_run_ok _ _ (read_register s Register.x2 sp hx)]
  rw [bind_run_ok _ _ (transform_store_run s (sp + offset) hp hm hc)]
  rfl

theorem aligned8_same_page (addr : BitVec 64)
    (ha : is_aligned_vaddr (.Virtaddr addr) 8 = true) :
    (addr &&& (0xfffffffffffff000#64)) =
      ((addr + (7#64)) &&& (0xfffffffffffff000#64)) := by
  have halign : addr.toNat % 8 = 0 := by
    have ht : (addr.toNat : Int).tmod 8 = 0 := by
      simpa [is_aligned_vaddr, Sail.BitVec.toNatInt] using ha
    change (↑(addr.toNat % 8) : Int) = 0 at ht
    omega
  have hbound := addr.isLt
  have hlimit : addr.toNat + 7 < 2 ^ 64 := by omega
  have hdiv : (addr.toNat + 7) / 4096 = addr.toNat / 4096 := by omega
  have hshift : addr >>> 12 = (addr + (7#64)) >>> 12 := by
    apply _root_.BitVec.eq_of_toNat_eq
    simpa [_root_.BitVec.toNat_add, Nat.shiftRight_eq_div_pow,
      Nat.mod_eq_of_lt hlimit] using hdiv.symm
  change addr &&& (_root_.BitVec.allOnes 64 <<< 12) =
    (addr + (7#64)) &&& (_root_.BitVec.allOnes 64 <<< 12)
  rw [← _root_.BitVec.shiftLeft_ushiftRight, ← _root_.BitVec.shiftLeft_ushiftRight, hshift]

theorem aligned8_split_page (addr : BitVec 64)
    (ha : is_aligned_vaddr (.Virtaddr addr) 8 = true) :
    split_on_page_boundary addr 8 = pure (8, 0) := by
  have hp := aligned8_same_page addr ha
  unfold split_on_page_boundary
  have he : Sail.BitVec.subInt (Sail.BitVec.addInt addr 8) 1 = addr + (7#64) := by
    simp [Sail.BitVec.subInt, Sail.BitVec.addInt, _root_.BitVec.sub_eq_add_neg,
      _root_.BitVec.add_assoc]
  simp only [Functions.pagesize_bits, ones, zeros, Sail.BitVec.length,
    Sail.BitVec.updateSubrange]
  change (if ((addr &&& (0xfffffffffffff000#64)) ==
      (Sail.BitVec.subInt (Sail.BitVec.addInt addr 8) 1 &&& (0xfffffffffffff000#64))) then
      pure (8, 0) else _) = _
  rw [he, hp]
  simp

/-- Internal composition step: its physical-memory premise must be proved
from the concrete RAM model before claiming a complete instruction run. -/
theorem translate_read8_of_mem_read (s after : State) (addr value : BitVec 64)
    (hp : s.regs.get? Register.cur_privilege = some Privilege.Machine)
    (hm : s.regs.get? Register.mstatus = some (0#64))
    (hread : (mem_read (.Load .Data) .PBMT_PMA (.Physaddr addr) 8 false false false).run s =
      .ok (.Ok value) after) :
    (translate_and_read_value (.Virtaddr addr) 8 (.Load .Data) false false false).run s =
      .ok (.Ok (.Physaddr addr, value)) after := by
  unfold translate_and_read_value
  rw [bind_run_ok _ _ (translate_load_run s addr hp hm)]
  rw [bind_run_ok _ _ hread]
  rfl

/-- Internal composition step preserving the exact resulting physical state. -/
theorem vmem_read_addr8_of_mem_read (s after : State) (addr value : BitVec 64)
    (hp : s.regs.get? Register.cur_privilege = some Privilege.Machine)
    (hm : s.regs.get? Register.mstatus = some (0#64))
    (ha : is_aligned_vaddr (.Virtaddr addr) 8 = true)
    (hread : (mem_read (.Load .Data) .PBMT_PMA (.Physaddr addr) 8 false false false).run s =
      .ok (.Ok value) after) :
    (vmem_read_addr (.Virtaddr addr) 8 (.Load .Data) false false false).run s =
      .ok (.Ok value) after := by
  have hvalue := translate_read8_of_mem_read s after addr value hp hm hread
  simp only [EStateM.run] at hvalue
  unfold vmem_read_addr
  simp only [ha, Functions.not, if_false, bits_of_virtaddr, aligned8_split_page addr ha]
  simp [SailME.run, PreSail.PreSailME.run, ExceptT.run, ExceptT.bind,
    ExceptT.map, ExceptT.lift, ExceptT.mk, ExceptT.pure, ExceptT.bindCont, liftM, monadLift,
    MonadLift.monadLift, Bind.bind, Functor.map, EStateM.bind, EStateM.map, EStateM.run,
    PreSail.readReg, MonadState.get, getThe, MonadStateOf.get, EStateM.get,
    Pure.pure, EStateM.pure, hm, hp, machine_effective, machine_bare,
    sys_misaligned_order_decreasing, hvalue, effectivePrivilege, _get_Mstatus_MPRV,
    Sail.BitVec.extractLsb, translationMode, Sail.BitVec.updateSubrange,
    show (Privilege.Machine == Privilege.Machine) = true from rfl,
    Sail.BitVec.updateSubrange', zeros]

/-- Internal composition step. The effective-address phase is checked and
state preserving; the value phase may change the concrete byte memory. -/
theorem vmem_write_addr8_of_mem_write (s after : State) (addr value : BitVec 64)
    (hp : s.regs.get? Register.cur_privilege = some Privilege.Machine)
    (hm : s.regs.get? Register.mstatus = some (0#64))
    (ha : is_aligned_vaddr (.Virtaddr addr) 8 = true)
    (hea : (mem_write_ea (.Physaddr addr) 8 (.Store .Data) .PBMT_PMA false false false).run s =
      .ok (.Ok ()) s)
    (hwrite : (mem_write_value (.Physaddr addr) 8 value (.Store .Data) .PBMT_PMA
      false false false).run s = .ok (.Ok true) after) :
    (vmem_write_addr (.Virtaddr addr) 8 value (.Store .Data) false false false).run s =
      .ok (.Ok true) after := by
  have ht := translate_store_run s addr hp hm
  simp only [EStateM.run] at ht hea hwrite
  unfold vmem_write_addr
  simp only [ha, Functions.not, if_false, bits_of_virtaddr, aligned8_split_page addr ha]
  simp [SailME.run, PreSail.PreSailME.run, ExceptT.run, ExceptT.bind,
    ExceptT.map, ExceptT.lift, ExceptT.mk, ExceptT.pure, ExceptT.bindCont, liftM, monadLift,
    MonadLift.monadLift, Bind.bind, Functor.map, EStateM.bind, EStateM.map, EStateM.run,
    PreSail.readReg, MonadState.get, getThe, MonadStateOf.get, EStateM.get,
    Pure.pure, EStateM.pure, hm, hp, machine_effective, machine_bare,
    sys_misaligned_order_decreasing, ht, hea, hwrite, is_store_conditional,
    LeanRV64D.assert, PreSail.assert, Sail.BitVec.extractLsb, effectivePrivilege,
    _get_Mstatus_MPRV, translationMode,
    show (Privilege.Machine == Privilege.Machine) = true from rfl,
    _root_.BitVec.extractLsb]

/-- Internal stack-address composition step; the physical read premise is
discharged below by the concrete memory configuration and byte contents. -/
theorem vmem_read_stack8_of_mem_read (s after : State) (sp offset value : BitVec 64)
    (hx : s.regs.get? Register.x2 = some sp)
    (hp : s.regs.get? Register.cur_privilege = some Privilege.Machine)
    (hm : s.regs.get? Register.mstatus = some (0#64))
    (hc : s.regs.get? Register.mseccfg = some (0#64))
    (ha : is_aligned_vaddr (.Virtaddr (sp + offset)) 8 = true)
    (hread : (mem_read (.Load .Data) .PBMT_PMA (.Physaddr (sp + offset)) 8
      false false false).run s = .ok (.Ok value) after) :
    (vmem_read (.Regidx 2) offset 8 (.Load .Data) false false false).run s =
      .ok (.Ok value) after := by
  have haddr := stack_addr_load_run s sp offset hx hp hm hc
  have hvalue := vmem_read_addr8_of_mem_read s after (sp + offset) value hp hm ha hread
  simp only [EStateM.run] at haddr hvalue
  simp at haddr hvalue
  unfold vmem_read
  simp [SailME.run, PreSail.PreSailME.run, ExceptT.run, ExceptT.bind,
    ExceptT.map, ExceptT.lift, ExceptT.mk, ExceptT.pure, ExceptT.bindCont, liftM, monadLift,
    MonadLift.monadLift, Bind.bind, Functor.map, EStateM.bind, EStateM.map, EStateM.run,
    Pure.pure, EStateM.pure, haddr, hvalue]

/-- Internal stack-address composition step with explicit physical premises. -/
theorem vmem_write_stack8_of_mem_write (s after : State) (sp offset value : BitVec 64)
    (hx : s.regs.get? Register.x2 = some sp)
    (hp : s.regs.get? Register.cur_privilege = some Privilege.Machine)
    (hm : s.regs.get? Register.mstatus = some (0#64))
    (hc : s.regs.get? Register.mseccfg = some (0#64))
    (ha : is_aligned_vaddr (.Virtaddr (sp + offset)) 8 = true)
    (hea : (mem_write_ea (.Physaddr (sp + offset)) 8 (.Store .Data) .PBMT_PMA
      false false false).run s = .ok (.Ok ()) s)
    (hwrite : (mem_write_value (.Physaddr (sp + offset)) 8 value (.Store .Data) .PBMT_PMA
      false false false).run s = .ok (.Ok true) after) :
    (vmem_write (.Regidx 2) offset 8 value (.Store .Data) false false false).run s =
      .ok (.Ok true) after := by
  have haddr := stack_addr_store_run s sp offset hx hp hm hc
  have hvalue := vmem_write_addr8_of_mem_write s after (sp + offset) value hp hm ha hea hwrite
  simp only [EStateM.run] at haddr hvalue
  simp at haddr hvalue
  unfold vmem_write
  simp [SailME.run, PreSail.PreSailME.run, ExceptT.run, ExceptT.bind,
    ExceptT.map, ExceptT.lift, ExceptT.mk, ExceptT.pure, ExceptT.bindCont, liftM, monadLift,
    MonadLift.monadLift, Bind.bind, Functor.map, EStateM.bind, EStateM.map, EStateM.run,
    Pure.pure, EStateM.pure, haddr, hvalue]

/-- The actual virtual store succeeds from concrete register/platform facts;
its byte-memory effect is the eight little-endian insertions of store64. -/
theorem vmem_stack_store8_run (s : State) (sp offset value : BitVec 64)
    (regions : List PMA_Region) (region : PMA_Region)
    (hx : s.regs.get? Register.x2 = some sp) (hc : MemoryConfig s regions)
    (hr : RAMRegion regions (sp + offset) region) (hl : LowRAM (sp + offset)) :
    (vmem_write (.Regidx 2) offset 8 value (.Store .Data) false false false).run s =
      .ok (.Ok true) (store64 s (sp + offset).toNat value) := by
  apply vmem_write_stack8_of_mem_write s _ sp offset value hx hc.privilege hc.status hc.masking
  · exact hr.2.2.2
  · exact store_ea8_run s (sp + offset) regions region hc.regions hr
      hc.privilege hc.status hc.pmpcfg hc.pmpaddr
  · exact mem_store8_run s (sp + offset) value regions region hc hr hl

/-- The actual virtual load reads the eight concrete byte entries without
changing any sequential state component. -/
theorem vmem_stack_load8_run (s : State) (sp offset value : BitVec 64)
    (regions : List PMA_Region) (region : PMA_Region)
    (hx : s.regs.get? Register.x2 = some sp) (hc : MemoryConfig s regions)
    (hr : RAMRegion regions (sp + offset) region) (hl : LowRAM (sp + offset))
    (hb : ∀ i : Fin 8, s.mem.get? ((sp + offset).toNat + i.val) =
      some (value.extractLsb' (8 * i.val) 8)) :
    (vmem_read (.Regidx 2) offset 8 (.Load .Data) false false false).run s =
      .ok (.Ok value) s := by
  apply vmem_read_stack8_of_mem_read s s sp offset value hx hc.privilege hc.status hc.masking
  · exact hr.2.2.2
  · exact mem_load8_run s (sp + offset) value regions region hc hr hl hb

end OakSailBridge.BitwiseDecoded
