import OakSailBridge.FramedTranslation
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
noncomputable section
namespace OakSailBridge.BitwiseDecoded
open LeanRV64D LeanRV64D.Functions Sail Sail.ConcurrencyInterfaceV1

/-- Aligned readable/writable region membership is a pure configuration check,
not an assumed successful execution or memory response. -/
def RAMRegion (regions : List PMA_Region) (addr : BitVec 64) (region : PMA_Region) : Prop :=
  matching_pma_region regions (.Physaddr addr) 8 = some region ∧
  region.attributes.readable = true ∧ region.attributes.writable = true ∧
  is_aligned_paddr (.Physaddr addr) 8 = true

theorem pma_load_run (s : State) (addr : BitVec 64) (regions : List PMA_Region)
    (region : PMA_Region) (hr : s.regs.get? Register.pma_regions = some regions)
    (h : RAMRegion regions addr region) :
    (pmaCheck (.Physaddr addr) 8 (.Load .Data) .PBMT_PMA false).run s =
      .ok (.Ok { splittable := .CannotSplit, granule_size_exp := 0 }) s := by
  unfold pmaCheck
  simp only [SailME.run, PreSail.PreSailME.run, ExceptT.run, ExceptT.bind,
    ExceptT.map, ExceptT.lift, ExceptT.mk, ExceptT.bindCont, liftM, monadLift,
    MonadLift.monadLift, Bind.bind, Functor.map, EStateM.bind, EStateM.map, EStateM.run,
    PreSail.readReg, MonadState.get, getThe, MonadStateOf.get, EStateM.get,
    Pure.pure, EStateM.pure, hr, h.1]
  simp [override_PMA, h.2.1, mag_pma_check, h.2.2.2, is_mag_applicable_access,
    LeanRV64D.assert, PreSail.assert, Functions.not, Bind.bind, EStateM.bind,
    Pure.pure, EStateM.pure]
  simp only [ExceptT.pure, ExceptT.mk, ExceptT.bindCont, Bind.bind, EStateM.bind, EStateM.map,
    Pure.pure, EStateM.pure, h.2.1, h.2.2.1]
  rfl

theorem pma_store_run (s : State) (addr : BitVec 64) (regions : List PMA_Region)
    (region : PMA_Region) (hr : s.regs.get? Register.pma_regions = some regions)
    (h : RAMRegion regions addr region) :
    (pmaCheck (.Physaddr addr) 8 (.Store .Data) .PBMT_PMA false).run s =
      .ok (.Ok { splittable := .CannotSplit, granule_size_exp := 0 }) s := by
  unfold pmaCheck
  simp only [SailME.run, PreSail.PreSailME.run, ExceptT.run, ExceptT.bind,
    ExceptT.map, ExceptT.lift, ExceptT.mk, ExceptT.bindCont, liftM, monadLift,
    MonadLift.monadLift, Bind.bind, Functor.map, EStateM.bind, EStateM.map, EStateM.run,
    PreSail.readReg, MonadState.get, getThe, MonadStateOf.get, EStateM.get,
    Pure.pure, EStateM.pure, hr, h.1]
  simp [override_PMA, h.2.2.1, mag_pma_check, h.2.2.2, is_mag_applicable_access,
    LeanRV64D.assert, PreSail.assert, Functions.not, Bind.bind, EStateM.bind,
    Pure.pure, EStateM.pure]
  simp only [ExceptT.pure, ExceptT.mk, ExceptT.bindCont, Bind.bind, EStateM.bind, EStateM.map,
    Pure.pure, EStateM.pure, h.2.1, h.2.2.1]
  rfl

end OakSailBridge.BitwiseDecoded
