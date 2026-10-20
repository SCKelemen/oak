import Oak.OptIRStatefulCopy
import Oak.StatefulCopyControls

/-! Kernel controls for execution of the actual exported CFG. Concrete windows
instantiate the general theorem; these do not stand in for symbolic refinement. -/
namespace Oak.OptIRStatefulCopy.Controls
open Oak.OptIRExecution Oak.StatefulCopy Oak.Stdlib.Bytes
open Oak.StatefulCopy.Controls

/-- The complete window family remains inhabited, with arbitrary valid offsets
and lengths in both owner backings, including short and one-past empty cases. -/
theorem inhabited_windows (dv sv : Oak.ViewRefinement.View)
    (hd : dv.start+dv.len ≤ 5) (hs : sv.start+sv.len ≤ 4) :
    ∃ r after,
      execute ⟨allocations,8,permissions dv sv⟩ Generated.program "copy_checked"
        [.span (destination dv),.view (source sv)] memory
          (callerFuel (destination dv) (source sv)) =
        .returned [.bool (callerObservation sv.len.toUInt32 r)] after ∧
      ObservesCopy memory after (destination dv) (source sv) r
        (callerObservation sv.len.toUInt32 r) (fun _ => False) :=
  caller_cfg_total_observes (valid_windows dv sv hd hs)

/-- Same owner, disjoint nonzero-offset destination. Source *window* stays
unchanged, while byte 18 in that common backing must change from 9 to 201. -/
theorem same_owner_window_frame :
    ∃ (r : Result_u32_CopyError) (after : Memory),
      execute ⟨allocations,8,⟨(destination ⟨0,1⟩).contains,(destination ⟨2,2⟩).contains⟩⟩
        Generated.program "copy_checked"
        [.span (destination ⟨2,2⟩),.view (destination ⟨0,1⟩)] memory
        (callerFuel (destination ⟨2,2⟩) (destination ⟨0,1⟩)) =
        .returned [.bool true] after ∧
      r = .Ok 1 ∧ after 16 = some 201 ∧ after 18 = some 201 ∧
      after 18 ≠ memory 18 ∧ after 19 = some 10 ∧ after 255 = none := by
  obtain ⟨r,after,he,ho⟩ := caller_cfg_total_observes same_owner_disjoint
  have hr : r = .Ok 1 := ho.result
  have hs : after 16 = memory 16 := ho.source 0 (by decide)
  have hd : after 18 = memory 16 := ho.destination 0 (by decide)
  have ht : after 19 = memory 19 := ho.destination 1 (by decide)
  have hf : after 255 = memory 255 := ho.frame 255 (by simp [inCopiedPrefix,destination,ByteView.base,copiedLength]) (by simp)
  refine ⟨r,after,?_,hr,?_,?_,?_,?_,?_⟩
  · simpa [hr,callerObservation,destination] using he
  · exact hs.trans (by decide)
  · exact hd.trans (by decide)
  · rw [hd]; decide
  · exact ht.trans (by decide)
  · exact hf.trans (by decide)

/-- A valid short case reaches Err/false without writing, not an admission
failure. Its exact IR budget is sixteen transitions. -/
theorem short_case :
    execute ⟨allocations,8,permissions ⟨1,1⟩ ⟨1,2⟩⟩ Generated.program "copy_checked"
      [.span (destination ⟨1,1⟩),.view (source ⟨1,2⟩)] memory 16 =
      .returned [.bool false] memory :=
  caller_cfg_short (valid_windows ⟨1,1⟩ ⟨1,2⟩ (by decide) (by decide)) (by decide)

theorem one_past_empty_case :
    execute ⟨allocations,8,permissions ⟨5,0⟩ ⟨4,0⟩⟩ Generated.program "copy_checked"
      [.span (destination ⟨5,0⟩),.view (source ⟨4,0⟩)] memory 19 =
      .returned [.bool true] memory :=
  caller_cfg_empty (valid_windows ⟨5,0⟩ ⟨4,0⟩ (by decide) (by decide)) rfl

theorem exhausted_not_error :
    execute ⟨allocations,8,permissions ⟨1,3⟩ ⟨1,2⟩⟩ Generated.program "copy_checked"
      [.span dst,.view src] memory 0 = .exhausted := caller_zero_fuel _ _ _ _

theorem missing_closure_refused : checkProjection [] = false := by decide

theorem inactive_payload_fault (world : World) (mem : Memory) :
    evalOperation world mem
      {code:="adt.payload",results:=[{id:=1,ty:="u32"}],operands:=[2],
       attributes:=[⟨"variant","Result_u32_bytes__CopyError.Ok"⟩]}
      [.result (.Err .DestinationTooSmall)] = none := by rfl

theorem unmapped_byte_fault (world : World) (view : ByteView) (index : UInt32) :
    loadByte world (fun _ => none) view index = none := by
  classical
  simp [loadByte]

theorem unmapped_store_fault (world : World) (view : ByteView) (index : UInt32) (byte : UInt8) :
    storeByte world (fun _ => none) view index byte = none := by
  classical
  simp [storeByte]

end Oak.OptIRStatefulCopy.Controls
