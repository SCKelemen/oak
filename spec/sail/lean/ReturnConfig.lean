import ReturnExecution
import Std.Data.ExtDHashMap.Lemmas
namespace Oak.SailBridge.ReturnConfig
open ReturnExecution ReturnExecution.Functions Sail PreSail
set_option linter.unusedSimpArgs false
abbrev State := PreSail.SequentialState ReturnExecution.RegisterType Sail.trivialChoiceSource
/-- Explicit values of the five pinned architecture-version configuration registers. -/
structure Values where
 v81 : Bool := true
 v82 : Bool := true
 v83 : Bool := true
 v84 : Bool := true
 v85 : Bool := true
/-- All five reads are retained by the unchanged eager generated expression. -/
structure Initialized (s : State) (v : Values) : Prop where
 v81 : s.regs.get? Register.__v81_implemented = some v.v81
 v82 : s.regs.get? Register.__v82_implemented = some v.v82
 v83 : s.regs.get? Register.__v83_implemented = some v.v83
 v84 : s.regs.get? Register.__v84_implemented = some v.v84
 v85 : s.regs.get? Register.__v85_implemented = some v.v85

theorem havePAC_run (s : State) (v : Values) (h : Initialized s v) :
 (HavePACExt ()).run s = .ok v.v83 s := by
 simp +decide [HavePACExt, HasArchVersion, readReg, h.v81, h.v82, h.v83, h.v84, h.v85,
 EStateM.run, Bind.bind, Pure.pure, EStateM.bind, EStateM.pure,
 MonadStateOf.get, MonadState.get, EStateM.get, getThe]
 cases v.v83 <;> rfl

def withValues (s : State) (v : Values) : State :=
 {s with regs := ((((s.regs.insert .__v81_implemented v.v81).insert .__v82_implemented v.v82).insert .__v83_implemented v.v83).insert .__v84_implemented v.v84).insert .__v85_implemented v.v85}

theorem withValues_valid (s : State) (v : Values) : Initialized (withValues s v) v := by
 constructor <;> simp +decide [withValues, Std.ExtDHashMap.get?_insert]

/-- Initializing the profile preserves the existing function-entry observations. -/
theorem withValues_frame (s : State) (v : Values) :
 (withValues s v).regs.get? Register._R = s.regs.get? Register._R ∧
 (withValues s v).regs.get? Register.PSTATE = s.regs.get? Register.PSTATE ∧
 (withValues s v).regs.get? Register.TCR_EL1 = s.regs.get? Register.TCR_EL1 ∧
 (withValues s v).mem = s.mem ∧ (withValues s v).tags = s.tags := by
 simp [withValues, Std.ExtDHashMap.get?_insert]

theorem default_true (s : State) :
 (HavePACExt ()).run (withValues s {}) = .ok true (withValues s {}) :=
 havePAC_run (withValues s {}) {} (withValues_valid s {})

theorem configured_false (s : State) :
 (HavePACExt ()).run (withValues s {v83 := false}) = .ok false (withValues s {v83 := false}) :=
 havePAC_run (withValues s {v83 := false}) {v83 := false} (withValues_valid s _)

/-- Even an irrelevant version register must exist: the export eagerly reads v8.1 first. -/
theorem missing_v81 (s : State) (missing : s.regs.get? Register.__v81_implemented = none) :
 (HavePACExt ()).run s = .error .Unreachable s := by
 simp +decide [HavePACExt, HasArchVersion, readReg, missing, EStateM.run, Bind.bind,
 Pure.pure, EStateM.bind, EStateM.pure, MonadStateOf.get, MonadState.get,
 EStateM.get, getThe, throw, throwThe, MonadExceptOf.throw, EStateM.throw]

theorem haveBTI_run (s : State) (v : Values) (h : Initialized s v) :
 (HaveBTIExt ()).run s = .ok v.v85 s := by
 simp [HaveBTIExt,HasArchVersion,readReg,h.v81,h.v82,h.v83,h.v84,h.v85,
 EStateM.run,Bind.bind,Pure.pure,EStateM.bind,EStateM.pure,
 MonadStateOf.get,MonadState.get,EStateM.get,getThe]
 cases v.v85 <;> rfl

theorem bti_default_true (s : State) :
 (HaveBTIExt ()).run (withValues s {}) = .ok true (withValues s {}) :=
 haveBTI_run _ {} (withValues_valid s {})

theorem bti_configured_false (s : State) :
 (HaveBTIExt ()).run (withValues s {v85 := false}) = .ok false (withValues s {v85 := false}) :=
 haveBTI_run _ _ (withValues_valid s {v85 := false})

def withoutVersion (s : State) (r : Register) : State := {s with regs := s.regs.erase r}
def versionRegisters : List Register := [.__v81_implemented,.__v82_implemented,
 .__v83_implemented,.__v84_implemented,.__v85_implemented]

theorem bti_each_missing_version (s : State) (v : Values) (r : Register)
 (required : r ∈ versionRegisters) :
 (HaveBTIExt ()).run (withoutVersion (withValues s v) r) =
 .error .Unreachable (withoutVersion (withValues s v) r) := by
 simp only [versionRegisters,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at required
 rcases required with rfl|rfl|rfl|rfl|rfl
 all_goals simp [HaveBTIExt,HasArchVersion,readReg,withoutVersion,withValues,
 Std.ExtDHashMap.get?_erase,Std.ExtDHashMap.get?_insert,
 EStateM.run,Bind.bind,Pure.pure,EStateM.bind,EStateM.pure,
 MonadStateOf.get,MonadState.get,EStateM.get,getThe,throw,throwThe,MonadExceptOf.throw,EStateM.throw]

end Oak.SailBridge.ReturnConfig
