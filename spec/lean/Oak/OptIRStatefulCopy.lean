import Oak.OptIRStatefulCopyValidation

/-!
# Refinement of the freshly generated raw copy CFG

The generated module contains the actual owned raw CFG exported by the compiler.
All execution below fetches that graph. Its metadata is not assumed correct by a
hash: the Go closed-profile/reprojection checks bind that separate tested trust
boundary. This file does not establish frontend or Go serialization correctness.
-/
namespace Oak.OptIRStatefulCopy

open Oak.OptIRExecution Oak.StatefulCopy Oak.Stdlib.Bytes

set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

@[simp] theorem one_toNat : decimal "1" = some 1 := by decide
@[simp] theorem zero_toNat : decimal "0" = some 0 := by decide

def callee : CFG := Generated.program[0]'(by decide)
def caller : CFG := Generated.program[1]'(by decide)

def calleeState (mem : Memory) (env : Env) (block : Nat) (pc : Nat)
    (stack : List Continuation) : State := ⟨mem,⟨callee,block,pc,env⟩,stack⟩

def Header (env : Env) (dst src : ByteView) (n i : UInt32) : Prop :=
  env 1 = some (.span dst) ∧ env 2 = some (.view src) ∧
  env 3 = some (.u32 n) ∧ env 18 = some (.u32 i)

def iterationEnv (env : Env) (i : UInt32) (byte : UInt8) : Env :=
  ((((((env.set 12 (.bool true)).set 19 (.u32 i)).set 13 (.u8 byte)).set 14 (.u32 1)).set 15 (.u32 (i+1))).set 18 (.u32 (i+1)))

theorem iteration_header (env : Env) (dst src : ByteView) (n i : UInt32)
    (byte : UInt8) (h : Header env dst src n i) :
    Header (iterationEnv env i byte) dst src n (i+1) := by
  rcases h with ⟨h1,h2,h3,h18⟩
  simp [Header,iterationEnv,Env.set,h1,h2,h3]

/-- Seven fetched CFG transitions comprise one body iteration: the comparison,
conditional edge, byte read, byte write, constant one, addition, and backedge. -/
theorem iteration (world : World) (mem : Memory) (env : Env) (dst src : ByteView)
    (n i : UInt32) (stack : List Continuation) (byte : UInt8)
    (h : Header env dst src n i) (hlt : i < n)
    (hr : loadByte world mem src i = some byte)
    (hw : storeByte world mem dst i byte = some (writeByte mem (dst.base+i.toNat) byte)) :
    advance world Generated.program 7 (calleeState mem env 4 0 stack) =
      some (calleeState (writeByte mem (dst.base+i.toNat) byte)
        (iterationEnv env i byte) 4 0 stack) := by
  rcases h with ⟨h1,h2,h3,h18⟩
  simp [advance, step, calleeState, callee, Generated.program,
    findBlock, readValues, bindValues, evalOperation, branch,
    iterationEnv, Value.type, Env.set, h1,h2,h3,h18,hlt,hr,hw]


def exitEnv (env : Env) (n i : UInt32) : Env :=
  (((env.set 12 (.bool false)).set 9 (.u32 i)).set 16 (.result (.Ok n))).set 17 (.result (.Ok n))

/-- The false loop edge, Ok construction and join transfer are fetched from
blocks 4 and 6 of the generated callee. -/
theorem loop_exit (world : World) (mem : Memory) (env : Env) (dst src : ByteView)
    (n i : UInt32) (stack : List Continuation)
    (h : Header env dst src n i) (hlt : ¬ i < n) :
    advance world Generated.program 4 (calleeState mem env 4 0 stack) =
      some (calleeState mem (exitEnv env n i) 3 0 stack) := by
  rcases h with ⟨h1,h2,h3,h18⟩
  simp [advance, step, calleeState, callee, Generated.program,
    findBlock, readValues, bindValues, evalOperation, branch,
    exitEnv, Value.type, Env.set, h1,h2,h3,h18,hlt]

/-- Exact writeback/update agreement. This lemma is about one generic store,
not about copying or about preserving an owner's entire backing. -/
theorem writeByte_writeWindow (before : Memory) (dst : ByteView)
    (out : Array UInt8) (index : Nat) (byte : UInt8)
    (hsize : out.size = dst.window.len) (hi : index < dst.window.len) :
    writeByte (writeWindow before dst out) (dst.base+index) byte =
      writeWindow before dst (out.setIfInBounds index byte) := by
  funext a
  by_cases ha : dst.contains a
  · have hk : a - dst.base < dst.window.len := by unfold ByteView.contains at ha; omega
    have he : dst.base + (a-dst.base) = a := by unfold ByteView.contains at ha; omega
    rw [← he, writeWindow_inside _ _ _ _ hk]
    simp only [writeByte]
    by_cases hki : a-dst.base = index
    · simp [hki, writeWindow_inside _ _ _ _ hi, Array.getD_eq_getD_getElem?,
        Array.getElem?_setIfInBounds, hsize, hi]
    · have hne : dst.base + (a-dst.base) ≠ dst.base+index := by omega
      rw [if_neg hne, writeWindow_inside _ _ _ _ hk]
      simp [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds, hki, Ne.symm hki]
  · have hne : a ≠ dst.base+index := by
      intro he; apply ha; subst a; exact ⟨by omega,by omega⟩
    simp [writeByte, hne, writeWindow, ha]

/-- Only the source window must remain represented after writing destination
bytes. In particular this works for disjoint windows of the *same* owner. -/
theorem source_read_writeWindow {allocs : Allocations} {bits : Nat} {permissions : Permissions}
    {before : Memory} {dst src : ByteView} {db sb : Array UInt8}
    (h : Invocation allocs bits permissions before dst src db sb)
    (out : Array UInt8) (i : UInt32) (hi : i.toNat < src.window.len) :
    loadByte ⟨allocs,bits,permissions⟩ (writeWindow before dst out) src i =
      some ((logical sb src).getD i.toNat 0) := by
  classical
  have hs : src.contains (src.base+i.toNat) := ⟨by omega,by omega⟩
  have hd : ¬ dst.contains (src.base+i.toNat) := fun hd => h.disjoint _ hd hs
  simp [loadByte, represented_live h.source, hi, h.read _ hs,
    writeWindow_outside _ _ _ _ hd, represented_read h.source i.toNat hi]

theorem destination_store_writeWindow {allocs : Allocations} {bits : Nat} {permissions : Permissions}
    {before : Memory} {dst src : ByteView} {db sb : Array UInt8}
    (h : Invocation allocs bits permissions before dst src db sb)
    (out : Array UInt8) (i : UInt32) (byte : UInt8) (hi : i.toNat < dst.window.len) :
    storeByte ⟨allocs,bits,permissions⟩ (writeWindow before dst out) dst i byte =
      some (writeByte (writeWindow before dst out) (dst.base+i.toNat) byte) := by
  classical
  have hd : dst.contains (dst.base+i.toNat) := ⟨by omega,by omega⟩
  simp [storeByte,represented_live h.destination,hi,h.write _ hd,
    writeWindow_inside _ _ _ _ hi]


theorem toUInt32_toNat (n : Nat) (h : n < 2^32) : n.toUInt32.toNat = n := by
  rw [UInt32.toNat_ofNat']; exact Nat.mod_eq_of_lt h

/-- Loop-head simulation against the actual extracted loop. The memory is a
writeback of the current extracted destination, not a second copy semantics. -/
theorem loop_refines_extracted {allocs : Allocations} {bits : Nat} {permissions : Permissions}
    {before : Memory} {dst src : ByteView} {db sb : Array UInt8}
    (h : Invocation allocs bits permissions before dst src db sb)
    (hfit : src.window.len ≤ dst.window.len) (stack : List Continuation) (fuel : Nat) :
    ∀ (out : Array UInt8) (i : UInt32) (env : Env),
      out.size = dst.window.len → i.toNat ≤ src.window.len →
      src.window.len-i.toNat < fuel →
      Header env dst src src.window.len.toUInt32 i →
      ∃ final finalEnv,
        copy_into.loop1 out (logical sb src) src.window.len.toUInt32 i fuel =
          some (final,src.window.len.toUInt32) ∧
        advance ⟨allocs,bits,permissions⟩ Generated.program
          (7*(src.window.len-i.toNat)+4)
          (calleeState (writeWindow before dst out) env 4 0 stack) =
          some (calleeState (writeWindow before dst final) finalEnv 3 0 stack) ∧
        finalEnv 17 = some (.result (.Ok src.window.len.toUInt32)) := by
  induction fuel with
  | zero => intro out i env hsize hi hf he; omega
  | succ fuel ih =>
    intro out i env hsize hi hf he
    have hn : src.window.len.toUInt32.toNat = src.window.len :=
      toUInt32_toNat _ h.source.length
    by_cases hlt : i.toNat < src.window.len
    · have hcond : i < src.window.len.toUInt32 := by
        rw [UInt32.lt_iff_toNat_lt,hn]; exact hlt
      have hi1 : (i+1).toNat = i.toNat+1 := by
        rw [UInt32.toNat_add, show (1 : UInt32).toNat = 1 by decide]
        exact Nat.mod_eq_of_lt (by have := h.source.length; omega)
      let byte := (logical sb src).getD i.toNat 0
      let out' := out.setIfInBounds i.toNat byte
      let env' := iterationEnv env i byte
      have hwrite := writeByte_writeWindow before dst out i.toNat byte hsize (by omega)
      obtain ⟨final,finalEnv,hex,hadv,hfinal⟩ := ih out' (i+1) env'
        (by simp [out',hsize]) (by omega) (by omega)
        (iteration_header env dst src src.window.len.toUInt32 i byte he)
      refine ⟨final,finalEnv,?_,?_,hfinal⟩
      · simpa only [copy_into.loop1,hcond,decide_true,↓reduceIte] using hex
      · have hcost : 7*(src.window.len-i.toNat)+4 =
            7+(7*(src.window.len-(i+1).toNat)+4) := by omega
        rw [hcost,advance_add]
        rw [iteration _ _ _ dst src _ _ stack byte he hcond
          (source_read_writeWindow h out i hlt)
          (destination_store_writeWindow h out i byte (by omega))]
        simp only [Option.bind_some]
        rw [hwrite]
        exact hadv
    · have heq : i = src.window.len.toUInt32 := by
        apply UInt32.toNat_inj.mp; omega
      have hcond : ¬ i < src.window.len.toUInt32 := by
        rw [UInt32.lt_iff_toNat_lt,hn]; exact hlt
      refine ⟨out,exitEnv env src.window.len.toUInt32 i,?_,?_,?_⟩
      · simp [copy_into.loop1,hcond,heq]
      · have hcost : 7*(src.window.len-i.toNat)+4 = 4 := by omega
        rw [hcost]; exact loop_exit _ _ _ dst src _ _ stack he hcond
      · simp [exitEnv]


def initialEnv (dst src : ByteView) : Env :=
  (emptyEnv.set 1 (.span dst)).set 2 (.view src)

def successEntryEnv (dst src : ByteView) : Env :=
  (((((initialEnv dst src).set 3 (.u32 src.window.len.toUInt32)).set 4
    (.u32 dst.window.len.toUInt32)).set 5 (.bool false)).set 8 (.u32 0)).set 18 (.u32 0)

def shortEntryEnv (dst src : ByteView) : Env :=
  (((((initialEnv dst src).set 3 (.u32 src.window.len.toUInt32)).set 4
    (.u32 dst.window.len.toUInt32)).set 5 (.bool true)).set 6
      (.copyError .DestinationTooSmall)).set 7 (.result (.Err .DestinationTooSmall)) |>.set 17 (.result (.Err .DestinationTooSmall))

theorem enter_callee (dst src : ByteView) :
    enter callee [.span dst,.view src] = some ⟨callee,0,0,initialEnv dst src⟩ := by
  simp [enter,callee,Generated.program,findBlock,bindValues,Value.type,initialEnv]

theorem success_entry (world : World) (mem : Memory) (dst src : ByteView)
    (stack : List Continuation)
    (hd : dst.window.len < 2^32) (hs : src.window.len < 2^32)
    (hf : src.window.len ≤ dst.window.len) :
    advance world Generated.program 6 (calleeState mem (initialEnv dst src) 0 0 stack) =
      some (calleeState mem (successEntryEnv dst src) 4 0 stack) := by
  have hc : ¬ dst.window.len.toUInt32 < src.window.len.toUInt32 := by
    rw [UInt32.lt_iff_toNat_lt,toUInt32_toNat _ hd,toUInt32_toNat _ hs]; omega
  simp [advance,step,calleeState,callee,Generated.program,findBlock,readValues,
    bindValues,evalOperation,branch,Value.type,Env.set,initialEnv,successEntryEnv,hd,hs,hc]

theorem short_entry (world : World) (mem : Memory) (dst src : ByteView)
    (stack : List Continuation)
    (hd : dst.window.len < 2^32) (hs : src.window.len < 2^32)
    (hf : dst.window.len < src.window.len) :
    advance world Generated.program 7 (calleeState mem (initialEnv dst src) 0 0 stack) =
      some (calleeState mem (shortEntryEnv dst src) 3 0 stack) := by
  have hc : dst.window.len.toUInt32 < src.window.len.toUInt32 := by
    rw [UInt32.lt_iff_toNat_lt,toUInt32_toNat _ hd,toUInt32_toNat _ hs]; exact hf
  simp [advance,step,calleeState,callee,Generated.program,findBlock,readValues,
    bindValues,evalOperation,branch,Value.type,Env.set,initialEnv,shortEntryEnv,hd,hs,hc]

/-- The generic return fetches the real join parameter, without decoding a
sentinel or inventing a Result from destination length. -/
theorem callee_return (world : World) (mem : Memory) (env : Env)
    (r : Result_u32_CopyError) (h : env 17 = some (.result r)) :
    run world Generated.program 1 (calleeState mem env 3 0 []) = .returned [.result r] mem := by
  simp [run,step,calleeState,callee,Generated.program,findBlock,readValues,h]

def calleePrefixCost (dst src : ByteView) : Nat :=
  if src.window.len ≤ dst.window.len then 10+7*src.window.len else 7

/-- Entry, loop, result constructor, and all phi-like edge arguments are joined
here. The existential array is the actual extracted function's returned array. -/
theorem copy_cfg_prefix {allocs : Allocations} {bits : Nat} {permissions : Permissions}
    {before : Memory} {dst src : ByteView} {db sb : Array UInt8}
    (h : Invocation allocs bits permissions before dst src db sb)
    (stack : List Continuation) :
    ∃ r out finalEnv,
      copy_into (logical db dst) (logical sb src) (src.window.len+1) = some (r,out) ∧
      advance ⟨allocs,bits,permissions⟩ Generated.program (calleePrefixCost dst src)
        (calleeState before (initialEnv dst src) 0 0 stack) =
        some (calleeState (writeWindow before dst out) finalEnv 3 0 stack) ∧
      finalEnv 17 = some (.result r) := by
  have hd := logical_size dst db h.destination.bounds
  have hs := logical_size src sb h.source.bounds
  have hbefore := writeWindow_original h.destination
  by_cases hfit : src.window.len ≤ dst.window.len
  · obtain ⟨out,env,hex,hadv,hres⟩ := loop_refines_extracted h hfit stack (src.window.len+1)
      (logical db dst) 0 (successEntryEnv dst src) hd (by simp) (by simp)
      (by simp [Header,successEntryEnv,initialEnv,Env.set])
    refine ⟨.Ok src.window.len.toUInt32,out,env,?_,?_,hres⟩
    · have hc : ¬ (logical db dst).size.toUInt32 < (logical sb src).size.toUInt32 := by
        rw [hd,hs,UInt32.lt_iff_toNat_lt,toUInt32_toNat _ h.destination.length,
          toUInt32_toNat _ h.source.length]; omega
      simp only [copy_into,hc,decide_false,Bool.false_eq_true,↓reduceIte]
      simp [hs,hex]
    · have hcost : calleePrefixCost dst src = 6+(7*(src.window.len-(0:UInt32).toNat)+4) := by
        simp [calleePrefixCost,hfit]; omega
      rw [hcost,advance_add,success_entry _ _ _ _ stack h.destination.length h.source.length hfit]
      simpa only [Option.bind_some,hbefore] using hadv
  · refine ⟨.Err .DestinationTooSmall,logical db dst,shortEntryEnv dst src,?_,?_,?_⟩
    · have hc : (logical db dst).size.toUInt32 < (logical sb src).size.toUInt32 := by
        rw [hd,hs,UInt32.lt_iff_toNat_lt,toUInt32_toNat _ h.destination.length,
          toUInt32_toNat _ h.source.length]; omega
      exact copy_short_atomic _ _ _ hc
    · simp only [calleePrefixCost,hfit,↓reduceIte,hbefore]
      exact short_entry _ _ _ _ stack h.destination.length h.source.length (by omega)
    · simp [shortEntryEnv]


theorem find_callee : findFunction Generated.program "bytes__copy_uinto" = some callee := by
  rfl

theorem find_caller : findFunction Generated.program "copy_checked" = some caller := by
  rfl

/-- Execution of the *actual produced callee CFG* agrees with the existing
extracted `copy_into` and generic writeback, at its derived exact IR cost. -/
theorem copy_cfg_refines_extracted {allocs : Allocations} {bits : Nat} {permissions : Permissions}
    {before : Memory} {dst src : ByteView} {db sb : Array UInt8}
    (h : Invocation allocs bits permissions before dst src db sb) :
    ∃ r out,
      copy_into (logical db dst) (logical sb src) (src.window.len+1) = some (r,out) ∧
      execute ⟨allocs,bits,permissions⟩ Generated.program "bytes__copy_uinto"
        [.span dst,.view src] before (calleePrefixCost dst src+1) =
          .returned [.result r] (writeWindow before dst out) := by
  obtain ⟨r,out,env,hex,hadv,hres⟩ := copy_cfg_prefix h []
  refine ⟨r,out,hex,?_⟩
  simp only [execute,find_callee,enter_callee]
  change run _ _ _ (calleeState before (initialEnv dst src) 0 0 []) = _
  rw [advance_run _ _ _ _ _ 1 hadv,callee_return _ _ _ r hres]

/-- Exact symbolic IR costs; these are not target instruction counts. -/
theorem copy_cfg_fuel (dst src : ByteView) :
    calleePrefixCost dst src+1 ≤ 11+7*src.window.len := by
  unfold calleePrefixCost; split <;> omega

def savedEnv (dst src : ByteView) : Env :=
  (initialEnv dst src).set 3 (.u32 src.window.len.toUInt32)

def callResults : List ValueDef :=
  ((caller.blocks[0]'(by decide)).operations[1]'(by decide)).results

def callerContinuation (dst src : ByteView) : Continuation :=
  ⟨⟨caller,0,2,savedEnv dst src⟩,callResults⟩

def callerState (mem : Memory) (env : Env) (block : Nat) (pc : Nat) : State :=
  ⟨mem,⟨caller,block,pc,env⟩,[]⟩

theorem enter_caller (dst src : ByteView) :
    enter caller [.span dst,.view src] = some ⟨caller,0,0,initialEnv dst src⟩ := by
  simp [enter,caller,Generated.program,findBlock,bindValues,Value.type,initialEnv]

/-- The actual call saves `n` in the suspended caller environment and enters
callee block zero with a *new* environment over the same memory. -/
theorem caller_call (world : World) (mem : Memory) (dst src : ByteView)
    (hs : src.window.len < 2^32) :
    advance world Generated.program 2 (callerState mem (initialEnv dst src) 0 0) =
      some (calleeState mem (initialEnv dst src) 0 0 [callerContinuation dst src]) := by
  simp [advance,step,callerState,caller,calleeState,callee,Generated.program,
    findBlock,readValues,bindValues,evalOperation,findFunction,enter,
    Value.type,Env.set,initialEnv,savedEnv,callerContinuation,callResults,hs]

theorem call_returns (world : World) (mem : Memory) (env : Env)
    (dst src : ByteView) (r : Result_u32_CopyError)
    (hres : env 17 = some (.result r)) :
    step world Generated.program (calleeState mem env 3 0 [callerContinuation dst src]) =
      .next (callerState mem ((savedEnv dst src).set 4 (.result r)) 0 2) := by
  simp [step,calleeState,callee,callerState,caller,Generated.program,findBlock,
    readValues,bindValues,Value.type,callerContinuation,callResults,hres]

/-- Exhaustive Result matching observes the retained caller-local length. Both
payload projections are executed only in their matching constructor branch. -/
theorem caller_finish (world : World) (mem : Memory) (dst src : ByteView)
    (r : Result_u32_CopyError) :
    run world Generated.program 6
      (callerState mem ((savedEnv dst src).set 4 (.result r)) 0 2) =
        .returned [.bool (callerObservation src.window.len.toUInt32 r)] mem := by
  cases r with
  | Ok count =>
    simp [run,step,callerState,caller,Generated.program,findBlock,readValues,
      bindValues,evalOperation,branch,Value.type,Env.set,savedEnv,callerObservation]
  | Err error =>
    cases error
    simp [run,step,callerState,caller,Generated.program,findBlock,readValues,
      bindValues,evalOperation,branch,Value.type,Env.set,savedEnv,callerObservation]

def callerFuel (dst src : ByteView) : Nat := 2+calleePrefixCost dst src+1+6

theorem caller_cfg_fuel (dst src : ByteView) :
    callerFuel dst src ≤ 19+7*src.window.len := by
  have := copy_cfg_fuel dst src; unfold callerFuel; omega

/-- Exact dynamic caller/callee execution, not an assumption about the
callee's result. One non-inlined call shares data memory and restores the
caller SSA environment containing its original saved length. -/
theorem caller_cfg_refines_extracted {allocs : Allocations} {bits : Nat} {permissions : Permissions}
    {before : Memory} {dst src : ByteView} {db sb : Array UInt8}
    (h : Invocation allocs bits permissions before dst src db sb) :
    ∃ r out,
      copy_into (logical db dst) (logical sb src) (src.window.len+1) = some (r,out) ∧
      execute ⟨allocs,bits,permissions⟩ Generated.program "copy_checked"
        [.span dst,.view src] before (callerFuel dst src) =
          .returned [.bool (callerObservation src.window.len.toUInt32 r)]
            (writeWindow before dst out) := by
  obtain ⟨r,out,env,hex,hadv,hres⟩ := copy_cfg_prefix h [callerContinuation dst src]
  refine ⟨r,out,hex,?_⟩
  simp only [execute,find_caller,enter_caller]
  change run _ _ _ (callerState before (initialEnv dst src) 0 0) = _
  have hc : callerFuel dst src = 2+(calleePrefixCost dst src+(6+1)) := by
    unfold callerFuel; omega
  rw [hc,advance_run _ _ 2 _ _ _ (caller_call _ _ _ _ h.source.length),
    advance_run _ _ _ _ _ _ hadv]
  simp only [run,call_returns _ _ _ dst src r hres]
  exact caller_finish _ _ dst src r

/-- Total physical byte/window and caller observations follow from the actual
CFG execution and the already-proved extracted postcondition. -/
theorem caller_cfg_total_observes {allocs : Allocations} {bits : Nat} {permissions : Permissions}
    {before : Memory} {dst src : ByteView} {db sb : Array UInt8}
    (h : Invocation allocs bits permissions before dst src db sb) :
    ∃ r after,
      execute ⟨allocs,bits,permissions⟩ Generated.program "copy_checked"
        [.span dst,.view src] before (callerFuel dst src) =
          .returned [.bool (callerObservation src.window.len.toUInt32 r)] after ∧
      ObservesCopy before after dst src r
        (callerObservation src.window.len.toUInt32 r) (fun _ => False) := by
  obtain ⟨r,out,hex,hcfg⟩ := caller_cfg_refines_extracted h
  have hd := logical_size dst db h.destination.bounds
  have hs := logical_size src sb h.source.bounds
  obtain ⟨r',out',hex',hpost⟩ := extracted_total (logical db dst) (logical sb src)
    (src.window.len+1) (by rw [hd]; exact h.destination.length)
    (by rw [hs]; exact h.source.length) (by intro _; rw [hs]; omega)
  rw [hex] at hex'; cases hex'
  exact ⟨r,writeWindow before dst out,hcfg,writeback_observes h out r hpost⟩

theorem accepted_caller_cfg_total_observes (candidate : Program)
    (accepted : checkProjection candidate = true)
    {allocs : Allocations} {bits : Nat} {permissions : Permissions}
    {before : Memory} {dst src : ByteView} {db sb : Array UInt8}
    (h : Invocation allocs bits permissions before dst src db sb) :
    ∃ r after,
      execute ⟨allocs,bits,permissions⟩ candidate "copy_checked"
        [.span dst,.view src] before (callerFuel dst src) =
          .returned [.bool (callerObservation src.window.len.toUInt32 r)] after ∧
      ObservesCopy before after dst src r
        (callerObservation src.window.len.toUInt32 r) (fun _ => False) := by
  rw [(check_projection_sound candidate).mp accepted]
  exact caller_cfg_total_observes h


/-- Valid short capacity executes the ordinary Err constructor and preserves
memory. It is never confused with profile refusal or fuel exhaustion. -/
theorem copy_cfg_short {allocs : Allocations} {bits : Nat} {permissions : Permissions}
    {before : Memory} {dst src : ByteView} {db sb : Array UInt8}
    (h : Invocation allocs bits permissions before dst src db sb)
    (hshort : dst.window.len < src.window.len) :
    execute ⟨allocs,bits,permissions⟩ Generated.program "bytes__copy_uinto"
      [.span dst,.view src] before 8 = .returned [.result (.Err .DestinationTooSmall)] before := by
  obtain ⟨r,out,hex,hcfg⟩ := copy_cfg_refines_extracted h
  have hd := logical_size dst db h.destination.bounds
  have hs := logical_size src sb h.source.bounds
  have hc : (logical db dst).size.toUInt32 < (logical sb src).size.toUInt32 := by
    rw [hd,hs,UInt32.lt_iff_toNat_lt,toUInt32_toNat _ h.destination.length,
      toUInt32_toNat _ h.source.length]; exact hshort
  rw [copy_short_atomic _ _ _ hc] at hex
  cases hex
  simpa [calleePrefixCost,show ¬src.window.len ≤ dst.window.len by omega,
    writeWindow_original h.destination] using hcfg

theorem caller_cfg_short {allocs : Allocations} {bits : Nat} {permissions : Permissions}
    {before : Memory} {dst src : ByteView} {db sb : Array UInt8}
    (h : Invocation allocs bits permissions before dst src db sb)
    (hshort : dst.window.len < src.window.len) :
    execute ⟨allocs,bits,permissions⟩ Generated.program "copy_checked"
      [.span dst,.view src] before 16 = .returned [.bool false] before := by
  obtain ⟨r,out,hex,hcfg⟩ := caller_cfg_refines_extracted h
  have hd := logical_size dst db h.destination.bounds
  have hs := logical_size src sb h.source.bounds
  have hc : (logical db dst).size.toUInt32 < (logical sb src).size.toUInt32 := by
    rw [hd,hs,UInt32.lt_iff_toNat_lt,toUInt32_toNat _ h.destination.length,
      toUInt32_toNat _ h.source.length]; exact hshort
  rw [copy_short_atomic _ _ _ hc] at hex
  cases hex
  simpa [callerFuel,calleePrefixCost,show ¬src.window.len ≤ dst.window.len by omega,
    writeWindow_original h.destination,callerObservation] using hcfg

/-- Empty one-past windows require valid owners but no byte at their pointers;
no byte operation executes. -/
theorem copy_cfg_empty {allocs : Allocations} {bits : Nat} {permissions : Permissions}
    {before : Memory} {dst src : ByteView} {db sb : Array UInt8}
    (h : Invocation allocs bits permissions before dst src db sb)
    (hempty : src.window.len = 0) :
    execute ⟨allocs,bits,permissions⟩ Generated.program "bytes__copy_uinto"
      [.span dst,.view src] before 11 = .returned [.result (.Ok 0)] before := by
  obtain ⟨r,out,hex,hcfg⟩ := copy_cfg_refines_extracted h
  have hs : logical sb src = #[] := Array.eq_empty_of_size_eq_zero (by
    rw [logical_size _ _ h.source.bounds,hempty])
  simp only [hs,hempty,Nat.zero_add,copy_empty] at hex
  cases hex
  simpa [calleePrefixCost,hempty,writeWindow_original h.destination] using hcfg

theorem caller_cfg_empty {allocs : Allocations} {bits : Nat} {permissions : Permissions}
    {before : Memory} {dst src : ByteView} {db sb : Array UInt8}
    (h : Invocation allocs bits permissions before dst src db sb)
    (hempty : src.window.len = 0) :
    execute ⟨allocs,bits,permissions⟩ Generated.program "copy_checked"
      [.span dst,.view src] before 19 = .returned [.bool true] before := by
  obtain ⟨r,out,hex,hcfg⟩ := caller_cfg_refines_extracted h
  have hs : logical sb src = #[] := Array.eq_empty_of_size_eq_zero (by
    rw [logical_size _ _ h.source.bounds,hempty])
  simp only [hs,hempty,Nat.zero_add,copy_empty] at hex
  cases hex
  simpa [callerFuel,calleePrefixCost,hempty,writeWindow_original h.destination,
    callerObservation] using hcfg

theorem caller_zero_fuel (world : World) (before : Memory) (dst src : ByteView) :
    execute world Generated.program "copy_checked" [.span dst,.view src] before 0 = .exhausted := by
  simp [execute,find_caller,enter_caller,run]


/-- Source inventories may contain more declarations, but the executable raw
closure used by the theorem has exactly these two named functions. -/
theorem projection_closed_functions :
    Generated.program.map CFG.name = ["bytes__copy_uinto","copy_checked"] := by rfl

/-- Any budget at least the graph-derived uniform bound suffices. Exhaustion
below that budget remains a distinct runtime outcome, never a Result error. -/
theorem caller_cfg_total_observes_with_fuel {allocs : Allocations} {bits : Nat}
    {permissions : Permissions} {before : Memory} {dst src : ByteView}
    {db sb : Array UInt8} (h : Invocation allocs bits permissions before dst src db sb)
    (fuel : Nat) (hf : 19+7*src.window.len ≤ fuel) :
    ∃ r after,
      execute ⟨allocs,bits,permissions⟩ Generated.program "copy_checked"
        [.span dst,.view src] before fuel =
          .returned [.bool (callerObservation src.window.len.toUInt32 r)] after ∧
      ObservesCopy before after dst src r
        (callerObservation src.window.len.toUInt32 r) (fun _ => False) := by
  obtain ⟨r,after,hex,ho⟩ := caller_cfg_total_observes h
  refine ⟨r,after,?_,ho⟩
  simp only [execute,find_caller,enter_caller] at hex ⊢
  have hle : callerFuel dst src ≤ fuel := Nat.le_trans (caller_cfg_fuel dst src) hf
  have heq : callerFuel dst src + (fuel-callerFuel dst src) = fuel := by omega
  simpa only [heq] using run_more _ _ (callerFuel dst src) _ _ _
    (fuel-callerFuel dst src) hex

end Oak.OptIRStatefulCopy
