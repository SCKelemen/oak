/-! Resource protocol for the normally returning LRAT allocating entry.
The source-shape audit in lrat_lifecycle_test.go checks the complete wrapper
against the schema that emits LRATLifecyclePlan. This is not general FFI
extraction. malloc results denote fresh distinct blocks or null; own/disown
transfer the same block; the checker borrows and returns; free(null) is a no-op.
Native allocator/compiler correctness and abnormal termination remain outside
this protocol. Every illegal ownership transition returns none. -/
set_option autoImplicit false
namespace Oak.LRATLifecycle

inductive Slot where
  | starts | lengths | alive | store | assign | trail
  deriving DecidableEq, BEq, Repr
inductive Phase where
  | vacant | absent | raw | owned | freed
  deriving DecidableEq, BEq, Repr
inductive Action where
  | allocate (slot : Slot)
  | own (slot : Slot)
  | check
  | disown (slot : Slot)
  | free (slot : Slot)
  deriving DecidableEq, BEq, Repr

def slots : List Slot := [.starts, .lengths, .alive, .store, .assign, .trail]
abbrev Heap := Slot → Phase
abbrev Results := Slot → Bool

def put (heap : Heap) (slot : Slot) (value : Phase) : Heap :=
  fun other => if other = slot then value else heap other

def step (results : Results) (heap : Heap) : Action → Option Heap
  | .allocate slot => if heap slot = .vacant then
      some (put heap slot (if results slot then .raw else .absent)) else none
  | .own slot => if heap slot = .raw then some (put heap slot .owned) else none
  | .check => if slots.all (fun slot => heap slot == .owned) then some heap else none
  | .disown slot => if heap slot = .owned then some (put heap slot .raw) else none
  | .free slot => if heap slot = .absent then some heap else
      if heap slot = .raw then some (put heap slot .freed) else none

def run (results : Results) (heap : Heap) : List Action → Option Heap
  | [] => some heap
  | action :: rest => (step results heap action).bind (fun next => run results next rest)

def allPresent (results : Results) : Bool := slots.all results

def observe (heap : Heap) : List Phase := slots.map heap

def released (results : Results) : List Phase :=
  slots.map (fun slot => if results slot then .freed else .absent)

end Oak.LRATLifecycle
