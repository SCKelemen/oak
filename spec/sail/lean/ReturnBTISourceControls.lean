import ReturnBTISource
import ReturnBTIControls
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 8192
namespace Oak.SailBridge.ReturnBTISourceControls
open ReturnExecution Sail PreSail
open Oak.BitwiseFunction
open Oak.BitwiseSource (Bytes Decl ascii render)
open ReturnBTISource

/-- Explicit arbitrary upper halves, including dirty ones. No clean-X0/X1
entry assumption is needed for the u32 ABI. Other incoming registers are free. -/
def inputBank (bank : Bank) (left right upperLeft upperRight : BitVec 32) : Bank :=
 (bank.set! 0 (upperLeft ++ left)).set! 1 (upperRight ++ right)

theorem input_bank_halves (bank : Bank) (left right upperLeft upperRight : BitVec 32) :
 (inputBank bank left right upperLeft upperRight)[0].extractLsb' 0 32 = left ∧
 (inputBank bank left right upperLeft upperRight)[1].extractLsb' 0 32 = right ∧
 (inputBank bank left right upperLeft upperRight)[0].extractLsb' 32 32 = upperLeft ∧
 (inputBank bank left right upperLeft upperRight)[1].extractLsb' 32 32 = upperRight := by
 simp only [inputBank,Vector.getElem_set!]
 bv_decide

def initial (s : State) (ps : ProcState) (bank : Bank)
 (left right upperLeft upperRight : BitVec 32) (guarded : Bool) : State :=
 ReturnBTIControls.initial s ps (inputBank bank left right upperLeft upperRight) guarded

/-- Nonvacuity for every u32 pair, every upper-half pair and both page classes.
The context is constructed, not a premise that an unspecified machine starts
correctly. Reset/boot/OS reachability remains outside this local theorem. -/
theorem initialized_source_success {source body : Bytes} {claim : Decl}
 (accepted : accepts source claim .arm64 .aapcs64U32 body = true)
 (scalar : ScalarBoundaries) (returns : Boundaries)
 (s : State) (ps : ProcState) (bank : Bank)
 (left right upperLeft upperRight : BitVec 32) (guarded : Bool) (fuel : Nat) :
 Outcome source body claim scalar returns
  (initial s ps bank left right upperLeft upperRight guarded)
  (inputBank bank left right upperLeft upperRight) left right fuel := by
 have h := ReturnBTIControls.initial_admits s ps (inputBank bank left right upperLeft upperRight) guarded
 obtain ⟨elMode⟩ := h.2.1
 have halves := input_bank_halves bank left right upperLeft upperRight
 exact accepted_source_execution accepted scalar returns _ _ {} {} guarded false h.1 elMode rfl
  h.2.2.2 _ h.2.2.1 left right halves.1 halves.2.1 fuel

def claim (op : Op) : Decl := ⟨ascii "mix", ascii "a", ascii "b", op⟩

theorem canonical_admitted (op : Op) :
 accepts (render (claim op)) (claim op) .arm64 .aapcs64U32
  (Oak.AArch64BitwiseFunction.functionBytes op) = true := by
 cases op <;> decide +kernel

/-- Real initialized executions exist for all three operators, arbitrary
operands/upper halves and both guarded-page settings, with arbitrary callbacks. -/
theorem canonical_all_inputs (op : Op) (scalar : ScalarBoundaries) (returns : Boundaries)
 (s : State) (ps : ProcState) (bank : Bank)
 (left right upperLeft upperRight : BitVec 32) (guarded : Bool) (fuel : Nat) :
 Outcome (render (claim op)) (Oak.AArch64BitwiseFunction.functionBytes op) (claim op)
  scalar returns (initial s ps bank left right upperLeft upperRight guarded)
  (inputBank bank left right upperLeft upperRight) left right fuel :=
 initialized_source_success (canonical_admitted op) scalar returns s ps bank
  left right upperLeft upperRight guarded fuel

/-- Every single-bit body mutation, including changed register/width/opcode,
shift and return fields, refuses replay even when it is another valid function. -/
theorem body_mutations_refused (op : Op) :
 ((List.range 8).all fun index => (List.range 8).all fun bit =>
  !(accepts (render (claim op)) (claim op) .arm64 .aapcs64U32
   ((Oak.AArch64BitwiseFunction.functionBytes op).set index
    ((Oak.AArch64BitwiseFunction.functionBytes op).getD index 0 ^^^ UInt8.ofNat (2^bit))))) = true := by
 cases op <;> decide +kernel

theorem body_extent_refused (op : Op) :
 accepts (render (claim op)) (claim op) .arm64 .aapcs64U32
  (Oak.AArch64BitwiseFunction.functionBytes op).dropLast = false ∧
 accepts (render (claim op)) (claim op) .arm64 .aapcs64U32
  (Oak.AArch64BitwiseFunction.functionBytes op ++ [0]) = false := by
 cases op <;> decide +kernel

theorem wrong_profiles_refused (source body : Bytes) (d : Decl) :
 accepts source d .wasm .aapcs64U32 body = false ∧
 accepts source d .rv64 .aapcs64U32 body = false ∧
 accepts source d .arm64 .wasmLocals body = false ∧
 accepts source d .arm64 .rv64 body = false := by
 simp [ReturnBTISource.accepts,Oak.AArch64BitwiseFunction.accepts]

/-- Identity-sensitive controls include changed name, bound-parameter order,
operator, input/output width, same-name parameters, and unconsumed suffixes. -/
def changedSources : List Bytes :=
 (["other: (a: u32, b: u32): u32 = a & b\n",
   "mix: (b: u32, a: u32): u32 = b & a\n",
   "mix: (a: u32, b: u32): u32 = a | b\n",
   "mix: (a: u64, b: u32): u32 = a & b\n",
   "mix: (a: u32, b: u32): u64 = a & b\n",
   "mix: (a: u32, a: u32): u32 = a & a\n",
   "mix: (a: u32, b: u32): u32 = b & a\n",
   "mix: (a: u32, b: u32): u32 = a & b\r\n",
   "mix: (a: u32, b: u32): u32 = a & b\n// comment\n",
   "mix: (a: u32, b: u32): u32 = a & b\nother: (): u32 = 0\n"] : List String).map ascii

theorem changed_sources_refused :
 (changedSources.all fun source => !(accepts source (claim .and) .arm64 .aapcs64U32
  (Oak.AArch64BitwiseFunction.functionBytes .and))) = true := by decide +kernel

end Oak.SailBridge.ReturnBTISourceControls
