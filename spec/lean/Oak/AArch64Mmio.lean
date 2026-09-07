namespace Oak.AArch64Mmio

inductive Access where
  | readOnly
  | writeOnly
  | readWrite
  deriving DecidableEq, Repr

inductive Width where
  | w8
  | w16
  | w32
  | w64
  deriving DecidableEq, Repr

def canRead : Access -> Bool
  | .readOnly | .readWrite => true
  | .writeOnly => false

def canWrite : Access -> Bool
  | .writeOnly | .readWrite => true
  | .readOnly => false

def bytes : Width -> Nat
  | .w8 => 1
  | .w16 => 2
  | .w32 => 4
  | .w64 => 8

def aligned (address : Nat) (width : Width) : Prop :=
  address % bytes width = 0

inductive Operation where
  | construct
  | read
  | write
  deriving DecidableEq, Repr

/-- The source-level admission predicate. Construction records an assumption;
    reads and writes are admitted solely by static access authority. -/
def legal : Operation -> Access -> Bool
  | .construct, _ => true
  | .read, access => canRead access
  | .write, access => canWrite access

theorem writeOnly_cannot_read : legal .read .writeOnly = false := rfl
theorem readOnly_cannot_write : legal .write .readOnly = false := rfl
theorem readWrite_can_read : legal .read .readWrite = true := rfl
theorem readWrite_can_write : legal .write .readWrite = true := rfl

theorem legal_read_has_read_authority (access : Access)
    (h : legal .read access = true) : canRead access = true := by
  simpa [legal] using h

theorem legal_write_has_write_authority (access : Access)
    (h : legal .write access = true) : canWrite access = true := by
  simpa [legal] using h

/-- Width identity fixes the natural-alignment obligation exactly. -/
theorem aligned32_means_mod4 (address : Nat) :
    aligned address .w32 ↔ address % 4 = 0 := by
  rfl

theorem aligned64_means_mod8 (address : Nat) :
    aligned address .w64 ↔ address % 8 = 0 := by
  rfl

/-- MMIO access itself carries no ordering/completion capability. Barriers are
    a separate source operation and must be composed explicitly. -/
structure Capability where
  readsDevice : Bool
  writesDevice : Bool
  ordersMemory : Bool
  completesMemory : Bool
  instructionSync : Bool
  deriving DecidableEq, Repr

def capability : Operation -> Access -> Capability
  | .construct, _ => ⟨false, false, false, false, false⟩
  | .read, access => ⟨canRead access, false, false, false, false⟩
  | .write, access => ⟨false, canWrite access, false, false, false⟩

theorem mmio_does_not_hide_barrier (op : Operation) (access : Access) :
    (capability op access).ordersMemory = false ∧
    (capability op access).completesMemory = false ∧
    (capability op access).instructionSync = false := by
  cases op <;> cases access <;> rfl

end Oak.AArch64Mmio
