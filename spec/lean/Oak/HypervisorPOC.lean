namespace Oak.HypervisorPOC

/-! # Hypervisor proof-of-concepts

These are deliberately small proofs over the same semantic shapes exercised by
`compiler/hypervisor_poc_test.go`. They demonstrate the intended Oak workflow:
executable systems code and mathematical laws evolve together, while the status
remains honest about the missing implementation-refinement link.

This file does **not** claim that the generated C is formally refined to these
models. That is a later proof obligation.
-/

/-! ## Virtual IRQ lifecycle -/

inductive IrqState where
  | disabled
  | idle
  | pending
  | active
  | activePending
  deriving DecidableEq, Repr

open IrqState

def raise : IrqState → IrqState
  | disabled => disabled
  | idle => pending
  | pending => pending
  | active => activePending
  | activePending => activePending


def acknowledge : IrqState → IrqState
  | pending => active
  | s => s


def eoi : IrqState → IrqState
  | active => idle
  | activePending => pending
  | s => s

/-- An edge arriving while an IRQ is active is not lost: EOI exposes it as a
    fresh pending interrupt. -/
theorem edge_while_active_repends : eoi (raise active) = pending := by
  rfl

/-- A normal pending interrupt acknowledges to active and EOI returns it idle. -/
theorem pending_ack_eoi_idle : eoi (acknowledge pending) = idle := by
  rfl

/-- Disabled IRQs remain disabled under injection. -/
theorem disabled_does_not_raise : raise disabled = disabled := by
  rfl

/-! ## Deliverability -/

structure Irq where
  enabled : Bool
  pending : Bool
  active : Bool
  priority : Nat
  deriving DecidableEq, Repr


def Deliverable (mask : Nat) (irq : Irq) : Prop :=
  irq.enabled = true ∧
  irq.pending = true ∧
  irq.active = false ∧
  irq.priority < mask


theorem deliverable_enabled {mask : Nat} {irq : Irq}
    (h : Deliverable mask irq) : irq.enabled = true :=
  h.1


theorem deliverable_pending {mask : Nat} {irq : Irq}
    (h : Deliverable mask irq) : irq.pending = true :=
  h.2.1


theorem deliverable_not_active {mask : Nat} {irq : Irq}
    (h : Deliverable mask irq) : irq.active = false :=
  h.2.2.1


theorem deliverable_priority_below_mask {mask : Nat} {irq : Irq}
    (h : Deliverable mask irq) : irq.priority < mask :=
  h.2.2.2

/-! ## Stage-2 page arithmetic -/

abbrev PageSize : Nat := 4096


def pageBase (addr : Nat) : Nat :=
  (addr / PageSize) * PageSize


def pageOffset (addr : Nat) : Nat :=
  addr % PageSize


def pageIndex (addr : Nat) : Nat :=
  addr / PageSize

/-- Every page base is aligned to the 4 KiB granule used by the initial OS
    stage-2 model. -/
theorem page_base_aligned (addr : Nat) : pageBase addr % PageSize = 0 := by
  simp [pageBase, PageSize]

/-- The offset is always inside the page. -/
theorem page_offset_in_range (addr : Nat) : pageOffset addr < PageSize := by
  exact Nat.mod_lt addr (by decide)

/-- Page index/base/offset reconstruct the original address exactly in the
    mathematical model. Machine-u64 overflow correspondence remains a separate
    refinement obligation. -/
theorem page_decomposition (addr : Nat) : pageBase addr + pageOffset addr = addr := by
  unfold pageBase pageOffset
  rw [Nat.mul_comm (addr / PageSize) PageSize]
  exact Nat.div_add_mod addr PageSize

/-- `pageBase` is exactly the indexed page multiplied by the granule. -/
theorem page_base_from_index (addr : Nat) :
    pageBase addr = pageIndex addr * PageSize := by
  rfl

/-! ## Generational handles -/

structure Handle where
  slot : Nat
  generation : Nat
  deriving DecidableEq, Repr

structure Slot where
  generation : Nat
  occupied : Bool
  deriving DecidableEq, Repr


def Resolves (h : Handle) (s : Slot) : Prop :=
  s.occupied = true ∧ h.generation = s.generation


def reuse (s : Slot) : Slot :=
  { generation := s.generation + 1, occupied := true }

/-- If a handle matched the old generation, advancing the slot generation on
    reuse makes that handle stale. The production finite-width implementation
    must retire on generation exhaustion rather than wrap; that policy is
    already modeled separately by Oak's handle work. -/
theorem stale_handle_fails_after_reuse {h : Handle} {s : Slot}
    (old : h.generation = s.generation) : ¬ Resolves h (reuse s) := by
  intro resolved
  unfold Resolves reuse at resolved
  dsimp at resolved
  omega

end Oak.HypervisorPOC
