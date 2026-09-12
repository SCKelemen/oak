import Oak.MemoryOrder

/-! # Compiler correspondence for the atomic order tables

`Oak.MemoryOrder` states Oak's memory-order legality — which orders each
atomic operation admits (`legal`), which success/failure pairs a strong
compare-exchange admits (`casLegal`) — and the closed set of source
builtins (`docs/spec/65-machine-memory.md` §2–§4). The compiler carries the
same decisions as Go functions (`semir.LegalAtomicOrder`,
`semir.LegalCompareExchangeOrders`, `semir.LookupAtomicBuiltin`) and the C
backend maps each order to its C11 constant (`codegen.cMemoryOrder`).

This module states the correspondence in the form `Oak.ModulesRefinement`
uses: the two relations are enumerated into explicit truth tables, proved
by `decide`, and the source builtin catalogue — name, operation, order,
failure order — is listed with every entry proved legal. The Go tests in
`semir/memory_refinement_test.go` pin the identical tables and catalogue
against the Go functions, so the two pins are the correspondence: a change
to either side has to visit the other.

The catalogue here includes the five `atomic_exchange_*` builtins the Go
side defines (`65-machine-memory.md` §4), which `Oak.MemoryOrder.Builtin`
predates; exchange is an RMW and shares the RMW row. -/

namespace Oak.MemoryOrderRefinement

open Oak.MemoryOrder

/-- Every order, in the Go enumeration's order (`semir.MemoryOrder`). -/
def orders : List Order := [.relaxed, .acquire, .release, .acqRel, .seqCst]

/-- Every single-order operation, in the Go enumeration's order
    (`semir.AtomicOperation`: load, store, rmw, fence). Compare-exchange is
    judged by `casLegal` and is never legal as a single-order operation. -/
def ops : List AtomicOp := [.load, .store, .rmw, .fence]

/-- `legal` as a table: one row per operation, one column per order. -/
def legalTable : List (List Bool) := ops.map fun op => orders.map (legal op)

/-- The pinned table (`semir/memory_refinement_test.go`, `legalTable`). -/
theorem legal_table :
    legalTable =
      [[true, true, false, false, true],    -- load: relaxed, acquire, seq_cst
       [true, false, true, false, true],    -- store: relaxed, release, seq_cst
       [true, true, true, true, true],      -- rmw: every order
       [false, true, true, true, true]] := by decide  -- fence: every order but relaxed

/-- Compare-exchange as a single-order operation is never legal. -/
theorem compare_exchange_single_order_illegal : orders.map (legal .compareExchange) = [false, false, false, false, false] := by
  decide

/-- `casLegal` as a table: one row per success order, one column per
    failure order. -/
def casTable : List (List Bool) := orders.map fun success => orders.map (casLegal success)

/-- The pinned table (`semir/memory_refinement_test.go`, `casTable`). -/
theorem cas_table :
    casTable =
      [[true, false, false, false, false],   -- relaxed success: relaxed failure
       [true, true, false, false, false],    -- acquire: relaxed, acquire
       [true, false, false, false, false],   -- release: relaxed
       [true, true, false, false, false],    -- acq_rel: relaxed, acquire
       [true, true, false, false, true]] := by decide  -- seq_cst: relaxed, acquire, seq_cst

/-- One source builtin: its name, operation, order, and failure order for a
    compare-exchange. -/
structure Entry where
  name : String
  op : AtomicOp
  order : Order
  failure : Option Order
  deriving Repr

/-- The closed source surface (`65-machine-memory.md` §2–§4), in the order
    `semir.LookupAtomicBuiltin` spells it. Exchange shares the RMW row. -/
def catalogue : List Entry :=
  [ ⟨"atomic_load_relaxed", .load, .relaxed, none⟩,
    ⟨"atomic_load_acquire", .load, .acquire, none⟩,
    ⟨"atomic_load_seq_cst", .load, .seqCst, none⟩,
    ⟨"atomic_store_relaxed", .store, .relaxed, none⟩,
    ⟨"atomic_store_release", .store, .release, none⟩,
    ⟨"atomic_store_seq_cst", .store, .seqCst, none⟩,
    ⟨"atomic_fetch_add_relaxed", .rmw, .relaxed, none⟩,
    ⟨"atomic_fetch_add_acquire", .rmw, .acquire, none⟩,
    ⟨"atomic_fetch_add_release", .rmw, .release, none⟩,
    ⟨"atomic_fetch_add_acq_rel", .rmw, .acqRel, none⟩,
    ⟨"atomic_fetch_add_seq_cst", .rmw, .seqCst, none⟩,
    ⟨"atomic_exchange_relaxed", .rmw, .relaxed, none⟩,
    ⟨"atomic_exchange_acquire", .rmw, .acquire, none⟩,
    ⟨"atomic_exchange_release", .rmw, .release, none⟩,
    ⟨"atomic_exchange_acq_rel", .rmw, .acqRel, none⟩,
    ⟨"atomic_exchange_seq_cst", .rmw, .seqCst, none⟩,
    ⟨"atomic_compare_exchange_relaxed_relaxed", .compareExchange, .relaxed, some .relaxed⟩,
    ⟨"atomic_compare_exchange_acquire_relaxed", .compareExchange, .acquire, some .relaxed⟩,
    ⟨"atomic_compare_exchange_acquire_acquire", .compareExchange, .acquire, some .acquire⟩,
    ⟨"atomic_compare_exchange_release_relaxed", .compareExchange, .release, some .relaxed⟩,
    ⟨"atomic_compare_exchange_acq_rel_relaxed", .compareExchange, .acqRel, some .relaxed⟩,
    ⟨"atomic_compare_exchange_acq_rel_acquire", .compareExchange, .acqRel, some .acquire⟩,
    ⟨"atomic_compare_exchange_seq_cst_relaxed", .compareExchange, .seqCst, some .relaxed⟩,
    ⟨"atomic_compare_exchange_seq_cst_acquire", .compareExchange, .seqCst, some .acquire⟩,
    ⟨"atomic_compare_exchange_seq_cst_seq_cst", .compareExchange, .seqCst, some .seqCst⟩,
    ⟨"atomic_fence_acquire", .fence, .acquire, none⟩,
    ⟨"atomic_fence_release", .fence, .release, none⟩,
    ⟨"atomic_fence_acq_rel", .fence, .acqRel, none⟩,
    ⟨"atomic_fence_seq_cst", .fence, .seqCst, none⟩ ]

/-- An entry's legality: the compare-exchange pair relation for a CAS, the
    single-order relation otherwise — what `semir.AtomicBuiltinSpec.Legal`
    decides. -/
def entryLegal (e : Entry) : Bool :=
  match e.failure with
  | some failure => casLegal e.order failure
  | none => legal e.op e.order

/-- Every catalogued builtin is legal. -/
theorem catalogue_legal : catalogue.all entryLegal = true := by decide

/-- The catalogue has twenty-nine entries, each name once — the count the Go
    pin checks against `LookupAtomicBuiltin`. -/
theorem catalogue_size : catalogue.length = 29 := by decide

theorem catalogue_names_distinct : (catalogue.map Entry.name).Nodup := by decide

/-- Every compare-exchange entry carries a failure order and nothing else
    does: the Go `FailureOrder` field is set exactly for the CAS family. -/
theorem failure_iff_cas : catalogue.all (fun e => (e.failure.isSome) == (e.op == .compareExchange)) = true := by
  decide

/-- The fence family omits relaxed: no relaxed fence is spelled. -/
theorem no_relaxed_fence : catalogue.all (fun e => !(e.op == .fence && e.order == .relaxed)) = true := by
  decide

end Oak.MemoryOrderRefinement
