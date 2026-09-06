namespace Oak.MemoryOrder

inductive Order where
  | relaxed
  | acquire
  | release
  | acqRel
  | seqCst
  deriving DecidableEq, Repr

inductive AtomicOp where
  | load
  | store
  | rmw
  | fence
  deriving DecidableEq, Repr

/-- Oak's v1 atomic memory-order legality matrix. This is deliberately
    independent of any compiler backend. -/
def legal : AtomicOp -> Order -> Bool
  | .load, .relaxed => true
  | .load, .acquire => true
  | .load, .seqCst => true
  | .load, _ => false
  | .store, .relaxed => true
  | .store, .release => true
  | .store, .seqCst => true
  | .store, _ => false
  | .rmw, _ => true
  | .fence, .relaxed => false
  | .fence, _ => true

theorem load_relaxed_legal : legal .load .relaxed = true := rfl
theorem load_acquire_legal : legal .load .acquire = true := rfl
theorem load_seqCst_legal : legal .load .seqCst = true := rfl

theorem load_release_illegal : legal .load .release = false := rfl
theorem load_acqRel_illegal : legal .load .acqRel = false := rfl

theorem store_relaxed_legal : legal .store .relaxed = true := rfl
theorem store_release_legal : legal .store .release = true := rfl
theorem store_seqCst_legal : legal .store .seqCst = true := rfl

theorem store_acquire_illegal : legal .store .acquire = false := rfl
theorem store_acqRel_illegal : legal .store .acqRel = false := rfl

theorem rmw_all_orders_legal (o : Order) : legal .rmw o = true := by
  cases o <;> rfl

theorem relaxed_fence_illegal : legal .fence .relaxed = false := rfl

theorem synchronization_fences_legal (o : Order)
    (h : o != .relaxed) : legal .fence o = true := by
  cases o <;> simp_all [legal]

/-- A legal load never has release-only or acquire-release ordering. -/
theorem legal_load_not_release (o : Order)
    (h : legal .load o = true) : o != .release ∧ o != .acqRel := by
  cases o <;> simp_all [legal]

/-- A legal store never has acquire-only or acquire-release ordering. -/
theorem legal_store_not_acquire (o : Order)
    (h : legal .store o = true) : o != .acquire ∧ o != .acqRel := by
  cases o <;> simp_all [legal]

end Oak.MemoryOrder
