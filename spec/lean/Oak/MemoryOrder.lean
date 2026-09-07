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
  | compareExchange
  | fence
  deriving DecidableEq, Repr

/-- Oak's single-order atomic legality matrix. Compare-exchange is checked by
    `casLegal` because success and failure orders are related. -/
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
  | .compareExchange, _ => false
  | .fence, .relaxed => false
  | .fence, _ => true

/-- Strong compare-exchange legality. Failure never writes, hence release and
    acq-rel are forbidden, and failure may not be stronger than success. -/
def casLegal : Order -> Order -> Bool
  | .relaxed, .relaxed => true
  | .acquire, .relaxed => true
  | .acquire, .acquire => true
  | .release, .relaxed => true
  | .acqRel, .relaxed => true
  | .acqRel, .acquire => true
  | .seqCst, .relaxed => true
  | .seqCst, .acquire => true
  | .seqCst, .seqCst => true
  | _, _ => false

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

theorem legal_load_not_release (o : Order)
    (h : legal .load o = true) : o != .release ∧ o != .acqRel := by
  cases o <;> simp_all [legal]

theorem legal_store_not_acquire (o : Order)
    (h : legal .store o = true) : o != .acquire ∧ o != .acqRel := by
  cases o <;> simp_all [legal]

/-- Failure ordering of a legal CAS can never have release semantics. -/
theorem cas_failure_not_release (success failure : Order)
    (h : casLegal success failure = true) :
    failure != .release ∧ failure != .acqRel := by
  cases success <;> cases failure <;> simp_all [casLegal]

/-- Relaxed success permits only relaxed failure. -/
theorem relaxed_cas_failure_relaxed (failure : Order)
    (h : casLegal .relaxed failure = true) : failure = .relaxed := by
  cases failure <;> simp_all [casLegal]

/-- Release-only success cannot acquire on failure. -/
theorem release_cas_failure_relaxed (failure : Order)
    (h : casLegal .release failure = true) : failure = .relaxed := by
  cases failure <;> simp_all [casLegal]

/-- The exact source-level atomic builtin set. Order is encoded in builtin
    identity, so no runtime order enum exists. CAS names encode success then
    failure order. -/
inductive Builtin where
  | loadRelaxed
  | loadAcquire
  | loadSeqCst
  | storeRelaxed
  | storeRelease
  | storeSeqCst
  | fetchAddRelaxed
  | fetchAddAcquire
  | fetchAddRelease
  | fetchAddAcqRel
  | fetchAddSeqCst
  | compareExchangeRelaxedRelaxed
  | compareExchangeAcquireRelaxed
  | compareExchangeAcquireAcquire
  | compareExchangeReleaseRelaxed
  | compareExchangeAcqRelRelaxed
  | compareExchangeAcqRelAcquire
  | compareExchangeSeqCstRelaxed
  | compareExchangeSeqCstAcquire
  | compareExchangeSeqCstSeqCst
  | fenceAcquire
  | fenceRelease
  | fenceAcqRel
  | fenceSeqCst
  deriving DecidableEq, Repr

def builtinOp : Builtin -> AtomicOp
  | .loadRelaxed | .loadAcquire | .loadSeqCst => .load
  | .storeRelaxed | .storeRelease | .storeSeqCst => .store
  | .fetchAddRelaxed | .fetchAddAcquire | .fetchAddRelease
  | .fetchAddAcqRel | .fetchAddSeqCst => .rmw
  | .compareExchangeRelaxedRelaxed
  | .compareExchangeAcquireRelaxed
  | .compareExchangeAcquireAcquire
  | .compareExchangeReleaseRelaxed
  | .compareExchangeAcqRelRelaxed
  | .compareExchangeAcqRelAcquire
  | .compareExchangeSeqCstRelaxed
  | .compareExchangeSeqCstAcquire
  | .compareExchangeSeqCstSeqCst => .compareExchange
  | .fenceAcquire | .fenceRelease | .fenceAcqRel | .fenceSeqCst => .fence

def builtinOrder : Builtin -> Order
  | .loadRelaxed => .relaxed
  | .loadAcquire => .acquire
  | .loadSeqCst => .seqCst
  | .storeRelaxed => .relaxed
  | .storeRelease => .release
  | .storeSeqCst => .seqCst
  | .fetchAddRelaxed => .relaxed
  | .fetchAddAcquire => .acquire
  | .fetchAddRelease => .release
  | .fetchAddAcqRel => .acqRel
  | .fetchAddSeqCst => .seqCst
  | .compareExchangeRelaxedRelaxed => .relaxed
  | .compareExchangeAcquireRelaxed | .compareExchangeAcquireAcquire => .acquire
  | .compareExchangeReleaseRelaxed => .release
  | .compareExchangeAcqRelRelaxed | .compareExchangeAcqRelAcquire => .acqRel
  | .compareExchangeSeqCstRelaxed | .compareExchangeSeqCstAcquire
  | .compareExchangeSeqCstSeqCst => .seqCst
  | .fenceAcquire => .acquire
  | .fenceRelease => .release
  | .fenceAcqRel => .acqRel
  | .fenceSeqCst => .seqCst

def builtinFailureOrder : Builtin -> Option Order
  | .compareExchangeRelaxedRelaxed => some .relaxed
  | .compareExchangeAcquireRelaxed => some .relaxed
  | .compareExchangeAcquireAcquire => some .acquire
  | .compareExchangeReleaseRelaxed => some .relaxed
  | .compareExchangeAcqRelRelaxed => some .relaxed
  | .compareExchangeAcqRelAcquire => some .acquire
  | .compareExchangeSeqCstRelaxed => some .relaxed
  | .compareExchangeSeqCstAcquire => some .acquire
  | .compareExchangeSeqCstSeqCst => some .seqCst
  | _ => none

def builtinLegal (b : Builtin) : Bool :=
  match builtinFailureOrder b with
  | some failure => casLegal (builtinOrder b) failure
  | none => legal (builtinOp b) (builtinOrder b)

/-- Every operation expressible by the source surface satisfies the applicable
    single-order or compare-exchange legality relation. -/
theorem source_builtin_legal (b : Builtin) : builtinLegal b = true := by
  cases b <;> rfl

theorem source_load_not_release (b : Builtin)
    (h : builtinOp b = .load) :
    builtinOrder b != .release ∧ builtinOrder b != .acqRel := by
  cases b <;> simp_all [builtinOp, builtinOrder]

theorem source_store_not_acquire (b : Builtin)
    (h : builtinOp b = .store) :
    builtinOrder b != .acquire ∧ builtinOrder b != .acqRel := by
  cases b <;> simp_all [builtinOp, builtinOrder]

theorem source_fence_not_relaxed (b : Builtin)
    (h : builtinOp b = .fence) : builtinOrder b != .relaxed := by
  cases b <;> simp_all [builtinOp, builtinOrder]

/-- Any source CAS constructor has a failure order and that pair is legal.
    The failure-order equality is eliminated before reducing `casLegal`; this
    keeps the proof tied directly to the source constructor table. -/
theorem source_cas_pair_legal (b : Builtin) (failure : Order)
    (hOp : builtinOp b = .compareExchange)
    (hFailure : builtinFailureOrder b = some failure) :
    casLegal (builtinOrder b) failure = true := by
  cases b <;> simp_all [builtinOp, builtinFailureOrder, builtinOrder, casLegal]

/-- No source CAS can express release/acq-rel failure ordering. -/
theorem source_cas_failure_not_release (b : Builtin) (failure : Order)
    (hOp : builtinOp b = .compareExchange)
    (hFailure : builtinFailureOrder b = some failure) :
    failure != .release ∧ failure != .acqRel := by
  have hLegal := source_cas_pair_legal b failure hOp hFailure
  exact cas_failure_not_release (builtinOrder b) failure hLegal

end Oak.MemoryOrder
