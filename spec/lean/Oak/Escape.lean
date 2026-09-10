namespace Oak.Escape

/-! # Borrow escape discipline

Model for `docs/spec/50-borrowing.md` section 5: a borrowed value may not
outlive its owner. Scopes are modeled by lexical depth. A live borrow records
the depth of the owner that proves its lifetime and the depth of its own
binding; well-formedness says the owner is at least as long-lived as the
borrow and the borrow does not outlive the current scope.

The conservative rule the compiler implements today — a view or span may
never leave the function that proves its owner's lifetime — corresponds to
`exit`, which drops every borrow bound in the exiting scope. `escape` models
what admitting a returned borrow would mean; escaping a borrow whose owner
lives in the exiting scope is proven to break well-formedness (the dangling
case), while escaping a borrow of a longer-lived owner is proven safe, which
is why future region-indexed signatures can relax the conservative rule
without changing the ownership model. -/

/-- A live borrow: the lexical depth of its owner and of its own binding. -/
structure LiveBorrow where
  ownerDepth : Nat
  borrowDepth : Nat
  deriving DecidableEq, Repr

/-- Checker state: current lexical depth and the live borrows. -/
structure State where
  depth : Nat
  live : List LiveBorrow
  deriving Repr

/-- Every live borrow is bound no shallower than its owner and no deeper than
    the current scope; its owner is therefore still in scope. -/
def WF (s : State) : Prop :=
  ∀ b ∈ s.live, b.ownerDepth ≤ b.borrowDepth ∧ b.borrowDepth ≤ s.depth

/-- Entering a nested lexical scope. -/
def enter (s : State) : State :=
  { s with depth := s.depth + 1 }

/-- Borrowing from an owner currently in scope binds the borrow at the
    current depth; owners not in scope cannot be borrowed. -/
def borrowFrom (s : State) (ownerDepth : Nat) : Option State :=
  if ownerDepth ≤ s.depth then
    some { s with live := ⟨ownerDepth, s.depth⟩ :: s.live }
  else
    none

/-- Leaving a scope drops every borrow bound in it. This is the conservative
    escape rule: nothing borrowed inside survives the exit. -/
def exit (s : State) : State :=
  { depth := s.depth - 1
    live := s.live.filter (fun b => b.borrowDepth < s.depth) }

/-- What admitting an escaping borrow would mean: leave the scope but keep
    one chosen borrow alive, rebound at the enclosing depth. -/
def escape (s : State) (b : LiveBorrow) : State :=
  { depth := s.depth - 1
    live := ⟨b.ownerDepth, s.depth - 1⟩ :: (exit s).live }

theorem enter_preserves_wf {s : State} (h : WF s) : WF (enter s) := by
  intro b hb
  obtain ⟨h1, h2⟩ := h b hb
  refine ⟨h1, ?_⟩
  show b.borrowDepth ≤ s.depth + 1
  omega

theorem borrow_preserves_wf {s s' : State} {ownerDepth : Nat}
    (h : WF s) (hb : borrowFrom s ownerDepth = some s') : WF s' := by
  unfold borrowFrom at hb
  by_cases hin : ownerDepth ≤ s.depth
  · simp [hin] at hb
    subst hb
    intro b hb
    cases hb with
    | head => simp; omega
    | tail _ hmem => exact h b hmem
  · simp [hin] at hb

/-- The conservative rule is sound: exiting a scope preserves the invariant
    that every live borrow's owner remains in scope. -/
theorem exit_preserves_wf {s : State} (h : WF s) : WF (exit s) := by
  intro b hb
  have hb' : b ∈ s.live.filter (fun b => b.borrowDepth < s.depth) := hb
  simp at hb'
  obtain ⟨hmem, hdepth⟩ := hb'
  obtain ⟨h1, h2⟩ := h b hmem
  refine ⟨h1, ?_⟩
  show b.borrowDepth ≤ s.depth - 1
  omega

/-- Escaping a borrow whose owner lives in the exiting scope dangles: the
    resulting state cannot be well-formed. This is the case the compiler
    must reject. -/
theorem escape_local_owner_dangles {s : State} {b : LiveBorrow}
    (hpos : 0 < s.depth) (hlocal : b.ownerDepth = s.depth) :
    ¬ WF (escape s b) := by
  intro hwf
  have hmem : (⟨b.ownerDepth, s.depth - 1⟩ : LiveBorrow) ∈ (escape s b).live :=
    List.mem_cons_self ..
  have hbound : b.ownerDepth ≤ s.depth - 1 := (hwf _ hmem).1
  omega

/-- Escaping a borrow of a strictly longer-lived owner is safe: this is the
    headroom future region-indexed signatures can claim, and why rejecting
    every escape today is conservative rather than necessary. -/
theorem escape_outer_owner_preserves_wf {s : State} {b : LiveBorrow}
    (h : WF s) (houter : b.ownerDepth < s.depth) :
    WF (escape s b) := by
  intro c hc
  unfold escape at hc
  simp at hc
  cases hc with
  | inl heq =>
    subst heq
    simp [escape]
    omega
  | inr hmem =>
    unfold exit at hmem
    simp at hmem
    obtain ⟨hlive, hdepth⟩ := hmem
    have := h c hlive
    simp [escape]
    omega

/-! ## Region-indexed returns (docs/spec/50-borrowing.md section 8c)

A call enters the callee's scope from the caller's. The callee's parameters
are borrows of owners that live at the caller's depth or shallower, so a
returned borrow whose owner is a parameter's owner has `ownerDepth ≤ depth - 1`
inside the callee: strictly shallower than the callee's scope. Returning it is
`escape` in the safe case. The compiler's elision rule (one view parameter of
the return's element type) and provenance check (`OAK-B0112`) establish
exactly the hypothesis `hparam` below; a returned borrow of a callee-local
owner is `escape_local_owner_dangles`. -/

/-- The callee's obligation discharged: a returned borrow drawn from a
    parameter's owner preserves well-formedness. -/
theorem return_param_borrow_wf {s : State} {b : LiveBorrow}
    (h : WF s) (hpos : 0 < s.depth) (hparam : b.ownerDepth ≤ s.depth - 1) :
    WF (escape s b) :=
  escape_outer_owner_preserves_wf h (by omega)

/-- The caller's side: the result of a region-indexed call is a reborrow of
    the argument — a new borrow of the argument's owner, bound at the
    caller's current depth. -/
def reborrow (s : State) (b : LiveBorrow) : State :=
  { s with live := ⟨b.ownerDepth, s.depth⟩ :: s.live }

/-- Reborrowing a live borrow preserves well-formedness: the argument's owner
    is in scope because the argument's borrow was, and the result is bound
    no deeper than the current scope. -/
theorem reborrow_wf {s : State} {b : LiveBorrow} (h : WF s) (hb : b ∈ s.live) :
    WF (reborrow s b) := by
  intro c hc
  unfold reborrow at hc
  simp at hc
  cases hc with
  | inl heq =>
    subst heq
    obtain ⟨h1, h2⟩ := h b hb
    simp [reborrow]
    omega
  | inr hmem =>
    exact h c hmem

end Oak.Escape
