namespace Oak.Discipline

/-! # Bounded-execution discipline: safe recursion

Model for `docs/spec/85-discipline.md`. The strict discipline profile
(MISRA C, NASA Power of Ten rule 1, TigerStyle) requires statically bounded
stack depth. Oak does not ban recursion; it requires recursion to be safe:
tail calls cost no stack frame once the backend eliminates them, so only
non-tail ("stack") calls may consume depth.

The compiler accepts a call graph by producing a **rank certificate**:
ranks strictly decrease across every stack call and never increase across a
tail call (the SCC condensation order, with every member of a recursive
group sharing one rank). This module proves the certificate is the right
acceptance criterion: stack depth along any call chain — of any length,
including unbounded tail loops — is bounded by the start's rank, and every
call cycle in an accepted graph is tail-only, hence eliminable.

Nodes are function identities (`Nat`). A chain step `(isTail, next)` records
one call; `stackDepth` counts the steps that consume a stack frame. -/

/-- The rank certificate: strict decrease on stack calls, no increase on
    tail calls. A completed topological sort of the call graph's strongly
    connected components provides exactly this. -/
def Ranked (stackEdges tailEdges : List (Nat × Nat)) (rank : Nat → Nat) : Prop :=
  (∀ e ∈ stackEdges, rank e.2 < rank e.1) ∧
  (∀ e ∈ tailEdges, rank e.2 ≤ rank e.1)

/-- `IsCallChain stackEdges tailEdges start steps`: each step is a call from
    the current node to the step's node, labeled tail or stack. -/
def IsCallChain (stackEdges tailEdges : List (Nat × Nat)) :
    Nat → List (Bool × Nat) → Prop
  | _, [] => True
  | a, (isTail, b) :: rest =>
    (if isTail then (a, b) ∈ tailEdges else (a, b) ∈ stackEdges) ∧
      IsCallChain stackEdges tailEdges b rest

/-- Frames consumed by a chain: tail steps are free. -/
def stackDepth (steps : List (Bool × Nat)) : Nat :=
  (steps.filter (fun s => !s.1)).length

/-- The node a chain ends on. -/
def endNode (start : Nat) : List (Bool × Nat) → Nat
  | [] => start
  | (_, b) :: rest => endNode b rest

theorem stackDepth_cons_tail (b : Nat) (rest : List (Bool × Nat)) :
    stackDepth ((true, b) :: rest) = stackDepth rest := by
  simp [stackDepth]

theorem stackDepth_cons_stack (b : Nat) (rest : List (Bool × Nat)) :
    stackDepth ((false, b) :: rest) = stackDepth rest + 1 := by
  simp [stackDepth]

/-- The engine: along any chain, the end's rank plus the frames consumed
    never exceeds the start's rank. -/
theorem rank_absorbs_stack_depth {stackEdges tailEdges : List (Nat × Nat)}
    {rank : Nat → Nat} (hranked : Ranked stackEdges tailEdges rank) :
    ∀ (start : Nat) (steps : List (Bool × Nat)),
      IsCallChain stackEdges tailEdges start steps →
      rank (endNode start steps) + stackDepth steps ≤ rank start := by
  intro start steps
  induction steps generalizing start with
  | nil =>
    intro _
    simp [endNode, stackDepth]
  | cons step rest ih =>
    intro ⟨hedge, hchain⟩
    obtain ⟨isTail, b⟩ := step
    have hrest := ih b hchain
    have hend : endNode start ((isTail, b) :: rest) = endNode b rest := rfl
    cases isTail with
    | true =>
      have hb : rank b ≤ rank start := hranked.2 (start, b) hedge
      rw [hend, stackDepth_cons_tail]
      omega
    | false =>
      have hb : rank b < rank start := hranked.1 (start, b) hedge
      rw [hend, stackDepth_cons_stack]
      omega

/-- **Static stack bound**: no chain from `start` — however long its tail
    segments — consumes more than `rank start` frames. -/
theorem stack_depth_bounded {stackEdges tailEdges : List (Nat × Nat)}
    {rank : Nat → Nat} (hranked : Ranked stackEdges tailEdges rank)
    {start : Nat} {steps : List (Bool × Nat)}
    (hchain : IsCallChain stackEdges tailEdges start steps) :
    stackDepth steps ≤ rank start := by
  have := rank_absorbs_stack_depth hranked start steps hchain
  omega

/-- **No stack-consuming self call**: direct non-tail recursion cannot be
    ranked. Direct tail recursion remains admissible. -/
theorem no_stack_self_call {stackEdges tailEdges : List (Nat × Nat)}
    {rank : Nat → Nat} (hranked : Ranked stackEdges tailEdges rank)
    (f : Nat) : (f, f) ∉ stackEdges := by
  intro hmem
  exact absurd (hranked.1 (f, f) hmem) (Nat.lt_irrefl _)

/-- **Cycles are tail-only**: any chain returning to its start consumed no
    stack frame, so every recursive group in an accepted graph is fully
    eliminable by tail-call elimination or trampolining. -/
theorem cycle_is_all_tail {stackEdges tailEdges : List (Nat × Nat)}
    {rank : Nat → Nat} (hranked : Ranked stackEdges tailEdges rank)
    {f : Nat} {steps : List (Bool × Nat)}
    (hchain : IsCallChain stackEdges tailEdges f steps)
    (hcycle : endNode f steps = f) : stackDepth steps = 0 := by
  have := rank_absorbs_stack_depth hranked f steps hchain
  rw [hcycle] at this
  omega

end Oak.Discipline
