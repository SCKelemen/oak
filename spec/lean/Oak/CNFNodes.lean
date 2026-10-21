import Oak.CNFGates

set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace Oak.CNFNodes
open Oak.CNFEmission

-- Addresses retain the extracted UInt32 arithmetic. Native memory safety is a
-- separate layout obligation; readback lemmas below require bounds explicitly.
def allocate (l : Layout) (mem : Array UInt32) (key a b h n : UInt32) : Array UInt32 :=
  let mem := mem.setIfInBounds (l.var_at + n).toNat key
  let mem := mem.setIfInBounds (l.low_at + n).toNat a
  let mem := mem.setIfInBounds (l.high_at + n).toNat b
  let mem := mem.setIfInBounds (l.unique_at + h).toNat (n + 1)
  let mem := mem.setIfInBounds (l.state_at + STATE_COUNT).toNat (n + 1)
  mem.setIfInBounds (l.state_at + STATE_CREATED).toNat 1

def Matches (l : Layout) (mem : Array UInt32) (key a b n : UInt32) : Prop :=
  mem.getD (l.var_at + n).toNat 0 = key ∧
  mem.getD (l.low_at + n).toNat 0 = a ∧
  mem.getD (l.high_at + n).toNat 0 = b

theorem stopped (l : Layout) (mem : Array UInt32) (key a b h found : UInt32)
    (remaining : UInt32) (fuel : Nat) (stop : found ≠ NONE ∨ mem.getD (l.state_at + STATE_EXCEEDED).toNat 0 ≠ 0) :
    cnf_node.loop1 l mem key a b h found remaining (fuel + 1) = some (mem, h, found, remaining) := by
  rcases stop with stop | stop <;> simp only [cnf_node.loop1, beq_iff_eq, Bool.and_eq_true,
    Bool.true_and, Bool.and_true, Bool.false_and, Bool.and_false, beq_self_eq_true, if_true,
    if_false, Option.pure_def, Bind.bind, Option.bind, decide_eq_true_eq, and_true, true_and,
    and_false, false_and, not_false_eq_true, reduceCtorEq, Prod.fst, Prod.snd, stop]

theorem reuse (l : Layout) (mem : Array UInt32) (key a b h e : UInt32) (remaining : UInt32) (fuel : Nat)
    (running : mem.getD (l.state_at + STATE_EXCEEDED).toNat 0 = 0)
    (slot : mem.getD (l.unique_at + h).toNat 0 = e) (occupied : e ≠ 0)
    (inRange : ¬ e - 1 ≥ l.cap) (valid : e - 1 ≠ NONE) (hit : Matches l mem key a b (e - 1)) :
    cnf_node.loop1 l mem key a b h NONE remaining (fuel + 2) = some (mem, h, e - 1, remaining) := by
  rcases hit with ⟨hk, ha, hb⟩
  simp only [cnf_node.loop1, beq_iff_eq, Bool.and_eq_true, Bool.true_and, Bool.and_true,
    Bool.false_and, Bool.and_false, beq_self_eq_true, if_true, if_false, Option.pure_def, Bind.bind,
    Option.bind, decide_eq_true_eq, and_true, true_and, and_false, false_and, not_false_eq_true,
    reduceCtorEq, Prod.fst, Prod.snd, running, slot, occupied, inRange, hk, ha, hb, valid]

theorem collision (l : Layout) (mem : Array UInt32) (key a b h e : UInt32) (remaining : UInt32) (fuel : Nat)
    (running : mem.getD (l.state_at + STATE_EXCEEDED).toNat 0 = 0)
    (slot : mem.getD (l.unique_at + h).toNat 0 = e) (occupied : e ≠ 0)
    (inRange : ¬ e - 1 ≥ l.cap) (budget : remaining ≠ 0)
    (miss : ¬ Matches l mem key a b (e - 1)) :
    cnf_node.loop1 l mem key a b h NONE remaining (fuel + 1) =
      cnf_node.loop1 l mem key a b ((h + 1) &&& l.umask) NONE (remaining - 1) fuel := by
  have miss' : ¬ ((mem.getD (l.var_at + (e - 1)).toNat 0 = key ∧ mem.getD (l.low_at + (e - 1)).toNat 0 = a) ∧ mem.getD (l.high_at + (e - 1)).toNat 0 = b) := by
    simpa only [Matches, and_assoc] using miss
  simp only [cnf_node.loop1, beq_iff_eq, Bool.and_eq_true, Bool.true_and, Bool.and_true,
    Bool.false_and, Bool.and_false, beq_self_eq_true, if_true, if_false, Option.pure_def, Bind.bind,
    Option.bind, decide_eq_true_eq, and_true, true_and, and_false, false_and, not_false_eq_true,
    reduceCtorEq, Prod.fst, Prod.snd, running, slot, occupied, inRange, budget, miss']

theorem fresh (l : Layout) (mem : Array UInt32) (key a b h n : UInt32) (remaining : UInt32) (fuel : Nat)
    (running : mem.getD (l.state_at + STATE_EXCEEDED).toNat 0 = 0)
    (slot : mem.getD (l.unique_at + h).toNat 0 = 0)
    (count : mem.getD (l.state_at + STATE_COUNT).toNat 0 = n)
    (room : n < l.cap) (valid : n ≠ NONE) :
    cnf_node.loop1 l mem key a b h NONE remaining (fuel + 2) =
      some (allocate l mem key a b h n, h, n, remaining) := by
  have hn : ¬ n ≥ l.cap := by
    simp only [UInt32.lt_iff_toNat_lt] at room
    simp only [UInt32.le_iff_toNat_le]; omega
  simp only [cnf_node.loop1, beq_iff_eq, Bool.and_eq_true, Bool.true_and, Bool.and_true,
    Bool.false_and, Bool.and_false, beq_self_eq_true, if_true, if_false, Option.pure_def, Bind.bind,
    Option.bind, decide_eq_true_eq, and_true, true_and, and_false, false_and, not_false_eq_true,
    reduceCtorEq, Prod.fst, Prod.snd, running, slot, count, hn, valid, allocate]

theorem exhausted (l : Layout) (mem : Array UInt32) (key a b h : UInt32) (remaining : UInt32) (fuel : Nat)
    (running : mem.getD (l.state_at + STATE_EXCEEDED).toNat 0 = 0)
    (slot : mem.getD (l.unique_at + h).toNat 0 = 0)
    (full : mem.getD (l.state_at + STATE_COUNT).toNat 0 ≥ l.cap)
    (bound : (l.state_at + STATE_EXCEEDED).toNat < mem.size) :
    cnf_node.loop1 l mem key a b h NONE remaining (fuel + 2) =
      some (mem.setIfInBounds (l.state_at + STATE_EXCEEDED).toNat 1, h, NONE, remaining) := by
  simp only [cnf_node.loop1, beq_iff_eq, Bool.and_eq_true, Bool.true_and, Bool.and_true,
    Bool.false_and, Bool.and_false, beq_self_eq_true, if_true, if_false, Option.pure_def, Bind.bind,
    Option.bind, decide_eq_true_eq, and_true, true_and, and_false, false_and, not_false_eq_true,
    reduceCtorEq, Prod.fst, Prod.snd, running, slot, full,
    Oak.LRATChecker.array_getD_set_self _ _ _ _ bound,
    show (1 : UInt32) ≠ 0 by decide]

-- Refuse a corrupt table reference before reading any node field.
theorem invalid_entry (l : Layout) (mem : Array UInt32) (key a b h e remaining : UInt32)
    (fuel : Nat) (running : mem.getD (l.state_at + STATE_EXCEEDED).toNat 0 = 0)
    (slot : mem.getD (l.unique_at + h).toNat 0 = e) (occupied : e ≠ 0)
    (invalid : e - 1 ≥ l.cap)
    (bound : (l.state_at + STATE_EXCEEDED).toNat < mem.size) :
    cnf_node.loop1 l mem key a b h NONE remaining (fuel + 2) =
      some (mem.setIfInBounds (l.state_at + STATE_EXCEEDED).toNat 1, h, NONE, remaining) := by
  simp only [cnf_node.loop1, beq_iff_eq, Bool.and_eq_true, Bool.true_and, Bool.and_true,
    Bool.false_and, Bool.and_false, beq_self_eq_true, if_true, if_false, Option.pure_def, Bind.bind,
    Option.bind, decide_eq_true_eq, and_true, true_and, and_false, false_and, not_false_eq_true,
    reduceCtorEq, Prod.fst, Prod.snd, running, slot, occupied, invalid,
    Oak.LRATChecker.array_getD_set_self _ _ _ _ bound,
    show (1 : UInt32) ≠ 0 by decide]

-- The final occupied nonmatching probe refuses instead of wrapping forever.
theorem probe_exhausted (l : Layout) (mem : Array UInt32) (key a b h e : UInt32)
    (fuel : Nat) (running : mem.getD (l.state_at + STATE_EXCEEDED).toNat 0 = 0)
    (slot : mem.getD (l.unique_at + h).toNat 0 = e) (occupied : e ≠ 0)
    (inRange : ¬ e - 1 ≥ l.cap) (miss : ¬ Matches l mem key a b (e - 1))
    (bound : (l.state_at + STATE_EXCEEDED).toNat < mem.size) :
    cnf_node.loop1 l mem key a b h NONE 0 (fuel + 2) =
      some (mem.setIfInBounds (l.state_at + STATE_EXCEEDED).toNat 1, h, NONE, 0) := by
  have miss' : ¬ ((mem.getD (l.var_at + (e - 1)).toNat 0 = key ∧ mem.getD (l.low_at + (e - 1)).toNat 0 = a) ∧ mem.getD (l.high_at + (e - 1)).toNat 0 = b) := by
    simpa only [Matches, and_assoc] using miss
  simp only [cnf_node.loop1, beq_iff_eq, Bool.and_eq_true, Bool.true_and, Bool.and_true,
    Bool.false_and, Bool.and_false, beq_self_eq_true, if_true, if_false, Option.pure_def, Bind.bind,
    Option.bind, decide_eq_true_eq, and_true, true_and, and_false, false_and, not_false_eq_true,
    reduceCtorEq, Prod.fst, Prod.snd, running, slot, occupied, inRange, miss',
    Oak.LRATChecker.array_getD_set_self _ _ _ _ bound,
    show (1 : UInt32) ≠ 0 by decide]

private theorem below_cap_ne_none (n cap : UInt32) (room : ¬ n ≥ cap) : n ≠ NONE := by
  have limit := cap.toNat_lt
  intro eq
  subst n
  simp [UInt32.le_iff_toNat_le, NONE] at room
  omega

-- Every probe loop returns with enough fuel, even for a saturated table.
-- Only the exceeded flag must be writable; table contents need no invariant.
theorem loop_terminates (l : Layout) (mem : Array UInt32) (key a b h remaining : UInt32)
    (fuel : Nat) (bound : (l.state_at + STATE_EXCEEDED).toNat < mem.size) :
    ∃ out, cnf_node.loop1 l mem key a b h NONE remaining
      (fuel + remaining.toNat + 2) = some out := by
  generalize hr : remaining.toNat = r
  induction r using Nat.strongRecOn generalizing remaining h with
  | ind r ih =>
    by_cases running : mem.getD (l.state_at + STATE_EXCEEDED).toNat 0 = 0
    · let e := mem.getD (l.unique_at + h).toNat 0
      by_cases empty : e = 0
      · have slot : mem.getD (l.unique_at + h).toNat 0 = 0 := empty
        by_cases full : mem.getD (l.state_at + STATE_COUNT).toNat 0 ≥ l.cap
        · exact ⟨_, exhausted l mem key a b h remaining (fuel + r) running slot full bound⟩
        · have room : mem.getD (l.state_at + STATE_COUNT).toNat 0 < l.cap := by
            simp only [UInt32.le_iff_toNat_le] at full
            simp only [UInt32.lt_iff_toNat_lt]; omega
          exact ⟨_, fresh l mem key a b h _ remaining (fuel + r) running slot rfl room
            (below_cap_ne_none _ _ full)⟩
      · by_cases invalid : e - 1 ≥ l.cap
        · exact ⟨_, invalid_entry l mem key a b h e remaining (fuel + r) running rfl empty invalid bound⟩
        · by_cases hit : Matches l mem key a b (e - 1)
          · exact ⟨_, reuse l mem key a b h e remaining (fuel + r) running rfl empty invalid
              (below_cap_ne_none _ _ invalid) hit⟩
          · by_cases zero : remaining = 0
            · subst remaining
              have rz : r = 0 := by simpa using hr.symm
              subst r
              exact ⟨_, probe_exhausted l mem key a b h e fuel running rfl empty invalid hit bound⟩
            · have positive : 1 ≤ remaining := by
                simp only [UInt32.le_iff_toNat_le]
                have nz : remaining.toNat ≠ 0 := by
                  intro eq; apply zero; exact UInt32.toNat_inj.mp eq
                change 1 ≤ remaining.toNat
                omega
              have dec : (remaining - 1).toNat + 1 = r := by
                rw [UInt32.toNat_sub_of_le _ _ positive]
                change remaining.toNat - 1 + 1 = r
                simp only [UInt32.le_iff_toNat_le] at positive
                change 1 ≤ remaining.toNat at positive
                omega
              obtain ⟨out, run⟩ := ih (remaining - 1).toNat (by omega)
                ((h + 1) &&& l.umask) (remaining - 1) rfl
              refine ⟨out, ?_⟩
              rw [show fuel + r + 2 = (fuel + (remaining - 1).toNat + 2) + 1 by omega,
                collision l mem key a b h e remaining _ running rfl empty invalid zero hit]
              exact run
    · refine ⟨(mem, h, NONE, remaining), ?_⟩
      simpa [Nat.add_assoc] using
        stopped l mem key a b h NONE remaining (fuel + r + 1) (Or.inr running)

-- A finite sequence of occupied, in-range, nonmatching probes. The
-- countdown makes the execution bound explicit; global table uniqueness is
-- still a separate invariant.
inductive Probes (l : Layout) (mem : Array UInt32) (key a b : UInt32) :
    UInt32 → UInt32 → UInt32 → UInt32 → Nat → Prop
  | done (h remaining : UInt32) : Probes l mem key a b h h remaining remaining 0
  | step (h finish e remaining finalRemaining : UInt32) (n : Nat)
      (slot : mem.getD (l.unique_at + h).toNat 0 = e) (occupied : e ≠ 0)
      (inRange : ¬ e - 1 ≥ l.cap) (budget : remaining ≠ 0)
      (miss : ¬ Matches l mem key a b (e - 1))
      (tail : Probes l mem key a b ((h + 1) &&& l.umask) finish
        (remaining - 1) finalRemaining n) :
      Probes l mem key a b h finish remaining finalRemaining (n + 1)

theorem probes_execution (l : Layout) (mem : Array UInt32)
    (key a b start finish remaining finalRemaining : UInt32)
    (n fuel : Nat) (running : mem.getD (l.state_at + STATE_EXCEEDED).toNat 0 = 0)
    (path : Probes l mem key a b start finish remaining finalRemaining n) :
    cnf_node.loop1 l mem key a b start NONE remaining (fuel + n) =
      cnf_node.loop1 l mem key a b finish NONE finalRemaining fuel := by
  induction path with
  | done => rfl
  | step h finish e remaining finalRemaining n slot occupied inRange budget miss tail ih =>
    rw [show fuel + (n + 1) = (fuel + n) + 1 by omega,
      collision l mem key a b h e remaining (fuel + n) running slot occupied inRange budget miss, ih]

theorem production (l : Layout) (mem after : Array UInt32)
    (key a b hash finish result remaining : UInt32)
    (fuel : Nat) (hashed : hash3 key a b fuel = some hash)
    (run : cnf_node.loop1 l (mem.setIfInBounds (l.state_at + STATE_CREATED).toNat 0)
      key a b (hash &&& l.umask) NONE l.umask fuel = some (after, finish, result, remaining)) :
    cnf_node l mem key a b fuel = some (result, after) := by
  simp only [cnf_node, hashed, Bind.bind, Option.bind, run, Option.pure_def]

theorem production_terminates (l : Layout) (mem : Array UInt32) (key a b : UInt32)
    (fuel : Nat) (bound : (l.state_at + STATE_EXCEEDED).toNat < mem.size) :
    ∃ out, cnf_node l mem key a b (fuel + l.umask.toNat + 2) = some out := by
  obtain ⟨hash, hashed⟩ : ∃ hash, hash3 key a b (fuel + l.umask.toNat + 2) = some hash := ⟨_, rfl⟩
  obtain ⟨⟨after, finish, result, remaining⟩, run⟩ :=
    loop_terminates l (mem.setIfInBounds (l.state_at + STATE_CREATED).toNat 0)
      key a b (hash &&& l.umask) l.umask fuel (by simpa using bound)
  exact ⟨(result, after), production l mem after key a b hash finish result remaining
    (fuel + l.umask.toNat + 2) hashed run⟩

theorem allocate_size (l : Layout) (mem : Array UInt32) (key a b h n : UInt32) :
    (allocate l mem key a b h n).size = mem.size := by simp [allocate]

theorem allocate_frame (l : Layout) (mem : Array UInt32) (key a b h n : UInt32) (i : Nat)
    (hv : i ≠ (l.var_at + n).toNat) (hl : i ≠ (l.low_at + n).toNat)
    (hh : i ≠ (l.high_at + n).toNat) (hu : i ≠ (l.unique_at + h).toNat)
    (hc : i ≠ (l.state_at + STATE_COUNT).toNat) (hf : i ≠ (l.state_at + STATE_CREATED).toNat) :
    (allocate l mem key a b h n).getD i 0 = mem.getD i 0 := by
  simp only [allocate]
  repeat' rw [Oak.LRATChecker.array_getD_set_ne]
  all_goals omega

-- Pairwise disjoint, in-bounds write locations imply all six writes persist.
theorem allocate_readback (l : Layout) (mem : Array UInt32) (key a b h n : UInt32)
    (bounds : ∀ i ∈ [(l.var_at+n).toNat, (l.low_at+n).toNat, (l.high_at+n).toNat,
      (l.unique_at+h).toNat, (l.state_at+STATE_COUNT).toNat, (l.state_at+STATE_CREATED).toNat],
      i < mem.size)
    (separate : [(l.var_at+n).toNat, (l.low_at+n).toNat, (l.high_at+n).toNat,
      (l.unique_at+h).toNat, (l.state_at+STATE_COUNT).toNat,
      (l.state_at+STATE_CREATED).toNat].Pairwise (· ≠ ·)) :
    let out := allocate l mem key a b h n
    Matches l out key a b n ∧ out.getD (l.unique_at+h).toNat 0 = n+1 ∧
      out.getD (l.state_at+STATE_COUNT).toNat 0 = n+1 ∧
      out.getD (l.state_at+STATE_CREATED).toNat 0 = 1 := by
  simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
    List.pairwise_singleton, and_true] at separate
  simp only [List.mem_cons, List.not_mem_nil, or_false] at bounds
  simp only [or_imp, forall_and, forall_eq] at separate bounds
  dsimp only [allocate, Matches]
  all_goals
    simp (disch := (try simp only [Array.size_setIfInBounds]); omega) only [Oak.LRATChecker.array_getD_set_ne,
      Oak.LRATChecker.array_getD_set_self, Array.size_setIfInBounds, and_self]


theorem fresh_index (n cap old : UInt32) (room : n < cap)
    (limit : cap.toNat ≤ 2147483647) (prior : old < n) :
    n ≠ old ∧ (n + 1).toNat = n.toNat + 1 ∧ n + 1 ≠ 0 := by
  simp only [UInt32.lt_iff_toNat_lt] at room prior
  constructor
  · intro eq; subst old; omega
  constructor
  · change (n.toNat + 1) % 4294967296 = n.toNat + 1; omega
  · intro eq
    have := congrArg UInt32.toNat eq
    simp only [UInt32.toNat_add] at this
    change (n.toNat + 1) % 4294967296 = 0 at this
    omega

-- With count in [1, cap) and cap <= 2^31-1, the fresh edge cannot
-- collide with either sentinel polarity. Prior node indices are smaller.
theorem fresh_edge (n cap : UInt32) (positive : 1 ≤ n) (room : n < cap)
    (limit : cap.toNat ≤ 2147483647) :
    Oak.CNFGates.Regular (n <<< (1 : UInt32)) := by
  simp only [Oak.CNFGates.Regular, UInt32.le_iff_toNat_le, UInt32.lt_iff_toNat_lt,
    UInt32.toNat_shiftLeft] at *
  simp at *
  omega

end Oak.CNFNodes
