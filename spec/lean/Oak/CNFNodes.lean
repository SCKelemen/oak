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
    (fuel : Nat) (stop : found ≠ NONE ∨ mem.getD (l.state_at + STATE_EXCEEDED).toNat 0 ≠ 0) :
    cnf_node.loop1 l mem key a b h found (fuel + 1) = some (mem, h, found) := by
  rcases stop with stop | stop <;> simp only [cnf_node.loop1, beq_iff_eq, Bool.and_eq_true,
    Bool.true_and, Bool.and_true, Bool.false_and, Bool.and_false, beq_self_eq_true, if_true,
    if_false, Option.pure_def, Bind.bind, Option.bind, decide_eq_true_eq, and_true, true_and,
    and_false, false_and, not_false_eq_true, reduceCtorEq, Prod.fst, Prod.snd, stop]

theorem reuse (l : Layout) (mem : Array UInt32) (key a b h e : UInt32) (fuel : Nat)
    (running : mem.getD (l.state_at + STATE_EXCEEDED).toNat 0 = 0)
    (slot : mem.getD (l.unique_at + h).toNat 0 = e) (occupied : e ≠ 0)
    (valid : e - 1 ≠ NONE) (hit : Matches l mem key a b (e - 1)) :
    cnf_node.loop1 l mem key a b h NONE (fuel + 2) = some (mem, h, e - 1) := by
  rcases hit with ⟨hk, ha, hb⟩
  simp only [cnf_node.loop1, beq_iff_eq, Bool.and_eq_true, Bool.true_and, Bool.and_true,
    Bool.false_and, Bool.and_false, beq_self_eq_true, if_true, if_false, Option.pure_def, Bind.bind,
    Option.bind, decide_eq_true_eq, and_true, true_and, and_false, false_and, not_false_eq_true,
    reduceCtorEq, Prod.fst, Prod.snd, running, slot, occupied, hk, ha, hb, valid]

theorem collision (l : Layout) (mem : Array UInt32) (key a b h e : UInt32) (fuel : Nat)
    (running : mem.getD (l.state_at + STATE_EXCEEDED).toNat 0 = 0)
    (slot : mem.getD (l.unique_at + h).toNat 0 = e) (occupied : e ≠ 0)
    (miss : ¬ Matches l mem key a b (e - 1)) :
    cnf_node.loop1 l mem key a b h NONE (fuel + 1) =
      cnf_node.loop1 l mem key a b ((h + 1) &&& l.umask) NONE fuel := by
  have miss' : ¬ ((mem.getD (l.var_at + (e - 1)).toNat 0 = key ∧ mem.getD (l.low_at + (e - 1)).toNat 0 = a) ∧ mem.getD (l.high_at + (e - 1)).toNat 0 = b) := by
    simpa only [Matches, and_assoc] using miss
  simp only [cnf_node.loop1, beq_iff_eq, Bool.and_eq_true, Bool.true_and, Bool.and_true,
    Bool.false_and, Bool.and_false, beq_self_eq_true, if_true, if_false, Option.pure_def, Bind.bind,
    Option.bind, decide_eq_true_eq, and_true, true_and, and_false, false_and, not_false_eq_true,
    reduceCtorEq, Prod.fst, Prod.snd, running, slot, occupied, miss']

theorem fresh (l : Layout) (mem : Array UInt32) (key a b h n : UInt32) (fuel : Nat)
    (running : mem.getD (l.state_at + STATE_EXCEEDED).toNat 0 = 0)
    (slot : mem.getD (l.unique_at + h).toNat 0 = 0)
    (count : mem.getD (l.state_at + STATE_COUNT).toNat 0 = n)
    (room : n < l.cap) (valid : n ≠ NONE) :
    cnf_node.loop1 l mem key a b h NONE (fuel + 2) =
      some (allocate l mem key a b h n, h, n) := by
  have hn : ¬ n ≥ l.cap := by
    simp only [UInt32.lt_iff_toNat_lt] at room
    simp only [UInt32.le_iff_toNat_le]; omega
  simp only [cnf_node.loop1, beq_iff_eq, Bool.and_eq_true, Bool.true_and, Bool.and_true,
    Bool.false_and, Bool.and_false, beq_self_eq_true, if_true, if_false, Option.pure_def, Bind.bind,
    Option.bind, decide_eq_true_eq, and_true, true_and, and_false, false_and, not_false_eq_true,
    reduceCtorEq, Prod.fst, Prod.snd, running, slot, count, hn, valid, allocate]

theorem exhausted (l : Layout) (mem : Array UInt32) (key a b h : UInt32) (fuel : Nat)
    (running : mem.getD (l.state_at + STATE_EXCEEDED).toNat 0 = 0)
    (slot : mem.getD (l.unique_at + h).toNat 0 = 0)
    (full : mem.getD (l.state_at + STATE_COUNT).toNat 0 ≥ l.cap)
    (bound : (l.state_at + STATE_EXCEEDED).toNat < mem.size) :
    cnf_node.loop1 l mem key a b h NONE (fuel + 2) =
      some (mem.setIfInBounds (l.state_at + STATE_EXCEEDED).toNat 1, h, NONE) := by
  simp only [cnf_node.loop1, beq_iff_eq, Bool.and_eq_true, Bool.true_and, Bool.and_true,
    Bool.false_and, Bool.and_false, beq_self_eq_true, if_true, if_false, Option.pure_def, Bind.bind,
    Option.bind, decide_eq_true_eq, and_true, true_and, and_false, false_and, not_false_eq_true,
    reduceCtorEq, Prod.fst, Prod.snd, running, slot, full,
    Oak.LRATChecker.array_getD_set_self _ _ _ _ bound,
    show (1 : UInt32) ≠ 0 by decide]

-- A finite sequence of occupied, nonmatching probes. This does not assume
-- termination for a full table or global uniqueness of the hash table.
inductive Probes (l : Layout) (mem : Array UInt32) (key a b : UInt32) : UInt32 → UInt32 → Nat → Prop
  | done (h : UInt32) : Probes l mem key a b h h 0
  | step (h finish e : UInt32) (n : Nat)
      (slot : mem.getD (l.unique_at + h).toNat 0 = e) (occupied : e ≠ 0)
      (miss : ¬ Matches l mem key a b (e - 1))
      (tail : Probes l mem key a b ((h + 1) &&& l.umask) finish n) :
      Probes l mem key a b h finish (n + 1)

theorem probes_execution (l : Layout) (mem : Array UInt32) (key a b start finish : UInt32)
    (n fuel : Nat) (running : mem.getD (l.state_at + STATE_EXCEEDED).toNat 0 = 0)
    (path : Probes l mem key a b start finish n) :
    cnf_node.loop1 l mem key a b start NONE (fuel + n) =
      cnf_node.loop1 l mem key a b finish NONE fuel := by
  induction path with
  | done => rfl
  | step h finish e n slot occupied miss tail ih =>
    rw [show fuel + (n + 1) = (fuel + n) + 1 by omega,
      collision l mem key a b h e (fuel + n) running slot occupied miss, ih]

theorem production (l : Layout) (mem after : Array UInt32) (key a b hash finish result : UInt32)
    (fuel : Nat) (hashed : hash3 key a b fuel = some hash)
    (run : cnf_node.loop1 l (mem.setIfInBounds (l.state_at + STATE_CREATED).toNat 0)
      key a b (hash &&& l.umask) NONE fuel = some (after, finish, result)) :
    cnf_node l mem key a b fuel = some (result, after) := by
  simp only [cnf_node, hashed, Bind.bind, Option.bind, run, Option.pure_def]

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
