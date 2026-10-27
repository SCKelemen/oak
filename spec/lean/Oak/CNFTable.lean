import Oak.CNFNodes

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace Oak.CNFTable
open Oak.CNFEmission Oak.CNFNodes

-- The unique table encodes node i as i+1. Node zero is reserved. This
-- invariant relates every slot to the allocation frontier, and requires a
-- bijection between occupied slots and allocated nonzero nodes. It does not
-- yet say that distinct nodes have distinct (key, low, high) triples.
def slot (l : Layout) (mem : Array UInt32) (s : UInt32) : UInt32 :=
  mem.getD (l.unique_at + s).toNat 0

structure WellFormed (l : Layout) (mem : Array UInt32) (n : UInt32) : Prop where
  count : mem.getD (l.state_at + STATE_COUNT).toNat 0 = n
  positive : 1 ≤ n.toNat
  capacity : n.toNat ≤ l.cap.toNat
  references : ∀ s, s.toNat ≤ l.umask.toNat → slot l mem s ≠ 0 →
    2 ≤ (slot l mem s).toNat ∧ (slot l mem s).toNat ≤ n.toNat
  unique : ∀ s t, s.toNat ≤ l.umask.toNat → t.toNat ≤ l.umask.toNat →
    slot l mem s ≠ 0 → slot l mem s = slot l mem t → s = t
  covers : ∀ e : UInt32, 2 ≤ e.toNat → e.toNat ≤ n.toNat →
    ∃ s : UInt32, s.toNat ≤ l.umask.toNat ∧ slot l mem s = e

def writes (l : Layout) (h n : UInt32) : List Nat :=
  [(l.var_at+n).toNat, (l.low_at+n).toNat, (l.high_at+n).toNat,
   (l.unique_at+h).toNat, (l.state_at+STATE_COUNT).toNat,
   (l.state_at+STATE_CREATED).toNat]

-- These are physical layout obligations, not assumptions about the resulting
-- table contents. They prevent a node/count write from aliasing another slot.
structure Footprint (l : Layout) (mem : Array UInt32) (h n : UInt32) : Prop where
  bounds : ∀ i ∈ writes l h n, i < mem.size
  separate : (writes l h n).Pairwise (· ≠ ·)
  otherSlots : ∀ s, s.toNat ≤ l.umask.toNat → s ≠ h →
    (l.unique_at+s).toNat ∉ writes l h n

theorem other_slot (l : Layout) (mem : Array UInt32) (key a b h n s : UInt32)
    (safe : Footprint l mem h n) (within : s.toNat ≤ l.umask.toNat) (different : s ≠ h) :
    slot l (allocate l mem key a b h n) s = slot l mem s := by
  have disjoint := safe.otherSlots s within different
  simp only [writes, List.mem_cons, List.not_mem_nil, or_false, not_or] at disjoint
  change (allocate l mem key a b h n).getD (l.unique_at+s).toNat 0 =
    mem.getD (l.unique_at+s).toNat 0
  exact allocate_frame l mem key a b h n (l.unique_at+s).toNat disjoint.1 disjoint.2.1
    disjoint.2.2.1 disjoint.2.2.2.1 disjoint.2.2.2.2.1 disjoint.2.2.2.2.2

-- Initialization obligation separated from actual solver_init extraction.
-- Any zero table with count one satisfies the full table/frontier invariant.
theorem empty (l : Layout) (mem : Array UInt32)
    (count : mem.getD (l.state_at + STATE_COUNT).toNat 0 = 1)
    (cap : 1 ≤ l.cap.toNat)
    (zero : ∀ s, s.toNat ≤ l.umask.toNat → slot l mem s = 0) :
    WellFormed l mem 1 := by
  refine ⟨count, by decide, cap, ?_, ?_, ?_⟩
  · intro s hs hn; exact False.elim (hn (zero s hs))
  · intro s t hs ht hn he; exact False.elim (hn (zero s hs))
  · intro e lo hi; change e.toNat ≤ 1 at hi; omega

-- All old references are bounded by n, while the new encoding is n+1.
-- Consequently insertion cannot duplicate an old reference or lose a node.
theorem allocate_preserves (l : Layout) (mem : Array UInt32) (key a b h n : UInt32)
    (wf : WellFormed l mem n) (safe : Footprint l mem h n)
    (within : h.toNat ≤ l.umask.toNat) (vacant : slot l mem h = 0)
    (room : n < l.cap) (limit : l.cap.toNat ≤ 2147483647) :
    WellFormed l (allocate l mem key a b h n) (n+1) := by
  have read := allocate_readback l mem key a b h n safe.bounds safe.separate
  have next : (n+1).toNat = n.toNat+1 := (fresh_index n l.cap 0 room limit (by
    change 0 < n.toNat; have := wf.positive; omega)).2.1
  have nextnz : n+1 ≠ (0 : UInt32) := by
    intro eq; have := congrArg UInt32.toNat eq; rw [next] at this; simp at this
  have hit : slot l (allocate l mem key a b h n) h = n+1 := read.2.1
  have unchanged := other_slot l mem key a b h n
  have caproom : n.toNat < l.cap.toNat := by simpa only [UInt32.lt_iff_toNat_lt] using room
  refine ⟨read.2.2.1, by rw [next]; omega, by rw [next]; omega, ?_, ?_, ?_⟩
  · intro s hs occupied
    by_cases eq : s = h
    · subst s; rw [hit, next]; exact ⟨by have := wf.positive; omega, by omega⟩
    · rw [unchanged s safe hs eq] at occupied ⊢
      have old := wf.references s hs occupied
      rw [next]; exact ⟨old.1, by omega⟩
  · intro s t hs ht occupied same
    by_cases sh : s = h
    · subst s
      by_cases th : t = h
      · exact th.symm
      · rw [hit, unchanged t safe ht th] at same
        have oldnz : slot l mem t ≠ 0 := by rw [← same]; exact nextnz
        have old := wf.references t ht oldnz
        have val := congrArg UInt32.toNat same
        rw [next] at val; omega
    · by_cases th : t = h
      · subst t
        rw [unchanged s safe hs sh, hit] at same
        have oldnz : slot l mem s ≠ 0 := by rw [same]; exact nextnz
        have old := wf.references s hs oldnz
        have val := congrArg UInt32.toNat same
        rw [next] at val; omega
      · rw [unchanged s safe hs sh] at occupied
        rw [unchanged s safe hs sh, unchanged t safe ht th] at same
        exact wf.unique s t hs ht occupied same
  · intro e lo hi
    by_cases new : e = n+1
    · exact ⟨h, within, by rw [new]; exact hit⟩
    · have old : e.toNat ≤ n.toNat := by
        have ne : e.toNat ≠ (n+1).toNat := by
          intro eq; exact new (UInt32.toNat_inj.mp eq)
        rw [next] at hi ne; omega
      obtain ⟨s, hs, he⟩ := wf.covers e lo old
      have sh : s ≠ h := by
        intro eq; subst s; rw [vacant] at he
        have zero := congrArg UInt32.toNat he
        change 0 = e.toNat at zero; omega
      exact ⟨s, hs, by rw [unchanged s safe hs sh]; exact he⟩

-- Connect preservation to the real extracted loop branch, rather than only
-- a parallel mathematical insertion implementation.
theorem fresh_preserves (l : Layout) (mem : Array UInt32) (key a b h n remaining : UInt32)
    (fuel : Nat) (wf : WellFormed l mem n) (safe : Footprint l mem h n)
    (within : h.toNat ≤ l.umask.toNat) (vacant : slot l mem h = 0)
    (room : n < l.cap) (limit : l.cap.toNat ≤ 2147483647)
    (running : mem.getD (l.state_at + STATE_EXCEEDED).toNat 0 = 0) :
    ∃ after, cnf_node.loop1 l mem key a b h NONE remaining (fuel+2) =
      some (after, h, n, remaining) ∧ WellFormed l after (n+1) := by
  refine ⟨allocate l mem key a b h n, ?_, allocate_preserves l mem key a b h n wf safe within vacant room limit⟩
  apply fresh l mem key a b h n remaining fuel running vacant wf.count room
  intro eq; subst n
  have := l.cap.toNat_lt
  simp only [UInt32.lt_iff_toNat_lt, NONE] at room
  change 4294967295 < l.cap.toNat at room
  omega

-- A lookup can safely treat an occupied encoding as an already allocated
-- nonzero node index. This discharges the node-range part of reuse admission.
theorem live_reference (l : Layout) (mem : Array UInt32) (n s : UInt32)
    (wf : WellFormed l mem n) (within : s.toNat ≤ l.umask.toNat)
    (occupied : slot l mem s ≠ 0) :
    1 ≤ (slot l mem s - 1).toNat ∧ (slot l mem s - 1).toNat < n.toNat := by
  have bounds := wf.references s within occupied
  have max := (slot l mem s).toNat_lt
  simp only [UInt32.toNat_sub, UInt32.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  omega

-- Reuse obtains its range premises from the maintained table invariant.
theorem reuse_preserves (l : Layout) (mem : Array UInt32) (key a b h n remaining : UInt32)
    (fuel : Nat) (wf : WellFormed l mem n) (within : h.toNat ≤ l.umask.toNat)
    (occupied : slot l mem h ≠ 0)
    (hit : Matches l mem key a b (slot l mem h - 1))
    (running : mem.getD (l.state_at + STATE_EXCEEDED).toNat 0 = 0) :
    cnf_node.loop1 l mem key a b h NONE remaining (fuel+2) =
      some (mem, h, slot l mem h - 1, remaining) ∧ WellFormed l mem n := by
  have live := live_reference l mem n h wf within occupied
  have cap := wf.capacity
  have inRange : ¬ slot l mem h - 1 ≥ l.cap := by
    simp only [UInt32.le_iff_toNat_le]; omega
  have valid : slot l mem h - 1 ≠ NONE := by
    intro eq
    rw [eq] at live
    have max := n.toNat_lt
    change 1 ≤ 4294967295 ∧ 4294967295 < n.toNat at live
    omega
  exact ⟨reuse l mem key a b h (slot l mem h) remaining fuel running rfl occupied inRange valid hit, wf⟩

end Oak.CNFTable
