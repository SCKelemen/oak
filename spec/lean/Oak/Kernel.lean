/-!
# Oak.Kernel — a launch is its sequential loop

Model of docs/spec/56-kernels.md section 4. A kernel body is a function of
the grid position over shared memory; a launch runs it once per position.
The C realization runs the positions in order; a GPU runs them in any
order, interleaved. The two agree when the threads are *independent*: each
thread's writes are disjoint from every other thread's reads and writes —
the condition `55-parallelism.md` section 2 requires of a parallel iteration
space, and the one a kernel author owes (the checker does not yet prove
it; section 4 records the obligation).

* `Thread`: a step on memory with a read footprint and a write footprint,
  in the frame sense: the result depends only on the reads, and changes only
  the writes.
* `Independent`: pairwise footprint disjointness for distinct positions.
* `run_perm`: running the positions in any order gives the same memory as
  the sequential loop. Interleaving finer than whole threads is covered by
  the same argument once each thread's steps are themselves framed; the
  model states the whole-thread case, which is what the C loop and a GPU
  launch with independent threads both compute.
-/

namespace Oak.Kernel

/-- Memory: addresses to values. -/
def Mem (Addr Val : Type) := Addr → Val

variable {Addr Val : Type}

/-- One thread's step with its footprints, framed. -/
structure Thread (Addr Val : Type) where
  step : Mem Addr Val → Mem Addr Val
  reads : Addr → Prop
  writes : Addr → Prop
  /-- The step changes only addresses it writes. -/
  frame : ∀ m a, ¬ writes a → step m a = m a
  /-- The step's writes depend only on the addresses it reads. -/
  reads_only : ∀ m m', (∀ a, reads a → m a = m' a) → ∀ a, writes a → step m a = step m' a

/-- Two threads are independent when neither writes what the other touches. -/
def Independent (t u : Thread Addr Val) : Prop :=
  (∀ a, t.writes a → ¬ u.reads a ∧ ¬ u.writes a) ∧
  (∀ a, u.writes a → ¬ t.reads a ∧ ¬ t.writes a)

theorem Independent.symm {t u : Thread Addr Val} (h : Independent t u) : Independent u t :=
  ⟨h.2, h.1⟩

/-- Independent threads commute. -/
theorem commute (t u : Thread Addr Val) (h : Independent t u) (m : Mem Addr Val) :
    u.step (t.step m) = t.step (u.step m) := by
  funext a
  by_cases hu : u.writes a
  · -- u writes a: t does not touch a, and u sees the same reads either way.
    have ht : ¬ t.writes a := (h.2 a hu).2
    rw [t.frame (u.step m) a ht]
    exact u.reads_only (t.step m) m (fun b hb => t.frame m b (fun hw => (h.1 b hw).1 hb)) a hu
  · by_cases ht : t.writes a
    · rw [u.frame (t.step m) a hu]
      exact (t.reads_only (u.step m) m (fun b hb => u.frame m b (fun hw => (h.2 b hw).1 hb)) a ht).symm
    · rw [u.frame (t.step m) a hu, t.frame m a ht, t.frame (u.step m) a ht, u.frame m a hu]

/-- Run a list of threads in order. -/
def run : List (Thread Addr Val) → Mem Addr Val → Mem Addr Val
  | [], m => m
  | t :: ts, m => run ts (t.step m)

/-- **Order independence.** If every two distinct threads in a list are
independent, running them in any order gives the same memory. -/
theorem run_perm (l₁ l₂ : List (Thread Addr Val))
    (hind : ∀ t ∈ l₁, ∀ u ∈ l₁, t ≠ u → Independent t u)
    (hp : l₁.Perm l₂) : ∀ m, run l₁ m = run l₂ m := by
  induction hp with
  | nil => intro m; rfl
  | cons x _ ih =>
    intro m
    simp only [run]
    apply ih
    intro t ht u hu hne
    exact hind t (List.mem_cons_of_mem _ ht) u (List.mem_cons_of_mem _ hu) hne
  | swap x y l =>
    intro m
    simp only [run]
    by_cases hxy : x = y
    · subst hxy; rfl
    · have h := hind y (by simp) x (by simp) (Ne.symm hxy)
      rw [commute y x h m]
  | trans h₁ h₂ ih₁ ih₂ =>
    intro m
    rw [ih₁ hind m]
    apply ih₂
    intro t ht u hu hne
    exact hind t (h₁.mem_iff.mpr ht) u (h₁.mem_iff.mpr hu) hne

/-! ## The two shapes the checker discharges

`56-kernels.md` section 6: the checker admits a kernel whose every span
access is at the grid position (one element per thread) or at
`gid * T + k` with a proven offset `k < T` (a tile per thread), and rejects
every other. Offsets include a counter under `while k < T`, `lane(T)`,
and `s * G + lane(G)` under `while s < T / G`. These are the footprints;
their pairwise disjointness for distinct positions is what `Independent`
asks of the spans, so `run_perm`
applies. The tile fact is over `Nat`: the launch obligation recorded in
the descriptor is that `grid * T` fits the `u32` index, so the kernel's
wrapping arithmetic computes these numbers. -/

/-- The element shape: position `g` touches address `g`. -/
def elementFootprint (g a : Nat) : Prop := a = g

/-- The tile shape: position `g` touches `g * T + k` for `k < T`. -/
def tileFootprint (T g a : Nat) : Prop := ∃ k, k < T ∧ a = g * T + k

theorem element_disjoint {g h a : Nat} (hne : g ≠ h) :
    ¬ (elementFootprint g a ∧ elementFootprint h a) := by
  intro ⟨hg, hh⟩
  exact hne (hg.symm.trans hh)

/-- `g * T + k` with `k < T` determines `g`: it is the quotient by `T`. -/
theorem tile_index_div {T g k : Nat} (hk : k < T) : (g * T + k) / T = g := by
  have hT : 0 < T := Nat.lt_of_le_of_lt (Nat.zero_le k) hk
  rw [Nat.mul_comm, Nat.mul_add_div hT, Nat.div_eq_of_lt hk, Nat.add_zero]

theorem tile_disjoint {T g h a : Nat} (hne : g ≠ h) :
    ¬ (tileFootprint T g a ∧ tileFootprint T h a) := by
  intro ⟨⟨k, hk, hga⟩, ⟨k', hk', hha⟩⟩
  apply hne
  have h1 := tile_index_div (g := g) hk
  have h2 := tile_index_div (g := h) hk'
  rw [← h1, ← hga, hha, h2]

/-! ## Lanes and phases (docs/spec/56-kernels.md section 2a)

A group kernel with `lane(G)` runs its body once per lane per position; a
lane's stores at `gid * G + lane` are the tile footprint with `T = G`, so
positions stay independent (`lane_disjoint`). `barrier()` splits the body
into phases: on the device every lane of a group finishes a phase before
any lane starts the next; on the host the phases run in order and each
phase runs its lanes one after another. `phases_perm` is why the two agree:
when the lanes of each phase are pairwise independent — they write their
own slots of the outputs and of the threadgroup array, and read what the
previous phase left — running a phase's lanes in any order gives the same
memory, and the phases compose in sequence. -/

/-- The lane footprint: position `g` with `G` lanes touches `g * G + l`
for `l < G`, the tile shape at `T = G`. -/
def laneFootprint (G g a : Nat) : Prop := tileFootprint G g a

theorem lane_disjoint {G g h a : Nat} (hne : g ≠ h) :
    ¬ (laneFootprint G g a ∧ laneFootprint G h a) :=
  tile_disjoint hne

/-- A lane's strided offset stays in its row, including when T has a
partial tail. The quotient loop visits only complete groups of G. -/
theorem lane_strided_offset_lt {T G s l : Nat} (hs : s < T / G) (hl : l < G) :
    s * G + l < T := by
  have hstep : s * G + l < (s + 1) * G := by
    simpa [Nat.add_mul] using Nat.add_lt_add_left hl (s * G)
  have hbound : (s + 1) * G ≤ (T / G) * G :=
    Nat.mul_le_mul_right G hs
  exact Nat.lt_of_lt_of_le hstep (Nat.le_trans hbound (Nat.div_mul_le_self T G))

/-- Strided lane stores have the same disjoint tile footprints as the
ordinary bounded counter, so independent grid positions still commute. -/
theorem lane_strided_disjoint {T G g h s t l m : Nat} (hne : g ≠ h)
    (hs : s < T / G) (ht : t < T / G) (hl : l < G) (hm : m < G) :
    g * T + (s * G + l) ≠ h * T + (t * G + m) := by
  intro heq
  exact tile_disjoint hne
    ⟨⟨s * G + l, lane_strided_offset_lt hs hl, rfl⟩,
     ⟨t * G + m, lane_strided_offset_lt ht hm, heq⟩⟩

/-- Within a position, different lanes never share a strided slot, even
at different loop iterations. -/
theorem lane_strided_lanes_disjoint {G s t l m : Nat}
    (hne : l ≠ m) (hl : l < G) (hm : m < G) : s * G + l ≠ t * G + m := by
  intro heq
  have hs := tile_index_div (g := s) hl
  have ht := tile_index_div (g := t) hm
  have hst : s = t := by rw [← hs, heq, ht]
  subst t
  exact hne (Nat.add_left_cancel heq)

/-- A barrier-separated kernel: its phases, each the lanes' threads. -/
def runPhases : List (List (Thread Addr Val)) → Mem Addr Val → Mem Addr Val
  | [], m => m
  | p :: ps, m => runPhases ps (run p m)

/-- Phase by phase, running each phase's lanes in the device's order or the
host's gives one memory, when every phase's lanes are pairwise
independent. -/
theorem phases_perm (ps qs : List (List (Thread Addr Val)))
    (hlen : ps.length = qs.length)
    (hperm : ∀ i (hi : i < ps.length) (hj : i < qs.length), List.Perm ps[i] qs[i])
    (hind : ∀ i (hi : i < ps.length), ∀ t ∈ ps[i], ∀ u ∈ ps[i], t ≠ u → Independent t u)
    (m : Mem Addr Val) : runPhases ps m = runPhases qs m := by
  induction ps generalizing qs m with
  | nil =>
    cases qs with
    | nil => rfl
    | cons _ _ => simp at hlen
  | cons p ps ih =>
    cases qs with
    | nil => simp at hlen
    | cons q qs =>
      simp only [runPhases]
      have hpq : List.Perm p q := hperm 0 (by simp) (by simp)
      have hp : ∀ t ∈ p, ∀ u ∈ p, t ≠ u → Independent t u := hind 0 (by simp)
      rw [run_perm p q hp hpq m]
      exact ih qs (by simpa using hlen)
        (fun i hi hj => hperm (i + 1) (by simpa using hi) (by simpa using hj))
        (fun i hi => hind (i + 1) (by simpa using hi)) (run q m)

/-! ## Fusion (docs/spec/56-kernels.md section 2b)

A kernel that calls another kernel at its own position runs both bodies
as one thread per position: `fuse t u` is that thread — `u`'s step after
`t`'s, reading what either reads, writing what either writes — and it is a
thread in the model's sense (framed, its writes depending only on its
reads). `independent_fuse` is why the checker may judge the callee's
accesses as the caller's: when every stage of one position is independent
of every stage of another, the fused positions are independent, so
`run_perm` applies to the fused launch as it did to each stage's. -/

/-- Two stages of one position, run in order. -/
def fuse (t u : Thread Addr Val) : Thread Addr Val where
  step := fun m => u.step (t.step m)
  reads := fun a => t.reads a ∨ u.reads a
  writes := fun a => t.writes a ∨ u.writes a
  frame := by
    intro m a hw
    have ht : ¬ t.writes a := fun h => hw (Or.inl h)
    have hu : ¬ u.writes a := fun h => hw (Or.inr h)
    rw [u.frame (t.step m) a hu, t.frame m a ht]
  reads_only := by
    intro m m' hagree a hw
    -- After t's step the two memories agree on everything u reads: on
    -- t's writes by t's reads_only, elsewhere by t's frame and the
    -- agreement on u's reads.
    have hmid : ∀ b, u.reads b → t.step m b = t.step m' b := by
      intro b hb
      by_cases htb : t.writes b
      · exact t.reads_only m m' (fun c hc => hagree c (Or.inl hc)) b htb
      · rw [t.frame m b htb, t.frame m' b htb]
        exact hagree b (Or.inr hb)
    rcases hw with htw | huw
    · by_cases huw : u.writes a
      · exact u.reads_only (t.step m) (t.step m') hmid a huw
      · rw [u.frame (t.step m) a huw, u.frame (t.step m') a huw]
        exact t.reads_only m m' (fun c hc => hagree c (Or.inl hc)) a htw
    · exact u.reads_only (t.step m) (t.step m') hmid a huw

/-- **Fused positions stay independent** when each stage of one position is
independent of each stage of the other. -/
theorem independent_fuse {t₁ t₂ u₁ u₂ : Thread Addr Val}
    (h11 : Independent t₁ u₁) (h12 : Independent t₁ u₂)
    (h21 : Independent t₂ u₁) (h22 : Independent t₂ u₂) :
    Independent (fuse t₁ t₂) (fuse u₁ u₂) := by
  refine ⟨fun a hw => ?_, fun a hw => ?_⟩
  · rcases hw with h | h
    · exact ⟨fun hr => hr.elim (fun r => (h11.1 a h).1 r) (fun r => (h12.1 a h).1 r),
        fun hw' => hw'.elim (fun w => (h11.1 a h).2 w) (fun w => (h12.1 a h).2 w)⟩
    · exact ⟨fun hr => hr.elim (fun r => (h21.1 a h).1 r) (fun r => (h22.1 a h).1 r),
        fun hw' => hw'.elim (fun w => (h21.1 a h).2 w) (fun w => (h22.1 a h).2 w)⟩
  · rcases hw with h | h
    · exact ⟨fun hr => hr.elim (fun r => (h11.2 a h).1 r) (fun r => (h21.2 a h).1 r),
        fun hw' => hw'.elim (fun w => (h11.2 a h).2 w) (fun w => (h21.2 a h).2 w)⟩
    · exact ⟨fun hr => hr.elim (fun r => (h12.2 a h).1 r) (fun r => (h22.2 a h).1 r),
        fun hw' => hw'.elim (fun w => (h12.2 a h).2 w) (fun w => (h22.2 a h).2 w)⟩

/-- Fusing is running the stages in order: the fused launch and the two
launches compute one memory. -/
theorem run_fuse (t u : Thread Addr Val) (m : Mem Addr Val) :
    run [fuse t u] m = run [t, u] m := rfl

end Oak.Kernel
