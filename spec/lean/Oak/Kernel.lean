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

end Oak.Kernel
