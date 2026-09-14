/-! # Compiler correspondence for the argument layout

`asm/abi.go` places a function's integer-class arguments under AAPCS64
(`LayoutArguments`): the general registers x0–x7 take arguments in order
while they fit; once one does not, it and every later argument go to the
stack at increasing offsets, each rounded to its alignment — 8 bytes under
the standard convention, the argument's natural size and alignment under
Apple's packed one. The seam checker binds record parameters by the same
rule (`asm/check.go`): a record of up to 16 bytes takes `⌈size/8⌉`
consecutive registers, each an 8-byte chunk of its memory image; a larger
one is passed by reference in one register (`compositeChunks`).

This module transliterates both — the Go is maintained line for line with
them, and `asm/abi_refinement_test.go` renders the Go layouts as the
examples stated at the end — and proves what the checker relies on: every
register place lies inside x0–x7 and no two overlap; every stack place is
aligned as its class asks, no two overlap, and the stack area covers them
all; once an argument goes to the stack, so does every later one; and a
record's chunks cover its bytes with none empty. Sizes, offsets, and
alignments are non-negative in Go (`int64` from record sizes and the
classes below) and are modeled as `Nat`; Go's `/` on them is `Nat`
division. -/

namespace Oak.ArgumentLayout

/-- `asm.ArgClass`: registers when in registers, natural size and
    alignment when packed on the stack. -/
structure ArgClass where
  words : Nat
  bytes : Nat
  align : Nat
  deriving Repr, DecidableEq

/-- `asm.ArgPlace`, with the stack size and alignment the placement used
    kept for the laws (the Go recomputes them from the class). -/
structure ArgPlace where
  reg : Nat
  regs : Nat
  onStack : Bool
  offset : Nat
  size : Nat
  align : Nat
  deriving Repr, DecidableEq

/-- `(off + align - 1) / align * align`: the next multiple of `align` at or
    above `off`. -/
def roundUp (off align : Nat) : Nat := (off + align - 1) / align * align

/-- The bytes an argument takes on the stack: its natural size when
    packed, otherwise its registers' worth. -/
def stackSize (packed : Bool) (a : ArgClass) : Nat := if packed then a.bytes else a.words * 8

/-- Its stack alignment: natural when packed, otherwise 8; never below 1
    (`if align < 1 { align = 1 }`). -/
def stackAlign (packed : Bool) (a : ArgClass) : Nat := max 1 (if packed then a.align else 8)

/-- The placement fold: `next` the first free register, `off` the stack
    cursor, `stack` whether an argument has gone to the stack. Returns the
    places and the stack cursor after the last. -/
def layoutFrom (packed : Bool) : Nat → Nat → Bool → List ArgClass → List ArgPlace × Nat
  | _, off, _, [] => ([], off)
  | next, off, stack, a :: rest =>
    if stack = false ∧ next + a.words ≤ 8 then
      let tail := layoutFrom packed (next + a.words) off stack rest
      (⟨next, a.words, false, 0, 0, 0⟩ :: tail.1, tail.2)
    else
      let tail := layoutFrom packed next (roundUp off (stackAlign packed a) + stackSize packed a) true rest
      (⟨0, 0, true, roundUp off (stackAlign packed a), stackSize packed a, stackAlign packed a⟩ :: tail.1, tail.2)

/-- `asm.LayoutArguments`: the places and the stack area, rounded to 16. -/
def layoutArguments (args : List ArgClass) (packed : Bool) : List ArgPlace × Nat :=
  let out := layoutFrom packed 0 0 false args
  (out.1, roundUp out.2 16)

/-- The checker's record-parameter class (`compositeChunks` in
    `asm/abi.go`): up to 16 bytes in `⌈size/8⌉` registers, larger by
    reference in one. -/
def compositeChunks (size : Nat) : Nat × Bool :=
  if 16 < size then (1, true) else ((size + 7) / 8, false)

/-! ## Round-up -/

theorem roundUp_ge (off align : Nat) (h : 1 ≤ align) : off ≤ roundUp off align := by
  unfold roundUp
  have hmod := Nat.mod_lt (off + align - 1) (by omega : align > 0)
  have hdiv := Nat.div_add_mod (off + align - 1) align
  have := Nat.mul_comm align ((off + align - 1) / align)
  omega

theorem roundUp_aligned (off align : Nat) : roundUp off align % align = 0 := by
  unfold roundUp
  exact Nat.mul_mod_left _ _

theorem stackAlign_pos (packed : Bool) (a : ArgClass) : 1 ≤ stackAlign packed a :=
  Nat.le_max_left _ _

/-! ## What the fold guarantees -/

/-- The cursor never decreases. -/
theorem cursor_ge (packed : Bool) (next off : Nat) (stack : Bool) (args : List ArgClass) :
    off ≤ (layoutFrom packed next off stack args).2 := by
  induction args generalizing next off stack with
  | nil => simp [layoutFrom]
  | cons a rest ih =>
    unfold layoutFrom
    split
    · exact ih _ _ _
    · have h1 := roundUp_ge off _ (stackAlign_pos packed a)
      have h2 := ih next (roundUp off (stackAlign packed a) + stackSize packed a) true
      show _ ≤ (layoutFrom packed next (roundUp off (stackAlign packed a) + stackSize packed a) true rest).2
      omega

/-- With `stack` set, every place the fold produces is on the stack. -/
theorem on_stack_after (packed : Bool) (next off : Nat) (args : List ArgClass) (q : ArgPlace)
    (hq : q ∈ (layoutFrom packed next off true args).1) : q.onStack = true := by
  induction args generalizing next off with
  | nil => simp [layoutFrom] at hq
  | cons a rest ih =>
    simp only [layoutFrom, Bool.true_eq_false, false_and, if_false, List.mem_cons] at hq
    rcases hq with rfl | hq
    · rfl
    · exact ih next _ hq

/-- Every register place lies inside x0–x7 and starts at or after `next`. -/
theorem regs_within (packed : Bool) (next off : Nat) (stack : Bool) (args : List ArgClass)
    (p : ArgPlace) (hp : p ∈ (layoutFrom packed next off stack args).1) (hr : p.onStack = false) :
    next ≤ p.reg ∧ p.reg + p.regs ≤ 8 := by
  induction args generalizing next off stack with
  | nil => simp [layoutFrom] at hp
  | cons a rest ih =>
    unfold layoutFrom at hp
    split at hp
    · rename_i hfit
      simp only [List.mem_cons] at hp
      rcases hp with rfl | hp
      · exact ⟨Nat.le_refl _, hfit.2⟩
      · have := ih (next + a.words) off stack hp
        exact ⟨by omega, this.2⟩
    · simp only [List.mem_cons] at hp
      rcases hp with rfl | hp
      · simp at hr
      · exact ih next _ true hp

/-- Every stack place starts at or after the cursor `off`, is aligned as
    its class asks (with `1 ≤ align`), and ends at or before the cursor
    the fold returns. -/
theorem stack_within (packed : Bool) (next off : Nat) (stack : Bool) (args : List ArgClass)
    (p : ArgPlace) (hp : p ∈ (layoutFrom packed next off stack args).1) (hs : p.onStack = true) :
    off ≤ p.offset ∧ 1 ≤ p.align ∧ p.offset % p.align = 0 ∧
      p.offset + p.size ≤ (layoutFrom packed next off stack args).2 := by
  induction args generalizing next off stack with
  | nil => simp [layoutFrom] at hp
  | cons a rest ih =>
    unfold layoutFrom at hp ⊢
    split at hp
    · rename_i hfit
      rw [if_pos hfit]
      simp only [List.mem_cons] at hp
      rcases hp with rfl | hp
      · simp at hs
      · exact ih (next + a.words) off stack hp
    · rename_i hnot
      rw [if_neg hnot]
      simp only [List.mem_cons] at hp
      have halign := stackAlign_pos packed a
      have hge := roundUp_ge off _ halign
      rcases hp with rfl | hp
      · exact ⟨hge, halign, roundUp_aligned _ _, cursor_ge packed next _ true rest⟩
      · have := ih next _ true hp
        exact ⟨by omega, this.2.1, this.2.2.1, this.2.2.2⟩

/-- The stack area covers every stack place. -/
theorem stack_area_covers (args : List ArgClass) (packed : Bool) (p : ArgPlace)
    (hp : p ∈ (layoutArguments args packed).1) (hs : p.onStack = true) :
    p.offset + p.size ≤ (layoutArguments args packed).2 := by
  have h := stack_within packed 0 0 false args p hp hs
  have h16 := roundUp_ge (layoutFrom packed 0 0 false args).2 16 (by omega)
  show _ ≤ roundUp (layoutFrom packed 0 0 false args).2 16
  omega

/-- The places are ordered: each register place's registers end before
    the next register place begins, each stack place ends before the next
    stack place begins, and no register place follows a stack place — so
    register places are pairwise disjoint, stack places are pairwise
    disjoint, and once an argument goes to the stack so does every later
    one. -/
theorem places_ordered (packed : Bool) (next off : Nat) (stack : Bool) (args : List ArgClass) :
    (layoutFrom packed next off stack args).1.Pairwise (fun p q =>
      (p.onStack = false → q.onStack = false → p.reg + p.regs ≤ q.reg) ∧
      (p.onStack = true → q.onStack = true → p.offset + p.size ≤ q.offset) ∧
      (p.onStack = true → q.onStack = true)) := by
  induction args generalizing next off stack with
  | nil => simp [layoutFrom]
  | cons a rest ih =>
    unfold layoutFrom
    split
    · refine List.Pairwise.cons ?_ (ih _ _ _)
      intro q hq
      exact ⟨fun _ hqr => (regs_within packed _ off stack rest q hq hqr).1,
        fun h => by simp at h, fun h => by simp at h⟩
    · refine List.Pairwise.cons ?_ (ih _ _ _)
      intro q hq
      exact ⟨fun h => by simp at h,
        fun _ hqs => (stack_within packed next _ true rest q hq hqs).1,
        fun _ => on_stack_after packed next _ rest q hq⟩

/-! ## Record chunks -/

/-- A record of 1 to 16 bytes is passed in one or two registers whose
    chunks cover its bytes with none empty. -/
theorem composite_chunks_cover (size : Nat) (h1 : 1 ≤ size) (h16 : size ≤ 16) :
    (compositeChunks size).2 = false ∧
    size ≤ (compositeChunks size).1 * 8 ∧ ((compositeChunks size).1 - 1) * 8 < size ∧
    ((compositeChunks size).1 = 1 ∨ (compositeChunks size).1 = 2) := by
  have h : ¬ 16 < size := by omega
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [compositeChunks, if_neg h] <;> first | rfl | omega

/-- A larger record is passed by reference in one register. -/
theorem composite_indirect (size : Nat) (h : 16 < size) : compositeChunks size = (1, true) := by
  simp [compositeChunks, h]

/-! ## The Go layouts, as Lean checks them

Rendered by `TestArgumentLayoutMatchesLeanTransliteration`
(`asm/abi_refinement_test.go`) from `LayoutArguments` and
`compositeChunks`; the kernel evaluates each. -/

example : layoutArguments [⟨1, 8, 8⟩, ⟨1, 4, 4⟩, ⟨1, 1, 1⟩] false = ([⟨0, 1, false, 0, 0, 0⟩, ⟨1, 1, false, 0, 0, 0⟩, ⟨2, 1, false, 0, 0, 0⟩], 0) := by decide
example : layoutArguments [⟨2, 16, 8⟩, ⟨2, 16, 8⟩, ⟨1, 8, 8⟩] false = ([⟨0, 2, false, 0, 0, 0⟩, ⟨2, 2, false, 0, 0, 0⟩, ⟨4, 1, false, 0, 0, 0⟩], 0) := by decide
example : layoutArguments [⟨1, 8, 8⟩, ⟨1, 8, 8⟩, ⟨1, 8, 8⟩, ⟨1, 8, 8⟩, ⟨1, 8, 8⟩, ⟨1, 8, 8⟩, ⟨1, 8, 8⟩, ⟨1, 8, 8⟩, ⟨1, 4, 4⟩] false = ([⟨0, 1, false, 0, 0, 0⟩, ⟨1, 1, false, 0, 0, 0⟩, ⟨2, 1, false, 0, 0, 0⟩, ⟨3, 1, false, 0, 0, 0⟩, ⟨4, 1, false, 0, 0, 0⟩, ⟨5, 1, false, 0, 0, 0⟩, ⟨6, 1, false, 0, 0, 0⟩, ⟨7, 1, false, 0, 0, 0⟩, ⟨0, 0, true, 0, 8, 8⟩], 16) := by decide
example : layoutArguments [⟨1, 8, 8⟩, ⟨1, 8, 8⟩, ⟨1, 8, 8⟩, ⟨1, 8, 8⟩, ⟨1, 8, 8⟩, ⟨1, 8, 8⟩, ⟨1, 8, 8⟩, ⟨2, 16, 8⟩, ⟨1, 8, 8⟩] false = ([⟨0, 1, false, 0, 0, 0⟩, ⟨1, 1, false, 0, 0, 0⟩, ⟨2, 1, false, 0, 0, 0⟩, ⟨3, 1, false, 0, 0, 0⟩, ⟨4, 1, false, 0, 0, 0⟩, ⟨5, 1, false, 0, 0, 0⟩, ⟨6, 1, false, 0, 0, 0⟩, ⟨0, 0, true, 0, 16, 8⟩, ⟨0, 0, true, 16, 8, 8⟩], 32) := by decide
example : layoutArguments [⟨1, 8, 8⟩, ⟨1, 8, 8⟩, ⟨1, 8, 8⟩, ⟨1, 8, 8⟩, ⟨1, 8, 8⟩, ⟨1, 8, 8⟩, ⟨1, 8, 8⟩, ⟨1, 8, 8⟩, ⟨1, 1, 1⟩, ⟨1, 2, 2⟩, ⟨1, 4, 4⟩, ⟨2, 16, 8⟩] true = ([⟨0, 1, false, 0, 0, 0⟩, ⟨1, 1, false, 0, 0, 0⟩, ⟨2, 1, false, 0, 0, 0⟩, ⟨3, 1, false, 0, 0, 0⟩, ⟨4, 1, false, 0, 0, 0⟩, ⟨5, 1, false, 0, 0, 0⟩, ⟨6, 1, false, 0, 0, 0⟩, ⟨7, 1, false, 0, 0, 0⟩, ⟨0, 0, true, 0, 1, 1⟩, ⟨0, 0, true, 2, 2, 2⟩, ⟨0, 0, true, 4, 4, 4⟩, ⟨0, 0, true, 8, 16, 8⟩], 32) := by decide
example : layoutArguments [⟨1, 8, 8⟩, ⟨1, 8, 8⟩, ⟨1, 8, 8⟩, ⟨1, 8, 8⟩, ⟨1, 8, 8⟩, ⟨1, 8, 8⟩, ⟨1, 8, 8⟩, ⟨1, 8, 8⟩, ⟨1, 1, 1⟩, ⟨1, 2, 2⟩] false = ([⟨0, 1, false, 0, 0, 0⟩, ⟨1, 1, false, 0, 0, 0⟩, ⟨2, 1, false, 0, 0, 0⟩, ⟨3, 1, false, 0, 0, 0⟩, ⟨4, 1, false, 0, 0, 0⟩, ⟨5, 1, false, 0, 0, 0⟩, ⟨6, 1, false, 0, 0, 0⟩, ⟨7, 1, false, 0, 0, 0⟩, ⟨0, 0, true, 0, 8, 8⟩, ⟨0, 0, true, 8, 8, 8⟩], 16) := by decide
example : compositeChunks 1 = (1, false) := by decide
example : compositeChunks 4 = (1, false) := by decide
example : compositeChunks 8 = (1, false) := by decide
example : compositeChunks 9 = (2, false) := by decide
example : compositeChunks 16 = (2, false) := by decide
example : compositeChunks 17 = (1, true) := by decide
example : compositeChunks 32 = (1, true) := by decide

end Oak.ArgumentLayout
