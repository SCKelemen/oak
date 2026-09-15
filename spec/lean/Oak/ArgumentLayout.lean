/-! # Compiler correspondence for the argument layout

`asm/abi.go` places a function's arguments under AAPCS64
(`LayoutArguments`): the general registers x0–x7 take the integer-class
arguments in order while they fit, the vector registers v0–v7 the
vector-class ones (floats and fixed vectors); once an argument of a class
does not fit, it and every later argument of that class go to the stack,
at increasing offsets from one cursor shared by both classes, each
rounded to its alignment — 8 bytes under the standard convention for the
integer class (a vector-class argument its natural size and alignment,
at least 8), the argument's natural size and alignment under Apple's
packed one. The seam checker binds record parameters by the same
rule (`asm/check.go`): a record of up to 16 bytes takes `⌈size/8⌉`
consecutive registers, each an 8-byte chunk of its memory image; a larger
one is passed by reference in one register (`compositeChunks`).

This module transliterates both — the Go is maintained line for line with
them, and `asm/abi_refinement_test.go` renders the Go layouts as the
examples stated at the end — and proves what the checker relies on: every
register place lies inside x0–x7 and no two overlap; every stack place is
aligned as its class asks, no two overlap, and the stack area covers them
all; once an argument of a class goes to the stack, so does every later
one of that class; and a record's chunks cover its bytes with none
empty. Sizes, offsets, and
alignments are non-negative in Go (`int64` from record sizes and the
classes below) and are modeled as `Nat`; Go's `/` on them is `Nat`
division. -/

namespace Oak.ArgumentLayout

/-- `asm.ArgClass`: registers when in registers, natural size and
    alignment when packed on the stack, and the class (`vector`: a float
    or a fixed vector, its registers v0–v7). -/
structure ArgClass where
  words : Nat
  bytes : Nat
  align : Nat
  vector : Bool
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
  vector : Bool
  deriving Repr, DecidableEq

/-- `(off + align - 1) / align * align`: the next multiple of `align` at or
    above `off`. -/
def roundUp (off align : Nat) : Nat := (off + align - 1) / align * align

/-- The bytes an argument takes on the stack (`asm.stackSize`): its
    natural size when packed; otherwise a vector-class argument its
    natural size, at least 8, and an integer-class one its registers'
    worth. -/
def stackSize (packed : Bool) (a : ArgClass) : Nat :=
  if packed then a.bytes else if a.vector then max a.bytes 8 else a.words * 8

/-- Its stack alignment (`asm.stackAlign`): natural when packed; otherwise
    8, or a vector-class argument's natural alignment when larger; never
    below 1. -/
def stackAlign (packed : Bool) (a : ArgClass) : Nat :=
  max 1 (if packed then a.align else if a.vector then max a.align 8 else 8)

/-- The placement fold: `next` the first free general register, `nextV`
    the first free vector register, `off` the stack cursor, `stack` and
    `stackV` whether an argument of the class has gone to the stack.
    Returns the places and the stack cursor after the last. -/
def layoutFrom (packed : Bool) : Nat → Nat → Nat → Bool → Bool → List ArgClass → List ArgPlace × Nat
  | _, _, off, _, _, [] => ([], off)
  | next, nextV, off, stack, stackV, a :: rest =>
    if a.vector = true then
      if stackV = false ∧ nextV + a.words ≤ 8 then
        let tail := layoutFrom packed next (nextV + a.words) off stack stackV rest
        (⟨nextV, a.words, false, 0, 0, 0, true⟩ :: tail.1, tail.2)
      else
        let tail := layoutFrom packed next nextV (roundUp off (stackAlign packed a) + stackSize packed a) stack true rest
        (⟨0, 0, true, roundUp off (stackAlign packed a), stackSize packed a, stackAlign packed a, true⟩ :: tail.1, tail.2)
    else
      if stack = false ∧ next + a.words ≤ 8 then
        let tail := layoutFrom packed (next + a.words) nextV off stack stackV rest
        (⟨next, a.words, false, 0, 0, 0, false⟩ :: tail.1, tail.2)
      else
        let tail := layoutFrom packed next nextV (roundUp off (stackAlign packed a) + stackSize packed a) true stackV rest
        (⟨0, 0, true, roundUp off (stackAlign packed a), stackSize packed a, stackAlign packed a, false⟩ :: tail.1, tail.2)

/-- `asm.LayoutArguments`: the places and the stack area, rounded to 16. -/
def layoutArguments (args : List ArgClass) (packed : Bool) : List ArgPlace × Nat :=
  let out := layoutFrom packed 0 0 0 false false args
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
theorem cursor_ge (packed : Bool) (next nextV off : Nat) (stack stackV : Bool) (args : List ArgClass) :
    off ≤ (layoutFrom packed next nextV off stack stackV args).2 := by
  induction args generalizing next nextV off stack stackV with
  | nil => simp [layoutFrom]
  | cons a rest ih =>
    unfold layoutFrom
    have h1 := roundUp_ge off _ (stackAlign_pos packed a)
    split
    · split
      · exact ih _ _ _ _ _
      · have h2 := ih next nextV (roundUp off (stackAlign packed a) + stackSize packed a) stack true
        show _ ≤ (layoutFrom packed next nextV (roundUp off (stackAlign packed a) + stackSize packed a) stack true rest).2
        omega
    · split
      · exact ih _ _ _ _ _
      · have h2 := ih next nextV (roundUp off (stackAlign packed a) + stackSize packed a) true stackV
        show _ ≤ (layoutFrom packed next nextV (roundUp off (stackAlign packed a) + stackSize packed a) true stackV rest).2
        omega

/-- With a class's flag set, every place of that class the fold produces
    is on the stack. -/
theorem on_stack_after (packed : Bool) (next nextV off : Nat) (stack stackV : Bool) (args : List ArgClass) (q : ArgPlace)
    (hq : q ∈ (layoutFrom packed next nextV off stack stackV args).1)
    (hflag : (q.vector = false → stack = true) ∧ (q.vector = true → stackV = true)) : q.onStack = true := by
  induction args generalizing next nextV off stack stackV with
  | nil => simp [layoutFrom] at hq
  | cons a rest ih =>
    unfold layoutFrom at hq
    split at hq
    · rename_i hvec
      split at hq
      · rename_i hfit
        simp only [List.mem_cons] at hq
        rcases hq with rfl | hq
        · have := hflag.2 rfl
          simp_all
        · exact ih _ _ _ _ _ hq hflag
      · simp only [List.mem_cons] at hq
        rcases hq with rfl | hq
        · rfl
        · exact ih _ _ _ _ _ hq ⟨hflag.1, fun _ => rfl⟩
    · rename_i hvec
      split at hq
      · rename_i hfit
        simp only [List.mem_cons] at hq
        rcases hq with rfl | hq
        · have := hflag.1 rfl
          simp_all
        · exact ih _ _ _ _ _ hq hflag
      · simp only [List.mem_cons] at hq
        rcases hq with rfl | hq
        · rfl
        · exact ih _ _ _ _ _ hq ⟨fun _ => rfl, hflag.2⟩

/-- Every register place lies inside its class's eight registers and
    starts at or after the class's first free one. -/
theorem regs_within (packed : Bool) (next nextV off : Nat) (stack stackV : Bool) (args : List ArgClass)
    (p : ArgPlace) (hp : p ∈ (layoutFrom packed next nextV off stack stackV args).1) (hr : p.onStack = false) :
    (p.vector = false → next ≤ p.reg ∧ p.reg + p.regs ≤ 8) ∧
    (p.vector = true → nextV ≤ p.reg ∧ p.reg + p.regs ≤ 8) := by
  induction args generalizing next nextV off stack stackV with
  | nil => simp [layoutFrom] at hp
  | cons a rest ih =>
    unfold layoutFrom at hp
    split at hp
    · split at hp
      · rename_i hfit
        simp only [List.mem_cons] at hp
        rcases hp with rfl | hp
        · exact ⟨fun h => by simp at h, fun _ => ⟨Nat.le_refl _, hfit.2⟩⟩
        · have := ih _ _ _ _ _ hp
          exact ⟨this.1, fun hv => ⟨by have := this.2 hv; omega, (this.2 hv).2⟩⟩
      · simp only [List.mem_cons] at hp
        rcases hp with rfl | hp
        · simp at hr
        · exact ih _ _ _ _ _ hp
    · split at hp
      · rename_i hfit
        simp only [List.mem_cons] at hp
        rcases hp with rfl | hp
        · exact ⟨fun _ => ⟨Nat.le_refl _, hfit.2⟩, fun h => by simp at h⟩
        · have := ih _ _ _ _ _ hp
          exact ⟨fun hv => ⟨by have := this.1 hv; omega, (this.1 hv).2⟩, this.2⟩
      · simp only [List.mem_cons] at hp
        rcases hp with rfl | hp
        · simp at hr
        · exact ih _ _ _ _ _ hp

/-- Every stack place starts at or after the cursor `off`, is aligned as
    its class asks (with `1 ≤ align`), and ends at or before the cursor
    the fold returns. -/
theorem stack_within (packed : Bool) (next nextV off : Nat) (stack stackV : Bool) (args : List ArgClass)
    (p : ArgPlace) (hp : p ∈ (layoutFrom packed next nextV off stack stackV args).1) (hs : p.onStack = true) :
    off ≤ p.offset ∧ 1 ≤ p.align ∧ p.offset % p.align = 0 ∧
      p.offset + p.size ≤ (layoutFrom packed next nextV off stack stackV args).2 := by
  induction args generalizing next nextV off stack stackV with
  | nil => simp [layoutFrom] at hp
  | cons a rest ih =>
    have halign := stackAlign_pos packed a
    have hge := roundUp_ge off _ halign
    unfold layoutFrom at hp ⊢
    split at hp
    · rename_i hvec
      rw [if_pos hvec]
      split at hp
      · rename_i hfit
        rw [if_pos hfit]
        simp only [List.mem_cons] at hp
        rcases hp with rfl | hp
        · simp at hs
        · exact ih _ _ _ _ _ hp
      · rename_i hnot
        rw [if_neg hnot]
        simp only [List.mem_cons] at hp
        rcases hp with rfl | hp
        · exact ⟨hge, halign, roundUp_aligned _ _, cursor_ge packed next nextV _ stack true rest⟩
        · have := ih _ _ _ _ _ hp
          exact ⟨by omega, this.2.1, this.2.2.1, this.2.2.2⟩
    · rename_i hvec
      rw [if_neg hvec]
      split at hp
      · rename_i hfit
        rw [if_pos hfit]
        simp only [List.mem_cons] at hp
        rcases hp with rfl | hp
        · simp at hs
        · exact ih _ _ _ _ _ hp
      · rename_i hnot
        rw [if_neg hnot]
        simp only [List.mem_cons] at hp
        rcases hp with rfl | hp
        · exact ⟨hge, halign, roundUp_aligned _ _, cursor_ge packed next nextV _ true stackV rest⟩
        · have := ih _ _ _ _ _ hp
          exact ⟨by omega, this.2.1, this.2.2.1, this.2.2.2⟩

/-- The stack area covers every stack place. -/
theorem stack_area_covers (args : List ArgClass) (packed : Bool) (p : ArgPlace)
    (hp : p ∈ (layoutArguments args packed).1) (hs : p.onStack = true) :
    p.offset + p.size ≤ (layoutArguments args packed).2 := by
  have h := stack_within packed 0 0 0 false false args p hp hs
  have h16 := roundUp_ge (layoutFrom packed 0 0 0 false false args).2 16 (by omega)
  show _ ≤ roundUp (layoutFrom packed 0 0 0 false false args).2 16
  omega

/-- The places are ordered: each register place's registers end before
    the next register place of its class begins, each stack place ends
    before the next stack place begins, and no register place of a class
    follows a stack place of that class — so a class's register places are
    pairwise disjoint, stack places are pairwise disjoint, and once an
    argument of a class goes to the stack so does every later one of it. -/
theorem places_ordered (packed : Bool) (next nextV off : Nat) (stack stackV : Bool) (args : List ArgClass) :
    (layoutFrom packed next nextV off stack stackV args).1.Pairwise (fun p q =>
      (p.onStack = false → q.onStack = false → p.vector = q.vector → p.reg + p.regs ≤ q.reg) ∧
      (p.onStack = true → q.onStack = true → p.offset + p.size ≤ q.offset) ∧
      (p.onStack = true → p.vector = q.vector → q.onStack = true)) := by
  induction args generalizing next nextV off stack stackV with
  | nil => simp [layoutFrom]
  | cons a rest ih =>
    unfold layoutFrom
    split
    · split
      · refine List.Pairwise.cons ?_ (ih _ _ _ _ _)
        intro q hq
        refine ⟨fun _ hqr hcls => ?_, fun h => by simp at h, fun h => by simp at h⟩
        have := (regs_within packed _ _ off stack stackV rest q hq hqr).2 (by simp_all)
        simpa using this.1
      · refine List.Pairwise.cons ?_ (ih _ _ _ _ _)
        intro q hq
        refine ⟨fun h => by simp at h, fun _ hqs => (stack_within packed next nextV _ stack true rest q hq hqs).1,
          fun _ hcls => on_stack_after packed next nextV _ stack true rest q hq ⟨fun h => by simp_all, fun _ => rfl⟩⟩
    · split
      · refine List.Pairwise.cons ?_ (ih _ _ _ _ _)
        intro q hq
        refine ⟨fun _ hqr hcls => ?_, fun h => by simp at h, fun h => by simp at h⟩
        have := (regs_within packed _ _ off stack stackV rest q hq hqr).1 (by simp_all)
        simpa using this.1
      · refine List.Pairwise.cons ?_ (ih _ _ _ _ _)
        intro q hq
        refine ⟨fun h => by simp at h, fun _ hqs => (stack_within packed next nextV _ true stackV rest q hq hqs).1,
          fun _ hcls => on_stack_after packed next nextV _ true stackV rest q hq ⟨fun _ => rfl, fun h => by simp_all⟩⟩

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


example : layoutArguments [⟨1, 8, 8, false⟩, ⟨1, 4, 4, false⟩, ⟨1, 1, 1, false⟩] false = ([⟨0, 1, false, 0, 0, 0, false⟩, ⟨1, 1, false, 0, 0, 0, false⟩, ⟨2, 1, false, 0, 0, 0, false⟩], 0) := by decide
example : layoutArguments [⟨2, 16, 8, false⟩, ⟨2, 16, 8, false⟩, ⟨1, 8, 8, false⟩] false = ([⟨0, 2, false, 0, 0, 0, false⟩, ⟨2, 2, false, 0, 0, 0, false⟩, ⟨4, 1, false, 0, 0, 0, false⟩], 0) := by decide
example : layoutArguments [⟨1, 8, 8, false⟩, ⟨1, 8, 8, false⟩, ⟨1, 8, 8, false⟩, ⟨1, 8, 8, false⟩, ⟨1, 8, 8, false⟩, ⟨1, 8, 8, false⟩, ⟨1, 8, 8, false⟩, ⟨1, 8, 8, false⟩, ⟨1, 4, 4, false⟩] false = ([⟨0, 1, false, 0, 0, 0, false⟩, ⟨1, 1, false, 0, 0, 0, false⟩, ⟨2, 1, false, 0, 0, 0, false⟩, ⟨3, 1, false, 0, 0, 0, false⟩, ⟨4, 1, false, 0, 0, 0, false⟩, ⟨5, 1, false, 0, 0, 0, false⟩, ⟨6, 1, false, 0, 0, 0, false⟩, ⟨7, 1, false, 0, 0, 0, false⟩, ⟨0, 0, true, 0, 8, 8, false⟩], 16) := by decide
example : layoutArguments [⟨1, 8, 8, false⟩, ⟨1, 8, 8, false⟩, ⟨1, 8, 8, false⟩, ⟨1, 8, 8, false⟩, ⟨1, 8, 8, false⟩, ⟨1, 8, 8, false⟩, ⟨1, 8, 8, false⟩, ⟨2, 16, 8, false⟩, ⟨1, 8, 8, false⟩] false = ([⟨0, 1, false, 0, 0, 0, false⟩, ⟨1, 1, false, 0, 0, 0, false⟩, ⟨2, 1, false, 0, 0, 0, false⟩, ⟨3, 1, false, 0, 0, 0, false⟩, ⟨4, 1, false, 0, 0, 0, false⟩, ⟨5, 1, false, 0, 0, 0, false⟩, ⟨6, 1, false, 0, 0, 0, false⟩, ⟨0, 0, true, 0, 16, 8, false⟩, ⟨0, 0, true, 16, 8, 8, false⟩], 32) := by decide
example : layoutArguments [⟨1, 8, 8, false⟩, ⟨1, 8, 8, false⟩, ⟨1, 8, 8, false⟩, ⟨1, 8, 8, false⟩, ⟨1, 8, 8, false⟩, ⟨1, 8, 8, false⟩, ⟨1, 8, 8, false⟩, ⟨1, 8, 8, false⟩, ⟨1, 1, 1, false⟩, ⟨1, 2, 2, false⟩, ⟨1, 4, 4, false⟩, ⟨2, 16, 8, false⟩] true = ([⟨0, 1, false, 0, 0, 0, false⟩, ⟨1, 1, false, 0, 0, 0, false⟩, ⟨2, 1, false, 0, 0, 0, false⟩, ⟨3, 1, false, 0, 0, 0, false⟩, ⟨4, 1, false, 0, 0, 0, false⟩, ⟨5, 1, false, 0, 0, 0, false⟩, ⟨6, 1, false, 0, 0, 0, false⟩, ⟨7, 1, false, 0, 0, 0, false⟩, ⟨0, 0, true, 0, 1, 1, false⟩, ⟨0, 0, true, 2, 2, 2, false⟩, ⟨0, 0, true, 4, 4, 4, false⟩, ⟨0, 0, true, 8, 16, 8, false⟩], 32) := by decide
example : layoutArguments [⟨1, 8, 8, false⟩, ⟨1, 8, 8, false⟩, ⟨1, 8, 8, false⟩, ⟨1, 8, 8, false⟩, ⟨1, 8, 8, false⟩, ⟨1, 8, 8, false⟩, ⟨1, 8, 8, false⟩, ⟨1, 8, 8, false⟩, ⟨1, 1, 1, false⟩, ⟨1, 2, 2, false⟩] false = ([⟨0, 1, false, 0, 0, 0, false⟩, ⟨1, 1, false, 0, 0, 0, false⟩, ⟨2, 1, false, 0, 0, 0, false⟩, ⟨3, 1, false, 0, 0, 0, false⟩, ⟨4, 1, false, 0, 0, 0, false⟩, ⟨5, 1, false, 0, 0, 0, false⟩, ⟨6, 1, false, 0, 0, 0, false⟩, ⟨7, 1, false, 0, 0, 0, false⟩, ⟨0, 0, true, 0, 8, 8, false⟩, ⟨0, 0, true, 8, 8, 8, false⟩], 16) := by decide
example : layoutArguments [⟨1, 16, 16, true⟩, ⟨1, 16, 16, true⟩, ⟨1, 16, 16, true⟩, ⟨1, 16, 16, true⟩, ⟨1, 16, 16, true⟩, ⟨1, 16, 16, true⟩, ⟨1, 16, 16, true⟩, ⟨1, 16, 16, true⟩, ⟨1, 16, 16, true⟩, ⟨1, 16, 16, true⟩] true = ([⟨0, 1, false, 0, 0, 0, true⟩, ⟨1, 1, false, 0, 0, 0, true⟩, ⟨2, 1, false, 0, 0, 0, true⟩, ⟨3, 1, false, 0, 0, 0, true⟩, ⟨4, 1, false, 0, 0, 0, true⟩, ⟨5, 1, false, 0, 0, 0, true⟩, ⟨6, 1, false, 0, 0, 0, true⟩, ⟨7, 1, false, 0, 0, 0, true⟩, ⟨0, 0, true, 0, 16, 16, true⟩, ⟨0, 0, true, 16, 16, 16, true⟩], 32) := by decide
example : layoutArguments [⟨2, 16, 8, false⟩, ⟨2, 16, 8, false⟩, ⟨2, 16, 8, false⟩, ⟨2, 16, 8, false⟩, ⟨1, 4, 4, false⟩, ⟨1, 16, 16, true⟩, ⟨1, 16, 16, true⟩, ⟨1, 16, 16, true⟩, ⟨1, 16, 16, true⟩, ⟨1, 16, 16, true⟩, ⟨1, 16, 16, true⟩, ⟨1, 16, 16, true⟩, ⟨1, 16, 16, true⟩, ⟨1, 16, 16, true⟩, ⟨1, 4, 4, false⟩, ⟨1, 16, 16, true⟩] true = ([⟨0, 2, false, 0, 0, 0, false⟩, ⟨2, 2, false, 0, 0, 0, false⟩, ⟨4, 2, false, 0, 0, 0, false⟩, ⟨6, 2, false, 0, 0, 0, false⟩, ⟨0, 0, true, 0, 4, 4, false⟩, ⟨0, 1, false, 0, 0, 0, true⟩, ⟨1, 1, false, 0, 0, 0, true⟩, ⟨2, 1, false, 0, 0, 0, true⟩, ⟨3, 1, false, 0, 0, 0, true⟩, ⟨4, 1, false, 0, 0, 0, true⟩, ⟨5, 1, false, 0, 0, 0, true⟩, ⟨6, 1, false, 0, 0, 0, true⟩, ⟨7, 1, false, 0, 0, 0, true⟩, ⟨0, 0, true, 16, 16, 16, true⟩, ⟨0, 0, true, 32, 4, 4, false⟩, ⟨0, 0, true, 48, 16, 16, true⟩], 64) := by decide
example : layoutArguments [⟨1, 16, 16, true⟩, ⟨1, 16, 16, true⟩, ⟨1, 16, 16, true⟩, ⟨1, 16, 16, true⟩, ⟨1, 16, 16, true⟩, ⟨1, 16, 16, true⟩, ⟨1, 16, 16, true⟩, ⟨1, 16, 16, true⟩, ⟨1, 4, 4, true⟩, ⟨1, 1, 1, false⟩, ⟨1, 8, 8, true⟩] false = ([⟨0, 1, false, 0, 0, 0, true⟩, ⟨1, 1, false, 0, 0, 0, true⟩, ⟨2, 1, false, 0, 0, 0, true⟩, ⟨3, 1, false, 0, 0, 0, true⟩, ⟨4, 1, false, 0, 0, 0, true⟩, ⟨5, 1, false, 0, 0, 0, true⟩, ⟨6, 1, false, 0, 0, 0, true⟩, ⟨7, 1, false, 0, 0, 0, true⟩, ⟨0, 0, true, 0, 8, 8, true⟩, ⟨0, 1, false, 0, 0, 0, false⟩, ⟨0, 0, true, 8, 8, 8, true⟩], 16) := by decide
example : compositeChunks 1 = (1, false) := by decide
example : compositeChunks 4 = (1, false) := by decide
example : compositeChunks 8 = (1, false) := by decide
example : compositeChunks 9 = (2, false) := by decide
example : compositeChunks 16 = (2, false) := by decide
example : compositeChunks 17 = (1, true) := by decide
example : compositeChunks 32 = (1, true) := by decide

end Oak.ArgumentLayout
