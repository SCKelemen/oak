import Oak.AArch64ControlFlow

/-! Register-only SSA edge copies. Certificates compare decoded MOV W/X execution
with simultaneous assignments, allowing only reserved X17 clobbering. This is
not a universal proof of the Go scheduler. Spills and rematerialization remain
outside this no-fault PC/register/NZCV projection. -/
namespace Oak.AArch64EdgeCopies
open Oak.AArch64BranchExecution
open Oak.AArch64ControlFlow
structure Move where
  dst : BitVec 5
  src : BitVec 5
  narrow : Bool
  deriving DecidableEq, Repr

/-- MOV register aliases ORR W/Xd, W/XZR, W/Xm, LSL #0. -/
def decodeMove (w : BitVec 32) : Option Move :=
  if w &&& 0xffe0ffe0#32 == 0x2a0003e0#32 then
    some ⟨w.extractLsb' 0 5, w.extractLsb' 16 5, true⟩
  else if w &&& 0xffe0ffe0#32 == 0xaa0003e0#32 then
    some ⟨w.extractLsb' 0 5, w.extractLsb' 16 5, false⟩
  else none

def resize (narrow : Bool) (v : BitVec 64) : BitVec 64 :=
  if narrow then v &&& 0xffffffff#64 else v
theorem resize_w32 (v : BitVec 64) :
    resize true v = (v.extractLsb' 0 32).zeroExtend 64 := by
  simp only [resize, if_true]; bv_decide

structure Expr where
  source : BitVec 5
  narrow : Bool
  deriving DecidableEq, Repr
def eval (initial : Registers) (e : Expr) : BitVec 64 :=
  resize e.narrow (readX initial e.source)
def narrowExpr (n : Bool) (e : Expr) : Expr := ⟨e.source, n || e.narrow⟩

theorem eval_narrow (initial : Registers) (n : Bool) (e : Expr) :
    eval initial (narrowExpr n e) = resize n (eval initial e) := by
  rcases e with ⟨r, b⟩
  cases n <;> cases b <;> simp [eval, narrowExpr, resize, BitVec.and_assoc]

/-- Architectural move: read ZR as zero, ignore writes to ZR. -/
def applyMove {α : Type} (zero : α) (norm : Bool → α → α)
    (m : Move) (regs : BitVec 5 → α) : BitVec 5 → α :=
  fun r => if m.dst != 31#5 && r == m.dst then
    norm m.narrow (if m.src == 31#5 then zero else regs m.src) else regs r

def execute {α : Type} (zero : α) (norm : Bool → α → α) :
    List (BitVec 32) → (BitVec 5 → α) → Option (BitVec 5 → α)
  | [], regs => some regs
  | w :: ws, regs => do
    let m ← decodeMove w
    execute zero norm ws (applyMove zero norm m regs)
def initialExpr (r : BitVec 5) : Expr := ⟨r, false⟩
def symbolic (words : List (BitVec 32)) := execute (Expr.mk 31 false) narrowExpr words initialExpr

theorem eval_apply (initial : Registers) (m : Move) (regs : BitVec 5 → Expr) :
    (fun r => eval initial (applyMove ⟨31, false⟩ narrowExpr m regs r)) =
      applyMove 0 resize m (fun r => eval initial (regs r)) := by
  funext r
  simp only [applyMove]
  split
  · split
    · rw [eval_narrow]; simp [eval, resize, readX]
    · exact eval_narrow initial m.narrow (regs m.src)
  · rfl

theorem execute_eval (initial : Registers) (words : List (BitVec 32))
    (regs : BitVec 5 → Expr) :
    execute 0 resize words (fun r => eval initial (regs r)) =
      (execute ⟨31, false⟩ narrowExpr words regs).map (fun out r => eval initial (out r)) := by
  induction words generalizing regs with
  | nil => rfl
  | cons w ws ih =>
    cases hd : decodeMove w with
    | none => simp [execute, hd]
    | some m =>
      simp only [execute, hd, Bind.bind, Option.bind]
      rw [← eval_apply, ih]

/-- Read all inputs from the original register file. Elided self-copies do not
promise upper-bit normalization. The checker refuses duplicate destinations. -/
def expected (moves : List Move) (r : BitVec 5) : Expr :=
  match moves.find? (fun m => m.dst == r && m.dst != m.src) with
  | none => initialExpr r
  | some m => ⟨m.src, m.narrow⟩
def validMoves (moves : List Move) : Bool :=
  moves.all (fun m => m.dst != 17#5 && m.dst != 31#5 && m.src != 17#5) &&
    (moves.map Move.dst).eraseDups.length == moves.length
def checkCopies (moves : List Move) (words : List (BitVec 32)) : Bool :=
  validMoves moves && match symbolic words with
  | none => false
  | some out => decide (∀ r : BitVec 5, r ≠ 17#5 → out r = expected moves r)

/-- ZR's unused stored slot is canonicalized to zero. -/
def runCopies (words : List (BitVec 32)) (s : State) : Option State :=
  (execute 0 resize words (readX s.regs)).map fun regs =>
    ⟨s.pc + BitVec.ofNat 64 (4 * words.length), s.flags, regs⟩

theorem checked_copies (moves : List Move) (words : List (BitVec 32))
    (h : checkCopies moves words = true) (s : State) :
    ∃ out, runCopies words s = some out ∧
      out.pc = s.pc + BitVec.ofNat 64 (4 * words.length) ∧ out.flags = s.flags ∧
      ∀ r, r ≠ 17#5 → out.regs r = eval s.regs (expected moves r) := by
  simp only [checkCopies, Bool.and_eq_true] at h
  cases hs : symbolic words with
  | none => simp [hs] at h
  | some regs =>
    have he : ∀ r : BitVec 5, r ≠ 17#5 → regs r = expected moves r := by
      simpa [hs] using h.2
    have hx := execute_eval s.regs words initialExpr
    change execute 0 resize words (readX s.regs) = _ at hx
    change execute 0 resize words (readX s.regs) = (symbolic words).map _ at hx
    rw [hs] at hx
    simp only [Option.map_some] at hx
    refine ⟨⟨s.pc + BitVec.ofNat 64 (4 * words.length), s.flags, fun r => eval s.regs (regs r)⟩, ?_, rfl, rfl, ?_⟩
    · unfold runCopies; rw [hx]; rfl
    · intro r hr; change eval s.regs (regs r) = _; rw [he r hr]

/-- Copy prefix followed by an unconditional edge, including fall-through. -/
theorem checked_edge (moves : List Move) (copies branch : List (BitVec 32))
    (target : Nat) (next : Option Nat) (addr : Nat → BitVec 64) (s : State)
    (hc : checkCopies moves copies = true)
    (hb : check target target next (s.pc + BitVec.ofNat 64 (4 * copies.length)) addr 0 branch = true) :
    ∃ out, (runCopies copies s >>= run branch) = some out ∧
      out.pc = addr target ∧ out.flags = s.flags ∧
      ∀ r, r ≠ 17#5 → out.regs r = eval s.regs (expected moves r) := by
  obtain ⟨copied, hcRun, hp, hf, hr⟩ := checked_copies moves copies hc s
  have route := checked_successor target target next copied.pc addr 0 branch (hp ▸ hb) copied.flags copied.regs
  simp only [ite_self] at route
  refine ⟨⟨addr target, copied.flags, copied.regs⟩, ?_, rfl, hf, hr⟩
  rw [hcRun]
  exact route

def moveWord (m : Move) : BitVec 32 :=
  (if m.narrow then 0x2a0003e0#32 else 0xaa0003e0#32) |||
    (m.src.zeroExtend 32 <<< 16) ||| m.dst.zeroExtend 32

theorem decode_moveWord (m : Move) : decodeMove (moveWord m) = some m := by
  have tag : moveWord m &&& 0xffe0ffe0#32 =
      (if m.narrow then 0x2a0003e0#32 else 0xaa0003e0#32) := by
    unfold moveWord; bv_decide
  have hd : (moveWord m).extractLsb' 0 5 = m.dst := by unfold moveWord; bv_decide
  have hs : (moveWord m).extractLsb' 16 5 = m.src := by unfold moveWord; bv_decide
  simp only [decodeMove, tag, hd, hs]
  rcases m with ⟨d, s, n⟩
  cases n <;> rfl

/-- Fetch the selected edge stub by the PC produced by decoded dispatch. -/
def runConditional (dispatch yesCopies yesBranch noCopies noBranch : List (BitVec 32))
    (yesPC noPC : BitVec 64) (s : State) : Option State := do
  let selected ← run dispatch s
  if selected.pc == yesPC then
    let copied ← runCopies yesCopies selected
    run yesBranch copied
  else if selected.pc == noPC then
    let copied ← runCopies noCopies selected
    run noBranch copied
  else none

/-- Both edge stubs may overwrite the condition register: dispatch has already
selected the stub. The two dispatch addresses must be distinct. -/
theorem checked_conditional (yesMoves noMoves : List Move)
    (dispatch yesCopies yesBranch noCopies noBranch : List (BitVec 32))
    (yesPC noPC : BitVec 64) (yes no : Nat) (addr : Nat → BitVec 64)
    (rt : BitVec 5) (s : State) (distinct : yesPC ≠ noPC)
    (hd : check 0 1 none s.pc (fun id => if id = 0 then yesPC else noPC) rt dispatch = true)
    (hy : checkCopies yesMoves yesCopies = true)
    (hn : checkCopies noMoves noCopies = true)
    (hby : check yes yes none (yesPC + BitVec.ofNat 64 (4 * yesCopies.length)) addr 0 yesBranch = true)
    (hbn : check no no none (noPC + BitVec.ofNat 64 (4 * noCopies.length)) addr 0 noBranch = true) :
    ∃ out, runConditional dispatch yesCopies yesBranch noCopies noBranch yesPC noPC s = some out ∧
      out.pc = (if boolValue s.regs rt then addr yes else addr no) ∧ out.flags = s.flags ∧
      ∀ r, r ≠ 17#5 → out.regs r =
        eval s.regs (expected (if boolValue s.regs rt then yesMoves else noMoves) r) := by
  have route := checked_successor 0 1 none s.pc (fun id => if id = 0 then yesPC else noPC)
    rt dispatch hd s.flags s.regs
  cases hv : boolValue s.regs rt
  · simp only [hv, Bool.false_eq_true, if_false] at route
    obtain ⟨out, he, hp, hf, hr⟩ := checked_edge noMoves noCopies noBranch no none addr
      ⟨noPC, s.flags, s.regs⟩ hn hbn
    refine ⟨out, ?_, by simpa [hv] using hp, hf, ?_⟩
    · simp only [runConditional, route, Bind.bind, Option.bind]
      simpa [Ne.symm distinct, Bind.bind, Option.bind] using he
    · simpa [hv] using hr
  · simp only [hv, if_true] at route
    obtain ⟨out, he, hp, hf, hr⟩ := checked_edge yesMoves yesCopies yesBranch yes none addr
      ⟨yesPC, s.flags, s.regs⟩ hy hby
    refine ⟨out, ?_, by simpa [hv] using hp, hf, ?_⟩
    · simp only [runConditional, route, Bind.bind, Option.bind]
      simpa [Bind.bind, Option.bind] using he
    · simpa [hv] using hr

end Oak.AArch64EdgeCopies
