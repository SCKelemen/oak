import Oak.ArmDecoderClassification.Checker
import Oak.ArmDecoderPartition.Bytes

/-! Exact octet partitioning only; this is not a Sail parser. -/
namespace Oak.ArmDecoderPartition
open Oak.ArmDecoderClassification

structure Cell where
  bytes : Bytes
  size : Nat
  sized : bytes.length = size

structure Page where
  bytes : Bytes
  cells : List Cell
  covered : bytes = cells.flatMap Cell.bytes

structure Part where
  entry : CheckedRow
  cells : List Cell
  covered : rawBytes entry.raw = cells.flatMap Cell.bytes

def lf : Cell := ⟨[10], 1, rfl⟩

def separated {α : Type} (f : α → List Cell) : List α → List Cell
  | [] => []
  | [x] => f x
  | x :: y :: xs => f x ++ lf :: separated f (y :: xs)

def separatedBytes {α : Type} (f : α → Bytes) : List α → Bytes
  | [] => []
  | [x] => f x
  | x :: y :: xs => f x ++ 10 :: separatedBytes f (y :: xs)

theorem separated_sound {α : Type} (cells : α → List Cell) (bytes : α → Bytes)
    (bound : ∀ x, bytes x = (cells x).flatMap Cell.bytes) (xs : List α) :
    (separated cells xs).flatMap Cell.bytes = separatedBytes bytes xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases xs with
    | nil => exact (bound x).symm
    | cons y ys =>
      simp only [separated, List.flatMap_append, List.flatMap_cons, lf,
        List.singleton_append, separatedBytes]
      rw [ih, ← bound]

theorem pages_sound (pages : List Page) :
    pages.flatMap Page.bytes = (pages.flatMap Page.cells).flatMap Cell.bytes := by
  simp only [List.flatMap_assoc]
  exact congrArg (fun f => pages.flatMap f) (funext fun p => p.covered)

theorem partition_sound (pages : List Page) (pre : List Cell) (parts : List Part)
    (h : pages.flatMap Page.cells = pre ++ separated Part.cells parts) :
    pages.flatMap Page.bytes = pre.flatMap Cell.bytes ++
      separatedBytes (fun p => rawBytes p.entry.raw) parts := by
  rw [pages_sound, h, List.flatMap_append,
    separated_sound Part.cells (fun p => rawBytes p.entry.raw) (fun p => p.covered)]

theorem cell_lengths (cells : List Cell) :
    (cells.flatMap Cell.bytes).length = (cells.map Cell.size).sum := by
  induction cells with
  | nil => rfl
  | cons c cs ih => simp only [List.flatMap_cons, List.length_append, c.sized,
      List.map_cons, List.sum_cons, ih]

theorem separatedBytes_map {α β : Type} (f : β → Bytes) (g : α → β) (xs : List α) :
    separatedBytes f (xs.map g) = separatedBytes (fun x => f (g x)) xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases xs with
    | nil => rfl
    | cons y ys =>
      change f (g x) ++ 10 :: separatedBytes f (g y :: ys.map g) =
        f (g x) ++ 10 :: separatedBytes (fun z => f (g z)) (y :: ys)
      exact congrArg (fun tail => f (g x) ++ 10 :: tail) ih

theorem separatedBytes_length {α : Type} (f : α → Bytes) (xs : List α) :
    (separatedBytes f xs).length = (xs.map (fun x => (f x).length)).sum + (xs.length - 1) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases xs with
    | nil => simp [separatedBytes]
    | cons y ys =>
      change (f x ++ 10 :: separatedBytes f (y :: ys)).length = _
      simp only [List.length_append, List.length_cons]
      rw [ih]
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      omega

end Oak.ArmDecoderPartition
