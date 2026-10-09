import Oak.ArmDecoderPartition.Bytes

/-! A raw ASCII substring counter. It gives no Sail lexical/parser theorem. -/
namespace Oak.ArmDecoderPartition

def marker : Bytes := [100,101,99,111,100,101,54,52] -- decode64

/-- Count starts at every byte position, including overlapping occurrences. -/
def occurrences : Bytes → Nat
  | [] => 0
  | b :: bs => (if (b :: bs).take 8 == marker then 1 else 0) + occurrences bs

abbrev Scan := Bytes × Nat

def scanStep (b : UInt8) (s : Scan) : Scan :=
  ((b :: s.1).take 7,
   (if (b :: s.1).take 8 == marker then 1 else 0) + s.2)

def scan (xs : Bytes) (tail : Scan := ([],0)) : Scan := xs.foldr scanStep tail

theorem scan_exact (xs : Bytes) : scan xs = (xs.take 7, occurrences xs) := by
  induction xs with
  | nil => rfl
  | cons b bs ih =>
    simp only [scan, List.foldr_cons] at *
    rw [ih]
    simp [scanStep, occurrences, List.take_take]

theorem scan_append (xs ys : Bytes) (tail : Scan) :
    scan (xs ++ ys) tail = scan xs (scan ys tail) := by
  exact List.foldr_append

/-- Certificates carry the complete scanner state across every boundary. -/
inductive ScanTrace : List Bytes → Scan → Scan → Prop
  | nil (s) : ScanTrace [] s s
  | cons {xs : Bytes} {rest : List Bytes} {initial middle final : Scan}
      (step : scan xs middle = final) (tail : ScanTrace rest initial middle) :
      ScanTrace (xs :: rest) initial final

theorem ScanTrace.sound {blocks : List Bytes} {initial final : Scan}
    (trace : ScanTrace blocks initial final) : scan blocks.flatten initial = final := by
  induction trace with
  | nil => rfl
  | cons step tail ih =>
    rw [List.flatten_cons, scan_append, ih]
    exact step

end Oak.ArmDecoderPartition
