import Oak.ArmDecoderClassification.Selection
import Oak.AArch64BitwiseFunction

/-! A byte-to-classification bridge only. The byte reader and function artifact
are the existing native profile's definitions. This does not execute full Sail
or prove source extraction, register initialization, fetch or loader behavior. -/
namespace Oak.ArmDecoderClassification
open Oak.AArch64BitwiseFunction (functionBytes takeWord)
open Oak.BitwiseFunction (Op)

def classifyFunction (bytes : List UInt8) : Option (Nat × Nat) :=
  match takeWord bytes with
  | none => none
  | some (word, rest) =>
    match takeWord rest with
    | some (ret, []) => do
      let a ← first table word (-1)
      let b ← first table ret (-1)
      pure (a,b)
    | _ => none

def logicalIndex : Op → Nat
  | .and => 1845 | .or => 1858 | .xor => 1788

/-- Existing exact eight-byte artifacts yield these two ordered classifications. -/
theorem function_bytes_classified (op : Op) :
    classifyFunction (functionBytes op) = some (logicalIndex op,1522) := by
  cases op <;>
    simp [classifyFunction, functionBytes, takeWord, logicalIndex,
      first_and, first_orr, first_eor, first_ret]

theorem reject_trailing_bytes (op : Op) :
    classifyFunction (functionBytes op ++ [0]) = none := by
  cases op <;> rfl

theorem reject_short_bytes : classifyFunction [0,0,1,0x0a,0xc0,3,0x5f] = none := by rfl

end Oak.ArmDecoderClassification
