import Oak.WasmEncoding

/-! Scalar-profile instruction tokens. Control delimiters are explicit; the
module validator, not this encoder, checks nesting, stack types and indices.
The opcode partition is pinned to the same Core reference as WasmLEB. -/
namespace Oak.WasmInstruction

inductive Immediate where
  | plain | block | index | s32 | s64
  deriving DecidableEq, Repr

def kind (op : UInt8) : Option Immediate :=
  let n := op.toNat
  if n = 2 ∨ n = 3 ∨ n = 4 then some .block
  else if n = 12 ∨ n = 13 ∨ n = 16 ∨ n = 32 ∨ n = 33 ∨ n = 34 then some .index
  else if n = 65 then some .s32
  else if n = 66 then some .s64
  else if n = 0 ∨ n = 1 ∨ n = 5 ∨ n = 11 ∨ n = 15 ∨ n = 26 ∨
      (69 ≤ n ∧ n ≤ 79) ∨ (81 ≤ n ∧ n ≤ 90) ∨
      (106 ≤ n ∧ n ≤ 115) ∨ (124 ≤ n ∧ n ≤ 133) then some .plain
  else none

theorem scalar_opcode_count :
    ((List.range 256).filter (fun n => (kind (UInt8.ofNat n)).isSome)).length = 58 := by decide

def blockType (v : Int) : Prop := v = 64 ∨ v = 127 ∨ v = 126
instance (v : Int) : Decidable (blockType v) := by unfold blockType; infer_instance

def encode (op : UInt8) (v : Int) : Option (List UInt8) := do
  let k ← kind op
  match k with
  | .plain => if v = 0 then some [op] else none
  | .block => if blockType v then some [op, UInt8.ofNat v.toNat] else none
  | .index => if WasmLEB.inRange 32 false v then some (op :: WasmEncoding.encode 32 false v) else none
  | .s32 => if WasmLEB.inRange 32 true v then some (op :: WasmEncoding.encode 32 true v) else none
  | .s64 => if WasmLEB.inRange 64 true v then some (op :: WasmEncoding.encode 64 true v) else none

def decode (bytes : List UInt8) : Option ((UInt8 × Int) × List UInt8) := do
  let op :: rest := bytes | none
  let k ← kind op
  match k with
  | .plain => some ((op, 0), rest)
  | .block =>
    let b :: tail := rest | none
    if blockType b.toNat then some ((op, b.toNat), tail) else none
  | .index =>
    let (v, tail) ← WasmLEB.decode 32 false rest
    some ((op, v), tail)
  | .s32 =>
    let (v, tail) ← WasmLEB.decode 32 true rest
    some ((op, v), tail)
  | .s64 =>
    let (v, tail) ← WasmLEB.decode 64 true rest
    some ((op, v), tail)

/-- Complete operand-family coverage for every accepted instruction token. -/
theorem decode_encode {op value bytes} (h : encode op value = some bytes)
    (suffix : List UInt8) : decode (bytes ++ suffix) = some ((op, value), suffix) := by
  cases hk : kind op with
  | none => simp [encode, hk] at h
  | some k =>
    cases k with
    | plain =>
      simp [encode, hk] at h
      obtain ⟨rfl, rfl⟩ := h
      simp [decode, hk]
    | block =>
      simp [encode, hk] at h
      obtain ⟨hb, rfl⟩ := h
      rcases hb with rfl | rfl | rfl <;> simp [decode, hk, blockType]
    | index =>
      simp [encode, hk] at h
      obtain ⟨hr, rfl⟩ := h
      simp [decode, hk, WasmEncoding.decode_encode (by decide : 0 < 32) hr suffix]
    | s32 =>
      simp [encode, hk] at h
      obtain ⟨hr, rfl⟩ := h
      simp [decode, hk, WasmEncoding.decode_encode (by decide : 0 < 32) hr suffix]
    | s64 =>
      simp [encode, hk] at h
      obtain ⟨hr, rfl⟩ := h
      simp [decode, hk, WasmEncoding.decode_encode (by decide : 0 < 64) hr suffix]

theorem encoding_injective {op₁ op₂ value₁ value₂ bytes}
    (h₁ : encode op₁ value₁ = some bytes) (h₂ : encode op₂ value₂ = some bytes) :
    op₁ = op₂ ∧ value₁ = value₂ := by
  have h := decode_encode h₁ []
  rw [decode_encode h₂ []] at h
  simpa using h.symm

def assemble : List (UInt8 × Int) → Option (List UInt8)
  | [] => some []
  | (op, v) :: rest => do
    let front ← encode op v
    let tail ← assemble rest
    some (front ++ tail)

/-- Decode a syntactic instruction count, not execution steps or runtime fuel. -/
def decodeMany : Nat → List UInt8 → Option (List (UInt8 × Int) × List UInt8)
  | 0, bytes => some ([], bytes)
  | n + 1, bytes => do
    let (ins, tail) ← decode bytes
    let (instructions, suffix) ← decodeMany n tail
    some (ins :: instructions, suffix)

/-- Sequence composition preserves order, values, and the entire suffix. -/
theorem decode_assemble {instructions bytes} (h : assemble instructions = some bytes)
    (suffix : List UInt8) :
    decodeMany instructions.length (bytes ++ suffix) = some (instructions, suffix) := by
  induction instructions generalizing bytes with
  | nil => simp [assemble] at h; subst bytes; rfl
  | cons ins rest ih =>
    obtain ⟨op, v⟩ := ins
    cases he : encode op v with
    | none => simp [assemble, he] at h
    | some front =>
      cases hr : assemble rest with
      | none => simp [assemble, he, hr] at h
      | some tail =>
        simp [assemble, he, hr] at h
        subst bytes
        simp [decodeMany, List.append_assoc, decode_encode he (tail ++ suffix), ih hr]

end Oak.WasmInstruction
