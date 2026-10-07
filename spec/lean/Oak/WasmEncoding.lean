import Oak.WasmLEB

/-!
# Wasm canonical integer encoding

The assembler emits the shortest signed or unsigned LEB prefix. The theorem
is over every admitted integer and every suffix, not selected machine words.
The independent grammar/decoder is Oak.WasmLEB. Go/Oak implementations are
connected by separate production tests; this file does not verify their loops.
-/
namespace Oak.WasmEncoding
open Oak.WasmLEB

def terminal (signed : Bool) (v : Int) : Prop :=
  if signed then -64 ≤ v ∧ v < 64 else 0 ≤ v ∧ v < 128

instance (signed : Bool) (v : Int) : Decidable (terminal signed v) := by
  unfold terminal; infer_instance

/-- Width is a structural recursion bound, not a runtime execution fuel. -/
def encode (width : Nat) (signed : Bool) (v : Int) : List UInt8 :=
  if terminal signed v ∨ width ≤ 7 then [UInt8.ofNat (v % 128).toNat]
  else UInt8.ofNat ((v % 128).toNat + 128) :: encode (width - 7) signed (v / 128)
termination_by width
decreasing_by omega

private theorem payload_bounds (v : Int) : 0 ≤ v % 128 ∧ v % 128 < 128 :=
  ⟨Int.emod_nonneg _ (by decide), Int.emod_lt_of_pos _ (by decide)⟩

private theorem payload_nat (v : Int) : (UInt8.ofNat (v % 128).toNat).toNat = (v % 128).toNat := by
  have := payload_bounds v
  simp only [UInt8.toNat_ofNat']
  omega

private theorem continuation_nat (v : Int) :
    (UInt8.ofNat ((v % 128).toNat + 128)).toNat = (v % 128).toNat + 128 := by
  have := payload_bounds v
  simp only [UInt8.toNat_ofNat']
  omega

private theorem terminal_value {s v} (h : terminal s v) :
    terminalValue s (UInt8.ofNat (v % 128).toNat) = v := by
  have := payload_bounds v
  have := Int.emod_add_mul_ediv v 128
  simp only [terminalValue, payload_nat]
  cases s <;> simp only [terminal, Bool.false_eq_true, ↓reduceIte] at h
  · simp; omega
  · simp only [Bool.true_and, decide_eq_true_eq]
    split <;> omega

private theorem small_terminal {w s v} (hp : 0 < w) (hw : w ≤ 7)
    (h : inRange w s v) : terminal s v := by
  have hw' : w = 1 ∨ w = 2 ∨ w = 3 ∨ w = 4 ∨ w = 5 ∨ w = 6 ∨ w = 7 := by omega
  rcases hw' with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    cases s <;> simp_all [terminal, inRange] <;> omega

/-- Removing a continuation group preserves the remaining signed/unsigned range. -/
theorem quotient_range {w s v} (hw : 7 < w)
    (h : inRange w s v) : inRange (w - 7) s (v / 128) := by
  have splitPow (n : Nat) (hn : 7 ≤ n) : (2 ^ n : Int) = 128 * 2 ^ (n - 7) := by
    calc (2 ^ n : Int) = 2 ^ (7 + (n - 7)) := by congr 1; omega
         _ = 128 * 2 ^ (n - 7) := by rw [Int.pow_add]; rfl
  have := payload_bounds v
  have := Int.emod_add_mul_ediv v 128
  cases s with
  | false =>
    simp only [inRange, Bool.false_eq_true, ↓reduceIte] at h ⊢
    rw [splitPow w (by omega)] at h
    omega
  | true =>
    simp only [inRange, ↓reduceIte] at h ⊢
    rw [splitPow (w - 1) (by omega)] at h
    have he : w - 1 - 7 = w - 7 - 1 := by omega
    rw [he] at h
    omega

/-- An in-range value that needs another group has at least eight bits left. -/
theorem continuation_width {w s v} (hp : 0 < w) (hr : inRange w s v)
    (hn : ¬ terminal s v) : 7 < w := by
  by_cases hw : w ≤ 7
  · exact False.elim (hn (small_terminal hp hw hr))
  · omega

/-- On in-range values, the encoder stops exactly at the canonical terminal
range; the width bound cannot force an early terminal byte. -/
theorem encode_step {w s v} (hp : 0 < w) (hr : inRange w s v) :
    encode w s v = if terminal s v then [UInt8.ofNat (v % 128).toNat]
      else UInt8.ofNat ((v % 128).toNat + 128) :: encode (w - 7) s (v / 128) := by
  rw [encode]
  by_cases ht : terminal s v
  · simp [ht]
  · have hw := continuation_width hp hr ht
    simp [ht, show ¬w ≤ 7 by omega]

theorem encode_grammar {width signed value} (hp : 0 < width)
    (hr : inRange width signed value) :
    Encoding width signed (encode width signed value) value := by
  induction width using Nat.strongRecOn generalizing value with
  | ind w ih =>
    rw [encode]
    split
    next stop =>
      have ht : terminal signed value := stop.elim id (fun h => small_terminal hp h hr)
      have hv := terminal_value ht
      have hb := payload_bounds value
      have he := Encoding.terminal (b := UInt8.ofNat (value % 128).toNat) hp
        (by rw [payload_nat]; omega) (by rw [hv]; exact hr)
      simpa only [hv] using he
    next more =>
      have hw : 7 < w := by omega
      have he := Encoding.continuation (b := UInt8.ofNat ((value % 128).toNat + 128))
        hw (by rw [continuation_nat]; omega)
        (ih (w - 7) (by omega) (by omega) (quotient_range hw hr))
      have hb := payload_bounds value
      have hv := Int.emod_add_mul_ediv value 128
      have eqv : (((UInt8.ofNat ((value % 128).toNat + 128)).toNat % 128 : Nat) : Int) + 128 * (value / 128) = value := by
        rw [continuation_nat]
        omega
      simpa only [eqv] using he

/-- Every admissible immediate decodes to itself and leaves its suffix intact. -/
theorem decode_encode {width signed value} (hp : 0 < width)
    (hr : inRange width signed value) (suffix : List UInt8) :
    decode width signed (encode width signed value ++ suffix) = some (value, suffix) :=
  decode_complete (encode_grammar hp hr) suffix

theorem encode_nonempty {width signed value} (hp : 0 < width)
    (hr : inRange width signed value) : encode width signed value ≠ [] :=
  Encoding.nonempty (encode_grammar hp hr)

theorem encode_byte_budget {width signed value} (hp : 0 < width)
    (hr : inRange width signed value) :
    7 * (encode width signed value).length ≤ width + 6 :=
  Encoding.byte_budget (encode_grammar hp hr)

end Oak.WasmEncoding
