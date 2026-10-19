import Oak.CNFLiteralExtracted
import Oak.LRATRUPSoundness
import Std.Tactic.BVDecide

/-!
Production CNF edge-to-word encoding, composed with the LRAT word decoder.
Edges 0 and 1 are constants and must be folded before emission. Every other
UInt32 edge encodes a one-based node; LRAT uses its zero-based variable index.
Extraction drift is checked against the production solver package. This does
not prove the extractor, the gate producer, source lowering, or compiled code.
-/
set_option autoImplicit false
namespace Oak.CNFLiteral

def encode (edge : UInt32) : UInt32 :=
  (2 : UInt32) * ((edge >>> (1 : UInt32)) - 1) + (1 - (edge &&& 1))

theorem extracted (edge : UInt32) (fuel : Nat) :
    cnf_lit edge fuel = some (encode edge) := by rfl

theorem index_word (edge : UInt32) (h : 2 ≤ edge) :
    encode edge / (2 : UInt32) = (edge >>> 1) - 1 := by
  unfold encode
  bv_decide

theorem polarity_word (edge : UInt32) :
    (encode edge % 2 == 1) = (edge &&& 1 == 0) := by
  unfold encode
  bv_decide

theorem decode_exact (edge : UInt32) (h : 2 ≤ edge) :
    Oak.LRATRUP.decodeWord (encode edge) =
      ⟨((edge >>> 1) - 1).toNat, edge &&& 1 == 0⟩ := by
  simp only [Oak.LRATRUP.decodeWord, index_word edge h, polarity_word]

/-- The original Boolean edge meaning, indexed by the zero-based SAT inputs. -/
def edgeValue (assignment : Oak.RupCheck.Assignment) (edge : UInt32) : Bool :=
  if edge &&& 1 == 0 then assignment (((edge >>> 1) - 1).toNat)
  else !(assignment (((edge >>> 1) - 1).toNat))

theorem literal_semantics (assignment : Oak.RupCheck.Assignment)
    (edge : UInt32) (h : 2 ≤ edge) :
    Oak.RupCheck.Holds assignment (Oak.LRATRUP.decodeWord (encode edge)) ↔
      edgeValue assignment edge = true := by
  rw [decode_exact edge h]
  simp only [Oak.RupCheck.Holds, edgeValue]
  cases hp : (edge &&& 1 == 0) <;>
    cases hv : assignment (((edge >>> 1) - 1).toNat) <;> simp [hp, hv]

/-- Serialization of any nonconstant clause preserves its satisfaction. -/
theorem clause_semantics (assignment : Oak.RupCheck.Assignment)
    (edges : List UInt32) (valid : ∀ edge ∈ edges, 2 ≤ edge) :
    Oak.RupCheck.SatisfiesClause assignment
      (edges.map (fun edge => Oak.LRATRUP.decodeWord (encode edge))) ↔
      ∃ edge ∈ edges, edgeValue assignment edge = true := by
  simp only [Oak.RupCheck.SatisfiesClause, List.mem_map]
  constructor
  · rintro ⟨lit, ⟨edge, member, rfl⟩, holds⟩
    exact ⟨edge, member, (literal_semantics assignment edge (valid edge member)).mp holds⟩
  · rintro ⟨edge, member, holds⟩
    exact ⟨_, ⟨edge, member, rfl⟩,
      (literal_semantics assignment edge (valid edge member)).mpr holds⟩

end Oak.CNFLiteral
