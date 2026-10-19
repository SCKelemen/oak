import Oak.CNFReplayTerm
import Oak.CNFReplayMemo
import Oak.AssemblerSemantics

/-!
# Compositional typed word circuit rules

These circuits operate on already established child bits. Their interpretation
is independent of gate replay: arithmetic is proved against BitVec operations
using AssemblerSemantics, including truncation before widening. The rules are
suitable for a node-by-node checked DAG; they do not by themselves establish
complete DAG coverage, read-class binding, or a supplied production instance.
-/

set_option autoImplicit false

namespace Oak.CNFTypedCircuit

open Oak.RupCheck Oak.CNFReplayApply Oak.CNFReplayTerm
open Oak.AssemblerSemantics

/-- Local circuit leaves name already established CNF edges, including gate
outputs. This is deliberately distinct from designated source-input replay. -/
def replayCircuit (snapshot : Oak.CNFDenseAllocation.Snapshot) (maxInt : Nat) :
    Term → Option Nat
  | .constant value => some (if value then 1 else 0)
  | .input edge => some edge
  | .binary op left right =>
      match replayCircuit snapshot maxInt left, replayCircuit snapshot maxInt right with
      | some x, some y => replayApply snapshot.variables maxInt snapshot.memo op x y
      | _, _ => none
  | .complement term => (replayCircuit snapshot maxInt term).map flipEdge
  | .ite condition thenValue elseValue =>
      match replayCircuit snapshot maxInt condition,
          replayCircuit snapshot maxInt thenValue, replayCircuit snapshot maxInt elseValue with
      | some c, some t, some e => replayIte snapshot.variables maxInt snapshot.memo c t e
      | _, _, _ => none

def edgeAssignment (assignment : Assignment) : Assignment := evalEdge assignment

theorem replayCircuit_sound {snapshot : Oak.CNFDenseAllocation.Snapshot} {maxInt : Nat}
    {assignment : Assignment} (sound : MemoSound assignment snapshot.memo)
    {term : Term} {edge : Nat}
    (replayed : replayCircuit snapshot maxInt term = some edge) :
    evalEdge assignment edge = term.eval (edgeAssignment assignment) := by
  induction term generalizing edge with
  | constant value =>
      cases value <;> simp only [replayCircuit] at replayed <;>
        cases Option.some.inj replayed <;> rfl
  | input index =>
      cases Option.some.inj replayed
      rfl
  | binary op left right leftIH rightIH =>
      simp only [replayCircuit] at replayed
      cases leftRoot : replayCircuit snapshot maxInt left with
      | none => simp [leftRoot] at replayed
      | some x =>
          cases rightRoot : replayCircuit snapshot maxInt right with
          | none => simp [leftRoot, rightRoot] at replayed
          | some y =>
              simp only [leftRoot, rightRoot] at replayed
              rw [replayApply_sound sound replayed, leftIH leftRoot, rightIH rightRoot]
              rfl
  | complement term ih =>
      simp only [replayCircuit] at replayed
      cases root : replayCircuit snapshot maxInt term with
      | none => simp [root] at replayed
      | some value =>
          simp only [root, Option.map_some, Option.some.injEq] at replayed
          subst edge
          rw [evalEdge_flip, ih root]
          rfl
  | ite condition thenValue elseValue conditionIH thenIH elseIH =>
      simp only [replayCircuit] at replayed
      cases conditionRoot : replayCircuit snapshot maxInt condition with
      | none => simp [conditionRoot] at replayed
      | some c =>
          cases thenRoot : replayCircuit snapshot maxInt thenValue with
          | none => simp [conditionRoot, thenRoot] at replayed
          | some t =>
              cases elseRoot : replayCircuit snapshot maxInt elseValue with
              | none => simp [conditionRoot, thenRoot, elseRoot] at replayed
              | some e =>
                  simp only [conditionRoot, thenRoot, elseRoot] at replayed
                  rw [replayIte_sound sound replayed, conditionIH conditionRoot,
                    thenIH thenRoot, elseIH elseRoot]
                  rfl

abbrev Bits := Nat → Term

/-- Only in-range bits are observed; every use-width adaptation explicitly
supplies zeros beyond the child's width. -/
def Meaning {width : Nat} (assignment : Assignment) (bits : Bits)
    (value : BitVec width) : Prop :=
  ∀ bit, bit < width → (bits bit).eval assignment = value.getLsbD bit

def adapt (fromWidth toWidth : Nat) (bits : Bits) : Bits := fun bit =>
  if bit < toWidth ∧ bit < fromWidth then bits bit else .constant false

theorem adapt_meaning {fromWidth : Nat} (toWidth : Nat)
    {assignment : Assignment} {bits : Bits} {value : BitVec fromWidth}
    (meaning : Meaning assignment bits value) :
    Meaning assignment (adapt fromWidth toWidth bits) (value.setWidth toWidth) := by
  intro bit within
  by_cases source : bit < fromWidth
  · simp [adapt, within, source, meaning bit source]
  · simp [adapt, within, source, BitVec.getLsbD_of_ge value bit (Nat.le_of_not_gt source), Term.eval]

/-- Composition keeps the original modulus. In particular, a narrow sum is
formed at its own width before the result is widened. -/
theorem adapt_twice_meaning {sourceWidth : Nat} (middleWidth useWidth : Nat)
    {assignment : Assignment} {bits : Bits} {value : BitVec sourceWidth}
    (meaning : Meaning assignment bits value) :
    Meaning assignment
      (adapt middleWidth useWidth (adapt sourceWidth middleWidth bits))
      ((value.setWidth middleWidth).setWidth useWidth) :=
  adapt_meaning useWidth (adapt_meaning middleWidth meaning)

def complementBits (bits : Bits) : Bits := fun bit => .complement (bits bit)

theorem complementBits_meaning {width : Nat} {assignment : Assignment}
    {bits : Bits} {value : BitVec width} (meaning : Meaning assignment bits value) :
    Meaning assignment (complementBits bits) (~~~value) := by
  intro bit within
  simp [complementBits, Term.eval, meaning bit within, within]

def carryTerm (left right : Bits) (initial : Term) : Nat → Term
  | 0 => initial
  | bit + 1 => .binary 1 (.binary 0 (left bit) (right bit))
      (.binary 0 (carryTerm left right initial bit) (.binary 2 (left bit) (right bit)))

def sumTerm (left right : Bits) (initial : Term) : Bits := fun bit =>
  .binary 2 (.binary 2 (left bit) (right bit)) (carryTerm left right initial bit)

theorem carryTerm_meaning {width : Nat} {assignment : Assignment}
    {left right : Bits} {a b : BitVec width} {initial : Term} {carry : Bool}
    (leftMeaning : Meaning assignment left a) (rightMeaning : Meaning assignment right b)
    (initialMeaning : initial.eval assignment = carry) (bit : Nat) (within : bit ≤ width) :
    (carryTerm left right initial bit).eval assignment = rippleCarry a b carry bit := by
  induction bit with
  | zero => exact initialMeaning
  | succ bit ih =>
      have before : bit < width := by omega
      simp only [carryTerm, Term.eval, binaryValue, rippleCarry]
      rw [leftMeaning bit before, rightMeaning bit before, ih (by omega)]

theorem sumTerm_meaning {width : Nat} {assignment : Assignment}
    {left right : Bits} {a b : BitVec width} {initial : Term} {carry : Bool}
    (leftMeaning : Meaning assignment left a) (rightMeaning : Meaning assignment right b)
    (initialMeaning : initial.eval assignment = carry) (bit : Nat) (within : bit < width) :
    (sumTerm left right initial bit).eval assignment = rippleSum a b carry bit := by
  simp only [sumTerm, Term.eval, binaryValue, rippleSum]
  rw [leftMeaning bit within, rightMeaning bit within,
    carryTerm_meaning leftMeaning rightMeaning initialMeaning bit (by omega)]

theorem add_meaning {width : Nat} {assignment : Assignment}
    {left right : Bits} {a b : BitVec width}
    (leftMeaning : Meaning assignment left a) (rightMeaning : Meaning assignment right b) :
    Meaning assignment (sumTerm left right (.constant false)) (a + b) := by
  intro bit within
  exact (sumTerm_meaning leftMeaning rightMeaning rfl bit within).trans
    (rippleSum_eq_add a b bit within)

theorem sub_meaning {width : Nat} {assignment : Assignment}
    {left right : Bits} {a b : BitVec width}
    (leftMeaning : Meaning assignment left a) (rightMeaning : Meaning assignment right b) :
    Meaning assignment (sumTerm left (complementBits right) (.constant true)) (a - b) := by
  intro bit within
  exact (sumTerm_meaning leftMeaning (complementBits_meaning rightMeaning) rfl bit within).trans
    (rippleSum_eq_sub a b bit within)

/-- The no-borrow result is the full-width complement-chain carry. -/
theorem hs_meaning {width : Nat} {assignment : Assignment}
    {left right : Bits} {a b : BitVec width}
    (leftMeaning : Meaning assignment left a) (rightMeaning : Meaning assignment right b) :
    (carryTerm left (complementBits right) (.constant true) width).eval assignment =
      condHolds .hs a b := by
  exact (carryTerm_meaning (carry := true) leftMeaning
    (complementBits_meaning rightMeaning) rfl width (by omega)).trans
      ((rippleCarry_eq_carry a (~~~b) true width).trans (c_eq_carry a b).symm)

theorem lo_meaning {width : Nat} {assignment : Assignment}
    {left right : Bits} {a b : BitVec width}
    (leftMeaning : Meaning assignment left a) (rightMeaning : Meaning assignment right b) :
    (Term.complement (carryTerm left (complementBits right) (.constant true) width)).eval assignment =
      condHolds .lo a b := by
  simp only [Term.eval, hs_meaning leftMeaning rightMeaning]
  rfl

theorem hs_true_iff {width : Nat} {assignment : Assignment}
    {left right : Bits} {a b : BitVec width}
    (leftMeaning : Meaning assignment left a) (rightMeaning : Meaning assignment right b) :
    (carryTerm left (complementBits right) (.constant true) width).eval assignment = true ↔
      b.toNat ≤ a.toNat := by
  rw [hs_meaning leftMeaning rightMeaning, hs_holds_iff]

theorem lo_true_iff {width : Nat} {assignment : Assignment}
    {left right : Bits} {a b : BitVec width}
    (leftMeaning : Meaning assignment left a) (rightMeaning : Meaning assignment right b) :
    (Term.complement (carryTerm left (complementBits right) (.constant true) width)).eval assignment = true ↔
      a.ult b := by
  rw [lo_meaning leftMeaning rightMeaning, lo_holds_iff]

/-- Exact most-significant-to-least-significant fold, with the prior
conjunction on the left as in the production equality loop. -/
def equalFrom (left right : Bits) : Nat → Term → Term
  | 0, prior => prior
  | count + 1, prior => equalFrom left right count
      (.binary 0 prior (.complement (.binary 2 (left count) (right count))))

private theorem and_not_xor_true (prior left right : Bool) :
    (prior && !(xor left right)) = true ↔ prior = true ∧ left = right := by
  cases prior <;> cases left <;> cases right <;> decide

theorem equalFrom_true_iff (assignment : Assignment) (left right : Bits)
    (count : Nat) (prior : Term) :
    (equalFrom left right count prior).eval assignment = true ↔
      prior.eval assignment = true ∧
        ∀ bit, bit < count → (left bit).eval assignment = (right bit).eval assignment := by
  induction count generalizing prior with
  | zero => simp [equalFrom]
  | succ count ih =>
      rw [equalFrom, ih]
      simp only [Term.eval, binaryValue, and_not_xor_true]
      constructor
      · rintro ⟨⟨priorTrue, lastEqual⟩, restEqual⟩
        refine ⟨priorTrue, ?_⟩
        intro bit within
        by_cases last : bit = count
        · simpa [last] using lastEqual
        · exact restEqual bit (by omega)
      · rintro ⟨priorTrue, allEqual⟩
        exact ⟨⟨priorTrue, allEqual count (by omega)⟩,
          fun bit within => allEqual bit (by omega)⟩

theorem eq_meaning {width : Nat} {assignment : Assignment}
    {left right : Bits} {a b : BitVec width}
    (leftMeaning : Meaning assignment left a) (rightMeaning : Meaning assignment right b) :
    (equalFrom left right width (.constant true)).eval assignment = true ↔ a = b := by
  rw [equalFrom_true_iff]
  simp only [Term.eval, true_and]
  constructor
  · intro equalBits
    apply BitVec.eq_of_getLsbD_eq
    intro bit within
    exact (leftMeaning bit within).symm.trans ((equalBits bit within).trans (rightMeaning bit within))
  · intro equal bit within
    rw [leftMeaning bit within, rightMeaning bit within, equal]

theorem ne_meaning {width : Nat} {assignment : Assignment}
    {left right : Bits} {a b : BitVec width}
    (leftMeaning : Meaning assignment left a) (rightMeaning : Meaning assignment right b) :
    (Term.complement (equalFrom left right width (.constant true))).eval assignment = true ↔ a ≠ b := by
  simp only [Term.eval, Bool.not_eq_true']
  have h := eq_meaning leftMeaning rightMeaning
  cases value : (equalFrom left right width (.constant true)).eval assignment <;> simp_all

/-- Comparisons and Boolean-declared views carry one truth bit and zero high
bits, even when their use width is 32 or 64. -/
def boolBits (truth : Term) : Bits := fun bit =>
  if bit = 0 then truth else .constant false

def boolWord (width : Nat) (truth : Bool) : BitVec width :=
  (BitVec.ofBool truth).setWidth width

theorem boolBits_meaning (width : Nat) (assignment : Assignment) (truth : Term) :
    Meaning assignment (boolBits truth) (boolWord width (truth.eval assignment)) := by
  intro bit within
  by_cases zero : bit = 0
  · subst bit
    simp [boolBits, boolWord, BitVec.getLsbD_ofBool, within]
  · simp [boolBits, boolWord, BitVec.getLsbD_ofBool, within, zero, Term.eval]

theorem boolWord_range (width : Nat) (truth : Bool) :
    (boolWord width truth).toNat = 0 ∨ (boolWord width truth).toNat = 1 := by
  cases width with
  | zero => simp [boolWord, Nat.mod_one]
  | succ width => cases truth <;> simp [boolWord]

theorem boolWord_guard (width : Nat) (positive : 0 < width) (truth : Bool) :
    ((boolWord width truth).toNat != 0) = truth := by
  cases truth <;>
    simp [boolWord, BitVec.toNat_setWidth_of_le (by omega : 1 ≤ width)]

def muxBits (condition : Term) (left right : Bits) : Bits := fun bit =>
  .ite condition (left bit) (right bit)

theorem muxBits_meaning {width : Nat} {assignment : Assignment}
    {condition : Term} {left right : Bits} {a b : BitVec width}
    (leftMeaning : Meaning assignment left a) (rightMeaning : Meaning assignment right b) :
    Meaning assignment (muxBits condition left right)
      (if condition.eval assignment then a else b) := by
  intro bit within
  cases h : condition.eval assignment <;>
    simp [muxBits, Term.eval, h, leftMeaning bit within, rightMeaning bit within]

/-- Zero-filled constant shift of a finite word. -/
def shiftBits (width : Nat) (left : Bool) (amount : Nat) (bits : Bits) : Bits := fun bit =>
  if left then
    if amount ≤ bit then bits (bit - amount) else .constant false
  else
    if bit + amount < width then bits (bit + amount) else .constant false

def shiftValue {width : Nat} (left : Bool) (value : BitVec width) (amount : Nat) : BitVec width :=
  if left then value <<< amount else value >>> amount

theorem shiftBits_meaning {width : Nat} {assignment : Assignment}
    {bits : Bits} {value : BitVec width} (meaning : Meaning assignment bits value)
    (left : Bool) (amount : Nat) :
    Meaning assignment (shiftBits width left amount bits) (shiftValue left value amount) := by
  intro bit within
  cases left with
  | false =>
      change (if bit + amount < width then bits (bit + amount) else Term.constant false).eval assignment =
        (value >>> amount).getLsbD bit
      rw [BitVec.getLsbD_ushiftRight, Nat.add_comm amount bit]
      by_cases source : bit + amount < width
      · simp only [source, if_true]
        exact meaning (bit + amount) source
      · simp only [source, if_false, Term.eval]
        exact (BitVec.getLsbD_of_ge value (bit + amount) (Nat.le_of_not_gt source)).symm
  | true =>
      change (if amount ≤ bit then bits (bit - amount) else Term.constant false).eval assignment =
        (value <<< amount).getLsbD bit
      rw [BitVec.getLsbD_shiftLeft]
      by_cases source : amount ≤ bit
      · simp only [source, if_true, within, Nat.not_lt_of_ge source,
          decide_true, decide_false, Bool.not_false, Bool.true_and]
        exact meaning (bit - amount) (by omega)
      · simp only [source, if_false, Term.eval, within, Nat.lt_of_not_ge source,
          decide_true, Bool.not_true, Bool.true_and, Bool.false_and]

def lowCount {width : Nat} (count : BitVec width) : Nat → Nat
  | 0 => 0
  | stages + 1 => lowCount count stages + if count.getLsbD stages then 2 ^ stages else 0

theorem lowCount_eq_mod {width : Nat} (count : BitVec width) (stages : Nat) :
    lowCount count stages = count.toNat % 2 ^ stages := by
  have resized : lowCount count stages = (count.setWidth stages).toNat := by
    induction stages with
    | zero => simp only [lowCount, BitVec.toNat_setWidth, Nat.pow_zero, Nat.mod_one]
    | succ stages ih =>
        rw [lowCount, ih, BitVec.setWidth_succ, BitVec.toNat_cons']
        cases count.getLsbD stages <;> simp [Nat.shiftLeft_eq, Nat.add_comm]
  simpa using resized

/-- The production shifter visits count bits from low to high. -/
def barrelBits (width : Nat) (left : Bool) (value count : Bits) : Nat → Bits
  | 0 => value
  | stages + 1 =>
      let prior := barrelBits width left value count stages
      muxBits (count stages) (shiftBits width left (2 ^ stages) prior) prior

private theorem shiftValue_add {width : Nat} (left : Bool) (value : BitVec width)
    (first second : Nat) :
    shiftValue left (shiftValue left value first) second =
      shiftValue left value (first + second) := by
  cases left <;> simp [shiftValue, BitVec.shiftLeft_add, BitVec.shiftRight_add]

theorem barrelBits_meaning {width countWidth : Nat} {assignment : Assignment}
    {value count : Bits} {a : BitVec width} {b : BitVec countWidth}
    (valueMeaning : Meaning assignment value a) (countMeaning : Meaning assignment count b)
    (left : Bool) (stages : Nat) (within : stages ≤ countWidth) :
    Meaning assignment (barrelBits width left value count stages)
      (shiftValue left a (b.toNat % 2 ^ stages)) := by
  rw [← lowCount_eq_mod]
  induction stages with
  | zero => simpa [barrelBits, lowCount, shiftValue] using valueMeaning
  | succ stages ih =>
      have countWithin : stages < countWidth := by omega
      have prior := ih (by omega)
      have mux := muxBits_meaning (condition := count stages)
        (shiftBits_meaning prior left (2 ^ stages)) prior
      rw [countMeaning stages countWithin] at mux
      cases bit : b.getLsbD stages <;>
        simpa [barrelBits, lowCount, bit, shiftValue_add] using mux

/-- Exactly five stages implement a 32-bit modulo count. -/
theorem barrel32_meaning {assignment : Assignment} {value count : Bits}
    {a b : BitVec 32}
    (valueMeaning : Meaning assignment value a) (countMeaning : Meaning assignment count b)
    (left : Bool) :
    Meaning assignment (barrelBits 32 left value count 5)
      (shiftValue left a (b.toNat % 32)) := by
  simpa using barrelBits_meaning valueMeaning countMeaning left 5 (by decide)

/-- Exactly six stages implement a 64-bit modulo count. -/
theorem barrel64_meaning {assignment : Assignment} {value count : Bits}
    {a b : BitVec 64}
    (valueMeaning : Meaning assignment value a) (countMeaning : Meaning assignment count b)
    (left : Bool) :
    Meaning assignment (barrelBits 64 left value count 6)
      (shiftValue left a (b.toNat % 64)) := by
  simpa using barrelBits_meaning valueMeaning countMeaning left 6 (by decide)

end Oak.CNFTypedCircuit
