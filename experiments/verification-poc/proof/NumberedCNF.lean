import BooleanCNF
import RUPExecutable

/-! Executable finite numbering and the Boolean-expression-to-RUP bridge.
The allocator is deliberately independent of Go's optimized circuit allocator. -/
set_option autoImplicit false
namespace OakVerification.NumberedCNF
open BooleanCNF

def locate (atom : Atom) : List Atom → Nat
  | [] => 0
  | first :: rest => if atom = first then 0 else locate atom rest + 1

def lookup : List Atom → Nat → Option Atom
  | [], _ => none
  | first :: _, 0 => some first
  | _ :: rest, n + 1 => lookup rest n

theorem lookup_locate (table : List Atom) (atom : Atom) (member : atom ∈ table) :
    lookup table (locate atom table) = some atom := by
  induction table with
  | nil => simp at member
  | cons first rest ih =>
    by_cases eq : atom = first
    · subst atom
      simp [locate, lookup]
    · have tail : atom ∈ rest := (List.mem_cons.mp member).resolve_left eq
      simpa [locate, eq, lookup] using ih tail

theorem locate_lt (table : List Atom) (atom : Atom) (member : atom ∈ table) :
    locate atom table < table.length := by
  induction table with
  | nil => simp at member
  | cons first rest ih =>
    by_cases eq : atom = first
    · simp [locate, eq]
    · have tail : atom ∈ rest := (List.mem_cons.mp member).resolve_left eq
      simpa [locate, eq] using Nat.succ_lt_succ (ih tail)

-- First occurrence wins. Duplicate slots are harmless unused DIMACS IDs;
-- keeping the table uncompressed makes the inverse and its bound transparent.
def atoms (f : CNF) : List Atom := f.flatMap (fun c => c.map Lit.atom)
def code (table : List Atom) (atom : Atom) : Nat := locate atom table + 1

def numberLiteral (table : List Atom) (l : Lit) : OakVerification.Literal :=
  ⟨code table l.atom, l.positive⟩
def numberCNF (table : List Atom) (f : CNF) : List OakVerification.Clause :=
  f.map (fun c => c.map (numberLiteral table))

def pull (table : List Atom) (a : OakVerification.Assignment) : BooleanCNF.Assignment :=
  fun atom => a (code table atom)
def lift (table : List Atom) (a : BooleanCNF.Assignment) : OakVerification.Assignment :=
  fun n => match lookup table (n - 1) with | some atom => a atom | none => false

theorem lift_code (table : List Atom) (a : BooleanCNF.Assignment) (atom : Atom)
    (member : atom ∈ table) : lift table a (code table atom) = a atom := by
  simp [lift, code, lookup_locate table atom member]

theorem atom_member (f : CNF) (c : BooleanCNF.Clause) (l : Lit)
    (hc : c ∈ f) (hl : l ∈ c) : l.atom ∈ atoms f := by
  exact List.mem_flatMap.mpr ⟨c, hc, List.mem_map.mpr ⟨l, hl, rfl⟩⟩

def numberedSat (a : OakVerification.Assignment) (f : List OakVerification.Clause) : Bool :=
  f.all (fun c => c.any (fun l => decide (Holds a l)))

theorem number_holds (table : List Atom) (a : OakVerification.Assignment) (l : Lit) :
    decide (Holds a (numberLiteral table l)) = holds (pull table a) l := by
  cases l with
  | mk atom positive =>
    cases positive <;> cases value : a (code table atom) <;>
      simp [Holds, numberLiteral, holds, pull, value]

theorem number_semantics (table : List Atom) (a : OakVerification.Assignment) (f : CNF) :
    numberedSat a (numberCNF table f) = cnfSat (pull table a) f := by
  simp [numberedSat, numberCNF, cnfSat, clauseSat, number_holds]

theorem literal_lift (table : List Atom) (a : BooleanCNF.Assignment) (l : Lit)
    (member : l.atom ∈ table) :
    Holds (lift table a) (numberLiteral table l) ↔ holds a l = true := by
  unfold Holds numberLiteral
  rw [lift_code table a l.atom member]
  cases positive : l.positive <;> cases value : a l.atom <;> simp [holds, positive, value]

private theorem get_member {α : Type} (xs : List α) (x : α) (n : Nat)
    (found : xs[n]? = some x) : x ∈ xs := by
  induction xs generalizing n with
  | nil => simp at found
  | cons first rest ih =>
    cases n with
    | zero =>
      have eq : first = x := by simpa using found
      subst x
      exact List.mem_cons_self
    | succ n => exact List.mem_cons_of_mem first (ih n (by simpa using found))

private theorem member_get {α : Type} (xs : List α) (x : α) (member : x ∈ xs) :
    ∃ n, xs[n]? = some x := by
  induction xs with
  | nil => simp at member
  | cons first rest ih =>
    rcases List.mem_cons.mp member with eq | tail
    · subst x
      exact ⟨0, rfl⟩
    · obtain ⟨n, found⟩ := ih tail
      exact ⟨n + 1, by simpa using found⟩

theorem models_iff (a : OakVerification.Assignment) (f : List OakVerification.Clause) :
    Models a (initialDatabase f) ↔ ∀ c ∈ f, SatisfiesClause a c := by
  constructor
  · intro model c member
    obtain ⟨n, found⟩ := member_get f c member
    exact model (n + 1) c (by simpa [initialDatabase] using found)
  · intro satisfied id c found
    by_cases zero : id = 0
    · simp [initialDatabase, zero] at found
    · exact satisfied c (get_member f c (id - 1) (by simpa [initialDatabase, zero] using found))

theorem numberedSat_models (a : OakVerification.Assignment) (f : List OakVerification.Clause) :
    numberedSat a f = true ↔ Models a (initialDatabase f) := by
  rw [models_iff]
  simp [numberedSat, SatisfiesClause]

theorem lift_models (f : CNF) (a : BooleanCNF.Assignment) (sat : cnfSat a f = true) :
    Models (lift (atoms f) a) (initialDatabase (numberCNF (atoms f) f)) := by
  apply (models_iff _ _).mpr
  intro target member
  obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp member
  have satisfied : ∀ c ∈ f, ∃ l ∈ c, holds a l = true := by
    simpa [cnfSat, clauseSat] using sat
  obtain ⟨l, literalMember, trueLiteral⟩ := satisfied source sourceMember
  refine ⟨numberLiteral (atoms f) l, List.mem_map.mpr ⟨l, literalMember, rfl⟩, ?_⟩
  exact (literal_lift (atoms f) a l (atom_member f source l sourceMember literalMember)).mpr trueLiteral

theorem numbering_iff (f : CNF) :
    (∃ a, cnfSat a f = true) ↔
    ∃ a, Models a (initialDatabase (numberCNF (atoms f) f)) := by
  constructor
  · rintro ⟨a, sat⟩
    exact ⟨lift (atoms f) a, lift_models f a sat⟩
  · rintro ⟨a, model⟩
    refine ⟨pull (atoms f) a, ?_⟩
    rw [← number_semantics]
    exact (numberedSat_models a _).mpr model

theorem numbered_bounds (f : CNF) (c : OakVerification.Clause) (l : OakVerification.Literal)
    (hc : c ∈ numberCNF (atoms f) f) (hl : l ∈ c) :
    0 < l.index ∧ l.index ≤ (atoms f).length := by
  obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp hc
  obtain ⟨original, literalMember, rfl⟩ := List.mem_map.mp hl
  constructor
  · simp [numberLiteral, code]
  · have bound := locate_lt (atoms f) original.atom (atom_member f source original sourceMember literalMember)
    simpa [numberLiteral, code] using Nat.succ_le_of_lt bound

def checkEncoded (e : Expr) (commands : List Instruction) : Bool :=
  let f := encode e
  checkProof (atoms f).length (numberCNF (atoms f) f) commands

theorem checkEncoded_sound (e : Expr) (commands : List Instruction)
    (accepted : checkEncoded e commands = true) : ∀ input, eval input e = false := by
  have unsat := checkProof_sound (variables := (atoms (encode e)).length)
    (clauses := numberCNF (atoms (encode e)) (encode e)) (commands := commands) accepted
  intro input
  cases value : eval input e with
  | false => rfl
  | true =>
    exact False.elim (unsat _ (lift_models (encode e) (canonical input) (encode_complete input e value)))

def checkValid (e : Expr) (commands : List Instruction) : Bool := checkEncoded (.neg e) commands

theorem checkValid_sound (e : Expr) (commands : List Instruction)
    (accepted : checkValid e commands = true) : ∀ input, eval input e = true := by
  intro input
  have negated := checkEncoded_sound (.neg e) commands accepted input
  cases value : eval input e with
  | false => simp [eval, value] at negated
  | true => rfl

#print axioms numbering_iff
#print axioms numbered_bounds
#print axioms checkEncoded_sound
#print axioms checkValid_sound
end OakVerification.NumberedCNF
