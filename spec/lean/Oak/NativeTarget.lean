/-!
Closed native target selection. This models the shared Go dispatch contract,
not instruction semantics or a source-to-image refinement theorem.
-/
namespace Oak.NativeTarget

inductive Lane where
  | arm64 | rv64
  deriving DecidableEq

def resolve (arch : String) : Option Lane :=
  if arch == "arm64" then some .arm64
  else if arch == "rv64" then some .rv64 else none

theorem unknown_refused (arch : String) (ha : arch ≠ "arm64") (hr : arch ≠ "rv64") :
    resolve arch = none := by simp [resolve, ha, hr]

theorem empty_refused : resolve "" = none := by decide

def acceptsRelocation (lane : Option Lane) (kind : String) : Bool :=
  match lane with
  | none => false
  | some .arm64 => ["call26", "jump26", "branch26", "condbr19", "tbz14",
      "adr21", "adrp21", "lo12", "adrl21"].contains kind
  | some .rv64 => ["riscv_call_plt", "riscv_pcrel"].contains kind

theorem invalid_refuses_relocation (kind : String) :
    acceptsRelocation none kind = false := rfl

theorem relocation_ownership_disjoint (kind : String) :
    acceptsRelocation (some .arm64) kind = true →
    acceptsRelocation (some .rv64) kind = false := by
  intro h
  simp only [acceptsRelocation, List.contains_cons, List.contains_nil,
    Bool.or_eq_true, beq_iff_eq, Bool.false_eq_true, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h <;> subst kind <;> decide

end Oak.NativeTarget
