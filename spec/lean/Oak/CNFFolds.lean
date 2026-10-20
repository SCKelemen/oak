import Oak.CNFGates

/-!
The production CNF builder's folds, extracted with cnf_apply and cnf_ite.
Values include the two constant edges. Returning from a fold preserves memory;
remaining binary operands are regular, and mux arm reductions preserve meaning.
Allocation/freshness, whole-circuit composition and the final obligation remain
separate obligations. These proofs do not certify the extractor or compiler.
-/
set_option autoImplicit false
namespace Oak.CNFFolds
open Oak.CNFEmission Oak.CNFGates

/-- Node zero is the false terminal; its complement is true. -/
def value (a : Oak.RupCheck.Assignment) (e : UInt32) : Bool :=
  if e == 0 then false else if e == 1 then true else Oak.CNFLiteral.edgeValue a e

@[simp] theorem value_false (a : Oak.RupCheck.Assignment) : value a 0 = false := rfl
@[simp] theorem value_true (a : Oak.RupCheck.Assignment) : value a 1 = true := rfl

theorem value_flip (a : Oak.RupCheck.Assignment) (e : UInt32) :
    value a (e ^^^ 1) = !value a e := by
  by_cases h0 : e = 0
  · subst e; rfl
  by_cases h1 : e = 1
  · subst e; rfl
  have f0 : e ^^^ 1 ≠ 0 := by simpa using h1
  have f1 : e ^^^ 1 ≠ 1 := by
    intro h
    have hh := congrArg (fun x : UInt32 => x ^^^ 1) h
    simp [UInt32.xor_assoc] at hh
    exact h0 hh
  simp [value, h0, h1, f0, f1, flip_value]

theorem value_regular (a : Oak.RupCheck.Assignment) (e : UInt32) (h : Regular e) :
    value a e = Oak.CNFLiteral.edgeValue a e := by
  have h0 : e ≠ 0 := by intro he; subst e; have := h.1; contradiction
  have h1 : e ≠ 1 := by intro he; subst e; have := h.1; contradiction
  simp [value, h0, h1]

/-- The exact production folder preserves AND/OR/XOR semantics whenever it
returns an edge rather than the no-fold sentinel. Other op codes follow the
production XOR fallback; valid operation selection is a caller obligation. -/
theorem terminal_sound (a : Oak.RupCheck.Assignment) (op x y result : UInt32) (fuel : Nat)
    (run : terminal_case op x y fuel = some result) (folded : result ≠ NONE) :
    value a result = binaryValue op (value a x) (value a y) := by
  simp only [terminal_case, Option.pure_def, Option.some.injEq] at run
  repeat' split at run
  all_goals subst result
  all_goals simp_all [binaryValue, BDD_FALSE, BDD_TRUE, OP_AND, OP_OR, value_flip]
  all_goals grind [value_false, value_true, value_flip]

/-- Successful folding in cnf_apply performs no allocation and no writes. -/
theorem apply_folded (l : Layout) (mem : Array UInt32) (op x y result : UInt32) (fuel : Nat)
    (run : terminal_case op x y fuel = some result) (folded : result ≠ NONE) :
    cnf_apply l mem op x y fuel = some (result, mem) := by
  simp [cnf_apply, run, folded]

/-- Exclude the sentinel node, but permit both constants. -/
def Valid (e : UInt32) : Prop := e < 4294967294

theorem regular_of_valid (e : UInt32) (h : Valid e) (h0 : e ≠ 0) (h1 : e ≠ 1) :
    Regular e := by
  constructor
  · have n0 : e.toNat ≠ (0 : UInt32).toNat := fun hn => h0 (UInt32.toNat_inj.mp hn)
    have n1 : e.toNat ≠ (1 : UInt32).toNat := fun hn => h1 (UInt32.toNat_inj.mp hn)
    change e.toNat ≠ 0 at n0
    change e.toNat ≠ 1 at n1
    apply UInt32.le_iff_toNat_le.mpr
    change 2 ≤ e.toNat
    omega
  · exact h

theorem valid_flip (e : UInt32) (h : Valid e) : Valid (e ^^^ 1) := by
  by_cases h0 : e = 0
  · subst e; unfold Valid; decide +kernel
  by_cases h1 : e = 1
  · subst e; unfold Valid; decide +kernel
  exact (regular_flip e (regular_of_valid e h h0 h1)).2

theorem terminal_valid (op x y result : UInt32) (fuel : Nat)
    (hx : Valid x) (hy : Valid y)
    (run : terminal_case op x y fuel = some result) (folded : result ≠ NONE) :
    Valid result := by
  have xf := valid_flip x hx
  have yf := valid_flip y hy
  have zero : Valid 0 := by unfold Valid; decide +kernel
  have one : Valid 1 := by unfold Valid; decide +kernel
  simp only [terminal_case, Option.pure_def, Option.some.injEq] at run
  repeat' split at run
  all_goals subst result
  all_goals simp_all [BDD_FALSE, BDD_TRUE]

theorem terminal_residual (op x y : UInt32) (fuel : Nat)
    (hx : Valid x) (hy : Valid y)
    (run : terminal_case op x y fuel = some NONE) :
    Regular x ∧ Regular y ∧ x ≠ y ∧ x ≠ y ^^^ 1 := by
  have xf : x ^^^ 1 ≠ NONE := by
    intro he
    have hh := congrArg (fun z : UInt32 => z ^^^ 1) he
    have : x = 4294967294 := by
      have one : NONE ^^^ (1 : UInt32) = 4294967294 := by decide +kernel
      simpa only [UInt32.xor_assoc, UInt32.xor_self, UInt32.xor_zero, one] using hh
    subst x
    exact (by unfold Valid; decide +kernel : ¬ Valid 4294967294) hx
  have yf : y ^^^ 1 ≠ NONE := by
    intro he
    have hh := congrArg (fun z : UInt32 => z ^^^ 1) he
    have : y = 4294967294 := by
      have one : NONE ^^^ (1 : UInt32) = 4294967294 := by decide +kernel
      simpa only [UInt32.xor_assoc, UInt32.xor_self, UInt32.xor_zero, one] using hh
    subst y
    exact (by unfold Valid; decide +kernel : ¬ Valid 4294967294) hy
  simp only [terminal_case, Option.pure_def, Option.some.injEq] at run
  repeat' split at run
  all_goals simp_all [BDD_FALSE, BDD_TRUE]
  all_goals simp_all [Valid, Regular, NONE,
    UInt32.lt_iff_toNat_lt, UInt32.le_iff_toNat_le, ← UInt32.toNat_inj]
  all_goals omega

/-- The five direct-result mux folds, in production order. -/
def simple (c t e : UInt32) : Option UInt32 :=
  if c == 1 then some t else if c == 0 then some e else if t == e then some t
  else if t == 1 && e == 0 then some c
  else if t == 0 && e == 1 then some (c ^^^ 1) else none

theorem simple_execution (l : Layout) (mem : Array UInt32) (c t e result : UInt32) (fuel : Nat)
    (h : simple c t e = some result) : cnf_ite l mem c t e fuel = some (result, mem) := by
  unfold simple at h
  repeat' split at h
  all_goals simp_all [cnf_ite, BDD_FALSE, BDD_TRUE]

theorem simple_sound (a : Oak.RupCheck.Assignment) (c t e result : UInt32)
    (h : simple c t e = some result) :
    value a result = (if value a c then value a t else value a e) := by
  unfold simple at h
  repeat' split at h
  all_goals try simp only [Option.some.injEq] at h
  all_goals try subst result
  all_goals simp_all [value_flip]
  all_goals grind [value_false, value_true]

/-- The remaining four constant-arm mux folds become binary gates. -/
def reduction (c t e : UInt32) : Option (UInt32 × UInt32 × UInt32) :=
  if t == 1 then some (OP_OR, c, e)
  else if t == 0 then some (OP_AND, c ^^^ 1, e)
  else if e == 1 then some (OP_OR, c ^^^ 1, t)
  else if e == 0 then some (OP_AND, c, t) else none

theorem reduction_execution (l : Layout) (mem : Array UInt32)
    (c t e op x y : UInt32) (fuel : Nat)
    (hs : simple c t e = none) (hr : reduction c t e = some (op, x, y)) :
    cnf_ite l mem c t e fuel = cnf_apply l mem op x y fuel := by
  simp only [simple] at hs
  repeat' split at hs
  all_goals simp_all only [Option.some_ne_none]
  unfold reduction at hr
  repeat' split at hr
  all_goals simp_all [cnf_ite, BDD_FALSE, BDD_TRUE]
  all_goals cases cnf_apply l mem op x y fuel <;> rfl

theorem reduction_sound (a : Oak.RupCheck.Assignment) (c t e op x y : UInt32)
    (hr : reduction c t e = some (op, x, y)) :
    binaryValue op (value a x) (value a y) =
      (if value a c then value a t else value a e) := by
  unfold reduction at hr
  repeat' split at hr
  all_goals try simp only [Option.some.injEq, Prod.mk.injEq] at hr
  all_goals first | contradiction | obtain ⟨rfl, rfl, rfl⟩ := hr
  all_goals simp_all [binaryValue, OP_AND, OP_OR, value_flip]
  all_goals cases value a c <;> simp_all

/-- Direct mux folds also preserve the non-sentinel edge range. -/
theorem simple_valid (c t e result : UInt32) (hc : Valid c) (ht : Valid t) (he : Valid e)
    (h : simple c t e = some result) : Valid result := by
  have cf := valid_flip c hc
  unfold simple at h
  repeat' split at h
  all_goals simp_all

/-- Constant-arm reduction supplies regular operands to the binary builder. -/
theorem reduction_regular (c t e op x y : UInt32)
    (hc : Valid c) (ht : Valid t) (he : Valid e)
    (hs : simple c t e = none) (hr : reduction c t e = some (op, x, y)) :
    Regular x ∧ Regular y := by
  have c0 : c ≠ 0 := by intro h; subst c; simp [simple] at hs
  have c1 : c ≠ 1 := by intro h; subst c; simp [simple] at hs
  have cr := regular_of_valid c hc c0 c1
  have cf := regular_flip c cr
  unfold reduction at hr
  repeat' split at hr
  all_goals try simp only [Option.some.injEq, Prod.mk.injEq] at hr
  all_goals first | contradiction | obtain ⟨rfl, rfl, rfl⟩ := hr
  all_goals simp_all [simple]
  all_goals apply regular_of_valid
  all_goals first | assumption | (intro hz; subst_vars; simp_all)

/-- If no direct fold or constant-arm reduction applies, every mux input
is suitable for the stored-gate theorem. -/
theorem mux_residual (c t e : UInt32) (hc : Valid c) (ht : Valid t) (he : Valid e)
    (hs : simple c t e = none) (hr : reduction c t e = none) :
    Regular c ∧ Regular t ∧ Regular e ∧ t ≠ e := by
  simp only [simple] at hs
  repeat' split at hs
  all_goals simp_all only [Option.some_ne_none]
  simp only [reduction] at hr
  repeat' split at hr
  all_goals simp_all [Regular, Valid, UInt32.lt_iff_toNat_lt,
    UInt32.le_iff_toNat_le, ← UInt32.toNat_inj]
  all_goals omega

/-- Sorting binary inputs for the unique-table key preserves their meaning. -/
theorem sorted_value (a : Oak.RupCheck.Assignment) (op x y : UInt32) :
    binaryValue op (value a (if x > y then y else x))
      (value a (if x > y then x else y)) = binaryValue op (value a x) (value a y) := by
  split <;> simp [binaryValue]
  all_goals split <;> (try split) <;> cases value a x <;> cases value a y <;> rfl

end Oak.CNFFolds
