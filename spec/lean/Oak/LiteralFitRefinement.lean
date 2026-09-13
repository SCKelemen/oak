import Oak.Target

/-! # Compiler correspondence for integer literal ranges

`docs/spec/25-type-inference.md` §3a: an integer literal has no type of its
own; it takes the integer type its context requires, and the checker reports
an error at the literal when the value does not fit that type — never a
silent fallback. `20-types.md` §11 gives each type its range: the fixed
widths `u8..u64`, `u128`, `i8..i64` exactly, and the machine-sized `int`,
`uint`, `ptr`, `uptr` at the widths the target's data model supplies
(`Oak.Target.dataModel`; `NewWithPlatformSizes` configures the checker).

The checker decides the fit in `typechecker.literalFitsInType` (an `int64`
value against a type name) and `typechecker.literalFits` (a parsed literal,
which above `2^63 - 1` is *wide* — `IntegerLiteral.Wide`, the value carried
as its `int64` bit pattern, `parser.parseIntegerLiteral`). This module
transliterates both line for line over `Int` and proves the decision equal
to membership in the type's range: for every encoding the parser produces,
`literalFits` accepts exactly the literals whose denotation the type
represents (`fits_iff_represents`, and `fits_iff_represents_target` for the
data model of every supported target). The negated-literal rule
(`checkPrefixExpression` range-checks `-value`) is the same decision on the
negated value (`neg_fits_iff`); the one representable value it cannot spell
— `-2^63`, whose magnitude is wide — is named exactly (`min_int64_lost`).

Transliterating exposed a defect: the machine-sized types accepted every
`int64` (`int`, `ptr`) or every non-negative one (`uint`, `uptr`) whatever
the configured width, so an ILP32 build admitted `x: uint = 5000000000`.
The Go now resolves them through the data model (`machineSizedName`), as
`resolve` does here. `typechecker/literal_fit_refinement_test.go` pins the
Go decision to this module's table at every range boundary, under each data
model the checker can be configured with. -/

namespace Oak.LiteralFitRefinement

open Oak.Target (DataModel Target dataModel)

/-- The integer type names the decision ranges over: the fixed widths, the
machine-sized four, and the two aliases. -/
inductive IntType
  | u8 | u16 | u32 | u64 | u128 | i8 | i16 | i32 | i64
  | int | uint | ptr | uptr
  | byte | rune
  deriving DecidableEq, Repr

/-- A data model the checker can be configured with: `int`/`uint` and
`ptr`/`uptr` each 32 or 64 bits. -/
def WellFormed (p : DataModel) : Prop :=
  (p.intBits = 32 ∨ p.intBits = 64) ∧ (p.ptrBits = 32 ∨ p.ptrBits = 64)

/-- Every supported target's data model qualifies (LP64 or ILP32). -/
theorem wellFormed_dataModel (t : Target) : WellFormed (dataModel t) := by
  rcases Oak.Target.dataModel_lp64_or_ilp32 t with h | h <;>
    simp [WellFormed, h, Oak.Target.lp64, Oak.Target.ilp32]

/-! ## The specification's ranges (`20-types.md` §11) -/

/-- The least value each type represents. -/
def lo (p : DataModel) : IntType → Int
  | .i8 => -(2 ^ 7)
  | .i16 => -(2 ^ 15)
  | .i32 => -(2 ^ 31)
  | .i64 => -(2 ^ 63)
  | .int => -(2 ^ (p.intBits - 1))
  | .ptr => -(2 ^ (p.ptrBits - 1))
  | _ => 0

/-- The greatest value each type represents. -/
def hi (p : DataModel) : IntType → Int
  | .u8 | .byte => 2 ^ 8 - 1
  | .u16 => 2 ^ 16 - 1
  | .u32 | .rune => 2 ^ 32 - 1
  | .u64 => 2 ^ 64 - 1
  | .u128 => 2 ^ 128 - 1
  | .i8 => 2 ^ 7 - 1
  | .i16 => 2 ^ 15 - 1
  | .i32 => 2 ^ 31 - 1
  | .i64 => 2 ^ 63 - 1
  | .int => 2 ^ (p.intBits - 1) - 1
  | .uint => 2 ^ p.intBits - 1
  | .ptr => 2 ^ (p.ptrBits - 1) - 1
  | .uptr => 2 ^ p.ptrBits - 1

/-- `n` is a value of type `t` under data model `p`. -/
def represents (p : DataModel) (t : IntType) (n : Int) : Prop := lo p t ≤ n ∧ n ≤ hi p t

instance (p : DataModel) (t : IntType) (n : Int) : Decidable (represents p t n) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-! ## The checker's decision, transliterated -/

/-- `machineSizedName`: the aliases and the machine-sized types resolve to
the fixed width of the data model (`tc.intSize == 32`, `tc.ptrSize == 32`);
every other name is itself. -/
def resolve (p : DataModel) : IntType → IntType
  | .byte => .u8
  | .rune => .u32
  | .int => if p.intBits = 32 then .i32 else .i64
  | .uint => if p.intBits = 32 then .u32 else .u64
  | .ptr => if p.ptrBits = 32 then .i32 else .i64
  | .uptr => if p.ptrBits = 32 then .u32 else .u64
  | t => t

/-- `literalFitsInType(value int64, typeName string) bool`: the switch over
the resolved name, case for case. -/
def literalFitsInType (p : DataModel) (value : Int) (t : IntType) : Bool :=
  match resolve p t with
  | .u8 => decide (value ≥ 0 ∧ value ≤ 255)
  | .u16 => decide (value ≥ 0 ∧ value ≤ 65535)
  | .u32 => decide (value ≥ 0 ∧ value ≤ 4294967295)
  | .u64 | .u128 => decide (value ≥ 0)
  | .i8 => decide (value ≥ -128 ∧ value ≤ 127)
  | .i16 => decide (value ≥ -32768 ∧ value ≤ 32767)
  | .i32 => decide (value ≥ -2147483648 ∧ value ≤ 2147483647)
  | .i64 => true
  | _ => false

/-- `literalFits(lit *ast.IntegerLiteral, typeName string) bool`: a wide
literal fits only the unsigned types of 64 bits or more; otherwise the
value decides. -/
def literalFits (p : DataModel) (wide : Bool) (value : Int) (t : IntType) : Bool :=
  if wide then
    match resolve p t with
    | .u64 | .u128 => true
    | _ => false
  else literalFitsInType p value t

/-! ## The parser's encoding -/

/-- What `(Wide, Value)` denotes: a wide literal carries an integer in
`[2^63, 2^64)` as its `int64` bit pattern. -/
def denotes (wide : Bool) (value : Int) : Int := if wide then value + 2 ^ 64 else value

/-- An encoding `parseIntegerLiteral` produces: `Value` is an `int64`, and
negative (the bit pattern of a value at or above `2^63`) when wide. -/
def Encoded (wide : Bool) (value : Int) : Prop :=
  -(2 ^ 63) ≤ value ∧ value ≤ 2 ^ 63 - 1 ∧ (wide = true → value < 0)

theorem denotes_wide_range (value : Int) (h : -(2 ^ 63) ≤ value ∧ value < 0) :
    2 ^ 63 ≤ denotes true value ∧ denotes true value ≤ 2 ^ 64 - 1 := by
  simp only [denotes, if_true]; omega

/-! ## Correspondence -/

/-- `literalFitsInType` accepts an `int64` exactly when the type represents it. -/
theorem fitsInType_iff (p : DataModel) (hp : WellFormed p) (v : Int)
    (hv : -(2 ^ 63) ≤ v ∧ v ≤ 2 ^ 63 - 1) (t : IntType) :
    literalFitsInType p v t = true ↔ represents p t v := by
  obtain ⟨hint | hint, hptr | hptr⟩ := hp <;> cases t <;>
    simp [literalFitsInType, resolve, represents, lo, hi, hint, hptr] <;> omega

/-- `literalFits` accepts a parsed literal exactly when the type represents
what it denotes — the specification's rule, for every encoding the parser
produces. -/
theorem fits_iff_represents (p : DataModel) (hp : WellFormed p) (wide : Bool) (value : Int)
    (he : Encoded wide value) (t : IntType) :
    literalFits p wide value t = true ↔ represents p t (denotes wide value) := by
  obtain ⟨hlo, hhi, hneg⟩ := he
  cases wide with
  | false => simpa [literalFits, denotes] using fitsInType_iff p hp value ⟨hlo, hhi⟩ t
  | true =>
    have hv : value < 0 := hneg rfl
    obtain ⟨hint | hint, hptr | hptr⟩ := hp <;> cases t <;>
      simp [literalFits, resolve, represents, lo, hi, denotes, hint, hptr] <;> omega

/-- The same, under the data model of any supported target. -/
theorem fits_iff_represents_target (tg : Target) (wide : Bool) (value : Int)
    (he : Encoded wide value) (t : IntType) :
    literalFits (dataModel tg) wide value t = true ↔
      represents (dataModel tg) t (denotes wide value) :=
  fits_iff_represents (dataModel tg) (wellFormed_dataModel tg) wide value he t

/-- The negated-literal rule: `checkPrefixExpression` range-checks the
negation of a non-wide magnitude, which is the same decision on `-m`. -/
theorem neg_fits_iff (p : DataModel) (hp : WellFormed p) (m : Int)
    (hm : 0 ≤ m ∧ m ≤ 2 ^ 63 - 1) (t : IntType) :
    literalFitsInType p (-m) t = true ↔ represents p t (-m) :=
  fitsInType_iff p hp (-m) (by omega) t

/-- What the negated-literal rule cannot spell: a wide magnitude is rejected
under negation, and `-2^63` is the only value that loses — it is
representable exactly by `i64` and by 64-bit `int`/`ptr`. -/
theorem min_int64_lost (p : DataModel) (hp : WellFormed p) (t : IntType) :
    represents p t (-(2 ^ 63)) ↔
      t = .i64 ∨ (t = .int ∧ p.intBits = 64) ∨ (t = .ptr ∧ p.ptrBits = 64) := by
  obtain ⟨hint | hint, hptr | hptr⟩ := hp <;> cases t <;>
    simp [represents, lo, hi, hint, hptr] <;> omega

/-- The aliases decide as their targets. -/
theorem byte_as_u8 (p : DataModel) (wide : Bool) (v : Int) :
    literalFits p wide v .byte = literalFits p wide v .u8 := rfl

theorem rune_as_u32 (p : DataModel) (wide : Bool) (v : Int) :
    literalFits p wide v .rune = literalFits p wide v .u32 := rfl

/-- A wide literal never fits a signed type or a 32-bit unsigned one. -/
theorem wide_fits_only_wide_unsigned (p : DataModel) (v : Int) (t : IntType) :
    literalFits p true v t = true ↔ resolve p t = .u64 ∨ resolve p t = .u128 := by
  simp only [literalFits, if_true]
  cases h : resolve p t <;> simp

end Oak.LiteralFitRefinement
