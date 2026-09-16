import Oak.TypeLatticeRefinement
import Init.Data.List.Sort.Lemmas

/-!
# Closed checker-type atom identity

`Oak.TypeLatticeRefinement` is generic in a genuine `DecidableEq` on opaque
atoms.  The production checker supplies that premise with
`typechecker.latticeAtomIdentical`, rather than the broader compatibility
relation `Type.Equals`.  This module models the identity-relevant projection
of every current in-package `Type` implementation and turns it into equality
on a canonical key.

The model is intentionally bounded.  Its values are finite, well-founded
trees; it does not model cyclic Go heap graphs or implementations of the open
`Type` interface outside the `typechecker` package.  Pointer identity is an
abstract token, not a claim about numeric Go addresses.  The production hot
comparator remains allocation-free and is held to the examples below by
`typechecker/lattice_atom_identity_refinement_test.go`.
-/

namespace Oak.TypeLatticeAtomIdentity

/-- The 25 pointer-receiver `Type` constructors currently owned by the
    production `typechecker` package. -/
inductive ConstructorTag where
  | primitive | string | bool | unit | never | any | adt | narrowedADT
  | record | interface | union | intersection | fieldAccessor | function
  | array | generic | typeVar | constraintSet | cType | simd | mmio | buffer
  | atomic | cFn | constInt
  deriving DecidableEq, Repr, Ord

/-- Tokens of a prefix-delimited structural key.  Keeping the recursive key as
    a list of non-recursive tokens gives Lean a direct `DecidableEq`, while
    constructor tags and list lengths keep differently shaped types apart. -/
inductive KeyToken where
  | constructor (tag : ConstructorTag)
  | nilType
  | typedNil (tag : ConstructorTag)
  | text (value : String)
  | integer (value : Int)
  | natural (value : Nat)
  | flag (value : Bool)
  | listLength (value : Nat)
  | keyLength (value : Nat)
  | fieldName (value : String)
  | binder (value : Nat)
  | dynamicType (value : Nat)
  | object (value : Nat)
  deriving DecidableEq, Repr, Ord

/-- Canonical semantic identities consumed by the free type lattice. -/
abbrev AtomKey := List KeyToken

/-- Deterministic multiset representation used for unordered identity
    components.  Sorting preserves duplicates. -/
def canonicalBag [Ord α] (values : List α) : List α :=
  values.mergeSort fun left right => (compare left right).isLE

/-- A finite abstraction of the current Go `Type` graph.  Fields described as
    metadata are present so the projection states explicitly that they are
    ignored. -/
inductive CheckerType where
  | nilType
  | typedNil (tag : ConstructorTag)
  | primitive (name refinement : String)
  | string (encoding : String)
  | bool | unit | never | any
  | adt (name : String)
  | narrowedADT (adtName variantName : String) (arguments : List AtomKey)
  | record (fields : List (String × AtomKey)) (name : String)
      (order : List String) (isStruct isOpen : Bool) (row : String)
  | interface (name : String) (methodsMetadata : Nat)
  | union (members : List AtomKey)
  | intersection (members : List AtomKey)
  | fieldAccessor (field : String)
  | function (parameters : List AtomKey) (result : AtomKey) (variadic : Bool)
  | array (element : AtomKey) (length : Int) (slice span : Bool) (align : Nat)
  | generic (name : String) (arguments : List AtomKey)
  | typeVar (binder : Nat) (displayName : String) (displayID : Int)
      (monomorphicMetadata groupMetadata : Nat)
  | constraintSet (requirements : List String)
  | cType (name : String)
  | simd (name : String)
  | mmio (width : Nat) (access : String)
  | buffer (element : AtomKey) (custody : String)
  | atomic (element : AtomKey)
  | cFn (parameters : List AtomKey) (result : AtomKey) (exprMetadata : Nat)
  | constInt (value : Int)
  | opaquePointer (dynamicType object : Nat)
  deriving Repr

def normalizePrimitiveName : String → String
  | "byte" => "u8"
  | "rune" => "u32"
  | name => name

def normalizeStringEncoding (encoding : String) : String :=
  if encoding.isEmpty then "Utf8" else encoding

def normalizeCustody (custody : String) : String :=
  if custody.isEmpty then "Host" else custody

def orderedKeyList (keys : List AtomKey) : AtomKey :=
  .listLength keys.length ::
    keys.flatMap fun key => .keyLength key.length :: key

def unorderedKeyList (keys : List AtomKey) : AtomKey :=
  orderedKeyList (canonicalBag keys)

/-- The exact semantic key policy of `latticeAtomIdentical` for the closed
    current universe. -/
def identityKey : CheckerType → AtomKey
  | .nilType => [.nilType]
  | .typedNil tag => [.typedNil tag]
  | .primitive name refinement =>
      [.constructor .primitive, .text (normalizePrimitiveName name), .text refinement]
  | .string encoding => [.constructor .string, .text (normalizeStringEncoding encoding)]
  | .bool => [.constructor .bool]
  | .unit => [.constructor .unit]
  | .never => [.constructor .never]
  | .any => [.constructor .any]
  | .adt name => [.constructor .adt, .text name]
  | .narrowedADT adtName variantName arguments =>
      [.constructor .narrowedADT, .text adtName, .text variantName] ++
        orderedKeyList arguments
  | .record fields name _ isStruct isOpen _ =>
      if isStruct && !name.isEmpty then [.constructor .record, .flag true, .text name]
      else
        [.constructor .record, .flag false, .flag isOpen] ++
          unorderedKeyList (fields.map fun field => .fieldName field.1 :: field.2)
  | .interface name _ => [.constructor .interface, .text name]
  | .union members =>
      [.constructor .union] ++ unorderedKeyList members
  | .intersection members =>
      [.constructor .intersection] ++ unorderedKeyList members
  | .fieldAccessor field => [.constructor .fieldAccessor, .text field]
  | .function parameters result variadic =>
      [.constructor .function, .flag variadic] ++
        orderedKeyList parameters ++ result
  | .array element length slice span align =>
      [.constructor .array, .integer length, .flag slice, .flag span, .natural align] ++
        element
  | .generic name arguments =>
      [.constructor .generic, .text name] ++ orderedKeyList arguments
  | .typeVar binder _ _ _ _ => [.constructor .typeVar, .binder binder]
  | .constraintSet requirements =>
      [.constructor .constraintSet, .listLength requirements.length] ++
        requirements.map .text
  | .cType name => [.constructor .cType, .text name]
  | .simd name => [.constructor .simd, .text name]
  | .mmio width access => [.constructor .mmio, .natural width, .text access]
  | .buffer element custody =>
      [.constructor .buffer, .text (normalizeCustody custody)] ++ element
  | .atomic element => [.constructor .atomic] ++ element
  | .cFn parameters result _ =>
      [.constructor .cFn] ++ orderedKeyList parameters ++ result
  | .constInt value => [.constructor .constInt, .integer value]
  | .opaquePointer dynamicType object => [.dynamicType dynamicType, .object object]

/-- Boolean atom identity is genuine equality of canonical semantic keys. -/
def atomIdentical (left right : CheckerType) : Bool :=
  decide (identityKey left = identityKey right)

theorem atomIdentical_iff_key_eq (left right : CheckerType) :
    atomIdentical left right = true ↔ identityKey left = identityKey right := by
  simp [atomIdentical]

theorem atomIdentical_refl (value : CheckerType) :
    atomIdentical value value = true := by
  simp [atomIdentical]

theorem atomIdentical_symm (left right : CheckerType) :
    atomIdentical left right = atomIdentical right left := by
  simp [atomIdentical, eq_comm]

theorem atomIdentical_trans {left middle right : CheckerType}
    (hlm : atomIdentical left middle = true)
    (hmr : atomIdentical middle right = true) :
    atomIdentical left right = true := by
  rw [atomIdentical_iff_key_eq] at hlm hmr ⊢
  exact hlm.trans hmr

theorem canonicalBag_perm [Ord α] (values : List α) :
    List.Perm (canonicalBag values) values := by
  exact List.mergeSort_perm _ _

/-! ## The free-lattice theorem with Oak's atom premise discharged -/

open Oak.TypeLattice
open Oak.TypeLatticeRefinement

abbrev CheckerLatticeTy := LatticeTy AtomKey

theorem checker_isSubtype_sound {left right : CheckerLatticeTy}
    (h : decide (dnfOf left) (dnfOf right) = true)
    {X : Type} (valuation : AtomKey → Ty X) :
    denote valuation left ≤ₜ denote valuation right := by
  exact isSubtype_sound h valuation

theorem checker_isSubtype_complete {left right : CheckerLatticeTy}
    (h : decide (dnfOf left) (dnfOf right) = false) :
    ∃ valuation : AtomKey → Ty Unit,
      ¬ (denote valuation left ≤ₜ denote valuation right) := by
  exact isSubtype_complete h

/-! ## Production correspondence pins

These equations are rendered from live `latticeAtomIdentical` decisions by
`typechecker/lattice_atom_identity_refinement_test.go`. -/

example : atomIdentical (.nilType) (.nilType) = true := by decide
example : atomIdentical (.nilType) (.typedNil .primitive) = false := by decide
example : atomIdentical (.typedNil .primitive) (.typedNil .primitive) = true := by decide
example : atomIdentical (.typedNil .primitive) (.typedNil .string) = false := by decide
example : atomIdentical (.primitive "u8" "") (.primitive "byte" "") = true := by decide
example : atomIdentical (.primitive "u8" "") (.primitive "u8" "Small") = false := by decide
example : atomIdentical (.string "") (.string "Utf8") = true := by decide
example : atomIdentical (.string "") (.string "Ascii") = false := by decide
example : atomIdentical (.bool) (.bool) = true := by decide
example : atomIdentical (.unit) (.unit) = true := by decide
example : atomIdentical (.never) (.never) = true := by decide
example : atomIdentical (.any) (.any) = true := by decide
example : atomIdentical (.adt "Choice") (.adt "Choice") = true := by decide
example : atomIdentical (.adt "Choice") (.adt "Other") = false := by decide
example : atomIdentical (.narrowedADT "Choice" "Left" [(identityKey (.primitive "u8" ""))]) (.narrowedADT "Choice" "Left" [(identityKey (.primitive "byte" ""))]) = true := by decide
example : atomIdentical (.narrowedADT "Choice" "Left" []) (.narrowedADT "Other" "Left" []) = false := by decide
example : atomIdentical (.narrowedADT "Choice" "Left" []) (.narrowedADT "Choice" "Right" []) = false := by decide
example : atomIdentical (.narrowedADT "Choice" "Left" [(identityKey (.primitive "u8" ""))]) (.narrowedADT "Choice" "Left" [(identityKey (.bool))]) = false := by decide
example : atomIdentical (.narrowedADT "Choice" "Left" [(identityKey (.primitive "u8" ""))]) (.narrowedADT "Choice" "Left" [(identityKey (.primitive "u8" "")), (identityKey (.bool))]) = false := by decide
example : atomIdentical (.narrowedADT "Choice" "Left" [(identityKey (.primitive "u8" "")), (identityKey (.bool))]) (.narrowedADT "Choice" "Left" [(identityKey (.bool)), (identityKey (.primitive "u8" ""))]) = false := by decide
example : atomIdentical (.narrowedADT "Choice" "Left" []) (.adt "Choice") = false := by decide
example : atomIdentical (.record [("x", (identityKey (.primitive "u8" "")))] "Left" ["x"] false false "r") (.record [("x", (identityKey (.primitive "byte" "")))] "Right" ["other"] false false "s") = true := by native_decide
example : atomIdentical (.record [("x", (identityKey (.primitive "u8" "")))] "" [] false false "") (.record [("x", (identityKey (.primitive "u8" "")))] "" [] false true "") = false := by decide
example : atomIdentical (.record [("x", (identityKey (.primitive "u8" "")))] "" [] false false "") (.record [] "" [] false false "") = false := by native_decide
example : atomIdentical (.record [("x", (identityKey (.primitive "u8" "")))] "" [] false false "") (.record [("y", (identityKey (.primitive "u8" "")))] "" [] false false "") = false := by native_decide
example : atomIdentical (.record [("x", (identityKey (.primitive "u8" "")))] "" [] false false "") (.record [("x", (identityKey (.bool)))] "" [] false false "") = false := by native_decide
example : atomIdentical (.record [("x", (identityKey (.primitive "u8" "")))] "" [] false false "") (.record [("x", (identityKey (.primitive "byte" "")))] "" [] true false "") = true := by native_decide
example : atomIdentical (.record [("x", (identityKey (.primitive "u8" "")))] "Stored" [] true false "") (.record [("other", (identityKey (.bool)))] "Stored" [] true true "") = true := by decide
example : atomIdentical (.record [] "StoredA" [] true false "") (.record [] "StoredB" [] true false "") = false := by decide
example : atomIdentical (.record [] "Stored" [] true false "") (.record [] "Stored" [] false false "") = false := by decide
example : atomIdentical (.unit) (.record [] "" [] false false "") = false := by decide
example : atomIdentical (.interface "Readable" 0) (.interface "Readable" 1) = true := by decide
example : atomIdentical (.interface "Readable" 0) (.interface "Writable" 0) = false := by decide
example : atomIdentical (.union [(identityKey (.primitive "u8" "")), (identityKey (.bool))]) (.union [(identityKey (.bool)), (identityKey (.primitive "byte" ""))]) = true := by native_decide
example : atomIdentical (.union [(identityKey (.primitive "u8" "")), (identityKey (.primitive "u8" ""))]) (.union [(identityKey (.primitive "u8" ""))]) = false := by native_decide
example : atomIdentical (.intersection [(identityKey (.primitive "u8" "")), (identityKey (.bool))]) (.intersection [(identityKey (.bool)), (identityKey (.primitive "byte" ""))]) = true := by native_decide
example : atomIdentical (.intersection [(identityKey (.primitive "u8" "")), (identityKey (.primitive "u8" ""))]) (.intersection [(identityKey (.primitive "u8" ""))]) = false := by native_decide
example : atomIdentical (.fieldAccessor "x") (.fieldAccessor "x") = true := by decide
example : atomIdentical (.fieldAccessor "x") (.fieldAccessor "y") = false := by decide
example : atomIdentical (.function [(identityKey (.primitive "u8" ""))] (identityKey (.bool)) false) (.function [(identityKey (.primitive "byte" ""))] (identityKey (.bool)) false) = true := by decide
example : atomIdentical (.function [(identityKey (.primitive "u8" ""))] (identityKey (.primitive "u8" "")) false) (.function [(identityKey (.primitive "u8" ""))] (identityKey (.bool)) false) = false := by decide
example : atomIdentical (.function [(identityKey (.primitive "u8" ""))] (identityKey (.bool)) false) (.function [(identityKey (.primitive "u8" "")), (identityKey (.bool))] (identityKey (.bool)) false) = false := by decide
example : atomIdentical (.function [(identityKey (.primitive "u8" "")), (identityKey (.bool))] (identityKey (.bool)) false) (.function [(identityKey (.bool)), (identityKey (.primitive "u8" ""))] (identityKey (.bool)) false) = false := by decide
example : atomIdentical (.function [(identityKey (.primitive "u8" ""))] (identityKey (.bool)) false) (.function [(identityKey (.primitive "u8" ""))] (identityKey (.bool)) true) = false := by decide
example : atomIdentical (.array (identityKey (.primitive "u8" "")) (-1 : Int) false true 0) (.array (identityKey (.primitive "byte" "")) (-1 : Int) false true 0) = true := by decide
example : atomIdentical (.array (identityKey (.primitive "u8" "")) (-1 : Int) false true 0) (.array (identityKey (.bool)) (-1 : Int) false true 0) = false := by decide
example : atomIdentical (.array (identityKey (.primitive "u8" "")) (-1 : Int) false true 0) (.array (identityKey (.primitive "u8" "")) (4 : Int) false true 0) = false := by decide
example : atomIdentical (.array (identityKey (.primitive "u8" "")) (-1 : Int) false true 0) (.array (identityKey (.primitive "u8" "")) (-1 : Int) false true 64) = false := by decide
example : atomIdentical (.array (identityKey (.primitive "u8" "")) (-1 : Int) false true 0) (.array (identityKey (.primitive "u8" "")) (-1 : Int) true true 0) = false := by decide
example : atomIdentical (.array (identityKey (.primitive "u8" "")) (-1 : Int) false true 0) (.array (identityKey (.primitive "u8" "")) (-1 : Int) false false 0) = false := by decide
example : atomIdentical (.generic "Option" [(identityKey (.primitive "u8" ""))]) (.generic "Option" [(identityKey (.primitive "byte" ""))]) = true := by decide
example : atomIdentical (.generic "Option" [(identityKey (.primitive "u8" ""))]) (.generic "Result" [(identityKey (.primitive "u8" ""))]) = false := by decide
example : atomIdentical (.generic "Result" [(identityKey (.primitive "u8" ""))]) (.generic "Result" [(identityKey (.primitive "u8" "")), (identityKey (.bool))]) = false := by decide
example : atomIdentical (.generic "Result" [(identityKey (.primitive "u8" "")), (identityKey (.bool))]) (.generic "Result" [(identityKey (.bool)), (identityKey (.primitive "u8" ""))]) = false := by decide
example : atomIdentical (.typeVar 1 "T" (7 : Int) 0 0) (.typeVar 1 "T" (7 : Int) 0 0) = true := by decide
example : atomIdentical (.typeVar 1 "T" (7 : Int) 0 0) (.typeVar 2 "T" (7 : Int) 0 0) = false := by decide
example : atomIdentical (.constraintSet ["Read", "Write"]) (.constraintSet ["Write", "Read"]) = false := by decide
example : atomIdentical (.cType "UInt8") (.cType "UInt8") = true := by decide
example : atomIdentical (.cType "UInt8") (.cType "Int8") = false := by decide
example : atomIdentical (.simd "U8x16") (.simd "U8x16") = true := by decide
example : atomIdentical (.simd "U8x16") (.simd "U16x8") = false := by decide
example : atomIdentical (.mmio 32 "read-only") (.mmio 32 "read-only") = true := by decide
example : atomIdentical (.mmio 32 "read-only") (.mmio 64 "read-only") = false := by decide
example : atomIdentical (.mmio 32 "read-only") (.mmio 32 "read-write") = false := by decide
example : atomIdentical (.buffer (identityKey (.primitive "u8" "")) "") (.buffer (identityKey (.primitive "byte" "")) "Host") = true := by decide
example : atomIdentical (.buffer (identityKey (.primitive "u8" "")) "") (.buffer (identityKey (.bool)) "") = false := by decide
example : atomIdentical (.buffer (identityKey (.primitive "u8" "")) "") (.buffer (identityKey (.primitive "u8" "")) "Device") = false := by decide
example : atomIdentical (.atomic (identityKey (.primitive "u8" ""))) (.atomic (identityKey (.primitive "byte" ""))) = true := by decide
example : atomIdentical (.atomic (identityKey (.primitive "u8" ""))) (.atomic (identityKey (.bool))) = false := by decide
example : atomIdentical (.cFn [(identityKey (.cType "UInt8"))] (identityKey (.primitive "u8" "")) 0) (.cFn [(identityKey (.cType "UInt8"))] (identityKey (.primitive "byte" "")) 1) = true := by decide
example : atomIdentical (.cFn [(identityKey (.primitive "u8" ""))] (identityKey (.primitive "u8" "")) 0) (.cFn [(identityKey (.bool))] (identityKey (.primitive "u8" "")) 0) = false := by decide
example : atomIdentical (.cFn [(identityKey (.primitive "u8" ""))] (identityKey (.primitive "u8" "")) 0) (.cFn [(identityKey (.primitive "u8" "")), (identityKey (.bool))] (identityKey (.primitive "u8" "")) 0) = false := by decide
example : atomIdentical (.cFn [(identityKey (.primitive "u8" "")), (identityKey (.bool))] (identityKey (.primitive "u8" "")) 0) (.cFn [(identityKey (.bool)), (identityKey (.primitive "u8" ""))] (identityKey (.primitive "u8" "")) 0) = false := by decide
example : atomIdentical (.cFn [] (identityKey (.primitive "u8" "")) 0) (.cFn [] (identityKey (.bool)) 0) = false := by decide
example : atomIdentical (.constInt (4 : Int)) (.constInt (4 : Int)) = true := by decide
example : atomIdentical (.constInt (4 : Int)) (.constInt (5 : Int)) = false := by decide

end Oak.TypeLatticeAtomIdentity
