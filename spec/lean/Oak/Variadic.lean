namespace Oak.Variadic

/-! # Variadic call bundling

Model for the variadic trailing parameter of `docs/spec/10-syntax.md`: a
call to `fn f(a: T1, .., rest: ...E)` splits its arguments at the fixed
arity; the trailing arguments are materialized as one caller-owned array
passed as a view. Bundling must neither drop nor duplicate arguments, and
the bundled view's length is exactly the trailing count. -/

/-- Splitting a call's arguments at the fixed arity. -/
def bundle {β : Type} (fixedArity : Nat) (args : List β) : List β × List β :=
  (args.take fixedArity, args.drop fixedArity)

/-- **Nothing is lost or duplicated**: the fixed arguments followed by the
    bundled trailing arguments are exactly the original argument list. -/
theorem bundle_roundtrip {β : Type} (fixedArity : Nat) (args : List β) :
    (bundle fixedArity args).1 ++ (bundle fixedArity args).2 = args :=
  List.take_append_drop fixedArity args

/-- **The view's length is exactly the trailing count** when the call meets
    the arity floor. -/
theorem bundle_length {β : Type} {fixedArity : Nat} {args : List β}
    (h : fixedArity ≤ args.length) :
    (bundle fixedArity args).2.length = args.length - fixedArity := by
  simp [bundle]

/-- **The arity floor is exact**: the fixed side carries the full fixed
    arity whenever the call supplies at least that many arguments. -/
theorem bundle_fixed_length {β : Type} {fixedArity : Nat} {args : List β}
    (h : fixedArity ≤ args.length) :
    (bundle fixedArity args).1.length = fixedArity := by
  simp [bundle, h]

end Oak.Variadic
