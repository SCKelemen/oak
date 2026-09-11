/-!
# Method name mangling is injective

`docs/spec/90-backend.md` lowers a method `Type::method` on an ADT receiver to
the C function `oak_<len(Type)><Type>_<method>` (package-prefixed like every
Oak function). The scheme must never let two Oak callables share a C symbol:
not two methods of different types (`A_b::c` versus `A::b_c`), and not a
method and a plain function (`Handle::peek` versus `Handle_peek`).

Identifiers are modeled as character lists that are non-empty and do not
begin with a digit — the lexical rule for Oak and for C. The length prefix is
any rendering of a natural number into digits that is injective; the
implementation uses decimal (`strconv.Itoa`), which satisfies both
hypotheses. The proof is the combinatorial part: a digit-only prefix followed
by a non-digit is recoverable from the concatenation, so the prefix fixes
where the type name ends.
-/

namespace Oak.MethodMangling

/-- A non-empty identifier whose first character is not a digit. -/
def Ident : List Char -> Prop
  | [] => False
  | c :: _ => ¬ c.isDigit

/-- Every character of the list is a digit. -/
def AllDigits (xs : List Char) : Prop := ∀ c, c ∈ xs → c.isDigit

section

variable (lenPrefix : Nat -> List Char)

/-- The mangled spelling of `Type::method`, before the `oak_` and package
prefixes every callable shares. -/
def mangle (typeName method : List Char) : List Char :=
  lenPrefix typeName.length ++ typeName ++ '_' :: method

/-- A digit-only prefix followed by a non-digit is unique in a concatenation:
both sides must switch from digits to the non-digit at the same place. -/
theorem digit_prefix_unique :
    ∀ (xs ys rest rest' : List Char),
      AllDigits xs → AllDigits ys → Ident rest → Ident rest' →
      xs ++ rest = ys ++ rest' → xs = ys ∧ rest = rest' := by
  intro xs
  induction xs with
  | nil =>
      intro ys rest rest' _ hys hrest _ heq
      cases ys with
      | nil => exact ⟨rfl, by simpa using heq⟩
      | cons y ys' =>
          simp at heq
          -- rest begins with y, a digit, yet rest is an identifier
          have hy : y.isDigit := hys y (by simp)
          rw [heq] at hrest
          exact absurd hy hrest
  | cons x xs' ih =>
      intro ys rest rest' hxs hys hrest hrest' heq
      cases ys with
      | nil =>
          simp at heq
          have hx : x.isDigit := hxs x (by simp)
          rw [← heq] at hrest'
          exact absurd hx hrest'
      | cons y ys' =>
          simp at heq
          obtain ⟨hxy, htail⟩ := heq
          have hxs' : AllDigits xs' := fun c hc => hxs c (by simp [hc])
          have hys' : AllDigits ys' := fun c hc => hys c (by simp [hc])
          obtain ⟨h1, h2⟩ := ih ys' rest rest' hxs' hys' hrest hrest' htail
          subst hxy h1 h2
          exact ⟨rfl, rfl⟩

/-- Two methods with the same mangled spelling are the same method. -/
theorem mangle_injective
    (hdigits : ∀ n, AllDigits (lenPrefix n))
    (hinj : ∀ a b, lenPrefix a = lenPrefix b → a = b)
    (t t' m m' : List Char) (ht : Ident t) (ht' : Ident t')
    (heq : mangle lenPrefix t m = mangle lenPrefix t' m') : t = t' ∧ m = m' := by
  unfold mangle at heq
  rw [List.append_assoc, List.append_assoc] at heq
  obtain ⟨hlen, hrest⟩ := digit_prefix_unique (lenPrefix t.length) (lenPrefix t'.length)
    (t ++ '_' :: m) (t' ++ '_' :: m') (hdigits _) (hdigits _)
    (by cases t with | nil => exact absurd ht id | cons c _ => simpa [Ident] using ht)
    (by cases t' with | nil => exact absurd ht' id | cons c _ => simpa [Ident] using ht')
    heq
  have hlength : t.length = t'.length := hinj _ _ hlen
  obtain ⟨hteq, hmeq⟩ := List.append_inj hrest hlength
  exact ⟨hteq, by simpa using hmeq⟩

/-- A method's mangled spelling is never a plain function's name: it begins
with a digit and an identifier cannot. -/
theorem mangle_ne_ident
    (hdigits : ∀ n, AllDigits (lenPrefix n))
    (hne : ∀ n, lenPrefix n ≠ [])
    (t m f : List Char) (hf : Ident f) :
    mangle lenPrefix t m ≠ f := by
  intro heq
  unfold mangle at heq
  cases hp : lenPrefix t.length with
  | nil => exact hne _ hp
  | cons d ds =>
      have hd : d.isDigit := hdigits t.length d (by simp [hp])
      rw [hp] at heq
      simp at heq
      rw [← heq] at hf
      exact hf hd

end

end Oak.MethodMangling
