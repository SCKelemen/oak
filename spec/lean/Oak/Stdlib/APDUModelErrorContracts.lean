import Oak.Stdlib.APDULengthModel

/-! Uncompiled source-only exact error characterization of the unchanged natural
model. This is consumed by the generated equality later; it does not itself
establish correspondence with emitted parser code. -/
set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000
namespace Oak.Stdlib.APDUModelErrorContracts
open APDUModel

def ErrorPredicate (x : Input) (e : Error) : Prop :=
  match e with
  | .tooLong => 65544 < x.n
  | .truncatedHeader => x.n < 4
  | .truncatedLength => x.n ≤ 65544 ∧ x.first.val = 0 ∧
      (x.n = 6 ∨ (0 < x.word.val ∧ x.n = 8 + x.word.val))
  | .zeroDataLength => 7 < x.n ∧ x.n ≤ 65544 ∧ x.first.val = 0 ∧ x.word.val = 0
  | .truncatedData => 5 < x.n ∧ x.n ≤ 65544 ∧
      ((0 < x.first.val ∧ x.n - 5 < x.first.val) ∨
       (x.first.val = 0 ∧ 7 < x.n ∧ 0 < x.word.val ∧ x.n - 7 < x.word.val))
  | .trailingBytes => x.n ≤ 65544 ∧
      ((0 < x.first.val ∧ 7 + x.first.val ≤ x.n) ∨
       (x.first.val = 0 ∧ 0 < x.word.val ∧ 10 + x.word.val ≤ x.n))

-- Each split follows the unchanged model's actual decision tree. This proves
-- both directions, including branches ruled out by earlier guards.
theorem decode_error_iff (x : Input) (e : Error) :
    decode x = .error e ↔ ErrorPredicate x e := by
  have hByte := x.first.isLt
  have hWord := x.word.isLt
  unfold decode
  by_cases hLong : x.n > 65544
  · rw [if_pos hLong]
    cases e <;> simp only [ErrorPredicate, Except.error.injEq, reduceCtorEq] <;> constructor <;> intro h <;> (first | exact True.intro | contradiction | omega)
  · rw [if_neg hLong]
    by_cases hHeader : x.n < 4
    · rw [if_pos hHeader]
      cases e <;> simp only [ErrorPredicate, Except.error.injEq, reduceCtorEq] <;> constructor <;> intro h <;> (first | exact True.intro | contradiction | omega)
    · rw [if_neg hHeader]
      by_cases hFour : x.n = 4
      · rw [if_pos hFour]
        cases e <;> simp only [ErrorPredicate, reduceCtorEq] <;> constructor <;> intro h <;> (first | exact True.intro | contradiction | omega)
      · rw [if_neg hFour]
        by_cases hFive : x.n = 5
        · rw [if_pos hFive]
          cases e <;> simp only [ErrorPredicate, reduceCtorEq] <;> constructor <;> intro h <;> (first | exact True.intro | contradiction | omega)
        · rw [if_neg hFive]
          by_cases hFirst : x.first.val = 0
          · rw [if_pos hFirst]
            by_cases hShort : x.n < 7
            · rw [if_pos hShort]
              cases e <;> simp only [ErrorPredicate, Except.error.injEq, reduceCtorEq] <;> constructor <;> intro h <;> (first | exact True.intro | contradiction | omega)
            · rw [if_neg hShort]
              by_cases hSeven : x.n = 7
              · rw [if_pos hSeven]
                cases e <;> simp only [ErrorPredicate, reduceCtorEq] <;> constructor <;> intro h <;> (first | exact True.intro | contradiction | omega)
              · rw [if_neg hSeven]
                by_cases hWordZero : x.word.val = 0
                · rw [if_pos hWordZero]
                  cases e <;> simp only [ErrorPredicate, Except.error.injEq, reduceCtorEq] <;> constructor <;> intro h <;> (first | exact True.intro | contradiction | omega)
                · rw [if_neg hWordZero]
                  unfold extendedData
                  by_cases hData : x.word.val > x.n - 7
                  · rw [if_pos hData]
                    cases e <;> simp only [ErrorPredicate, Except.error.injEq, reduceCtorEq] <;> constructor <;> intro h <;> (first | exact True.intro | contradiction | omega)
                  · rw [if_neg hData]
                    by_cases hRest0 : x.n - (7 + x.word.val) = 0
                    · rw [if_pos hRest0]
                      cases e <;> simp only [ErrorPredicate, reduceCtorEq] <;> constructor <;> intro h <;> (first | exact True.intro | contradiction | omega)
                    · rw [if_neg hRest0]
                      by_cases hRest1 : x.n - (7 + x.word.val) = 1
                      · rw [if_pos hRest1]
                        cases e <;> simp only [ErrorPredicate, Except.error.injEq, reduceCtorEq] <;> constructor <;> intro h <;> (first | exact True.intro | contradiction | omega)
                      · rw [if_neg hRest1]
                        by_cases hRest2 : x.n - (7 + x.word.val) = 2
                        · rw [if_pos hRest2]
                          cases e <;> simp only [ErrorPredicate, reduceCtorEq] <;> constructor <;> intro h <;> (first | exact True.intro | contradiction | omega)
                        · rw [if_neg hRest2]
                          cases e <;> simp only [ErrorPredicate, Except.error.injEq, reduceCtorEq] <;> constructor <;> intro h <;> (first | exact True.intro | contradiction | omega)
          · rw [if_neg hFirst]
            unfold shortData
            by_cases hData : x.first.val > x.n - 5
            · rw [if_pos hData]
              cases e <;> simp only [ErrorPredicate, Except.error.injEq, reduceCtorEq] <;> constructor <;> intro h <;> (first | exact True.intro | contradiction | omega)
            · rw [if_neg hData]
              by_cases hRest0 : x.n - (5 + x.first.val) = 0
              · rw [if_pos hRest0]
                cases e <;> simp only [ErrorPredicate, reduceCtorEq] <;> constructor <;> intro h <;> (first | exact True.intro | contradiction | omega)
              · rw [if_neg hRest0]
                by_cases hRest1 : x.n - (5 + x.first.val) = 1
                · rw [if_pos hRest1]
                  cases e <;> simp only [ErrorPredicate, reduceCtorEq] <;> constructor <;> intro h <;> (first | exact True.intro | contradiction | omega)
                · rw [if_neg hRest1]
                  cases e <;> simp only [ErrorPredicate, Except.error.injEq, reduceCtorEq] <;> constructor <;> intro h <;> (first | exact True.intro | contradiction | omega)

theorem too_long_iff (x : Input) :
    decode x = .error .tooLong ↔ ErrorPredicate x .tooLong :=
  decode_error_iff x .tooLong

theorem truncated_header_iff (x : Input) :
    decode x = .error .truncatedHeader ↔ ErrorPredicate x .truncatedHeader :=
  decode_error_iff x .truncatedHeader

theorem truncated_length_iff (x : Input) :
    decode x = .error .truncatedLength ↔ ErrorPredicate x .truncatedLength :=
  decode_error_iff x .truncatedLength

theorem zero_data_length_iff (x : Input) :
    decode x = .error .zeroDataLength ↔ ErrorPredicate x .zeroDataLength :=
  decode_error_iff x .zeroDataLength

theorem truncated_data_iff (x : Input) :
    decode x = .error .truncatedData ↔ ErrorPredicate x .truncatedData :=
  decode_error_iff x .truncatedData

theorem trailing_bytes_iff (x : Input) :
    decode x = .error .trailingBytes ↔ ErrorPredicate x .trailingBytes :=
  decode_error_iff x .trailingBytes

end Oak.Stdlib.APDUModelErrorContracts
