namespace Oak.Delimited

inductive Token where
  | open
  | close
  | separator
  | item : Nat -> Token
  deriving DecidableEq, Repr

/-- Canonical token body between opening and closing delimiters. -/
def body : List Nat -> Bool -> List Token
  | [], _ => []
  | [x], false => [.item x]
  | [x], true => [.item x, .separator]
  | x :: y :: rest, trailing =>
      .item x :: .separator :: body (y :: rest) trailing

/-- A complete delimited sequence. -/
def encode (items : List Nat) (trailing : Bool) : List Token :=
  .open :: (body items trailing ++ [.close])

/-- Cursor offset of the closing delimiter when the cursor enters on `open`. -/
def closeOffset (items : List Nat) (trailing : Bool) : Nat :=
  1 + (body items trailing).length

/-- Extract semantic items while ignoring delimiters and separators. -/
def itemValues : List Token -> List Nat
  | [] => []
  | .item x :: rest => x :: itemValues rest
  | _ :: rest => itemValues rest

theorem body_contains_no_open (items : List Nat) (trailing : Bool) :
    .open ∉ body items trailing := by
  induction items generalizing trailing with
  | nil => simp [body]
  | cons x rest ih =>
      cases rest with
      | nil => cases trailing <;> simp [body]
      | cons y ys =>
          simp [body, ih]

theorem body_contains_no_close (items : List Nat) (trailing : Bool) :
    .close ∉ body items trailing := by
  induction items generalizing trailing with
  | nil => simp [body]
  | cons x rest ih =>
      cases rest with
      | nil => cases trailing <;> simp [body]
      | cons y ys =>
          simp [body, ih]

theorem body_preserves_items (items : List Nat) (trailing : Bool) :
    itemValues (body items trailing) = items := by
  induction items generalizing trailing with
  | nil => simp [body, itemValues]
  | cons x rest ih =>
      cases rest with
      | nil => cases trailing <;> simp [body, itemValues]
      | cons y ys =>
          simp [body, itemValues, ih]

theorem encode_preserves_items (items : List Nat) (trailing : Bool) :
    itemValues (encode items trailing) = items := by
  simp [encode, itemValues, body_preserves_items]

theorem encode_starts_with_open (items : List Nat) (trailing : Bool) :
    encode items trailing = .open :: (body items trailing ++ [.close]) := by
  rfl

/-- At the specified postcondition offset, the remaining token stream begins
    exactly with the closing delimiter. -/
theorem drop_to_close (items : List Nat) (trailing : Bool) :
    List.drop (closeOffset items trailing) (encode items trailing) = [.close] := by
  simp [closeOffset, encode]

/-- The closing-delimiter cursor is always a valid token position. -/
theorem close_offset_in_bounds (items : List Nat) (trailing : Bool) :
    closeOffset items trailing < (encode items trailing).length := by
  have hlen :
      (encode items trailing).length = closeOffset items trailing + 1 := by
    simp [encode, closeOffset, Nat.add_assoc]
  rw [hlen]
  exact Nat.lt_succ_self _

/-- No closing delimiter can occur before the canonical close position. -/
theorem close_unique_to_suffix (items : List Nat) (trailing : Bool) :
    .close ∉ (.open :: body items trailing) := by
  simp [body_contains_no_close]

/-- Empty delimited sequences are structurally unambiguous. -/
theorem empty_encoding (trailing : Bool) :
    encode [] trailing = [.open, .close] := by
  simp [encode, body]

/-- A trailing separator changes only syntax, never the semantic item list. -/
theorem trailing_separator_semantically_transparent (items : List Nat) :
    itemValues (encode items false) = itemValues (encode items true) := by
  simp [encode_preserves_items]

end Oak.Delimited
