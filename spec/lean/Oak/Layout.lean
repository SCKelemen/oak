namespace Oak.Layout

/-- Abstract input events for the layout normalizer. `source` events represent
    original significant tokens; open/close events represent virtual block
    decisions made by the indentation layer. -/
inductive Event where
  | source : Nat -> Event
  | open
  | close
  deriving DecidableEq, Repr

/-- Abstract normalized output. Source tokens remain distinguishable from
    synthetic braces so erasure can state the no-reordering/no-fabrication law. -/
inductive Token where
  | source : Nat -> Token
  | open
  | close
  deriving DecidableEq, Repr

/-- Project only original source-token identities from normalized output. -/
def sourceValues : List Token -> List Nat
  | [] => []
  | .source value :: rest => value :: sourceValues rest
  | _ :: rest => sourceValues rest

/-- Project source-token identities from the input event stream. -/
def sourceEvents : List Event -> List Nat
  | [] => []
  | .source value :: rest => value :: sourceEvents rest
  | _ :: rest => sourceEvents rest

def opens : List Token -> Nat
  | [] => 0
  | .open :: rest => 1 + opens rest
  | _ :: rest => opens rest

def closes : List Token -> Nat
  | [] => 0
  | .close :: rest => 1 + closes rest
  | _ :: rest => closes rest

/-- Execute abstract layout decisions from an initial virtual-block depth.
    A close at depth zero is invalid. -/
def renderFrom : Nat -> List Event -> Option (Nat × List Token)
  | depth, [] => some (depth, [])
  | depth, .source value :: rest =>
      match renderFrom depth rest with
      | none => none
      | some (finalDepth, output) =>
          some (finalDepth, .source value :: output)
  | depth, .open :: rest =>
      match renderFrom (depth + 1) rest with
      | none => none
      | some (finalDepth, output) =>
          some (finalDepth, .open :: output)
  | 0, .close :: _ => none
  | depth + 1, .close :: rest =>
      match renderFrom depth rest with
      | none => none
      | some (finalDepth, output) =>
          some (finalDepth, .close :: output)

/-- EOF closes every still-open virtual block. -/
def finishTokens (depth : Nat) (output : List Token) : List Token :=
  output ++ List.replicate depth .close

theorem sourceValues_append (left right : List Token) :
    sourceValues (left ++ right) = sourceValues left ++ sourceValues right := by
  induction left with
  | nil => rfl
  | cons token rest ih =>
      cases token <;> simp [sourceValues, ih]

theorem opens_append (left right : List Token) :
    opens (left ++ right) = opens left + opens right := by
  induction left with
  | nil => rfl
  | cons token rest ih =>
      cases token <;> simp [opens, ih, Nat.add_assoc]

theorem closes_append (left right : List Token) :
    closes (left ++ right) = closes left + closes right := by
  induction left with
  | nil => rfl
  | cons token rest ih =>
      cases token <;> simp [closes, ih, Nat.add_assoc]

theorem sourceValues_replicate_close (count : Nat) :
    sourceValues (List.replicate count Token.close) = [] := by
  induction count with
  | zero => rfl
  | succ count ih => simp [List.replicate_succ, sourceValues, ih]

theorem opens_replicate_close (count : Nat) :
    opens (List.replicate count Token.close) = 0 := by
  induction count with
  | zero => rfl
  | succ count ih => simp [List.replicate_succ, opens, ih]

theorem closes_replicate_close (count : Nat) :
    closes (List.replicate count Token.close) = count := by
  induction count with
  | zero => rfl
  | succ count ih => simp [List.replicate_succ, closes, ih]

/-- Successful normalization preserves every original significant token in
    exactly the same order after synthetic braces are erased. -/
theorem render_preserves_source_order
    (events : List Event) (depth finalDepth : Nat) (output : List Token)
    (h : renderFrom depth events = some (finalDepth, output)) :
    sourceValues output = sourceEvents events := by
  induction events generalizing depth finalDepth output with
  | nil =>
      simp [renderFrom] at h
      cases h
      rfl
  | cons event rest ih =>
      cases event with
      | source value =>
          cases hr : renderFrom depth rest with
          | none => simp [renderFrom, hr] at h
          | some result =>
              rcases result with ⟨nextDepth, nextOutput⟩
              simp [renderFrom, hr] at h
              cases h
              simp [sourceValues, sourceEvents, ih rest depth nextDepth nextOutput hr]
      | open =>
          cases hr : renderFrom (depth + 1) rest with
          | none => simp [renderFrom, hr] at h
          | some result =>
              rcases result with ⟨nextDepth, nextOutput⟩
              simp [renderFrom, hr] at h
              cases h
              simp [sourceValues, sourceEvents, ih rest (depth + 1) nextDepth nextOutput hr]
      | close =>
          cases depth with
          | zero => simp [renderFrom] at h
          | succ depth =>
              cases hr : renderFrom depth rest with
              | none => simp [renderFrom, hr] at h
              | some result =>
                  rcases result with ⟨nextDepth, nextOutput⟩
                  simp [renderFrom, hr] at h
                  cases h
                  simp [sourceValues, sourceEvents, ih rest depth nextDepth nextOutput hr]

/-- For every successful trace, virtual opens minus virtual closes equals the
    change in stack depth. This is the core balance invariant. -/
theorem render_balance
    (events : List Event) (depth finalDepth : Nat) (output : List Token)
    (h : renderFrom depth events = some (finalDepth, output)) :
    opens output + depth = closes output + finalDepth := by
  induction events generalizing depth finalDepth output with
  | nil =>
      simp [renderFrom] at h
      cases h
      simp [opens, closes]
  | cons event rest ih =>
      cases event with
      | source value =>
          cases hr : renderFrom depth rest with
          | none => simp [renderFrom, hr] at h
          | some result =>
              rcases result with ⟨nextDepth, nextOutput⟩
              simp [renderFrom, hr] at h
              cases h
              simpa [opens, closes] using ih rest depth nextDepth nextOutput hr
      | open =>
          cases hr : renderFrom (depth + 1) rest with
          | none => simp [renderFrom, hr] at h
          | some result =>
              rcases result with ⟨nextDepth, nextOutput⟩
              simp [renderFrom, hr] at h
              cases h
              have hrest := ih rest (depth + 1) nextDepth nextOutput hr
              simp [opens, closes]
              omega
      | close =>
          cases depth with
          | zero => simp [renderFrom] at h
          | succ depth =>
              cases hr : renderFrom depth rest with
              | none => simp [renderFrom, hr] at h
              | some result =>
                  rcases result with ⟨nextDepth, nextOutput⟩
                  simp [renderFrom, hr] at h
                  cases h
                  have hrest := ih rest depth nextDepth nextOutput hr
                  simp [opens, closes]
                  omega

/-- EOF closure cannot change or reorder source tokens. -/
theorem finish_preserves_source_order (depth : Nat) (output : List Token) :
    sourceValues (finishTokens depth output) = sourceValues output := by
  simp [finishTokens, sourceValues_append, sourceValues_replicate_close]

/-- Starting at depth zero, EOF closure produces a balanced synthetic-brace
    stream for every successful trace. -/
theorem finish_balances
    (events : List Event) (finalDepth : Nat) (output : List Token)
    (h : renderFrom 0 events = some (finalDepth, output)) :
    opens (finishTokens finalDepth output) =
      closes (finishTokens finalDepth output) := by
  have hbalance := render_balance events 0 finalDepth output h
  simp [finishTokens, opens_append, closes_append,
    opens_replicate_close, closes_replicate_close]
  omega

/-- A synthetic close without an open block is rejected rather than silently
    fabricating stack state. -/
theorem close_underflow_rejected : renderFrom 0 [.close] = none := by
  rfl

end Oak.Layout
