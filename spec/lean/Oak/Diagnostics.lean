namespace Oak.Diagnostics

inductive Severity where
  | error
  | warning
  | information
  | hint
  deriving DecidableEq, Repr

structure Span where
  source : Nat
  start : Nat
  stop : Nat
  deriving DecidableEq, Repr

/-- A diagnostic has exactly one primary cause by construction. Secondary
    context, notes, and help cannot compete for primary ownership. -/
structure Diagnostic where
  code : Nat
  severity : Severity
  title : Nat
  primary : Span
  secondary : List Span
  notes : List Nat
  help : List Nat
  deriving DecidableEq, Repr

/-- Wording may improve without changing the stable semantic identity. -/
def retitle (d : Diagnostic) (title : Nat) : Diagnostic :=
  { d with title := title }

/-- Adding source context must not change the diagnostic identity or cause. -/
def addSecondary (d : Diagnostic) (span : Span) : Diagnostic :=
  { d with secondary := d.secondary ++ [span] }

/-- Adding explanatory context must not change the diagnostic identity or cause. -/
def addNote (d : Diagnostic) (note : Nat) : Diagnostic :=
  { d with notes := d.notes ++ [note] }

/-- Adding actionable advice must not change the diagnostic identity or cause. -/
def addHelp (d : Diagnostic) (help : Nat) : Diagnostic :=
  { d with help := d.help ++ [help] }

theorem retitle_preserves_code (d : Diagnostic) (title : Nat) :
    (retitle d title).code = d.code := by
  rfl

theorem retitle_preserves_primary (d : Diagnostic) (title : Nat) :
    (retitle d title).primary = d.primary := by
  rfl

theorem secondary_preserves_identity (d : Diagnostic) (span : Span) :
    (addSecondary d span).code = d.code ∧
    (addSecondary d span).primary = d.primary := by
  constructor <;> rfl

theorem note_preserves_identity (d : Diagnostic) (note : Nat) :
    (addNote d note).code = d.code ∧
    (addNote d note).primary = d.primary := by
  constructor <;> rfl

theorem help_preserves_identity (d : Diagnostic) (help : Nat) :
    (addHelp d help).code = d.code ∧
    (addHelp d help).primary = d.primary := by
  constructor <;> rfl

end Oak.Diagnostics
