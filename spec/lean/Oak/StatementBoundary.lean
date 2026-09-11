/-!
# Line breaks and statement boundaries

`docs/spec/10-syntax.md` §4a: a call or an index never continues across a
line break — a line that begins with `(` or `[` begins a new statement — and
the same holds for `-`: a line that begins with a minus negates what follows
rather than subtracting from the line above. An operator that continues an
expression sits at the *end* of a line. The parser applies the rule in one
place (`peekPrecedence`: the next token binds with the lowest precedence when
it is one of these kinds and sits on a later line than the current token).

This file models that rule alone — the decision "does this token continue
the expression on the previous line?" — over tokens tagged with their kind
and line, and proves the properties the spec states: the decision is a
function of the two tokens' lines and the next token's kind, a token on the
same line is never a boundary, a boundary kind on a later line always is, and
the three worked examples segment as the spec says. The grammar of what
follows the boundary is the parser's; only the boundary is modeled.
-/

namespace Oak.StatementBoundary

/-- Token kinds relevant to the rule: the three boundary kinds, and every
other token. -/
inductive Kind where
  | lparen
  | lbrack
  | minus
  | other
  deriving DecidableEq, Repr

structure Token where
  kind : Kind
  line : Nat
  deriving DecidableEq, Repr

/-- The kinds that begin a new statement when they begin a line. -/
def BoundaryKind : Kind -> Prop
  | .lparen => True
  | .lbrack => True
  | .minus => True
  | .other => False

instance (k : Kind) : Decidable (BoundaryKind k) := by
  cases k <;> simp only [BoundaryKind] <;> infer_instance

/-- `boundary prev next` holds when `next` cannot continue the expression
that `prev` ends: it is a boundary kind on a later line. -/
def boundary (prev next : Token) : Bool :=
  decide (BoundaryKind next.kind) && decide (prev.line < next.line)

/-- Segment a token stream into statements at the boundaries. Every token
lands in exactly one segment, in order. -/
def segment : List Token -> List (List Token)
  | [] => []
  | t :: rest => go t [t] rest
where
  go : Token -> List Token -> List Token -> List (List Token)
    | _, current, [] => [current.reverse]
    | prev, current, next :: rest =>
        if boundary prev next then current.reverse :: go next [next] rest
        else go next (next :: current) rest

/-- A token on the same line as its predecessor never begins a statement,
whatever its kind. -/
theorem same_line_continues (prev next : Token) (h : prev.line = next.line) :
    boundary prev next = false := by
  simp [boundary, h]

/-- A boundary kind on a later line always begins a statement. -/
theorem later_line_boundary (prev next : Token) (hk : BoundaryKind next.kind)
    (hl : prev.line < next.line) : boundary prev next = true := by
  simp [boundary, hk, hl]

/-- Any other kind continues the expression even across a line break: the
rule is exactly about the three kinds, nothing wider. -/
theorem other_kind_continues (prev next : Token) (hk : next.kind = .other) :
    boundary prev next = false := by
  simp [boundary, hk, BoundaryKind]

/-- The rule reads only the next token's kind and the two lines: tokens that
agree on those agree on the decision. -/
theorem boundary_depends_on_kind_and_lines (p p' n n' : Token)
    (hk : n.kind = n'.kind) (hp : p.line = p'.line) (hn : n.line = n'.line) :
    boundary p n = boundary p' n' := by
  simp [boundary, hk, hp, hn]

/-- Segmentation loses no token and keeps their order. -/
theorem segment_go_join (prev : Token) (current rest : List Token) :
    (segment.go prev current rest).flatten = current.reverse ++ rest := by
  induction rest generalizing prev current with
  | nil => simp [segment.go]
  | cons next rest ih =>
      simp only [segment.go]
      split
      · simp [ih]
      · rw [ih]
        simp

theorem segment_join (tokens : List Token) : (segment tokens).flatten = tokens := by
  cases tokens with
  | nil => rfl
  | cons t rest => simp [segment, segment_go_join]

/-! ## The spec's examples

`f(x)` on one line and `(a + b) == c` on the next are two statements; `x`
then `-y` on the next line are two statements; `1 -` at the end of a line
followed by `2` is one statement. -/

def f_x_paren : List Token :=
  [⟨.other, 1⟩, ⟨.lparen, 1⟩, ⟨.other, 1⟩, ⟨.other, 1⟩,   -- f ( x )
   ⟨.lparen, 2⟩, ⟨.other, 2⟩, ⟨.other, 2⟩, ⟨.other, 2⟩, ⟨.other, 2⟩]  -- ( a + b ) ...

theorem call_does_not_continue_across_lines :
    (segment f_x_paren).length = 2 := by
  decide

def x_then_negation : List Token :=
  [⟨.other, 1⟩, ⟨.minus, 2⟩, ⟨.other, 2⟩]   -- x ⏎ - y

theorem line_start_minus_is_new_statement :
    (segment x_then_negation).length = 2 := by
  decide

def trailing_minus : List Token :=
  [⟨.other, 1⟩, ⟨.minus, 1⟩, ⟨.other, 2⟩]   -- 1 - ⏎ 2

theorem line_end_minus_continues :
    (segment trailing_minus).length = 1 := by
  decide

end Oak.StatementBoundary
