/-!
# The propagation form: `try` is bind

`docs/spec/10-syntax.md` §2d: in a block whose value is the enclosing
function's `Result` or `Option`, `x: T = try e` binds the `Ok`/`Some`
payload and re-raises the `Err`/`None`. The compiler lowers it before
checking to the match the standard library writes by hand
(`compiler/try.go`):

    e ? | .Err(err) => .Err(err) | .Ok(x) => { rest }

This module states what that match is: the monad's bind, on `Except` and
on `Option`. The re-raise passes the error unchanged (the `MonadError`
view of `docs/notes/algebraic-semantics-2026-09.md` §2), and propagating
then re-wrapping is the identity — `try e` as a block's value is `e`.
-/

namespace Oak.Propagation

/-- The lowered match for a `Result` function: the Err arm re-raises, the
    Ok arm continues with the rest of the block. -/
def tryResult {ε α β : Type} (e : Except ε α) (rest : α → Except ε β) : Except ε β :=
  match e with
  | .error err => .error err
  | .ok a => rest a

/-- The lowered match for an `Option` function. -/
def tryOption {α β : Type} (e : Option α) (rest : α → Option β) : Option β :=
  match e with
  | none => none
  | some a => rest a

/-- `try` on `Result` is bind. -/
theorem tryResult_eq_bind {ε α β : Type} (e : Except ε α) (rest : α → Except ε β) :
    tryResult e rest = (e >>= rest) := by
  cases e <;> rfl

/-- `try` on `Option` is bind. -/
theorem tryOption_eq_bind {α β : Type} (e : Option α) (rest : α → Option β) :
    tryOption e rest = (e >>= rest) := by
  cases e <;> rfl

/-- The re-raise passes the error unchanged: nothing after the `try` runs. -/
theorem tryResult_err {ε α β : Type} (err : ε) (rest : α → Except ε β) :
    tryResult (.error err : Except ε α) rest = .error err := rfl

/-- The Ok payload is exactly what the rest of the block receives. -/
theorem tryResult_ok {ε α β : Type} (a : α) (rest : α → Except ε β) :
    tryResult (.ok a : Except ε α) rest = rest a := rfl

/-- Propagating and re-wrapping is the identity: `try e` as a block's value
    is `e` (the lowering's `rewrap` arm, `compiler/try.go`). -/
theorem tryResult_id {ε α : Type} (e : Except ε α) :
    tryResult e (fun a => .ok a) = e := by
  cases e <;> rfl

theorem tryOption_id {α : Type} (e : Option α) :
    tryOption e (fun a => some a) = e := by
  cases e <;> rfl

/-- Two propagations in sequence associate: nesting the second inside the
    first's Ok arm is the same as propagating the composite — the monad
    law that lets the lowering nest the rest of the block one try at a
    time. -/
theorem tryResult_assoc {ε α β γ : Type} (e : Except ε α)
    (f : α → Except ε β) (g : β → Except ε γ) :
    tryResult (tryResult e f) g = tryResult e (fun a => tryResult (f a) g) := by
  cases e <;> rfl

end Oak.Propagation
