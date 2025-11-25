import Validator.Expr.Grammar
import Validator.Expr.Regex
import Validator.Expr.Symbol
import Validator.Derive.Enter

namespace Leave

def leave (x: Regex (Fin ν)) (es: Symbol.Symbols (Pred α × Ref μ) ν) (ns: List.Vector Bool ν): (Rule μ α Pred) :=
  match x with
  | Regex.emptyset => Regex.emptyset
  | Regex.emptystr => Regex.emptyset
  | Regex.symbol i =>
    if List.Vector.get ns i
    then Regex.emptystr
    else Regex.emptyset
  | Regex.or r1 r2 =>
    Regex.smartOr (leave r1 es ns) (leave r2 es ns)
  | Regex.concat r1 r2 =>
    if Regex.nullable r1
    then
      Regex.smartOr (Regex.smartConcat (leave r1 es ns) (Symbol.replaceFrom r2 es)) (leave r2 es ns)
    else
      Regex.smartConcat (leave r1 es ns) (Symbol.replaceFrom r2 es)
  | Regex.star r1 =>
      Regex.smartConcat (leave r1 es ns) (Regex.smartStar (Symbol.replaceFrom r1 es))

-- deriveLeave takes a vector of expressions and vector of bools.
-- The vectors of bools represent the nullability of the derived child expressions.
-- Each bool will then replace each symbol expression with either an emptystr or emptyset.
def deriveLeave
  (xs: List.Vector (Regex (Fin ν)) μ1)
  (es: Symbol.Symbols (Pred α × Ref μ) ν)
  (ns: List.Vector Bool ν)
  : (Rules μ α Pred μ1) :=
  match xs with
  | ⟨[], h⟩ => ⟨[], h⟩
  | ⟨x::xs, h⟩ =>
    Symbol.Symbols.cast
      (List.Vector.cons
        (leave x es ns)
        (deriveLeave ⟨xs, congrArg Nat.pred h⟩ es ns))
      (by
        simp only [List.length_cons] at h
        rw [<- h]
        simp only [Nat.pred_eq_sub_one, add_tsub_cancel_right, Nat.succ_eq_add_one]
      )

def deriveLeaves
  (xs: Rules μ α Pred ν)
  (ns: List.Vector Bool (Symbol.nums xs))
  : (Rules μ α Pred ν) :=
  let (regexes, symbols) := Symbol.extracts xs List.Vector.nil
  deriveLeave regexes symbols (Symbol.Symbols.cast ns (by simp only [zero_add]))

def deriveLeaveM [Monad m] {μ: Nat} {ν: Nat} (xs: Rules μ α Pred ν) (ns: List.Vector Bool (Symbol.nums xs)): m (Rules μ α Pred ν) := do
  return deriveLeaves xs ns

class DeriveLeaveM (m: Type -> Type u) (μ: Nat) (α: outParam Type) where
  deriveLeaveM {ν: Nat} (xs: Rules μ α Pred ν) (ns: List.Vector Bool (Symbol.nums xs)): m (Rules μ α Pred ν)
