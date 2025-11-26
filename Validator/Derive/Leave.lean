import Validator.Expr.Grammar
import Validator.Expr.Regex
import Validator.Expr.Symbol
import Validator.Derive.Enter

namespace Leave

def leave (r: Regex (Fin l)) (es: Symbol.Symbols (Pred α × Ref n) l) (ns: List.Vector Bool l): (Rule n (Pred α)) :=
  match r with
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
  (xs: List.Vector (Regex (Fin l1)) l2)
  (es: Symbol.Symbols (Pred α × Ref n) l1)
  (ns: List.Vector Bool l1)
  : (Rules n (Pred α) l2) :=
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
  (xs: Rules n (Pred α) l)
  (ns: List.Vector Bool (Symbol.nums xs))
  : (Rules n (Pred α) l) :=
  let (regexes, symbols) := Symbol.extracts xs List.Vector.nil
  deriveLeave regexes symbols (Symbol.Symbols.cast ns (by simp only [zero_add]))

def deriveLeaveM [Monad m] {n: Nat} {l: Nat} (xs: Rules n (Pred α) l) (ns: List.Vector Bool (Symbol.nums xs)): m (Rules n (Pred α) l) := do
  return deriveLeaves xs ns

class DeriveLeaveM (m: Type -> Type u) (n: Nat) (α: outParam Type) where
  deriveLeaveM {l: Nat} (xs: Rules n (Pred α) l) (ns: List.Vector Bool (Symbol.nums xs)): m (Rules n (Pred α) l)
