import Validator.Expr.Grammar
import Validator.Expr.Regex
import Validator.Expr.Symbol
import Validator.Derive.Enter

namespace Leave

def leave (r: Regex (Fin l)) (es: Symbol.Symbols (Pred α × Ref n) l) (ns: List.Vector Bool l): (Rule n (Pred α)) :=
  let res: List.Vector ((Pred α × Ref n) × Bool) l := Vec.zip es ns
  let r': Regex ((Pred α × Ref n) × Bool) := Symbol.replaceFrom r res
  Regex.smartDerive2 r'

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
