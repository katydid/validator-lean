import Validator.Std.Vec

import Validator.Expr.Pred
import Validator.Expr.Regex
import Validator.Expr.Grammar

inductive IfExpr n α where
  | mk (cnd: Pred α) (thn: Fin n)

abbrev IfExprs n α l := Vec (IfExpr n α) l

namespace IfExpr

def eval {α: Type} [DecidableEq α] (g: Grammar n (Pred α)) (ifExpr: IfExpr n α) (t: α): Rule n (Pred α) :=
  match ifExpr with
  | IfExpr.mk cnd thn =>
    if Pred.eval cnd t
    then g.lookup thn
    else Regex.emptyset

def evals {α: Type} {n: Nat} [DecidableEq α] (g: Grammar n (Pred α)) (ifExprs: IfExprs n α l) (t: α): Rules n (Pred α) l :=
  Vec.map ifExprs (fun x => eval g x t)

theorem evals_nil_is_nil {α: Type} {n: Nat} [DecidableEq α] (g: Grammar n (Pred α)) (a: α):
  evals g (n := n) Vec.nil a = Vec.nil := by
  unfold evals
  simp only [Vec.map_nil]
