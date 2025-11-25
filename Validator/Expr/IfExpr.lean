import Mathlib.Data.Vector.Snoc
import Mathlib.Data.Vector.MapLemmas

import Validator.Expr.Pred
import Validator.Expr.Regex
import Validator.Expr.Grammar

inductive IfExpr n α where
  | mk (cnd: Pred α) (thn: Fin n)

abbrev IfExprs n α l := List.Vector (IfExpr n α) l

namespace IfExpr

def eval {α: Type} [DecidableEq α] (g: Grammar n α Pred) (ifExpr: IfExpr n α) (t: α): Rule n α Pred :=
  match ifExpr with
  | IfExpr.mk cnd thn =>
    if Pred.eval cnd t
    then g.lookup thn
    else Regex.emptyset

def evals {α: Type} {n: Nat} [DecidableEq α] (g: Grammar n α Pred) (ifExprs: IfExprs n α l) (t: α): Rules n α Pred l :=
  List.Vector.map (fun x => eval g x t) ifExprs

theorem evals_nil_is_nil {α: Type} {n: Nat} [DecidableEq α] (g: Grammar n α Pred) (a: α):
  evals g (n := n) List.Vector.nil a = List.Vector.nil := by
  unfold evals
  simp
