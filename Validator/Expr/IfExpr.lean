import Validator.Std.Linter.DetectClassical

import Validator.Expr.Pred
import Validator.Expr.Expr

inductive IfExpr α where
  | mk (cnd: Pred α) (thn: Expr α) (els: Expr α)

abbrev IfExprs α := List (IfExpr α)

namespace IfExpr

def eval {α: Type} [DecidableEq α] (ifExpr: IfExpr α) (t: α): Expr α :=
  match ifExpr with
  | IfExpr.mk cnd thn els =>
    if Pred.eval cnd t
    then thn
    else els

def evals {α: Type} [DecidableEq α] (ifExprs: IfExprs α) (t: α): List (Expr α) :=
  List.map (fun x => eval x t) ifExprs

theorem evals_nil_is_nil {α: Type} [DecidableEq α] (a: α):
  evals [] a = [] := by
  unfold evals
  simp

theorem evals_concat_is_concat {α: Type} [DecidableEq α] (xs ys: IfExprs α) (a: α):
  evals (xs ++ ys) a = evals xs a ++ evals ys a := by
  unfold evals
  simp
