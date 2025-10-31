import Mathlib.Data.Vector.Snoc
import Mathlib.Data.Vector.MapLemmas

import Validator.Expr.Pred
import Validator.Expr.Regex
import Validator.Expr.Grammar

inductive IfExpr μ α where
  | mk (cnd: Pred α) (thn: Fin μ)

abbrev IfExprs μ α ν := List.Vector (IfExpr μ α) ν

namespace IfExpr

def eval {α: Type} [DecidableEq α] (g: Grammar μ α Pred) (ifExpr: IfExpr μ α) (t: α): Rule μ α Pred :=
  match ifExpr with
  | IfExpr.mk cnd thn =>
    if Pred.eval cnd t
    then g.lookup thn
    else Regex.emptyset

def evals {α: Type} {μ: Nat} [DecidableEq α] (g: Grammar μ α Pred) (ifExprs: IfExprs μ α ν) (t: α): Rules μ α Pred ν :=
  List.Vector.map (fun x => eval g x t) ifExprs

theorem evals_nil_is_nil {α: Type} {μ: Nat} [DecidableEq α] (g: Grammar μ α Pred) (a: α):
  evals g (μ := μ) List.Vector.nil a = List.Vector.nil := by
  unfold evals
  simp
