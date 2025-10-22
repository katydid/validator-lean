import Validator.Expr.Pred
import Validator.Expr.Regex
import Validator.Expr.Grammar

inductive IfExpr μ α where
  | mk (cnd: Pred α) (thn: Fin μ)

abbrev IfExprs μ α := List (IfExpr μ α)

namespace IfExpr

def eval {α: Type} [DecidableEq α] (g: Grammar μ α Pred) (ifExpr: IfExpr μ α) (t: α): Rule μ α Pred :=
  match ifExpr with
  | IfExpr.mk cnd thn =>
    if Pred.eval cnd t
    then g.lookup thn
    else Regex.emptyset

def evals {α: Type} {μ: Nat} [DecidableEq α] (g: Grammar μ α Pred) (ifExprs: IfExprs μ α) (t: α): List (Rule μ α Pred) :=
  List.map (fun x => eval g x t) ifExprs

theorem evals_nil_is_nil {α: Type} {μ: Nat} [DecidableEq α] (g: Grammar μ α Pred) (a: α):
  evals g (μ := μ) [] a = [] := by
  unfold evals
  simp

theorem evals_concat_is_concat {α: Type} [DecidableEq α] (g: Grammar μ α Pred) (xs ys: IfExprs μ α) (a: α):
  evals g (xs ++ ys) a = evals g xs a ++ evals g ys a := by
  unfold evals
  simp
