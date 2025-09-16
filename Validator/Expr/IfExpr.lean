import Validator.Expr.Pred
import Validator.Expr.Expr

inductive IfExpr μ α where
  | mk (cnd: Pred α) (thn: Fin μ)

abbrev IfExprs μ α := List (IfExpr μ α)

namespace IfExpr

def eval {α: Type} [DecidableEq α] (g: Expr.Grammar μ α) (ifExpr: IfExpr μ α) (t: α): Expr μ α :=
  match ifExpr with
  | IfExpr.mk cnd thn =>
    if Pred.eval cnd t
    then g.lookup thn
    else Expr.emptyset

def evals {α: Type} {μ: Nat} [DecidableEq α] (g: Expr.Grammar μ α) (ifExprs: IfExprs μ α) (t: α): List (Expr μ α) :=
  List.map (fun x => eval g x t) ifExprs

theorem evals_nil_is_nil {α: Type} {μ: Nat} [DecidableEq α] (g: Expr.Grammar μ α) (a: α):
  evals g (μ := μ) [] a = [] := by
  unfold evals
  simp

theorem evals_concat_is_concat {α: Type} [DecidableEq α] (g: Expr.Grammar μ α) (xs ys: IfExprs μ α) (a: α):
  evals g (xs ++ ys) a = evals g xs a ++ evals g ys a := by
  unfold evals
  simp
