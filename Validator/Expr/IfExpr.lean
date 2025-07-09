import Validator.Expr.Pred
import Validator.Expr.Expr

inductive IfExpr where
  | mk (cnd: Pred) (thn: Expr) (els: Expr)

namespace IfExpr

def eval (ifExpr: IfExpr) (t: Token): Expr :=
  match ifExpr with
  | IfExpr.mk cnd thn els =>
    if Pred.eval cnd t
    then thn
    else els

def evals (ifExprs: List IfExpr) (t: Token): List Expr :=
  List.map (fun x => eval x t) ifExprs
