import Validator.Expr.Pred
import Validator.Expr.Expr

inductive IfExpr α where
  | mk (cnd: Pred α) (thn: Expr α) (els: Expr α)

abbrev IfExprs α := List (IfExpr α)

namespace IfExpr

def eval [BEq α] [DecidableEq α] (ifExpr: IfExpr α) (t: α): Expr α :=
  match ifExpr with
  | IfExpr.mk cnd thn els =>
    if Pred.eval cnd t
    then thn
    else els

def evals [BEq α] [DecidableEq α] (ifExprs: IfExprs α) (t: α): List (Expr α) :=
  List.map (fun x => eval x t) ifExprs
