import Validator.Expr.Pred
import Validator.Capturer.CaptureExpr

inductive CaptureIfExpr where
  | mk (cnd: Pred) (thn: CaptureExpr) (els: CaptureExpr)

namespace CaptureIfExpr

def eval (ifExpr: CaptureIfExpr) (t: Token): CaptureExpr :=
  match ifExpr with
  | CaptureIfExpr.mk cnd thn els =>
    if Pred.eval cnd t
    then thn
    else els

def evals (ifExprs: List CaptureIfExpr) (t: Token): List CaptureExpr :=
  List.map (fun x => eval x t) ifExprs
