import Validator.Expr.Pred
import Validator.Capturer.CaptureExpr

inductive CaptureIfExpr α where
  | mk (cnd: Pred α) (thn: CaptureExpr α) (els: CaptureExpr α)

abbrev CaptureIfExprs α := List (CaptureIfExpr α)

namespace CaptureIfExpr

def eval [DecidableEq α] (ifExpr: CaptureIfExpr α) (t: α): CaptureExpr α :=
  match ifExpr with
  | CaptureIfExpr.mk cnd thn els =>
    if Pred.eval cnd t
    then thn
    else els

def evals [DecidableEq α] (ifExprs: CaptureIfExprs α) (t: α): CaptureExprs α :=
  List.map (fun x => eval x t) ifExprs
