import Validator.Expr.Expr

inductive IfExpr where
  | mk (cnd: Predicate) (thn: Expr) (els: Expr)

def evalIfExpr (ifExpr: IfExpr) (t: Token): Expr :=
  match ifExpr with
  | IfExpr.mk cnd thn els =>
    if cnd t
    then thn
    else els
