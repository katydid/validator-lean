import Validator.Std.Vec

import Validator.Expr.Regex
import Validator.Expr.Grammar

abbrev IfExpr n φ := (φ × Fin n)

abbrev IfExprs n φ l := Vec (IfExpr n φ) l

namespace IfExpr

def eval {α: Type}
  (g: Grammar n φ) (Φ: φ -> α -> Prop) [DecidableRel Φ]
  (ifExpr: IfExpr n φ) (t: α): Rule n φ :=
  match ifExpr with
  | (cnd, thn) =>
    if Φ cnd t
    then g.lookup thn
    else Regex.emptyset

def evals {α: Type} {n: Nat}
  (g: Grammar n φ) (Φ: φ -> α -> Prop) [DecidableRel Φ]
  (ifExprs: IfExprs n φ l) (t: α): Rules n φ l :=
  Vec.map ifExprs (fun x => eval g Φ x t)

theorem evals_nil_is_nil {α: Type} {n: Nat}
  (g: Grammar n φ) (Φ: φ -> α -> Prop) [DecidableRel Φ]
  (a: α):
  evals g Φ (n := n) Vec.nil a = Vec.nil := by
  unfold evals
  simp only [Vec.map_nil]
