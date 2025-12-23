import Validator.Std.Vec

import Validator.Regex.Regex
import Validator.Hedge.Grammar

abbrev IfExprs n φ l := Vec (Symbol n φ) l

namespace IfExpr

def eval {α: Type}
  (G: Grammar n φ) (Φ: φ -> α -> Bool)
  (ifExpr: Symbol n φ) (t: α): Rule n φ :=
  match ifExpr with
  | (cnd, thn) =>
    if Φ cnd t
    then G.lookup thn
    else Regex.emptyset

def evals {α: Type} {n: Nat}
  (G: Grammar n φ) (Φ: φ -> α -> Bool)
  (ifExprs: IfExprs n φ l) (t: α): Rules n φ l :=
  Vec.map ifExprs (fun x => eval G Φ x t)

theorem evals_nil_is_nil {α: Type} {n: Nat}
  (G: Grammar n φ) (Φ: φ -> α -> Bool)
  (a: α):
  evals G Φ (n := n) Vec.nil a = Vec.nil := by
  unfold evals
  simp only [Vec.map_nil]
