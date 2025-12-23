import Validator.Std.Vec

import Validator.Regex.Regex
import Validator.Hedge.Grammar
import Validator.Hedge.Types

namespace Hedge.Grammar

def evalif {α: Type}
  (G: Hedge.Grammar n φ) (Φ: φ -> α -> Bool)
  (ifExpr: Symbol n φ) (t: α): Rule n φ :=
  match ifExpr with
  | (cnd, thn) =>
    if Φ cnd t
    then G.lookup thn
    else Regex.emptyset

def evalifs {α: Type} {n: Nat}
  (G: Grammar n φ) (Φ: φ -> α -> Bool)
  (ifExprs: Symbols n φ l) (t: α): Rules n φ l :=
  Vec.map ifExprs (fun x => evalif G Φ x t)

theorem evalifs_nil_is_nil {α: Type} {n: Nat}
  (G: Grammar n φ) (Φ: φ -> α -> Bool)
  (a: α):
  evalifs G Φ (n := n) Vec.nil a = Vec.nil := by
  unfold evalifs
  simp only [Vec.map_nil]
