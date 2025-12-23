import Validator.Std.Hedge

import Validator.Regex.Room
import Validator.Hedge.Grammar
import Validator.Hedge.IfExpr

namespace Hedge.Room

def derive {α: Type}
  (G: Grammar n φ) (Φ: φ -> α -> Bool)
  (r: Hedge.Grammar.Rule n φ) (x: Hedge.Node α): Hedge.Grammar.Rule n φ :=
  Regex.Room.derive (fun (symbol: Hedge.Grammar.Symbol n φ) =>
    match x with
    | Hedge.Node.mk label children =>
      let ifExpr: Hedge.Grammar.Symbol n φ := symbol
      let childr: Hedge.Grammar.Rule n φ := Hedge.Grammar.evalif G Φ ifExpr label
      let dchildr: Hedge.Grammar.Rule n φ := List.foldl (derive G Φ) childr children
      Hedge.Grammar.Rule.null dchildr
  ) r
