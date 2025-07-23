import Validator.Expr.Pred
import Validator.Parser.Token

abbrev TokenPred := Pred Token

instance : Ord TokenPred := inferInstance

instance : Repr TokenPred := inferInstance

instance : DecidableEq TokenPred := inferInstance

instance : Hashable TokenPred := inferInstance

namespace TokenPred

def eqStr (s: String): TokenPred :=
  Pred.eq (Token.string s)
