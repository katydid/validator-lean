import Validator.Pred.AnyEq
import Validator.Parser.Token

abbrev TokenPred := AnyEq.Pred Token

instance : Ord TokenPred := inferInstance

instance : Repr TokenPred := inferInstance

instance : DecidableEq TokenPred := inferInstance

instance : Hashable TokenPred := inferInstance

namespace TokenPred

def eqStr (s: String): TokenPred :=
  AnyEq.Pred.eq (Token.string s)
