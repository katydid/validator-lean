import Validator.Parser.Hint
import Validator.Parser.LTree
import Validator.Parser.Parser
import Validator.Parser.Stack
import Validator.Parser.Token

import Validator.Expr.Pred

inductive Expr where
  | emptyset
  | epsilon
  | tree (labelPred: Pred) (childrenExpr: Expr)
  | or (y z: Expr)
  | concat (y z: Expr)
  | star (y: Expr)
  deriving DecidableEq, Ord, Repr

namespace Expr

def nullable (x: Expr): Bool :=
  match x with
  | Expr.emptyset => false
  | Expr.epsilon => true
  | Expr.tree _ _ => false
  | Expr.or y z => nullable y || nullable z
  | Expr.concat y z => nullable y && nullable z
  | Expr.star _ => true

def unescapable (x: Expr): Bool :=
  match x with
  | Expr.emptyset => true
  | _ => false
