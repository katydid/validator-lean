import Validator.Parser.Hint
import Validator.Parser.LTree
import Validator.Parser.Parser
import Validator.Parser.Stack
import Validator.Parser.Token

import Validator.Expr.Pred

inductive Expr where
  | emptyset
  | epsilon
  | tree (labelPred: Predicate) (childrenExpr: Expr)
  | or (y z: Expr)
  | concat (y z: Expr)
  | star (y: Expr)

namespace Expr

def nullable (x: Expr): Bool :=
  match x with
  | Expr.emptyset => False
  | Expr.epsilon => True
  | Expr.tree _ _ => False
  | Expr.or y z => nullable y || nullable z
  | Expr.concat y z => nullable y && nullable z
  | Expr.star _ => True

def unescapable (x: Expr): Bool :=
  match x with
  | Expr.emptyset => true
  | _ => false
