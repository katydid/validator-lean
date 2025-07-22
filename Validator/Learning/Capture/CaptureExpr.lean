-- This extends the data type in https://github.com/katydid/regex-deriv-lean/blob/main/RegexDeriv/Group/Capture/CaptureRegex.lean
-- It extends the data type to handle capturing on ParseTrees.

import Validator.Parser.Token
import Validator.Parser.ParseTree

-- CaptureExpr includes capturing groups
inductive CaptureExpr where
  | emptyset
  | epsilon
  -- matched is extended to trees
  | matched (tok: Token) (childExpr: CaptureExpr)
  | tree (tok: Token) (childExpr: CaptureExpr)
  | or (y z: CaptureExpr)
  | concat (y z: CaptureExpr)
  | star (y: CaptureExpr)
  | group (id: Nat) (x: CaptureExpr)
  deriving DecidableEq, Ord, Repr, Hashable

def CaptureExpr.nullable (x: CaptureExpr): Bool :=
  match x with
  | CaptureExpr.emptyset => false
  | CaptureExpr.epsilon => true
  -- matched is technically the same as epsilon, except that it stores the matched token and childExpr.
  | CaptureExpr.matched _ _ => true
  | CaptureExpr.tree _ _ => false
  | CaptureExpr.or y z => nullable y || nullable z
  | CaptureExpr.concat y z => nullable y && nullable z
  | CaptureExpr.star _ => true
  | CaptureExpr.group _ y => nullable y

def CaptureExpr.unescapable (x: CaptureExpr): Bool :=
  match x with
  | CaptureExpr.emptyset => true
  | _ => false

-- smartOr is a smart constructor for the or operator.
def CaptureExpr.smartOr (x y: CaptureExpr): CaptureExpr :=
  match x with
  | CaptureExpr.emptyset => y
  | _ =>
    match y with
    | CaptureExpr.emptyset => x
    | _ => CaptureExpr.or x y

-- smartConcat is a smart constructor for the concat operator.
def CaptureExpr.smartConcat (x y: CaptureExpr): CaptureExpr :=
  match x with
  | CaptureExpr.emptyset => CaptureExpr.emptyset
  | _ =>
    match y with
    | CaptureExpr.emptyset => CaptureExpr.emptyset
    | _ => CaptureExpr.concat x y

-- smartStar is a smart constructor for the star operator.
def CaptureExpr.smartStar (x: CaptureExpr): CaptureExpr :=
  match x with
  | CaptureExpr.star _ => x
  | _ => CaptureExpr.star x
