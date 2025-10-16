-- ImperativeCompress is a memoizable version of the validation algorithm.
-- On top of ImperativeCompress it also includes compress and expand, which is more efficient.
-- It is intended to be used for explanation purposes. This means that it gives up speed for readability. Thus it has no memoization implemented.
-- This version of the algorithm also avoids using any Monads, so it is verbose compared to a version that would use monads.

import Validator.Std.Except

import Validator.Std.Hedge
import Validator.Parser.TokenTree

import Validator.Expr.Compress
import Validator.Expr.Expr
import Validator.Expr.IfExpr

import Validator.Derive.Enter
import Validator.Learning.ImperativeLeave

namespace ImperativeCompress

-- deriv is the same as ImperativeBasic's deriv function, except that it includes the use of the compress and expand functions.
def derive [DecidableEq α] (g: Expr.Grammar μ α) (xs: Exprs μ α) (t: Hedge.Node α): Except String (Exprs μ α) :=
  if List.all xs Expr.unescapable
  then Except.ok xs
  else
    match t with
    | Hedge.Node.mk label children =>
      let ifexprs: IfExprs μ α := Enter.deriveEnter xs
      let childxs: Exprs μ α := IfExpr.evals g ifexprs label
      -- cchildxs' = compressed expressions to evaluate on children. The ' is for the exception it is wrapped in.
      let cchildxs' : Except String ((Exprs μ α) × Compress.Indices) := Compress.compress childxs
      match cchildxs' with
      | Except.error err => Except.error err
      | Except.ok (cchildxs, indices) =>
      -- cdchildxs = compressed derivatives of children. The ' is for the exception it is wrapped in.
      -- see foldLoop for an explanation of what List.foldM does.
      let cdchildxs' : Except String (Exprs μ α) := List.foldlM (derive g) cchildxs children
      match cdchildxs' with
      | Except.error err => Except.error err
      | Except.ok cdchildxs =>
      -- dchildxs = uncompressed derivatives of children. The ' is for the exception it is wrapped in.
      let dchildxs' := Compress.expand indices cdchildxs
      match dchildxs' with
      | Except.error err => Except.error err
      | Except.ok dchildxs =>
      -- dxs = derivatives of xs. The ' is for the exception it is wrapped in.
      let dxs': Except String (Exprs μ α) := ImperativeLeave.deriveLeave xs (List.map Expr.nullable dchildxs)
      match dxs' with
      | Except.error err => Except.error err
      | Except.ok dxs => Except.ok dxs

def derivs [DecidableEq α] (g: Expr.Grammar μ α) (x: Expr μ α) (forest: Hedge α): Except String (Expr μ α) :=
  -- see foldLoop for an explanation of what List.foldM does.
  let dxs := List.foldlM (derive g) [x] forest
  match dxs with
  | Except.error err => Except.error err
  | Except.ok [dx] => Except.ok dx
  | Except.ok _ => Except.error "expected one expression"

def validate [DecidableEq α] (g: Expr.Grammar μ α) (x: Expr μ α) (forest: Hedge α): Except String Bool :=
  match derivs g x forest with
  | Except.error err => Except.error err
  | Except.ok x' => Except.ok (Expr.nullable x')

def run [DecidableEq α] (g: Expr.Grammar μ α) (t: Hedge.Node α): Except String Bool :=
  validate g g.lookup0 [t]

open TokenTree (node)

#guard run
  (Expr.Grammar.singleton Expr.emptyset)
  (node "a" [node "b" [], node "c" [node "d" []]]) =
  Except.ok false

#guard run
  (Expr.Grammar.mk (μ := 2)
    (Expr.tree (Pred.eq (Token.string "a")) 1)
    #v[Expr.epsilon]
  )
  (node "a" []) =
  Except.ok true

#guard run
  (Expr.Grammar.mk (μ := 2)
    (Expr.tree (Pred.eq (Token.string "a")) 1)
    #v[Expr.epsilon]
  )
  (node "a" [node "b" []]) =
  Except.ok false

#guard run
  (Expr.Grammar.mk (μ := 3)
    (Expr.tree (Pred.eq (Token.string "a")) 1)
    #v[
      (Expr.tree (Pred.eq (Token.string "b")) 2)
      , Expr.epsilon
    ]
  )
  (node "a" [node "b" []])
  = Except.ok true

#guard run
  (Expr.Grammar.mk (μ := 3)
    (Expr.tree (Pred.eq (Token.string "a")) 1)
    #v[
      (Expr.concat
        (Expr.tree (Pred.eq (Token.string "b")) 2)
        (Expr.tree (Pred.eq (Token.string "c")) 2)
      )
      , Expr.epsilon
    ]
  )
  (node "a" [node "b" [], node "c" []]) =
  Except.ok true

#guard run
  (Expr.Grammar.mk (μ := 4)
    (Expr.tree (Pred.eq (Token.string "a")) 1)
    #v[
      (Expr.concat
        (Expr.tree (Pred.eq (Token.string "b")) 2)
        (Expr.tree (Pred.eq (Token.string "c")) 3)
      )
      , Expr.epsilon
      , (Expr.tree (Pred.eq (Token.string "d")) 2)
    ]
  )
  (node "a" [node "b" [], node "c" [node "d" []]]) =
  Except.ok true
