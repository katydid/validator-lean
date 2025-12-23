-- ImperativeBasic is a memoizable version of the validation algorithm.
-- This is intended to be as approachable as possible to imperative programmers and avoids using Monads.

import Validator.Std.Except

import Validator.Std.Hedge
import Validator.Parser.TokenTree

import Validator.Hedge.Grammar
import Validator.Hedge.IfExpr
import Validator.Regex.Regex

import Validator.Learning.ImperativeEnter
import Validator.Learning.ImperativeLeave

namespace ImperativeBasic

-- foldLoop is a more readable version of List.foldlM for imperative programmers:
private def foldLoop (deriv: List (Hedge.Grammar.Rule n φ) -> Hedge.Node α -> List (Hedge.Grammar.Rule n φ)) (start: List (Hedge.Grammar.Rule n φ)) (hedge: Hedge α): Id (List (Hedge.Grammar.Rule n φ)) := do
  let mut res := start
  for tree in hedge do
    res := deriv res tree
  return res

def derive
  (G: Hedge.Grammar n φ) (Φ: φ -> α -> Bool)
  (xs: List (Hedge.Grammar.Rule n φ)) (tree: Hedge.Node α): List (Hedge.Grammar.Rule n φ) :=
  -- If all expressions are unescapable, then simply return without look at the input tree.
  -- An example of an unescapable expression is emptyset, since its derivative is always emptyset, no matter the input.
  if List.all xs Regex.unescapable
  then xs
  else
    -- Desconstruct the tree to retrieve its label and children
    match tree with
    | Hedge.Node.mk label children =>
      -- enters is one of our two new memoizable functions.
      let ifexprs: List (Hedge.Grammar.Symbol n φ) := ImperativeEnter.deriveEnter xs
      -- childxs = expressions to evaluate on children.
      let childxs: List (Hedge.Grammar.Rule n φ) := List.map (fun x => Hedge.Grammar.evalif G Φ x label) ifexprs
      -- dchildxs = derivatives of children. The ' is for the exception it is wrapped in.
      -- see foldLoop for an explanation of what List.foldM does.
      let dchildxs: List (Hedge.Grammar.Rule n φ) := List.foldl (derive G Φ) childxs children
      -- dxs = derivatives of xs. The ' is for the exception it is wrapped in.
      -- leaves is the other one of our two new memoizable functions.
      let dxs: List (Hedge.Grammar.Rule n φ) := ImperativeLeave.deriveLeave xs (List.map Regex.null dchildxs)
      dxs

def derivs
  (G: Hedge.Grammar n φ) (Φ: φ -> α -> Bool)
  (x: Hedge.Grammar.Rule n φ) (hedge: Hedge α): Except String (Hedge.Grammar.Rule n φ) :=
  -- see foldLoop for an explanation of what List.foldM does.
  let dxs := List.foldl (derive G Φ) [x] hedge
  match dxs with
  | [dx] => Except.ok dx
  | _ => Except.error "expected one expression"

def validate
  (G: Hedge.Grammar n φ) (Φ: φ -> α -> Bool)
  (x: Hedge.Grammar.Rule n φ) (hedge: Hedge α): Except String Bool :=
  match derivs G Φ x hedge with
  | Except.error err => Except.error err
  | Except.ok x' => Except.ok (Hedge.Grammar.Rule.null x')

def run [DecidableEq α]
  (G: Hedge.Grammar n (AnyEq.Pred α)) (t: Hedge.Node α): Except String Bool :=
  validate G AnyEq.Pred.evalb G.start [t]

-- Tests

open TokenTree (node)

#guard run
  (Hedge.Grammar.singleton Regex.emptyset)
  (node "a" [node "b" [], node "c" [node "d" []]]) =
  Except.ok false

#guard run
  (Hedge.Grammar.mk (n := 1)
    (Regex.symbol (AnyEq.Pred.eq (Token.string "a"), 0))
    #vec[Regex.emptystr]
  )
  (node "a" []) =
  Except.ok true

#guard run
  (Hedge.Grammar.mk (n := 1)
    (Regex.symbol (AnyEq.Pred.eq (Token.string "a"), 0))
    #vec[Regex.emptystr]
  )
  (node "a" [node "b" []]) =
  Except.ok false

#guard run
  (Hedge.Grammar.mk (n := 2)
    (Regex.symbol (AnyEq.Pred.eq (Token.string "a"), 0))
    #vec[
      (Regex.symbol (AnyEq.Pred.eq (Token.string "b"), 1))
      , Regex.emptystr
    ]
  )
  (node "a" [node "b" []])
  = Except.ok true

#guard run
  (Hedge.Grammar.mk (n := 2)
    (Regex.symbol (AnyEq.Pred.eq (Token.string "a"), 0))
    #vec[
      (Regex.concat
        (Regex.symbol (AnyEq.Pred.eq (Token.string "b"), 1))
        (Regex.symbol (AnyEq.Pred.eq (Token.string "c"), 1))
      )
      , Regex.emptystr
    ]
  )
  (node "a" [node "b" [], node "c" []]) =
  Except.ok true

#guard run
  (Hedge.Grammar.mk (n := 3)
    (Regex.symbol (AnyEq.Pred.eq (Token.string "a"), 0))
    #vec[
      (Regex.concat
        (Regex.symbol (AnyEq.Pred.eq (Token.string "b"), 1))
        (Regex.symbol (AnyEq.Pred.eq (Token.string "c"), 2))
      )
      , Regex.emptystr
      , (Regex.symbol (AnyEq.Pred.eq (Token.string "d"), 1))
    ]
  )
  (node "a" [node "b" [], node "c" [node "d" []]]) =
  Except.ok true
