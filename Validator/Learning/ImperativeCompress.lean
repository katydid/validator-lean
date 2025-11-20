-- ImperativeCompress is a memoizable version of the validation algorithm.
-- On top of ImperativeCompress it also includes compress and expand, which is more efficient.
-- It is intended to be used for explanation purposes. This means that it gives up speed for readability. Thus it has no memoization implemented.
-- This version of the algorithm also avoids using any Monads, so it is verbose compared to a version that would use monads.

import Validator.Std.Except

import Validator.Std.Hedge
import Validator.Parser.TokenTree

import Validator.Expr.Compress
import Validator.Expr.Grammar
import Validator.Expr.IfExpr
import Validator.Expr.Regex

import Validator.Derive.Enter
import Validator.Learning.ImperativeLeave

namespace ImperativeCompress

inductive Index where
 | val (n: Nat)
 | emptyset

def indexOf [DecidableEq α] (xs: List (Regex (Pred α × Ref μ))) (y: (Rule μ α Pred)): Except String Index :=
  match y with
  | Regex.emptyset => Except.ok Index.emptyset
  | _ =>
    match List.idxOf? y xs with
    | Option.none => Except.error "indexOf: unable to find expression"
    | Option.some idx => Except.ok (Index.val idx)

def ofIndex' (xs: List (Rule μ α Pred)) (index: Nat): Except String (Rule μ α Pred) :=
  match xs with
  | [] => Except.error "index overflow"
  | x::xs' =>
    match index with
    | 0 => Except.ok x
    | (n' + 1) => ofIndex' xs' n'

def ofIndex (xs: List (Rule μ α Pred)) (index: Index): Except String (Rule μ α Pred) :=
  match index with
  | Index.emptyset => Except.ok Regex.emptyset
  | Index.val n =>
    ofIndex' xs n

-- Indices represents compressed indexes
-- that resulted from compressing a list of expressions.
-- This can be used to expanded to a list of expressions.
inductive Indices where
  | mk (indices: List Index)

def compressed [DecidableEq α] (xs: Rules μ α Pred ν): Nat :=
  (List.erase (List.eraseReps xs.toList) Regex.emptyset).length

-- compress compresses a list of expressions.
def compress [DecidableEq α] (xs: List (Rule μ α Pred)): Except String ((List (Rule μ α Pred)) × Indices) := do
  -- sort to increase chance of cache hit
  -- TODO: let sxs := List.mergeSort xs

  -- remove duplicates
  let sxs' := List.eraseReps xs

  -- remove unescapable expressions, currently only emptyset
  let sxs'' := List.erase sxs' Regex.emptyset

  -- find all indexes of the original expressions in the compressed expressions
  let indexes: List Index <- List.mapM (indexOf sxs'') xs
  return (
    Subtype.mk
      sxs'' (by
        simp only [sxs'', sxs']
        rfl
      ),
    Indices.mk indexes
  )

-- expand expands a list of expressions.
def expand (indices: Indices) (xs: List (Rule μ α Pred)): Except String (List (Rule μ α Pred)) :=
  match indices with
  | Indices.mk indexes =>
    match MonadExcept.ofExcept (List.mapM (ofIndex xs) indexes) with
    | Except.error e => Except.error e
    | Except.ok k => Except.ok k

-- deriv is the same as ImperativeBasic's deriv function, except that it includes the use of the compress and expand functions.
def derive [DecidableEq α] (g: Grammar μ α Pred) (xs: List (Rule μ α Pred)) (t: Hedge.Node α): Except String (List (Rule μ α Pred)) :=
  if List.all xs Regex.unescapable
  then Except.ok xs
  else
    match t with
    | Hedge.Node.mk label children =>
      let ifexprs: List (IfExpr μ α) := Enter.deriveEnter_list xs
      -- List.Vector.map (fun x => eval g x t) ifExprs
      let childxs: List (Rule μ α Pred) := List.map (fun x => IfExpr.eval g x label) ifexprs
      -- cchildxs' = compressed expressions to evaluate on children. The ' is for the exception it is wrapped in.
      let cchildxs' : Except String ((List (Rule μ α Pred)) × Indices) := compress childxs
      match cchildxs' with
      | Except.error err => Except.error err
      | Except.ok (cchildxs, indices) =>
      -- cdchildxs = compressed derivatives of children. The ' is for the exception it is wrapped in.
      -- see foldLoop for an explanation of what List.foldM does.
      let cdchildxs' : Except String (List (Rule μ α Pred)) := List.foldlM (derive g) cchildxs children
      match cdchildxs' with
      | Except.error err => Except.error err
      | Except.ok cdchildxs =>
      -- dchildxs = uncompressed derivatives of children. The ' is for the exception it is wrapped in.
      let dchildxs' := expand indices cdchildxs
      match dchildxs' with
      | Except.error err => Except.error err
      | Except.ok dchildxs =>
      -- dxs = derivatives of xs. The ' is for the exception it is wrapped in.
      let dxs: List (Rule μ α Pred) := ImperativeLeave.deriveLeave xs (List.map Rule.nullable dchildxs)
      Except.ok dxs

def derivs [DecidableEq α] (g: Grammar μ α Pred) (x: Rule μ α Pred) (hedge: Hedge α): Except String (Rule μ α Pred) :=
  -- see foldLoop for an explanation of what List.foldM does.
  let dxs := List.foldlM (derive g) [x] hedge
  match dxs with
  | Except.error err => Except.error err
  | Except.ok [dx] => Except.ok dx
  | Except.ok _ => Except.error "expected one expression"

def validate [DecidableEq α] (g: Grammar μ α Pred) (x: Rule μ α Pred) (hedge: Hedge α): Except String Bool :=
  match derivs g x hedge with
  | Except.error err => Except.error err
  | Except.ok x' => Except.ok (Regex.nullable x')

def run [DecidableEq α] (g: Grammar μ α Pred) (t: Hedge.Node α): Except String Bool :=
  validate g g.start [t]

-- Tests

open TokenTree (node)

#guard run
  (Grammar.singleton Regex.emptyset)
  (node "a" [node "b" [], node "c" [node "d" []]]) =
  Except.ok false

#guard run
  (Grammar.mk (μ := 1)
    (Regex.symbol (Pred.eq (Token.string "a"), 0))
    #v[Regex.emptystr]
  )
  (node "a" []) =
  Except.ok true

#guard run
  (Grammar.mk (μ := 1)
    (Regex.symbol (Pred.eq (Token.string "a"), 0))
    #v[Regex.emptystr]
  )
  (node "a" [node "b" []]) =
  Except.ok false

#guard run
  (Grammar.mk (μ := 2)
    (Regex.symbol (Pred.eq (Token.string "a"), 0))
    #v[
      (Regex.symbol (Pred.eq (Token.string "b"), 1))
      , Regex.emptystr
    ]
  )
  (node "a" [node "b" []])
  = Except.ok true

#guard run
  (Grammar.mk (μ := 2)
    (Regex.symbol (Pred.eq (Token.string "a"), 0))
    #v[
      (Regex.concat
        (Regex.symbol (Pred.eq (Token.string "b"), 1))
        (Regex.symbol (Pred.eq (Token.string "c"), 1))
      )
      , Regex.emptystr
    ]
  )
  (node "a" [node "b" [], node "c" []]) =
  Except.ok true

#guard run
  (Grammar.mk (μ := 3)
    (Regex.symbol (Pred.eq (Token.string "a"), 0))
    #v[
      (Regex.concat
        (Regex.symbol (Pred.eq (Token.string "b"), 1))
        (Regex.symbol (Pred.eq (Token.string "c"), 2))
      )
      , Regex.emptystr
      , (Regex.symbol (Pred.eq (Token.string "d"), 1))
    ]
  )
  (node "a" [node "b" [], node "c" [node "d" []]]) =
  Except.ok true
