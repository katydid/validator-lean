-- Basic is a memoizable version of the validation algorithm.
-- It is intended to be used for explanation purposes. This means that it gives up speed for readability. Thus it has no memoization implemented.
-- This version of the algorithm uses Monads to create a more concisely readible version of the algorithm.

import Validator.Std.Except
import Validator.Std.Hedge
import Validator.Std.Vec

import Validator.Parser.TokenTree

import Validator.Expr.Grammar
import Validator.Expr.IfExpr
import Validator.Expr.Language

import Validator.Derive.Enter
import Validator.Derive.Leave

namespace Basicer

-- TODO: prove termination
partial def derives_preds {α: Type} [DecidableEq α] (g: Grammar n (Pred α)) (rs: Rules n (Pred α) l) (t: Hedge.Node α): Rules n (Pred α) l :=
  Symbol.derives_preds (fun {l': Nat} (preds: Vec (Pred α × Ref n) l') (a: Hedge.Node α) =>
    match a with
    | Hedge.Node.mk label children =>
      let ifExprs: IfExprs n α l' := Vec.map
        (fun (pred, ref) => IfExpr.mk pred ref)
        preds
      let childxs: Rules n (Pred α) l' := IfExpr.evals g ifExprs label
      let dchildxs: Rules n (Pred α) l' := List.foldl (derives_preds g) childxs children
      Vec.map Rule.nullable dchildxs
  ) rs t

def derive {α: Type} [DecidableEq α] (g: Grammar n (Pred α)) (xs: Rules n (Pred α) l) (t: Hedge.Node α): Rules n (Pred α) l :=
  match t with
  | Hedge.Node.mk label children =>
    -- enters is one of our two new memoizable functions.
    let ifExprs: IfExprs n α (Symbol.nums xs) := Enter.deriveEnter xs
    -- childxs = expressions to evaluate on children.
    let childxs: Rules n (Pred α) (Symbol.nums xs) := IfExpr.evals g ifExprs label
    -- dchildxs = derivatives of children.
    let dchildxs: Rules n (Pred α) (Symbol.nums xs) := List.foldl (derive g) childxs children
    -- leaves is the other one of our two new memoizable functions.
    let lchildxs: Rules n (Pred α) l := Leave.deriveLeaves xs (Vec.map Rule.nullable dchildxs)
    lchildxs

theorem derive_commutes {α: Type} [DecidableEq α] (g: Grammar n (Pred α)) (r: Rule n (Pred α)) (x: Hedge.Node α):
  Rule.denote g (derive g (Vec.singleton r) x).head = Language.derive (Rule.denote g r) x := by
  induction r with
  | emptyset =>
    rw [Rule.denote_emptyset]
    rw [Language.derive_emptyset]
    unfold derive
    cases x with
    | mk label children =>
    simp only
    sorry
  | emptystr =>
    rw [Rule.denote_emptystr]
    rw [Language.derive_emptystr]
    unfold derive
    cases x with
    | mk label children =>
    simp only
    sorry
  | symbol s =>
    cases x with
    | mk label children =>
    rw [Rule.denote_symbol]
    rw [Language.derive_tree]
    unfold derive


    simp only
    sorry
  | or r1 r2 ih1 ih2 =>
    sorry
  | concat r1 r2 ih1 ih2 =>
    sorry
  | star r1 ih1 =>
    sorry

def derivs {α: Type} [DecidableEq α] (g: Grammar n (Pred α)) (x: Rule n (Pred α)) (hedge: Hedge α): Rule n (Pred α) :=
  let dxs := List.foldl (derive g) (Vec.singleton x) hedge
  dxs.head

def validate {α: Type} [DecidableEq α] (g: Grammar n (Pred α)) (x: Rule n (Pred α)) (hedge: Hedge α): Bool :=
  let dx := derivs g x hedge
  Rule.nullable dx

def run {α: Type} [DecidableEq α] (g: Grammar n (Pred α)) (t: Hedge.Node α): Bool :=
  validate g g.start [t]

-- Tests

open TokenTree (node)

#guard run
  (Grammar.singleton Regex.emptyset)
  (node "a" [node "b" [], node "c" [node "d" []]])
  = false

#guard run
  (Grammar.mk (n := 1)
    (Regex.symbol (Pred.eq (Token.string "a"), 0))
    #v[Regex.emptystr]
  )
  (node "a" [])
  = true

#guard run
  (Grammar.mk (n := 1)
    (Regex.symbol (Pred.eq (Token.string "a"), 0))
    #v[Regex.emptystr]
  )
  (node "a" [node "b" []])
  = false

#guard run
  (Grammar.mk (n := 2)
    (Regex.symbol (Pred.eq (Token.string "a"), 0))
    #v[
      (Regex.symbol (Pred.eq (Token.string "b"), 1))
      , Regex.emptystr
    ]
  )
  (node "a" [node "b" []])
  = true

#guard run
  (Grammar.mk (n := 2)
    (Regex.symbol (Pred.eq (Token.string "a"), 0))
    #v[
      (Regex.concat
        (Regex.symbol (Pred.eq (Token.string "b"), 1))
        (Regex.symbol (Pred.eq (Token.string "c"), 1))
      )
      , Regex.emptystr
    ]
  )
  (node "a" [node "b" [], node "c" []])
  = true

#guard run
  (Grammar.mk (n := 3)
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
  (node "a" [node "b" [], node "c" [node "d" []]])
  = true
