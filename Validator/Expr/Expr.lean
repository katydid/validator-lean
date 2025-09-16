import Mathlib.Tactic.RewriteSearch

import Validator.Expr.Pred

inductive Expr μ α where
  | emptyset
  | epsilon
  | tree (labelPred: Pred α) (ref: Fin μ)
  | or (y z: Expr μ α)
  | concat (y z: Expr μ α)
  | star (y: Expr μ α)
  deriving DecidableEq, Ord, Repr, Hashable

abbrev Exprs μ α := List (Expr μ α)

instance [Ord α]: Ord (Expr μ α) := inferInstance

instance [Repr α]: Repr (Expr μ α) := inferInstance

instance [DecidableEq α]: DecidableEq (Expr μ α) := inferInstance

instance [DecidableEq α]: BEq (Expr μ α) := inferInstance

instance [Hashable α]: Hashable (Expr μ α) := inferInstance

def Expr.nullable (x: Expr μ α): Bool :=
  match x with
  | Expr.emptyset => false
  | Expr.epsilon => true
  | Expr.tree _ _ => false
  | Expr.or y z => nullable y || nullable z
  | Expr.concat y z => nullable y && nullable z
  | Expr.star _ => true

def Expr.unescapable (x: Expr μ α): Bool :=
  match x with
  | Expr.emptyset => true
  | _ => false

namespace Expr

def onlyif (cond: Prop) [dcond: Decidable cond] (x: Expr μ α): Expr μ α :=
  if cond then x else Expr.emptyset

def smartOr (x y: Expr μ α): Expr μ α :=
  match x with
  | Expr.emptyset => y
  | _ =>
    match y with
    | Expr.emptyset => x
    | _ => Expr.or x y

def smartConcat (x y: Expr μ α): Expr μ α :=
  match x with
  | Expr.emptyset => Expr.emptyset
  | Expr.epsilon => y
  | _ =>
    match y with
    | Expr.emptyset => Expr.emptyset
    | Expr.epsilon => x
    | _ => Expr.concat x y

def smartStar (x: Expr μ α): Expr μ α :=
  match x with
  | Expr.star _ => x
  | Expr.emptyset => Expr.epsilon
  | _ => Expr.star x

def references (x: Expr μ α): List (Fin μ) :=
  match x with
  | Expr.emptyset => []
  | Expr.epsilon => []
  | Expr.tree _ r => [r]
  | Expr.or y z => references y ++ references z
  | Expr.concat y z => references y ++ references z
  | Expr.star y => references y

structure Grammar μ α where
  main: Expr μ α
  refs: Vector (Expr μ α) (μ - 1)

def Grammar.references (g: Grammar μ α): List (Fin μ) :=
  List.flatten (List.map Expr.references (g.main :: g.refs.toList))

def Grammar.lookup (g: Grammar μ α) (ref: Fin μ): Expr μ α :=
  match ref with
  | Fin.mk 0 _ =>
    g.main
  | Fin.mk (m + 1) _ =>
    Vector.get g.refs (Fin.mk m (by omega))

def Grammar.singleton (x: Expr 1 α): Grammar 1 α :=
  Grammar.mk x #v[]

def Grammar.lookup0 (g: Grammar μ α): Expr μ α :=
  g.main

def Grammar.emptyset: Grammar 1 α :=
  Grammar.mk Expr.emptyset #v[]

def Grammar.epsilon: Grammar 1 α :=
  Grammar.mk Expr.epsilon #v[]

def setMaxRef (μ1: Nat) (h: μ1 >= μ0) (x: Expr μ0 α): Expr μ1 α :=
  match x with
  | emptyset => Expr.emptyset
  | epsilon => Expr.epsilon
  | tree p ref => Expr.tree p (Fin.mk ref.val (by omega))
  | or y z => Expr.or (Expr.setMaxRef μ1 h y) (Expr.setMaxRef μ1 h z)
  | concat y z => Expr.concat (Expr.setMaxRef μ1 h y) (Expr.setMaxRef μ1 h z)
  | star y => Expr.star (Expr.setMaxRef μ1 h y)

def maxref (μold μnew μ: Nat): Nat :=
  if μold + 1 = μ -- if mold is the maximum ref
  then
    max (μ - 1) (μnew + 1) -- then downgrade to m - 1 or upgrade to mnew
  else
    (max μ (μnew + 1)) -- otherwise upgrade to mnew

def rewriteRef (μold μnew: Nat) (x: Expr μ α): Expr (maxref μold μnew μ) α :=
  match x with
  | emptyset => Expr.emptyset
  | epsilon => Expr.epsilon
  | tree p ref =>
    if h: ref = μold
    then Expr.tree p (Fin.mk μnew (by
      unfold maxref
      split_ifs
      · omega
      · omega
      ))
    else Expr.tree p (Fin.mk ref.val (by
      unfold maxref
      split_ifs
      · omega
      · omega
      ))
  | or y z => Expr.or (Expr.rewriteRef μold μnew y) (Expr.rewriteRef μold μnew z)
  | concat y z => Expr.concat (Expr.rewriteRef μold μnew y) (Expr.rewriteRef μold μnew z)
  | star y => Expr.star (Expr.rewriteRef μold μnew y)

example :
  Expr.rewriteRef 2 2
  ((Expr.tree (Pred.eq 'a') (Fin.mk 2 (by omega))): Expr 3 Char)
  =
  ((Expr.tree (Pred.eq 'a') (Fin.mk 2 (by omega))): Expr 3 Char) := by
  simp only [Expr.rewriteRef, ↓reduceDIte, ↓Char.isValue]

example :
  Expr.rewriteRef 2 3
  ((Expr.tree (Pred.eq 'a') (Fin.mk 2 (by omega))): Expr 3 Char)
  =
  ((Expr.tree (Pred.eq 'a') (Fin.mk 3 (by omega))): Expr 4 Char) := by
  simp only [Expr.rewriteRef, ↓reduceDIte, ↓Char.isValue]

example :
  Expr.rewriteRef 2 5
  ((Expr.tree (Pred.eq 'a') (Fin.mk 2 (by omega))): Expr 3 Char)
  =
  ((Expr.tree (Pred.eq 'a') (Fin.mk 5 (by omega))): Expr 6 Char) := by
  simp only [Expr.rewriteRef, ↓reduceDIte, ↓Char.isValue]

example :
  Expr.rewriteRef 2 1
  ((Expr.tree (Pred.eq 'a') (Fin.mk 2 (by omega))): Expr 3 Char)
  =
  ((Expr.tree (Pred.eq 'a') (Fin.mk 1 (by omega))): Expr 2 Char) := by
  simp only [Expr.rewriteRef, ↓reduceDIte, ↓Char.isValue, Fin.mk_one, Fin.isValue]

example :
  Expr.rewriteRef 5 2
  ((Expr.tree (Pred.eq 'a') (Fin.mk 5 (by omega))): Expr 6 Char)
  =
  -- We only downgrade by one to 5, since the previous one was erroniously set to 6
  -- It might be part of a grammar with expressions of higher
  ((Expr.tree (Pred.eq 'a') (Fin.mk 2 (by omega))): Expr 5 Char) := by
  simp only [Expr.rewriteRef, ↓reduceDIte, ↓Char.isValue]

def rewriteIncRef (μold μnew: Nat) (x: Expr μ α): Expr (max μ (μnew + 1)) α :=
  match x with
  | emptyset => Expr.emptyset
  | epsilon => Expr.epsilon
  | tree p ref =>
    if h: ref = μold
    then Expr.tree p (Fin.mk μnew (by omega))
    else Expr.tree p (Fin.mk ref.val (by omega))
  | or y z => Expr.or (Expr.rewriteIncRef μold μnew y) (Expr.rewriteIncRef μold μnew z)
  | concat y z => Expr.concat (Expr.rewriteIncRef μold μnew y) (Expr.rewriteIncRef μold μnew z)
  | star y => Expr.star (Expr.rewriteIncRef μold μnew y)

def incRefs (x: Expr μ α): Expr (μ + 1) α :=
  match x with
  | emptyset => Expr.emptyset
  | epsilon => Expr.epsilon
  | tree p ref => Expr.tree p (Fin.mk (ref.val + 1) (by omega))
  | or y z => Expr.or (Expr.incRefs y) (Expr.incRefs z)
  | concat y z => Expr.concat (Expr.incRefs y) (Expr.incRefs z)
  | star y => Expr.star (Expr.incRefs y)

theorem max_pos {x y: Nat}:
  x < y -> y = (max x y) := by omega

theorem max_neg {x y: Nat}:
  ¬ x < y -> x = (max x y) := by omega

theorem lt_ge {x y: Nat}:
  x < y -> y >= x := by omega

theorem not_lt_ge {x y: Nat}:
  ¬ x < y -> x >= y := by omega

def example_grammar: Grammar 2 Char :=
  Grammar.mk
    (Expr.or Expr.epsilon (Expr.tree (Pred.eq 'a') 1))
    #v[Expr.epsilon]

#guard
  example_grammar.lookup (Fin.mk 0 (by omega))
  = (Expr.or Expr.epsilon (Expr.tree (Pred.eq 'a') 1))

#guard
  example_grammar.lookup (Fin.mk 1 (by omega))
  = Expr.epsilon

def lookup_all (g: Grammar μ α): Exprs μ α :=
  List.map g.lookup (Grammar.references g)

#guard
  lookup_all example_grammar
  = [Expr.epsilon]
