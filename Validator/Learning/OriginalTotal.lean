-- OriginalTotal is a total version of the original derivative algorithm that runs on a labelled tree.
-- This means the derive function is not partial, but total, because it includes a proof of termination.

import Validator.Std.Except
import Validator.Std.List

import Validator.Std.Hedge
import Validator.Parser.TokenTree

import Validator.Expr.Pred
import Validator.Expr.Expr
import Validator.Expr.Denote

namespace OriginalTotal

theorem decreasing_or_l (y: Expr μ α) (tree: Hedge.Node α):
  Prod.Lex
    (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂)
    (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂)
    (tree, y)
    (tree, y.or z) := by
  apply Prod.Lex.right
  simp +arith only [Expr.or.sizeOf_spec]

theorem decreasing_or_r (y: Expr μ α) (tree: Hedge.Node α):
  Prod.Lex
    (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂)
    (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂)
    (tree, z)
    (tree, y.or z) := by
  apply Prod.Lex.right
  simp +arith only [Expr.or.sizeOf_spec]

theorem decreasing_concat_l (y: Expr μ α) (tree: Hedge.Node α):
  Prod.Lex
    (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂)
    (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂)
    (tree, y)
    (tree, y.concat z) := by
  apply Prod.Lex.right
  simp +arith only [Expr.concat.sizeOf_spec]

theorem decreasing_concat_r (y: Expr μ α) (tree: Hedge.Node α):
  Prod.Lex
    (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂)
    (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂)
    (tree, z)
    (tree, y.concat z) := by
  apply Prod.Lex.right
  simp +arith only [Expr.concat.sizeOf_spec]

theorem decreasing_star (y: Expr μ α) (tree: Hedge.Node α):
  Prod.Lex
    (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂)
    (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂)
    (tree, y)
    (tree, y.star) := by
  apply Prod.Lex.right
  simp +arith only [Expr.star.sizeOf_spec]

theorem decreasing_tree {s: Expr μ α} {children: Hedge α} (h: tree ∈ children):
  Prod.Lex
    (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂)
    (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂)
    (tree, s)
    (Hedge.Node.mk label children, Expr.tree labelPred childrenExpr) := by
  apply Prod.Lex.left
  simp +arith only [Hedge.Node.mk.sizeOf_spec]
  have h' := List.list_elem_lt h
  omega

def derive [DecidableEq α] (g: Expr.Grammar μ α) (x: Expr μ α) (tree: Hedge.Node α): Expr μ α :=
  match x with
  | Expr.emptyset => Expr.emptyset
  | Expr.epsilon => Expr.emptyset
  | Expr.tree labelPred childRef =>
    match tree with
    | Hedge.Node.mk label children =>
      Expr.onlyif
        (
          (Pred.eval labelPred label)
          && Expr.nullable (List.foldl (derive g) (g.lookup childRef) children)
        )
      Expr.epsilon
  | Expr.or y z => Expr.or (derive g y tree) (derive g z tree)
  | Expr.concat y z =>
    Expr.or
      (Expr.concat (derive g y tree) z)
      (Expr.onlyif (Expr.nullable y) (derive g z tree))
  | Expr.star y => Expr.concat (derive g y tree) (Expr.star y)
-- Lean cannot guess how the recursive function terminates,
-- so we have to tell it how the arguments decrease in size.
-- The arguments decrease in the tree case first
-- (which only happens in the Expr.tree case)
-- and in the expression, x, second (which is all other cases).
-- This means if the tree is not destructed, then the expression is destructed.
termination_by (tree, x)
-- Once we tell Lean how the function terminates we have to prove that
-- the size of the arguments decrease on every call.
-- Prod.Lex.left represents the case where the tree argument decreases.
-- Prod.Lex.right represents the case where the tree argument does not decrease
-- and the expression x does decrease.
decreasing_by
  · apply decreasing_tree (by assumption)
  · apply decreasing_tree (by assumption)
  · apply decreasing_or_l
  · apply decreasing_or_r
  · apply decreasing_concat_l
  · apply decreasing_concat_r
  · apply decreasing_star

def validate [DecidableEq α] (g: Expr.Grammar μ α)(x: Expr μ α) (hedge: Hedge α): Bool :=
  Expr.nullable (List.foldl (derive g) x hedge)

def run [DecidableEq α] (g: Expr.Grammar μ α) (t: Hedge.Node α): Except String Bool :=
  Except.ok (validate g g.lookup0 [t])

-- Tests

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

theorem derive_commutes {α: Type} [DecidableEq α] (g: Expr.Grammar μ α) (x: Expr μ α) (a: Hedge.Node α):
  Denote.denote g (derive g x a) = Language.derive (Denote.denote g x) a := by
  fun_induction (derive g) x a with
  | case1 => -- emptyset
    rw [Denote.denote_emptyset]
    rw [Language.derive_emptyset]
  | case2 => -- epsilon
    rw [Denote.denote_emptyset]
    rw [Denote.denote_epsilon]
    rw [Language.derive_emptystr]
  | case3 p childRef label children ih =>
    rw [Denote.denote_tree]
    rw [Language.derive_tree]
    rw [Denote.denote_onlyif]
    rw [Denote.denote_epsilon]
    apply (congrArg fun x => Language.onlyif x Language.emptystr)
    simp only [Bool.and_eq_true]
    simp only [decide_eq_true_eq]
    congr
    generalize (g.lookup childRef) = childExpr
    rw [Denote.null_commutes]
    unfold Language.null
    induction children generalizing childExpr with
    | nil =>
      simp only [List.foldl_nil]
      rfl
    | cons c cs ih' =>
      simp only [List.foldl]
      rw [ih']
      · cases c
        rw [ih]
        simp only [Language.derive, Language.derives, List.cons_append, List.nil_append]
        rw [List.mem_cons]
        apply Or.inl
        rfl
      · intro x
        intro child
        intro hchild
        apply ih
        rw [List.mem_cons]
        apply Or.inr hchild
  | case4 a p q ihp ihq => -- or
    rw [Denote.denote_or]
    rw [Denote.denote_or]
    unfold Language.or
    rw [ihp]
    rw [ihq]
    rfl
  | case5 a p q ihp ihq => -- concat
    rw [Denote.denote_concat]
    rw [Denote.denote_or]
    rw [Denote.denote_concat]
    rw [Denote.denote_onlyif]
    rw [Language.derive_concat]
    rw [<- ihp]
    rw [<- ihq]
    congrm (Language.or (Language.concat (Denote.denote g (derive g p a)) (Denote.denote g q)) ?_)
    rw [Denote.null_commutes]
  | case6 a r ih => -- star
    rw [Denote.denote_star]
    rw [Denote.denote_concat]
    rw [Denote.denote_star]
    rw [Language.derive_star]
    rw [ih]
