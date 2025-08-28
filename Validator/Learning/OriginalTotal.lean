-- OriginalTotal is a total version of the original derivative algorithm that runs on a labelled tree.
-- This means the derive function is not partial, but total, because it includes a proof of termination.

import Validator.Std.Except
import Validator.Std.List

import Validator.Std.ParseTree
import Validator.Parser.TokenTree

import Validator.Expr.Pred
import Validator.Expr.Expr
import Validator.Expr.Denote

namespace OriginalTotal

theorem decreasing_or_l (y: Expr α) (tree: ParseTree α):
  Prod.Lex
    (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂)
    (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂)
    (tree, y)
    (tree, y.or z) := by
  apply Prod.Lex.right
  simp +arith only [Expr.or.sizeOf_spec]

theorem decreasing_or_r (y: Expr α) (tree: ParseTree α):
  Prod.Lex
    (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂)
    (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂)
    (tree, z)
    (tree, y.or z) := by
  apply Prod.Lex.right
  simp +arith only [Expr.or.sizeOf_spec]

theorem decreasing_concat_l (y: Expr α) (tree: ParseTree α):
  Prod.Lex
    (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂)
    (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂)
    (tree, y)
    (tree, y.concat z) := by
  apply Prod.Lex.right
  simp +arith only [Expr.concat.sizeOf_spec]

theorem decreasing_concat_r (y: Expr α) (tree: ParseTree α):
  Prod.Lex
    (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂)
    (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂)
    (tree, z)
    (tree, y.concat z) := by
  apply Prod.Lex.right
  simp +arith only [Expr.concat.sizeOf_spec]

theorem decreasing_star (y: Expr α) (tree: ParseTree α):
  Prod.Lex
    (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂)
    (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂)
    (tree, y)
    (tree, y.star) := by
  apply Prod.Lex.right
  simp +arith only [Expr.star.sizeOf_spec]

theorem decreasing_tree {s: Expr α} {children: ParseForest α} (h: tree ∈ children):
  Prod.Lex
    (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂)
    (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂)
    (tree, s)
    (ParseTree.mk label children, Expr.tree labelPred childrenExpr) := by
  apply Prod.Lex.left
  simp +arith only [ParseTree.mk.sizeOf_spec]
  have h' := List.elem_lt_list h
  omega

def derive [DecidableEq α] (x: Expr α) (tree: ParseTree α): Expr α :=
  match x with
  | Expr.emptyset => Expr.emptyset
  | Expr.epsilon => Expr.emptyset
  | Expr.tree labelPred childrenExpr =>
    match tree with
    | ParseTree.mk label children =>
      Expr.onlyif
        (
          (Pred.eval labelPred label)
          && Expr.nullable (List.foldl derive childrenExpr children)
        )
      Expr.epsilon
  | Expr.or y z => Expr.or (derive y tree) (derive z tree)
  | Expr.concat y z =>
    Expr.or
      (Expr.concat (derive y tree) z)
      (Expr.onlyif (Expr.nullable y) (derive z tree))
  | Expr.star y => Expr.concat (derive y tree) (Expr.star y)
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
  · apply (decreasing_tree (by assumption))
  · apply (decreasing_tree (by assumption))
  · apply decreasing_or_l
  · apply decreasing_or_r
  · apply decreasing_concat_l
  · apply decreasing_concat_r
  · apply decreasing_star

def validate [DecidableEq α] (x: Expr α) (forest: ParseForest α): Bool :=
  Expr.nullable (List.foldl derive x forest)

def run [DecidableEq α] (x: Expr α) (t: ParseTree α): Except String Bool :=
  Except.ok (validate x [t])

-- Tests

open TokenTree (node)

#guard run
  Expr.emptyset
  (node "a" [node "b" [], node "c" [node "d" []]]) =
  Except.ok false

#guard run
  (Expr.tree (Pred.eq (Token.string "a")) Expr.epsilon)
  (node "a" []) =
  Except.ok true

#guard run
  (Expr.tree (Pred.eq (Token.string "a")) Expr.epsilon)
  (node "a" [node "b" []]) =
  Except.ok false

#guard run
  (Expr.tree (Pred.eq (Token.string "a"))
    (Expr.tree (Pred.eq (Token.string "b"))
      Expr.epsilon
    )
  )
  (node "a" [node "b" []]) =
  Except.ok true

#guard run
  (Expr.tree (Pred.eq (Token.string "a"))
    (Expr.concat
      (Expr.tree (Pred.eq (Token.string "b"))
        Expr.epsilon
      )
      (Expr.tree (Pred.eq (Token.string "c"))
        Expr.epsilon
      )
    )
  )
  (node "a" [node "b" [], node "c" []]) =
  Except.ok true

#guard run
  (Expr.tree (Pred.eq (Token.string "a"))
    (Expr.concat
      (Expr.tree (Pred.eq (Token.string "b"))
        Expr.epsilon
      )
      (Expr.tree (Pred.eq (Token.string "c"))
        (Expr.tree (Pred.eq (Token.string "d"))
          Expr.epsilon
        )
      )
    )
  )
  (node "a" [node "b" [], node "c" [node "d" []]]) =
  Except.ok true

theorem a [Decidable p]:
  decide p = true <-> p := by
  simp only [decide_eq_true_eq]

theorem derive_commutes {α: Type} [DecidableEq α] (x: Expr α) (a: ParseTree α):
  Denote.denote (derive x a) = Language.derive (Denote.denote x) a := by
  induction x generalizing a with
  | emptyset =>
    simp only [Denote.denote, derive]
    rw [Language.derive_emptyset]
  | epsilon =>
    simp only [Denote.denote, derive]
    rw [Language.derive_emptystr]
  | tree p childexpr ih =>
    cases a with
    | mk label children =>
    simp only [Denote.denote]
    rw [Language.derive_tree]
    simp only [derive]
    rw [Denote.denote_onlyif]
    simp only [Denote.denote]
    apply (congrArg fun x => Language.onlyif x Language.emptystr)
    simp only [Bool.and_eq_true]
    simp only [decide_eq_true_eq]
    congr
    rw [Denote.null_commutes]
    unfold Language.null
    induction children generalizing childexpr with
    | nil =>
      simp
    | cons c cs ih' =>
      simp only [List.foldl]
      rw [ih']
      · rw [ih]
        simp
      · intro a
        have h' : (derive (derive childexpr c) a) = List.foldl derive childexpr [c, a] := by sorry
        rw [h']
        sorry
  | or p q ihp ihq =>
    simp only [Denote.denote, derive]
    rw [Language.derive_or]
    unfold Language.or
    rw [ihp]
    rw [ihq]
  | concat p q ihp ihq =>
    simp only [Denote.denote, derive]
    rw [Language.derive_concat]
    rw [<- ihp]
    rw [<- ihq]
    rw [Denote.denote_onlyif]
    congrm (Language.or (Language.concat (Denote.denote (derive p a)) (Denote.denote q)) ?_)
    rw [Denote.null_commutes]
  | star r ih =>
    simp only [Denote.denote, derive]
    rw [Language.derive_star]
    -- guard_target =
    --   Language.concat (Denote.denote (derive x a)) (Language.star (Denote.denote x))
    --   = Language.concat (Language.derive (Denote.denote x) a) (Language.star (Denote.denote x))
    congrm ((Language.concat ?_ (Language.star (Denote.denote _))))
    -- guard_target = denote (Denote.derive x a) = Language.derive (Denote.denote x) a
    apply ih
