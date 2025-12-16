-- OriginalTotal is a total version of the original derivative algorithm that runs on a labelled tree.
-- This means the derive function is not partial, but total, because it includes a proof of termination.

import Validator.Std.Except
import Validator.Std.List

import Validator.Std.Hedge
import Validator.Parser.TokenTree

import Validator.Expr.Pred
import Validator.Expr.Grammar
import Validator.Expr.Regex

namespace OriginalTotal

theorem decreasing_or_l {α: Type} {σ: Type} [SizeOf σ] (r1 r2: Regex σ) (x: Hedge.Node α):
  Prod.Lex
    (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂)
    (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂)
    (x, r1)
    (x, Regex.or r1 r2) := by
  apply Prod.Lex.right
  simp +arith only [Regex.or.sizeOf_spec]

theorem decreasing_or_r {α: Type} {σ: Type} [SizeOf σ] (r1 r2: Regex σ) (x: Hedge.Node α):
  Prod.Lex
    (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂)
    (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂)
    (x, r2)
    (x, Regex.or r1 r2) := by
  apply Prod.Lex.right
  simp +arith only [Regex.or.sizeOf_spec]

theorem decreasing_concat_l {α: Type} {σ: Type} [SizeOf σ] (r1 r2: Regex σ) (x: Hedge.Node α):
  Prod.Lex
    (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂)
    (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂)
    (x, r1)
    (x, Regex.concat r1 r2) := by
  apply Prod.Lex.right
  simp +arith only [Regex.concat.sizeOf_spec]

theorem decreasing_concat_r {α: Type} {σ: Type} [SizeOf σ] (r1 r2: Regex σ) (x: Hedge.Node α):
  Prod.Lex
    (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂)
    (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂)
    (x, r2)
    (x, Regex.concat r1 r2) := by
  apply Prod.Lex.right
  simp +arith only [Regex.concat.sizeOf_spec]

theorem decreasing_star {α: Type} {σ: Type} [SizeOf σ] (r: Regex σ) (x: Hedge.Node α):
  Prod.Lex
    (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂)
    (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂)
    (x, r)
    (x, Regex.star r) := by
  apply Prod.Lex.right
  simp +arith only [Regex.star.sizeOf_spec]

theorem decreasing_symbol {α: Type} {σ: Type} [SizeOf σ] (r1 r2: Regex σ) (label: α) (children: Hedge α) (x: Hedge.Node α) (h: x ∈ children):
  Prod.Lex
    (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂)
    (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂)
    (x, r1)
    (Hedge.Node.mk label children, r2) := by
  apply Prod.Lex.left
  simp +arith only [Hedge.Node.mk.sizeOf_spec]
  have h' := List.list_elem_lt h
  omega

def Rule.derive
  (G: Grammar n φ) (Φ: φ -> α -> Bool)
  (r: Rule n φ) (x: Hedge.Node α): Rule n φ :=
  match r with
  | Regex.emptyset => Regex.emptyset
  | Regex.emptystr => Regex.emptyset
  | Regex.symbol (p, ref) =>
    match x with
    | Hedge.Node.mk label children =>
      Regex.onlyif
        (
          Φ p label
          /\ Rule.nullable (List.foldl (Rule.derive G Φ) (G.lookup ref) children)
        )
        Regex.emptystr
  | Regex.or r1 r2 =>
    Regex.or (Rule.derive G Φ r1 x) (Rule.derive G Φ r2 x)
  | Regex.concat r1 r2 =>
    Regex.or
      (Regex.concat (Rule.derive G Φ r1 x) r2)
      (Regex.onlyif (Rule.nullable r1) (Rule.derive G Φ r2 x))
  | Regex.star r1 =>
    Regex.concat (Rule.derive G Φ r1 x) (Regex.star r1)
  -- Lean cannot guess how the recursive function terminates,
  -- so we have to tell it how the arguments decrease in size.
  -- The arguments decrease in the tree case first
  -- (which only happens in the Regex.symbol case)
  -- and in the expression, r, second (which is all other cases).
  -- This means if the tree is not destructed, then the expression is destructed.
  termination_by (x, r)
  -- Once we tell Lean how the function terminates we have to prove that
  -- the size of the arguments decrease on every call.
  -- Prod.Lex.left represents the case where the tree argument decreases.
  -- Prod.Lex.right represents the case where the tree argument does not decrease
  -- and the expression r does decrease.
  decreasing_by
    · apply decreasing_symbol (h := by assumption)
    · apply decreasing_symbol (h := by assumption)
    · apply decreasing_symbol (h := by assumption)
    · apply decreasing_or_l
    · apply decreasing_or_r
    · apply decreasing_concat_l
    · apply decreasing_concat_r
    · apply decreasing_star

def Rule.derive'
  (G: Grammar n φ) (Φ: φ -> α -> Bool)
  (r: Rule n φ) (x: Hedge.Node α): Rule n φ :=
  Rule.derive G (fun p a => Φ p a) r x

def validate
  (G: Grammar n φ) (Φ: φ -> α -> Bool)
  (r: Rule n φ) (hedge: Hedge α): Bool :=
  Rule.nullable (List.foldl (Rule.derive' G Φ) r hedge)

def run [DecidableEq α] (G: Grammar n (Pred α)) (t: Hedge.Node α): Except String Bool :=
  Except.ok (validate G Pred.evalb G.start [t])

-- Tests

open TokenTree (node)

#guard run
  (Grammar.singleton Regex.emptyset)
  (node "a" [node "b" [], node "c" [node "d" []]]) =
  Except.ok false

#guard run
  (Grammar.mk (n := 1)
    (Regex.symbol (Pred.eq (Token.string "a"), 0))
    #vec[Regex.emptystr]
  )
  (node "a" []) =
  Except.ok true

#guard run
  (Grammar.mk (n := 1)
    (Regex.symbol (Pred.eq (Token.string "a"), 0))
    #vec[Regex.emptystr]
  )
  (node "a" [node "b" []]) =
  Except.ok false

#guard run
  (Grammar.mk (n := 2)
    (Regex.symbol (Pred.eq (Token.string "a"), 0))
    #vec[
      (Regex.symbol (Pred.eq (Token.string "b"), 1))
      , Regex.emptystr
    ]
  )
  (node "a" [node "b" []])
  = Except.ok true

#guard run
  (Grammar.mk (n := 2)
    (Regex.symbol (Pred.eq (Token.string "a"), 0))
    #vec[
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
  (Grammar.mk (n := 3)
    (Regex.symbol (Pred.eq (Token.string "a"), 0))
    #vec[
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

theorem derive_commutes {α: Type} {φ: Type}
  (G: Grammar n φ) (Φ: φ -> α -> Bool)
  (r: Rule n φ) (x: Hedge.Node α):
  Rule.denote G Φ (Rule.derive' G Φ r x) = Language.derive (Rule.denote G Φ r) x := by
  unfold Rule.derive'
  fun_induction (Rule.derive G (fun p a => Φ p a)) r x with
  | case1 => -- emptyset
    rw [Rule.denote_emptyset]
    rw [Language.derive_emptyset]
  | case2 => -- emptystr
    rw [Rule.denote_emptyset]
    rw [Rule.denote_emptystr]
    rw [Language.derive_emptystr]
  | case3 p childRef label children ih =>
    rw [Rule.denote_symbol]
    rw [Language.derive_tree]
    rw [Rule.denote_onlyif]
    rw [Rule.denote_emptystr]
    apply (congrArg fun x => Language.onlyif x Language.emptystr)
    congr
    generalize (G.lookup childRef) = childExpr
    rw [Rule.null_commutes]
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
      · intro x child hchild
        apply ih
        rw [List.mem_cons]
        apply Or.inr hchild
  | case4 x p q ihp ihq => -- or
    rw [Rule.denote_or]
    rw [Rule.denote_or]
    unfold Language.or
    rw [ihp]
    rw [ihq]
    rfl
  | case5 x p q ihp ihq => -- concat
    rw [Rule.denote_concat]
    rw [Rule.denote_or]
    rw [Rule.denote_concat]
    rw [Rule.denote_onlyif]
    rw [Language.derive_concat]
    rw [<- ihp]
    rw [<- ihq]
    congrm (Language.or (Language.concat (Rule.denote G Φ (Rule.derive G (fun p a => Φ p a) p x)) (Rule.denote G Φ q)) ?_)
    rw [Rule.null_commutes]
  | case6 x r ih => -- star
    rw [Rule.denote_star]
    rw [Rule.denote_concat]
    rw [Rule.denote_star]
    rw [Language.derive_star]
    rw [ih]
