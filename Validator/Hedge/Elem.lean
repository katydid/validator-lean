import Validator.Std.List

import Validator.Regex.Regex
import Validator.Hedge.Grammar

namespace Hedge.Elem

theorem decreasing_or_l {α: Type} {σ: Type} [SizeOf σ] (r1 r2: Regex σ) (xs: Hedge α):
  Prod.Lex
    (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂)
    (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂)
    (xs, r1)
    (xs, Regex.or r1 r2) := by
  apply Prod.Lex.right
  simp +arith only [Regex.or.sizeOf_spec]

theorem decreasing_or_r {α: Type} {σ: Type} [SizeOf σ] (r1 r2: Regex σ) (xs: Hedge α):
  Prod.Lex
    (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂)
    (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂)
    (xs, r2)
    (xs, Regex.or r1 r2) := by
  apply Prod.Lex.right
  simp +arith only [Regex.or.sizeOf_spec]

theorem decreasing_concat_l {α: Type} {σ: Type} [SizeOf σ] (r1 r2: Regex σ) (xs: Hedge α):
  Prod.Lex
    (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂)
    (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂)
    (xs, r1)
    (xs, Regex.concat r1 r2) := by
  apply Prod.Lex.right
  simp +arith only [Regex.concat.sizeOf_spec]

theorem decreasing_concat_r {α: Type} {σ: Type} [SizeOf σ] (r1 r2: Regex σ) (xs: Hedge α):
  Prod.Lex
    (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂)
    (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂)
    (xs, r2)
    (xs, Regex.concat r1 r2) := by
  apply Prod.Lex.right
  simp +arith only [Regex.concat.sizeOf_spec]

theorem decreasing_star {α: Type} {σ: Type} [SizeOf σ] (r: Regex σ) (xs: Hedge α):
  Prod.Lex
    (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂)
    (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂)
    (xs, r)
    (xs, Regex.star r) := by
  apply Prod.Lex.right
  simp +arith only [Regex.star.sizeOf_spec]

theorem decreasing_symbol {α: Type} {σ: Type} [SizeOf σ] (r1 r2: Regex σ) (x: Hedge.Node α):
  Prod.Lex
    (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂)
    (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂)
    (x.getChildren, r1)
    ([x], r2) := by
  apply Prod.Lex.left
  cases x with
  | mk label children =>
  simp only [Hedge.Node.getChildren]
  simp only [List.cons.sizeOf_spec, Node.mk.sizeOf_spec, sizeOf_default, add_zero,
    List.nil.sizeOf_spec]
  omega

theorem denote_elem_sizeOf_concat_left {α: Type} {σ: Type} [SizeOf σ] {r1 r2: Regex σ} {xs: Hedge α}:
  Prod.Lex (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂) (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂) (List.take n xs, r1) (xs, Regex.concat r1 r2) := by
  have h := Hedge.sizeOf_take n xs
  cases h with
  | inl h =>
    rw [h]
    apply decreasing_concat_l
  | inr h =>
    apply Prod.Lex.left
    assumption

theorem denote_elem_sizeOf_concat_right {α: Type} {σ: Type} [SizeOf σ] {p q: Regex σ} {xs: Hedge α}:
  Prod.Lex (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂) (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂) ((List.drop n xs), q) (xs, Regex.concat p q) := by
  have h := Hedge.sizeOf_drop n xs
  cases h with
  | inl h =>
    rw [h]
    apply decreasing_concat_r
  | inr h =>
    apply Prod.Lex.left
    assumption

theorem denote_elem_sizeOf_star_left {α: Type} {σ: Type} [SizeOf σ] {p: Regex σ} {xs: Hedge α}:
  Prod.Lex (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂) (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂) ((List.take n xs), p) (xs, Regex.star p) := by
  have h := Hedge.sizeOf_take n xs
  cases h with
  | inl h =>
    rw [h]
    apply decreasing_star
  | inr h =>
    apply Prod.Lex.left
    assumption

theorem denote_elem_sizeOf_star_right {α: Type} {σ: Type} [SizeOf σ] {p: Regex σ} {x: Hedge.Node α} {xs: Hedge α}:
  Prod.Lex (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂) (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂) ((List.drop (n + 1) (x::xs)), Regex.star p) ((x::xs), Regex.star p) := by
  simp only [List.drop_succ_cons]
  apply Prod.Lex.left
  have h := Hedge.sizeOf_drop n xs
  cases h with
  | inl h =>
    rw [h]
    simp only [List.cons.sizeOf_spec, lt_add_iff_pos_left, add_pos_iff, zero_lt_one, true_or]
  | inr h =>
    simp only [List.cons.sizeOf_spec, gt_iff_lt]
    omega

-- denote_symbol_lift_take and denote_symbol_lift_drop is used by denote_elem to lift
--   a Φ predicate to work on an element of the original list:
-- * (denote_symbol: σ -> List.ElemOf xs -> Prop) -> (σ -> List.ElemOf (List.take n xs) -> Prop)
-- * (denote_symbol: σ -> List.ElemOf xs -> Prop) -> (σ -> List.ElemOf (List.drop n xs) -> Prop)
-- This works, because take and drop create infixes of a list and an element of an infix is a element.
-- We need these lifting functions to make the prove that denote_list = Regex.denote possible.
-- See denote_list_concat_n and denote_list_star_n for the exact detail.

def denote_symbol_lift_take (n: Nat) (Φ: σ -> Hedge.LabelIn xs -> Prop): (σ -> Hedge.LabelIn (List.take n xs) -> Prop) :=
  fun (s: σ) (y: Hedge.LabelIn (List.take n xs)) =>
    Φ s (Hedge.LabelIn.mk y.val xs (by apply Hedge.labelin_take_is_labelelem))

def denote_symbol_lift_drop (n: Nat) (Φ: σ -> Hedge.LabelIn xs -> Prop): (σ -> Hedge.LabelIn (List.drop n xs) -> Prop) :=
  fun (s: σ) (y: Hedge.LabelIn (List.drop n xs)) =>
    Φ s (Hedge.LabelIn.mk y.val xs (by apply Hedge.labelin_drop_is_labelelem))

def lift_symbol {x: Hedge.Node α}
  (Φ: φ -> LabelIn [x] -> Prop): (φ -> LabelIn x.getChildren -> Prop) :=
  fun p hchildren => Φ p (by
    clear Φ
    clear p
    clear φ
    unfold LabelIn at *
    cases hchildren with
    | mk childlabel hchildren' =>
    refine (Subtype.mk childlabel ?_)
    cases x with
    | mk label children =>
    simp only [Node.getChildren] at *
    unfold Hedge.LabelElem
    simp only [List.flatMap]
    simp only [List.map, List.flatten]
    simp only [List.append_eq, List.append_nil]
    simp only [Node.getLabels]
    -- aesop?
    simp_all only [List.mem_flatMap, List.mem_cons, or_true]
  )

-- denote_elem is an alternative version of Regex.denote that is later proven to be equivalent definitions.
-- The difference is that the denote_symbol function now has a relationship with the original input list, List.InfixOf.
-- This relationship is used for proving termination of regular expressions on trees.
-- The only other changes is that denote_elem contains unfolded versions of Language.or, Language.concat_n and Language.star_n.
def denote_elem
  {α: Type} {φ: Type}
  (G: Hedge.Grammar n φ)
  (r: Hedge.Grammar.Rule n φ) (xs: Hedge α)
  (Φ: φ -> Hedge.LabelIn xs -> Prop): Prop :=
  match r with
  | Regex.emptyset => Regex.Language.emptyset xs
  | Regex.emptystr => Regex.Language.emptystr xs
  | Regex.symbol (pred, ref) =>
    match xs with
    | [x] =>
      (Φ pred (Hedge.LabelIn.self x))
      /\ denote_elem G (G.lookup ref) x.getChildren (lift_symbol Φ)
    | _ => False
  | Regex.or r1 r2 =>
       (denote_elem G r1 xs Φ)
    \/ (denote_elem G r2 xs Φ)
  | Regex.concat r1 r2 =>
     ∃ (i: Fin (xs.length + 1)),
       (denote_elem G r1 (List.take i xs) (denote_symbol_lift_take i Φ))
    /\ (denote_elem G r2 (List.drop i xs) (denote_symbol_lift_drop i Φ))
  | Regex.star r1 =>
    match xs with
    | [] => True
    | (x'::xs') =>
       ∃ (i: Fin xs.length),
         (denote_elem G r1 (List.take (i + 1) (x'::xs')) (denote_symbol_lift_take (i + 1) Φ))
      /\ (denote_elem G (Regex.star r1) (List.drop (i + 1) (x'::xs')) (denote_symbol_lift_drop (i + 1) Φ))
  termination_by (xs, r)
  decreasing_by
    · apply decreasing_symbol
    · apply decreasing_or_l
    · apply decreasing_or_r
    · apply denote_elem_sizeOf_concat_left
    · apply denote_elem_sizeOf_concat_right
    · apply denote_elem_sizeOf_star_left
    · apply denote_elem_sizeOf_star_right
