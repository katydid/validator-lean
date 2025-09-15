import Validator.Std.List

import Validator.Expr.Expr
import Validator.Expr.Pred
import Validator.Expr.Language

namespace Denote

local elab "simp_sizeOf" : tactic => do
  Lean.Elab.Tactic.evalTactic (<- `(tactic|
    simp only [ParseTree.mk.sizeOf_spec, List.cons.sizeOf_spec, List.nil.sizeOf_spec])
  )

theorem sizeOf_lex [SizeOf α] [SizeOf β]
  (x1 x2: α)
  (y1 y2: β)
  (hx: x1 = x2 \/ sizeOf x1 < sizeOf x2)
  (hy: sizeOf y1 < sizeOf y2)
  :Prod.Lex
    (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂)
    (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂)
    (x1, y1)
    (x2, y2) := by
  rw [Prod.lex_def]
  simp only
  cases hx
  · apply Or.inr
    apply And.intro
    assumption
    assumption
  · apply Or.inl
    assumption

theorem sizeOf_list_append [SizeOf α] (xs ys: List α):
  sizeOf xs <= sizeOf (ys ++ xs) := by
  induction ys with
  | nil =>
    simp only [List.nil_append, le_refl]
  | cons y ys ih =>
    simp +arith only [List.cons_append, List.cons.sizeOf_spec]
    omega

theorem lt_plus (x y z: Nat):
  y < z -> x + y < x + z := by
  simp

theorem sizeOf_list_cons [SizeOf α] (xs ys: List α):
  sizeOf xs < sizeOf (y::ys ++ xs) := by
  induction ys with
  | nil =>
    simp +arith only [List.cons_append, List.cons.sizeOf_spec]
    simp only [List.nil_append, le_add_iff_nonneg_left, zero_le]
  | cons y ys ih =>
    simp only [List.cons_append] at *
    simp only [List.cons.sizeOf_spec] at *
    omega

theorem split_zero_right: (List.splitAt 0 xs).2 = xs := by
  simp

theorem exists_drop (n: Nat) (xs: List α): ∃ ys, xs = ys ++ (List.drop n xs) := by
  induction n with
  | zero =>
    exists []
  | succ n ih =>
    cases ih with
    | intro ys ih =>
      cases xs with
      | nil =>
        simp at *
      | cons x xs =>
        simp only [List.drop_succ_cons]
        exists (x::List.take n xs)
        simp

theorem sizeOf_take (xs: ParseForest α):
  List.take n xs = xs \/ sizeOf (List.take n xs) < sizeOf xs := by
  simp
  by_cases (List.length xs > n)
  case pos h =>
    apply Or.inr
    induction n generalizing xs with
    | zero =>
      simp only [List.take]
      simp_sizeOf
      cases xs with
      | nil =>
        simp at h
      | cons x xs =>
        simp_sizeOf
        cases x
        simp_sizeOf
        omega
    | succ n' ih =>
      cases xs with
      | nil =>
        simp at h
      | cons x xs =>
        simp only [List.take]
        simp_sizeOf
        simp at h
        apply lt_plus
        apply ih
        exact h
  case neg h =>
    simp at h
    apply Or.inl
    assumption

def denote {α: Type} [BEq α] (g: Expr.Grammar μ α) (x: Expr μ α) (as: ParseForest α): Prop :=
  match x with
  | Expr.emptyset => False
  | Expr.epsilon => as = []
  | Expr.tree p childref => -- (tree (Pred.eval p) (denote g (g.lookup childref))) xs
    match as with
    | [ParseTree.mk label children] => Pred.eval p label /\ (denote g (g.lookup childref) children)
    | _ => False
  | Expr.or y z => (denote g y as) \/ (denote g z as)
  | Expr.concat y z => ∃ n,
      denote g y (List.take n as) /\ denote g z (List.drop n as)
  | Expr.star y =>
    match as with
    | [] => True
    | (a::as) => ∃ n,
        (denote g y (a::(List.take n as)))
        /\ (denote g (Expr.star y) (List.drop n as))
  termination_by (as, x)
  decreasing_by
  · apply Prod.Lex.left
    simp +arith only [List.cons.sizeOf_spec, ParseTree.mk.sizeOf_spec, sizeOf_default, add_zero,
      List.nil.sizeOf_spec]
  · apply Prod.Lex.right
    simp +arith only [Expr.or.sizeOf_spec]
  · apply Prod.Lex.right
    simp +arith only [Expr.or.sizeOf_spec]
  · apply sizeOf_lex
    · apply sizeOf_take
    · simp [Expr.concat.sizeOf_spec]
      omega
  · have h := exists_drop (xs := as) (n := n)
    cases h with
    | intro ys h =>
    nth_rewrite 2 [h]
    cases ys with
    | nil =>
      apply Prod.Lex.right
      simp +arith only [Expr.concat.sizeOf_spec]
    | cons y ys =>
      apply Prod.Lex.left
      apply sizeOf_list_cons
  · nth_rw 1 [Prod.lex_def]
    simp only [List.cons.sizeOf_spec, add_lt_add_iff_left, List.cons.injEq,
      true_and, Expr.star.sizeOf_spec, lt_add_iff_pos_left, zero_lt_one, and_true]
    apply Or.symm
    apply sizeOf_take
  · apply Prod.Lex.left
    have h := exists_drop (xs := as) (n := n)
    cases h with
    | intro ys h =>
    nth_rewrite 2 [h]
    apply sizeOf_list_cons

theorem denote_emptyset {α: Type} [BEq α] {g: Expr.Grammar μ α}:
  denote g Expr.emptyset = Language.emptyset := by
  unfold Language.emptyset
  funext
  simp [denote]

theorem denote_epsilon {α: Type} [BEq α] {g: Expr.Grammar μ α}:
  denote g Expr.epsilon = Language.emptystr := by
  unfold Language.emptystr
  funext
  simp [denote]

theorem denote_tree {α: Type} [BEq α] {g: Expr.Grammar μ α} (p: Pred α):
  denote g (Expr.tree p r) = Language.tree (Pred.eval p) (denote g (g.lookup r)) := by
  unfold Language.tree
  funext xs
  simp
  apply Iff.intro
  case mp =>
    intro h
    cases xs with
    | nil =>
      simp [denote] at h
    | cons x xs =>
      cases xs with
      | nil =>
        cases x with
        | mk label children =>
          exists label
          exists children
          apply And.intro rfl
          simp [denote] at h
          assumption
      | cons x2 xs =>
        simp [denote] at h
  case mpr =>
    intro h
    cases h with
    | intro label h =>
    cases h with
    | intro children h =>
    cases h with
    | intro hxs h =>
    rw [hxs]
    simp [denote]
    assumption

theorem denote_or {α: Type} [BEq α] {g: Expr.Grammar μ α} (x y: Expr μ α):
  denote g (Expr.or x y) = Language.or (denote g x) (denote g y) := by
  unfold Language.or
  funext xs
  simp [denote]

theorem denote_concat {α: Type} [BEq α] {g: Expr.Grammar μ α} (x y: Expr μ α):
  denote g (Expr.concat x y) = Language.concat (denote g x) (denote g y) := by
  unfold Language.concat
  funext xs
  simp [denote]
  apply Iff.intro
  case mp =>
    intro h
    cases h with
    | intro n h =>
    cases h with
    | intro hx hy =>
    exists (List.take n xs)
    apply And.intro hx
    exists (List.drop n xs)
    apply And.intro hy
    simp
  case mpr =>
    intro h
    cases h with
    | intro xs h =>
    cases h with
    | intro hx h =>
    cases h with
    | intro ys h =>
    cases h with
    | intro hy hxsys =>
    rw [hxsys]
    exists List.length xs
    simp
    apply And.intro hx hy

theorem denote_star' {α: Type} [BEq α] {g: Expr.Grammar μ α} (y: Expr μ α) (as: ParseForest α):
  denote g (Expr.star y) as <-> Language.star (denote g y) as := by
  apply Iff.intro
  case mp =>
    intro h
    cases as with
    | nil =>
      apply Language.star.zero
    | cons a as =>
      simp [denote] at h
      cases h with
      | intro n h =>
      cases h with
      | intro h1 h2 =>
      apply Language.star.more a (List.take n as) (List.drop n as)
      · simp
      · exact h1
      · rw [<- denote_star']
        exact h2
  case mpr =>
    intro h
    cases as with
    | nil =>
      simp [denote]
    | cons a as =>
      simp [denote]
      cases h with
      | more a1 as1 as2 _ hxy h1 h2  =>
        cases hxy
        exists List.length as1
        simp
        apply And.intro h1
        rw [denote_star']
        exact h2
  termination_by as
  decreasing_by
    · have h' := exists_drop n tail
      cases h' with
      | intro ys h' =>
      nth_rewrite 2 [h']
      simp_sizeOf
      have h'' := sizeOf_list_append (List.drop n tail) ys
      omega
    · rename_i j1 j2 j3 j4 j5 j6 j7 j8 j9 _j10
      cases j4
      rw [<- j6]
      apply sizeOf_list_cons

theorem denote_star {α: Type} [BEq α] {g: Expr.Grammar μ α} (y: Expr μ α):
  denote g (Expr.star y) = Language.star (denote g y) := by
  funext xs
  rw [denote_star']

def denote_onlyif {α: Type} [BEq α] (condition: Prop) [dcond: Decidable condition] (g: Expr.Grammar μ α) (x: Expr μ α):
  denote g (Expr.onlyif condition x) = Language.onlyif condition (denote g x) := by
  unfold Language.onlyif
  unfold Expr.onlyif
  funext xs
  split_ifs
  case pos hc =>
    simp only [eq_iff_iff, iff_and_self]
    intro d
    assumption
  case neg hc =>
    simp only [eq_iff_iff]
    rw [denote]
    simp only [false_iff, not_and]
    intro hc'
    contradiction

theorem null_commutes {α: Type} [BEq α] (g: Expr.Grammar μ α) (x: Expr μ α):
  ((Expr.nullable x) = true) = Language.null (denote g x) := by
  induction x with
  | emptyset =>
    rw [denote_emptyset]
    rw [Language.null_emptyset]
    unfold Expr.nullable
    apply Bool.false_eq_true
  | epsilon =>
    rw [denote_epsilon]
    rw [Language.null_emptystr]
    unfold Expr.nullable
    simp only
  | tree p children =>
    rw [denote_tree]
    rw [Language.null_tree]
    unfold Expr.nullable
    apply Bool.false_eq_true
  | or p q ihp ihq =>
    rw [denote_or]
    rw [Language.null_or]
    unfold Expr.nullable
    rw [<- ihp]
    rw [<- ihq]
    rw [Bool.or_eq_true]
  | concat p q ihp ihq =>
    rw [denote_concat]
    rw [Language.null_concat]
    unfold Expr.nullable
    rw [<- ihp]
    rw [<- ihq]
    rw [Bool.and_eq_true]
  | star r ih =>
    rw [denote_star]
    rw [Language.null_star]
    unfold Expr.nullable
    simp only
