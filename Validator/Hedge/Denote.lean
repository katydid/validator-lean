import Validator.Std.List

import Validator.Regex.Regex
import Validator.Hedge.Grammar

namespace Hedge.Grammar.Elem

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

-- Hedge.Denote.Rule.denote_elem is an alternative version of Hedge.Grammar.Rule.denote.
-- The only other changes is that denote_elem contains unfolded versions of Language.or, Language.concat_n and Language.star_n.
def Rule.denote_elem
  {α: Type} {φ: Type}
  (G: Hedge.Grammar n φ)
  (r: Hedge.Grammar.Rule n φ) (xs: Hedge α)
  (Φ: φ -> α -> Prop): Prop :=
  match r with
  | Regex.emptyset => Regex.Language.emptyset xs
  | Regex.emptystr => Regex.Language.emptystr xs
  | Regex.symbol (pred, ref) =>
    match xs with
    | [x] =>
      (Φ pred x.getLabel)
      /\ denote_elem G (G.lookup ref) x.getChildren Φ
    | _ => False
  | Regex.or r1 r2 =>
       (denote_elem G r1 xs Φ)
    \/ (denote_elem G r2 xs Φ)
  | Regex.concat r1 r2 =>
     ∃ (i: Fin (xs.length + 1)),
       (denote_elem G r1 (List.take i xs) Φ)
    /\ (denote_elem G r2 (List.drop i xs) Φ)
  | Regex.star r1 =>
    match xs with
    | [] => True
    | (x'::xs') =>
       ∃ (i: Fin xs.length),
         (denote_elem G r1 (List.take (i + 1) (x'::xs')) Φ)
      /\ (denote_elem G (Regex.star r1) (List.drop (i + 1) (x'::xs')) Φ)
  termination_by (xs, r)
  decreasing_by
    · apply decreasing_symbol
    · apply decreasing_or_l
    · apply decreasing_or_r
    · apply denote_elem_sizeOf_concat_left
    · apply denote_elem_sizeOf_concat_right
    · apply denote_elem_sizeOf_star_left
    · apply denote_elem_sizeOf_star_right

def Rule.denote {α: Type} {φ: Type}
  (G: Hedge.Grammar n φ) (Φ: φ -> α -> Prop)
  (r: Hedge.Grammar.Rule n φ) (xs: Hedge α): Prop :=
  Rule.denote_elem G r xs (fun p x' => Φ p x')

theorem denote_emptyset {α: Type} {φ: Type} (G: Hedge.Grammar n φ) (Φ: φ -> α -> Prop):
  Rule.denote G Φ Regex.emptyset = Regex.Language.emptyset := by
  unfold Rule.denote
  simp only [Rule.denote_elem]

theorem denote_emptystr {α: Type} {φ: Type} (G: Hedge.Grammar n φ) (Φ: φ -> α -> Prop):
  Rule.denote G Φ Regex.emptystr = Regex.Language.emptystr := by
  unfold Rule.denote
  simp only [Rule.denote_elem]

theorem denote_onlyif {α: Type}
  (condition: Prop) [dcond: Decidable condition]
  (G: Grammar n φ) {Φ: φ -> α -> Prop} (x: Rule n φ):
  Rule.denote G Φ (Regex.onlyif condition x) = Regex.Language.onlyif condition (Rule.denote G Φ x) := by
  unfold Regex.Language.onlyif
  unfold Regex.onlyif
  funext xs
  split_ifs
  case pos hc =>
    simp only [eq_iff_iff, iff_and_self]
    intro d
    assumption
  case neg hc =>
    simp only [eq_iff_iff]
    rw [Rule.denote]
    rw [Rule.denote_elem]
    simp only [Regex.Language.emptyset, false_iff, not_and]
    intro h
    contradiction

theorem denote_symbol {α: Type} {φ: Type} (G: Hedge.Grammar n φ) (Φ: φ -> α -> Prop) [DecidableRel Φ] (s: Symbol n φ):
  Rule.denote G Φ (Regex.symbol s) = Hedge.Language.tree (fun a => Φ s.1 a) (Rule.denote G Φ (G.lookup s.2)) := by
  unfold Rule.denote
  unfold Hedge.Language.tree
  funext xs
  simp only
  cases xs with
  | nil =>
    rw [Rule.denote_elem]
    simp only [List.ne_cons_self, decide_eq_true_eq, false_and, exists_const, exists_false]
    intro x h
    contradiction
  | cons x xs =>
    cases xs with
    | nil =>
      rw [Rule.denote_elem]
      simp only [List.cons.injEq, and_true, decide_eq_true_eq]
      cases x with
      | mk label children =>
      simp only [Node.mk.injEq, ↓existsAndEq, and_true, exists_eq_left']
      simp only [Node.getLabel]
      simp_all only [eq_iff_iff, and_congr_right_iff]
      intro a
      obtain ⟨fst, snd⟩ := s
      simp_all only
      rfl
    | cons x' xs =>
      rw [Rule.denote_elem]
      simp
      intro x h
      simp at h

theorem denote_or {α: Type} {φ: Type} (G: Hedge.Grammar n φ) (Φ: φ -> α -> Prop) (r1 r2: Rule n φ):
  Rule.denote G Φ (Regex.or r1 r2) = Regex.Language.or (Rule.denote G Φ r1) (Rule.denote G Φ r2) := by
  unfold Rule.denote
  funext
  simp only [Rule.denote_elem, Regex.Language.or]

theorem denote_concat_n {α: Type} {φ: Type} (G: Hedge.Grammar n φ) (Φ: φ -> α -> Prop) (p q: Rule n φ):
  Rule.denote G Φ (Regex.concat p q) = Regex.Language.concat_n (Rule.denote G Φ p) (Rule.denote G Φ q) := by
  unfold Rule.denote
  funext
  simp only [Rule.denote_elem]
  unfold Regex.Language.concat_n
  rfl

theorem unfold_denote_elem_star_n {α: Type} {φ: Type} (G: Hedge.Grammar n φ) (Φ: φ -> α -> Prop) (r: Rule n φ) (xs: Hedge α):
  Rule.denote_elem G (Regex.star r) xs (fun p x' => Φ p x')
  = (match xs with
    | [] => True
    | (x'::xs') =>
       ∃ (n: Fin xs.length),
         (Rule.denote_elem G r (List.take (n + 1) (x'::xs')) Φ)
      /\ (Rule.denote_elem G (Regex.star r) (List.drop (n + 1) (x'::xs')) Φ)) := by
  cases xs with
  | nil =>
    simp [Rule.denote_elem]
  | cons x xs =>
    cases xs with
    | cons _ _ =>
      simp only [Rule.denote_elem]
    | nil =>
      simp only [Rule.denote_elem]

theorem denote_elem_star_n_iff {α: Type} {φ: Type} (G: Hedge.Grammar n φ) (Φ: φ -> α -> Prop) (r: Rule n φ) (xs: Hedge α):
  Rule.denote_elem G (Regex.star r) xs (fun p x' => Φ p x') <-> Regex.Language.star_n (fun xs' => Rule.denote_elem G r xs' (fun p x' => Φ p x')) xs := by
  rw [<- eq_iff_iff]
  unfold Regex.Language.star_n
  rw [unfold_denote_elem_star_n]
  cases xs with
  | nil =>
    rfl
  | cons x xs =>
    simp only
    congr
    ext n
    rw [<- eq_iff_iff]
    congr
    simp only [List.length_cons, List.drop_succ_cons, eq_iff_iff]
    rw [<- denote_elem_star_n_iff]
  termination_by xs.length
  decreasing_by
    obtain ⟨n, hn⟩ := n
    apply List.list_length_drop_lt_cons

theorem denote_star_n_iff {α: Type} {φ: Type} (G: Hedge.Grammar n φ) (Φ: φ -> α -> Prop) (r: Rule n φ) (xs: Hedge α):
  Rule.denote G Φ (Regex.star r) xs <-> Regex.Language.star_n (Rule.denote G Φ r) xs := by
  unfold Rule.denote
  rw [denote_elem_star_n_iff]

theorem denote_star_n {α: Type} {φ: Type} (G: Hedge.Grammar n φ) (Φ: φ -> α -> Prop) (r: Rule n φ):
  Rule.denote G Φ (Regex.star r) = Regex.Language.star_n (Rule.denote G Φ r) := by
  funext
  rw [denote_star_n_iff]

theorem null_commutes {α: Type}
  (G: Grammar n φ) (Φ: φ -> α -> Prop) [DecidableRel Φ] (x: Rule n φ):
  ((Rule.null x) = true) = Regex.Language.null (Hedge.Grammar.Elem.Rule.denote G Φ x) := by
  unfold Rule.null
  induction x with
  | emptyset =>
    rw [denote_emptyset]
    rw [Regex.Language.null_emptyset]
    unfold Regex.null
    apply Bool.false_eq_true
  | emptystr =>
    rw [denote_emptystr]
    rw [Regex.Language.null_emptystr]
    unfold Regex.null
    simp only
  | symbol s =>
    obtain ⟨p, children⟩ := s
    rw [denote_symbol]
    rw [Hedge.Language.null_tree]
    unfold Regex.null
    apply Bool.false_eq_true
  | or p q ihp ihq =>
    rw [denote_or]
    rw [Regex.Language.null_or]
    unfold Regex.null
    rw [<- ihp]
    rw [<- ihq]
    unfold Regex.null
    rw [Bool.or_eq_true]
  | concat p q ihp ihq =>
    rw [denote_concat_n]
    rw [Regex.Language.null_concat_n]
    unfold Regex.null
    rw [<- ihp]
    rw [<- ihq]
    unfold Regex.null
    rw [Bool.and_eq_true]
  | star r ih =>
    rw [denote_star_n]
    rw [Regex.Language.null_star_n]
    unfold Regex.null
    simp only

theorem denote_nil_is_null (Φ: φ -> α -> Prop) [DecidableRel Φ]:
  Rule.denote G Φ r [] = Rule.null r := by
  rw [null_commutes G (fun s a => Φ s a)]
  cases r with
  | emptyset =>
    simp only [denote_emptyset, Regex.Language.emptyset, Regex.Language.null]
  | emptystr =>
    simp only [denote_emptystr, Regex.Language.emptystr, Regex.Language.null]
  | symbol s =>
    simp only [denote_symbol]
    simp only [Regex.Language.null]
  | or r1 r2 =>
    simp only [denote_or, Regex.Language.or, Regex.Language.null]
  | concat r1 r2 =>
    simp only [denote_concat_n, Regex.Language.null]
  | star r1 =>
    simp only [denote_star_n, Regex.Language.null]
