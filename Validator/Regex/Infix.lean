import Validator.Std.List

import Validator.Regex.Regex

namespace Regex.Elem

theorem denote_elem_sizeOf_or_left {α: Type} {σ: Type} {p q: Regex σ} {xs: List α}:
  Prod.Lex (fun x1 x2 => x1 < x2) (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂) (xs.length, p) (xs.length, Regex.or p q) := by
  apply Prod.Lex.right
  simp only [Regex.or.sizeOf_spec]
  omega

theorem denote_elem_sizeOf_or_right {α: Type} {σ: Type} {p q: Regex σ} {xs: List α}:
  Prod.Lex (fun x1 x2 => x1 < x2) (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂) (xs.length, q) (xs.length, Regex.or p q) := by
  apply Prod.Lex.right
  simp only [Regex.or.sizeOf_spec]
  omega

theorem denote_elem_sizeOf_concat_left {α: Type} {σ: Type} {p q: Regex σ} {xs: List α}:
  Prod.Lex (fun x1 x2 => x1 < x2) (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂) ((List.take n xs).length, p) (xs.length, Regex.concat p q) := by
  simp only [List.length_take]
  by_cases (n >= xs.length)
  case pos h' =>
    rw [Nat.min_eq_right h']
    apply Prod.Lex.right
    simp only [Regex.concat.sizeOf_spec]
    omega
  case neg h' =>
    apply Prod.Lex.left
    omega

theorem denote_elem_sizeOf_concat_right {α: Type} {σ: Type} {p q: Regex σ} {xs: List α}:
  Prod.Lex (fun x1 x2 => x1 < x2) (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂) ((List.drop n xs).length, q) (xs.length, Regex.concat p q) := by
  simp only [List.length_drop]
  by_cases (xs.length - n = xs.length)
  case pos h' =>
    rw [h']
    apply Prod.Lex.right
    simp only [Regex.concat.sizeOf_spec]
    omega
  case neg h' =>
    apply Prod.Lex.left
    omega

theorem denote_elem_sizeOf_star_left {α: Type} {σ: Type} {p: Regex σ} {xs: List α}:
  Prod.Lex (fun x1 x2 => x1 < x2) (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂) ((List.take n xs).length, p) (xs.length, Regex.star p) := by
  simp only [List.length_take]
  cases xs.length with
  | zero =>
    simp only [Nat.zero_le, inf_of_le_right]
    apply Prod.Lex.right
    simp only [Regex.star.sizeOf_spec]
    omega
  | succ l =>
    by_cases (min n (l + 1) = l + 1)
    case pos h'' =>
      rw [h'']
      apply Prod.Lex.right
      simp only [Regex.star.sizeOf_spec]
      omega
    case neg h'' =>
      apply Prod.Lex.left
      simp +arith only
      simp +arith only at h''
      omega

theorem denote_elem_sizeOf_star_right {α: Type} {σ: Type} {p: Regex σ} {x: α} {xs: List α}:
  Prod.Lex (fun x1 x2 => x1 < x2) (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂) ((List.drop (n + 1) (x::xs)).length, Regex.star p) ((x::xs).length, Regex.star p) := by
  simp only [List.drop_succ_cons, List.length_drop, List.length_cons]
  apply Prod.Lex.left
  omega

-- denote_symbol_lift_take and denote_symbol_lift_drop is used by denote_elem to lift
--   a Φ predicate to work on an element of the original list:
-- * (denote_symbol: σ -> List.ElemOf xs -> Prop) -> (σ -> List.ElemOf (List.take n xs) -> Prop)
-- * (denote_symbol: σ -> List.ElemOf xs -> Prop) -> (σ -> List.ElemOf (List.drop n xs) -> Prop)
-- This works, because take and drop create infixes of a list and an element of an infix is a element.
-- We need these lifting functions to make the prove that denote_list = Regex.denote possible.
-- See denote_list_concat_n and denote_list_star_n for the exact detail.

def denote_symbol_lift_take (n: Nat) (Φ: σ -> List.ElemOf xs -> Prop): (σ -> List.ElemOf (List.take n xs) -> Prop) :=
  fun (s: σ) (y: List.ElemOf (List.take n xs)) =>
    Φ s (List.ElemOf.mk y.val xs (by apply List.list_elemof_take_is_elem))

def denote_symbol_lift_drop (n: Nat) (Φ: σ -> List.ElemOf xs -> Prop): (σ -> List.ElemOf (List.drop n xs) -> Prop) :=
  fun (s: σ) (y: List.ElemOf (List.drop n xs)) =>
    Φ s (List.ElemOf.mk y.val xs (by apply List.list_elemof_drop_is_elem))

-- denote_elem is an alternative version of Regex.denote that is later proven to be equivalent definitions.
-- The difference is that the denote_symbol function now has a relationship with the original input list, List.InfixOf.
-- This relationship is used for proving termination of regular expressions on trees.
-- The only other changes is that denote_elem contains unfolded versions of Language.or, Language.concat_n and Language.star_n.
def denote_elem
  {α: Type} {σ: Type}
  (x: Regex σ) (xs: List α) (Φ: σ -> List.ElemOf xs -> Prop): Prop :=
  match x with
  | Regex.emptyset => Language.emptyset xs
  | Regex.emptystr => Language.emptystr xs
  | Regex.symbol s =>
    match xs with
    | [x] => Φ s (List.ElemOf.self x)
    | _ => False
  | Regex.or y z =>
       (denote_elem y xs Φ)
    \/ (denote_elem z xs Φ)
  | Regex.concat y z =>
     ∃ (n: Fin (xs.length + 1)),
       (denote_elem y (List.take n xs) (denote_symbol_lift_take n Φ))
    /\ (denote_elem z (List.drop n xs) (denote_symbol_lift_drop n Φ))
  | Regex.star y =>
    match xs with
    | [] => True
    | (x'::xs') =>
       ∃ (n: Fin xs.length),
         (denote_elem y (List.take (n + 1) (x'::xs')) (denote_symbol_lift_take (n + 1) Φ))
      /\ (denote_elem (Regex.star y) (List.drop (n + 1) (x'::xs')) (denote_symbol_lift_drop (n + 1) Φ))
  termination_by (xs.length, x)
  decreasing_by
    · apply denote_elem_sizeOf_or_left
    · apply denote_elem_sizeOf_or_right
    · apply denote_elem_sizeOf_concat_left
    · apply denote_elem_sizeOf_concat_right
    · apply denote_elem_sizeOf_star_left
    · apply denote_elem_sizeOf_star_right

-- denote_list has the same type signature as Regex.denote, but uses denote_elem.
-- We will prove that denote_list = Regex.denote
def denote_list {α: Type} {σ: Type} (Φ: σ -> α -> Prop) (r: Regex σ) (xs: List α): Prop :=
  denote_elem r xs (fun s (x': List.ElemOf xs) => Φ s x'.val)

-- We want to prove the correctness of our denote_list denotation function,
-- by proving it is equivalent to the original Regex.denote function:
-- * denote_list Φ r = Regex.denote Φ r
-- For this we need to prove the following helper theorems:
-- * denote_list Φ Regex.emptyset = Language.emptyset
-- * denote_list Φ Regex.emptystr = Language.emptystr
-- * denote_list Φ (Regex.symbol s) = Φ s
-- * denote_list Φ (Regex.or p q) = Language.or (denote_list Φ p) (denote_list Φ q)
-- * denote_list Φ (Regex.concat p q) = Language.concat_n (denote_list Φ p) (denote_list Φ q)
-- * denote_list Φ (Regex.star r) = Language.star_n (denote_list Φ r)

theorem denote_list_emptyset {α: Type} {σ: Type} (Φ: σ -> α -> Prop):
  denote_list Φ Regex.emptyset
  = Language.emptyset := by
  funext xs
  simp only [denote_list, denote_elem, Language.emptyset]

theorem denote_list_emptystr {α: Type} {σ: Type} (Φ: σ -> α -> Prop):
  denote_list Φ Regex.emptystr
  = Language.emptystr := by
  funext xs
  simp only [denote_list, denote_elem, Language.emptystr]

theorem denote_list_symbol {α: Type} {σ: Type} (Φ: σ -> α -> Prop) (s: σ):
  denote_list Φ (Regex.symbol s)
  = Language.symbol_pred Φ s := by
  unfold Language.symbol_pred
  funext xs
  simp only [denote_list]
  unfold denote_elem
  cases xs with
  | nil =>
    simp only [List.ne_cons_self, false_and, exists_false]
  | cons x xs =>
    cases xs with
    | nil =>
      simp only [List.ElemOf.self]
      simp only [List.cons.injEq, and_true, exists_eq_left']
    | cons x' xs =>
      simp only [List.cons.injEq, reduceCtorEq, and_false, false_and, exists_false]

theorem denote_list_or {α: Type} {σ: Type} (Φ: σ -> α -> Prop) (p q: Regex σ):
  denote_list Φ (Regex.or p q)
  = Language.or (denote_list Φ p) (denote_list Φ q) := by
  unfold Language.or
  funext xs
  simp only [denote_list, denote_elem]

-- We need the lifting functions denote_symbol_lift_take and denote_symbol_lift_drop to prove denote_list_concat_n.
-- When we unfold the definitions of denote_list, denote_elem and Language.concat_n, we get the following goal:
-- ∃ n,
--   denote_elem p (List.take (↑n) xs) (denote_symbol_lift_take ↑n fun s xs' => Φ s ↑xs') ∧
--   denote_elem q (List.drop (↑n) xs) (denote_symbol_lift_drop ↑n fun s xs' => Φ s ↑xs')
-- =
-- ∃ n,
--   denote_elem p (List.take (↑n) xs) (fun s xs' => Φ s ↑xs') ∧
--   denote_elem q (List.drop (↑n) xs) (fun s xs' => Φ s ↑xs')
--
-- On closer inspection, we can fill in some of the types:
--
-- ∃ n,
--   denote_elem p (List.take (↑n) xs) (denote_symbol_lift_take ↑n fun s (xs': xs.InfixOf) => Φ s ↑xs') ∧
--   denote_elem q (List.drop (↑n) xs) (denote_symbol_lift_drop ↑n fun s (xs': xs.InfixOf) => Φ s ↑xs')
-- =
-- ∃ n,
--   denote_elem p (List.take (↑n) xs) (fun s (xs': (List.take (↑n) xs).InfixOf) => Φ s ↑xs') ∧
--   denote_elem q (List.drop (↑n) xs) (fun s (xs': (List.drop (↑n) xs).InfixOf) => Φ s ↑xs')
--
-- If we didn't have these lifting functions, then the two sides would have have been equal, except for the types of xs'.
-- The functions denote_symbol_lift_take and denote_symbol_lift_drop is used to make the types of xs' the same:
-- * denote_symbol_lift_take: (denote_symbol: σ -> List.InfixOf xs -> Prop) -> (σ -> List.InfixOf (List.take n xs) -> Prop)
-- * denote_symbol_lift_drop: (denote_symbol: σ -> List.InfixOf xs -> Prop) -> (σ -> List.InfixOf (List.drop n xs) -> Prop)
theorem denote_list_concat_n {α: Type} {σ: Type} (Φ: σ -> α -> Prop) (p q: Regex σ):
  denote_list Φ (Regex.concat p q)
  = Language.concat_n (denote_list Φ p) (denote_list Φ q) := by
  funext xs
  simp only [denote_list, denote_elem, Language.concat_n]
  unfold denote_symbol_lift_drop
  unfold denote_symbol_lift_take
  unfold List.ElemOf.mk
  simp only

theorem denote_list_star_n_iff {α: Type} {σ: Type} (Φ: σ -> α -> Prop) (r: Regex σ) (xs: List α):
  denote_list Φ (Regex.star r) xs
  <-> Language.star_n (denote_list Φ r) xs := by
  cases xs with
  | nil =>
    simp only [denote_list, denote_elem, Language.star_n]
  | cons x' xs' =>
    apply Iff.intro
    case mp =>
      intro h
      simp only [denote_list, denote_elem] at h
      simp only [denote_list, Language.star_n]
      obtain ⟨⟨n, hn⟩, ⟨hp, hq⟩⟩ := h
      exists ⟨n, hn⟩
      simp only at hp hq
      simp only
      apply And.intro hp
      rw [<- denote_list_star_n_iff]
      simp only [denote_list]
      exact hq
    case mpr =>
      intro h
      simp only [Language.star_n] at h
      obtain ⟨⟨n, hn⟩, ⟨hp, hq⟩⟩ := h
      simp only [denote_list]
      simp only [denote_elem]
      exists ⟨n, hn⟩
      simp only at hp hq
      simp only
      apply And.intro hp
      unfold denote_symbol_lift_drop
      simp only
      unfold List.ElemOf.mk
      rw [<- denote_list]
      rw [denote_list_star_n_iff]
      exact hq
  termination_by xs.length

-- Just like concat_n, star_n also splits the string, using take and drop.
-- This means it also requires the lifting functions: denote_symbol_lift_take and denote_symbol_lift_drop to make this proof possible.
-- See denote_list_concat_n for details.
theorem denote_list_star_n {α: Type} {σ: Type} (Φ: σ -> α -> Prop) (r: Regex σ):
  denote_list Φ (Regex.star r)
  = Language.star_n (denote_list Φ r) := by
  funext xs
  rw [denote_list_star_n_iff]

-- Given the above theorems it is easy to prove that the definition of denote_list is the equivalent to Regex.denote:
theorem denote_list_is_Regex.denote {α: Type} {σ: Type} (Φ: σ -> α -> Prop) (r: Regex σ):
  denote_list Φ r = Regex.denote Φ r := by
  induction r with
  | emptyset =>
    rw [denote_list_emptyset]
    rw [Regex.denote_emptyset]
  | emptystr =>
    rw [denote_list_emptystr]
    rw [Regex.denote_emptystr]
  | symbol s =>
    rw [denote_list_symbol]
    rw [Regex.denote_symbol_pred]
  | or p q ihp ihq =>
    rw [denote_list_or]
    rw [Regex.denote_or]
    rw [ihp]
    rw [ihq]
  | concat p q ihp ihq =>
    rw [denote_list_concat_n]
    rw [Regex.denote_concat_n]
    rw [ihp]
    rw [ihq]
  | star p ihp =>
    rw [denote_list_star_n]
    rw [Regex.denote_star_n]
    rw [ihp]

-- Helper theorems for proofs of functions that use denote_elem

theorem denote_elem_emptyset {α: Type} {σ: Type} (xs: List α) (Φ: σ -> List.ElemOf xs -> Prop):
  denote_elem Regex.emptyset xs Φ
  = Language.emptyset xs := by
  simp only [denote_elem, denote_elem, Language.emptyset]

theorem denote_elem_emptystr {α: Type} {σ: Type} (xs: List α) (Φ: σ -> List.ElemOf xs -> Prop):
  denote_elem Regex.emptystr xs Φ
  = Language.emptystr xs := by
  simp only [denote_elem, denote_elem, Language.emptystr]

theorem denote_elem_symbol {α: Type} {σ: Type} (xs: List α) (Φ: σ -> List.ElemOf xs -> Prop) (s: σ):
  denote_elem (Regex.symbol s) xs Φ
  = Language.symbol_pred Φ s (List.ElemOf.selfs xs) := by
  unfold denote_elem
  cases xs with
  | nil =>
    simp only [Language.symbol_pred, List.ElemOf.selfs, List.attach_nil, List.map_nil,
      List.ne_cons_self, false_and, exists_false]
  | cons x xs =>
    cases xs with
    | nil =>
      simp only [List.ElemOf.self, Language.symbol_pred, List.ElemOf.selfs, List.ElemOf.mk, Subtype.coe_eta,
        List.attach_cons, List.attach_nil, List.map_nil, List.map_cons, List.cons.injEq, and_true,
        exists_eq_left']
    | cons x' xs =>
      simp only [Language.symbol_pred, List.ElemOf.selfs, List.attach_cons, List.map_cons, List.map_map,
        List.cons.injEq, reduceCtorEq, and_false, false_and, nonempty_subtype, List.mem_cons,
        exists_or_eq_left, exists_const]

theorem denote_elem_or {α: Type} {σ: Type} (xs: List α) (Φ: σ -> List.ElemOf xs -> Prop) (p q: Regex σ):
  denote_elem (Regex.or p q) xs Φ
  = ((denote_elem p xs Φ) \/ (denote_elem q xs Φ)) := by
  simp only [denote_elem]

theorem denote_elem_concat_n {α: Type} {σ: Type} (xs: List α) (Φ: σ -> List.ElemOf xs -> Prop) (p q: Regex σ):
  denote_elem (Regex.concat p q) xs Φ
  = (∃ (n: Fin (xs.length + 1)),
       (denote_elem p (List.take n xs) (denote_symbol_lift_take n Φ))
    /\ (denote_elem q (List.drop n xs) (denote_symbol_lift_drop n Φ))) := by
  simp only [denote_elem]

theorem denote_elem_concat_n' {α: Type} {σ: Type} (xs: List α) (Φ: σ -> List.ElemOf xs -> Prop) (p q: Regex σ):
  denote_elem (Regex.concat p q) xs Φ
  = (∃ (n: Fin (xs.length + 1)),
       (denote_elem p (List.take n xs) (denote_symbol_lift_take n Φ))
    /\ (denote_elem q (List.drop n xs) (denote_symbol_lift_drop n Φ))) := by
  simp only [denote_elem]

theorem denote_elem_star_n {α: Type} {σ: Type} (xs: List α) (Φ: σ -> List.ElemOf xs -> Prop) (r: Regex σ):
  denote_elem (Regex.star r) xs Φ
  = (match xs with
    | [] => True
    | (x'::xs') =>
       ∃ (n: Fin xs.length),
         (denote_elem r (List.take (n + 1) (x'::xs')) (denote_symbol_lift_take (n + 1) Φ))
      /\ (denote_elem (Regex.star r) (List.drop (n + 1) (x'::xs')) (denote_symbol_lift_drop (n + 1) Φ))) := by
  cases xs with
  | nil =>
    simp [denote_elem]
  | cons x xs =>
    cases xs with
    | cons _ _ =>
      simp only [denote_elem]
    | nil =>
      simp only [denote_elem]
