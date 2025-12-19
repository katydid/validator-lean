import Validator.Std.List

import Validator.Regex.Regex

namespace Regex.Infix

theorem denote_infix_sizeOf_or_left {α: Type} {σ: Type} {p q: Regex σ} {xs: List α}:
  Prod.Lex (fun x1 x2 => x1 < x2) (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂) (xs.length, p) (xs.length, Regex.or p q) := by
  apply Prod.Lex.right
  simp only [Regex.or.sizeOf_spec]
  omega

theorem denote_infix_sizeOf_or_right {α: Type} {σ: Type} {p q: Regex σ} {xs: List α}:
  Prod.Lex (fun x1 x2 => x1 < x2) (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂) (xs.length, q) (xs.length, Regex.or p q) := by
  apply Prod.Lex.right
  simp only [Regex.or.sizeOf_spec]
  omega

theorem denote_infix_sizeOf_concat_left {α: Type} {σ: Type} {p q: Regex σ} {xs: List α}:
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

theorem denote_infix_sizeOf_concat_right {α: Type} {σ: Type} {p q: Regex σ} {xs: List α}:
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

theorem denote_infix_sizeOf_star_left {α: Type} {σ: Type} {p: Regex σ} {xs: List α}:
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

theorem denote_infix_sizeOf_star_right {α: Type} {σ: Type} {p: Regex σ} {x: α} {xs: List α}:
  Prod.Lex (fun x1 x2 => x1 < x2) (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂) ((List.drop (n + 1) (x::xs)).length, Regex.star p) ((x::xs).length, Regex.star p) := by
  simp only [List.drop_succ_cons, List.length_drop, List.length_cons]
  apply Prod.Lex.left
  omega

-- denote_symbol_lift_take and denote_symbol_lift_drop is used by denote_infix to lift
--   a denote_symbol function to work on an infix of the original infix:
-- * (denote_symbol: σ -> List.InfixOf xs -> Prop) -> (σ -> List.InfixOf (List.take n xs) -> Prop)
-- * (denote_symbol: σ -> List.InfixOf xs -> Prop) -> (σ -> List.InfixOf (List.drop n xs) -> Prop)
-- This works, because take and drop create infixes of a list and the infix of an infix is an infix.
-- We need these lifting functions to make the prove that denote_list = Regex.denote possible.
-- See denote_list_concat_n and denote_list_star_n for the exact detail.

def denote_symbol_lift_take (n: Nat) (denote_symbol: σ -> List.InfixOf xs -> Prop): (σ -> List.InfixOf (List.take n xs) -> Prop) :=
  fun (s: σ) (ys: List.InfixOf (List.take n xs)) =>
    denote_symbol s (List.InfixOf.mk ys.val (by apply List.list_infixof_take_is_infix))

def denote_symbol_lift_drop (n: Nat) (denote_symbol: σ -> List.InfixOf xs -> Prop): (σ -> List.InfixOf (List.drop n xs) -> Prop) :=
  fun (s: σ) (ys: List.InfixOf (List.drop n xs)) =>
    denote_symbol s (List.InfixOf.mk ys.val (by apply List.list_infixof_drop_is_infix))

-- denote_infix is an alternative version of Regex.denote that is later proven to be equivalent definitions.
-- The difference is that the denote_symbol function now has a relationship with the original input list, List.InfixOf.
-- This relationship is used for proving termination of regular expressions on trees.
-- The only other changes is that denote_infix contains unfolded versions of Language.or, Language.concat_n and Language.star_n.
def denote_infix
  {α: Type} {σ: Type}
  (x: Regex σ) (xs: List α) (Φ: σ -> List.InfixOf xs -> Prop): Prop :=
  match x with
  | Regex.emptyset => Language.emptyset xs
  | Regex.emptystr => Language.emptystr xs
  | Regex.symbol s => Φ s (List.InfixOf.self xs)
  | Regex.or y z =>
       (denote_infix y xs Φ)
    \/ (denote_infix z xs Φ)
  | Regex.concat y z =>
     ∃ (n: Fin (xs.length + 1)),
       (denote_infix y (List.take n xs) (denote_symbol_lift_take n Φ))
    /\ (denote_infix z (List.drop n xs) (denote_symbol_lift_drop n Φ))
  | Regex.star y =>
    match xs with
    | [] => True
    | (x'::xs') =>
       ∃ (n: Fin xs.length),
         (denote_infix y (List.take (n + 1) (x'::xs')) (denote_symbol_lift_take (n + 1) Φ))
      /\ (denote_infix (Regex.star y) (List.drop (n + 1) (x'::xs')) (denote_symbol_lift_drop (n + 1) Φ))
  termination_by (xs.length, x)
  decreasing_by
    · apply denote_infix_sizeOf_or_left
    · apply denote_infix_sizeOf_or_right
    · apply denote_infix_sizeOf_concat_left
    · apply denote_infix_sizeOf_concat_right
    · apply denote_infix_sizeOf_star_left
    · apply denote_infix_sizeOf_star_right

-- denote_list has the same type signature as Regex.denote, but uses denote_infix.
-- We will prove that denote_list = Regex.denote
def denote_list {α: Type} {σ: Type} (denote_symbol: σ -> List α -> Prop) (r: Regex σ) (xs: List α): Prop :=
  denote_infix r xs (fun s (xs': List.InfixOf xs) => denote_symbol s xs'.val)

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

theorem denote_list_emptyset {α: Type} {σ: Type} (Φ: σ -> List α -> Prop):
  denote_list Φ Regex.emptyset
  = Language.emptyset := by
  funext xs
  simp only [denote_list, denote_infix, Language.emptyset]

theorem denote_list_emptystr {α: Type} {σ: Type} (Φ: σ -> List α -> Prop):
  denote_list Φ Regex.emptystr
  = Language.emptystr := by
  funext xs
  simp only [denote_list, denote_infix, Language.emptystr]

theorem denote_list_symbol {α: Type} {σ: Type} (Φ: σ -> List α -> Prop) (s: σ):
  denote_list Φ (Regex.symbol s)
  = Φ s := by
  funext xs
  simp only [denote_list, denote_infix, List.InfixOf.self]

theorem denote_list_or {α: Type} {σ: Type} (Φ: σ -> List α -> Prop) (p q: Regex σ):
  denote_list Φ (Regex.or p q)
  = Language.or (denote_list Φ p) (denote_list Φ q) := by
  unfold Language.or
  funext xs
  simp only [denote_list, denote_infix]

-- We need the lifting functions denote_symbol_lift_take and denote_symbol_lift_drop to prove denote_list_concat_n.
-- When we unfold the definitions of denote_list, denote_infix and Language.concat_n, we get the following goal:
-- ∃ n,
--   denote_infix p (List.take (↑n) xs) (denote_symbol_lift_take ↑n fun s xs' => Φ s ↑xs') ∧
--   denote_infix q (List.drop (↑n) xs) (denote_symbol_lift_drop ↑n fun s xs' => Φ s ↑xs')
-- =
-- ∃ n,
--   denote_infix p (List.take (↑n) xs) (fun s xs' => Φ s ↑xs') ∧
--   denote_infix q (List.drop (↑n) xs) (fun s xs' => Φ s ↑xs')
--
-- On closer inspection, we can fill in some of the types:
--
-- ∃ n,
--   denote_infix p (List.take (↑n) xs) (denote_symbol_lift_take ↑n fun s (xs': xs.InfixOf) => Φ s ↑xs') ∧
--   denote_infix q (List.drop (↑n) xs) (denote_symbol_lift_drop ↑n fun s (xs': xs.InfixOf) => Φ s ↑xs')
-- =
-- ∃ n,
--   denote_infix p (List.take (↑n) xs) (fun s (xs': (List.take (↑n) xs).InfixOf) => Φ s ↑xs') ∧
--   denote_infix q (List.drop (↑n) xs) (fun s (xs': (List.drop (↑n) xs).InfixOf) => Φ s ↑xs')
--
-- If we didn't have these lifting functions, then the two sides would have have been equal, except for the types of xs'.
-- The functions denote_symbol_lift_take and denote_symbol_lift_drop is used to make the types of xs' the same:
-- * denote_symbol_lift_take: (denote_symbol: σ -> List.InfixOf xs -> Prop) -> (σ -> List.InfixOf (List.take n xs) -> Prop)
-- * denote_symbol_lift_drop: (denote_symbol: σ -> List.InfixOf xs -> Prop) -> (σ -> List.InfixOf (List.drop n xs) -> Prop)
theorem denote_list_concat_n {α: Type} {σ: Type} (Φ: σ -> List α -> Prop) (p q: Regex σ):
  denote_list Φ (Regex.concat p q)
  = Language.concat_n (denote_list Φ p) (denote_list Φ q) := by
  funext xs
  simp only [denote_list, denote_infix, Language.concat_n]
  unfold denote_symbol_lift_drop
  unfold denote_symbol_lift_take
  unfold List.InfixOf.mk
  simp only

theorem denote_list_star_n_iff {α: Type} {σ: Type} (Φ: σ -> List α -> Prop) (r: Regex σ) (xs: List α):
  denote_list Φ (Regex.star r) xs
  <-> Language.star_n (denote_list Φ r) xs := by
  cases xs with
  | nil =>
    simp only [denote_list, denote_infix, Language.star_n]
  | cons x' xs' =>
    apply Iff.intro
    case mp =>
      intro h
      simp only [denote_list, denote_infix] at h
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
      simp only [denote_infix]
      exists ⟨n, hn⟩
      simp only at hp hq
      simp only
      apply And.intro hp
      unfold denote_symbol_lift_drop
      simp only
      unfold List.InfixOf.mk
      rw [<- denote_list]
      rw [denote_list_star_n_iff]
      exact hq
  termination_by xs.length

-- Just like concat_n, star_n also splits the string, using take and drop.
-- This means it also requires the lifting functions: denote_symbol_lift_take and denote_symbol_lift_drop to make this proof possible.
-- See denote_list_concat_n for details.
theorem denote_list_star_n {α: Type} {σ: Type} (Φ: σ -> List α -> Prop) (r: Regex σ):
  denote_list Φ (Regex.star r)
  = Language.star_n (denote_list Φ r) := by
  funext xs
  rw [denote_list_star_n_iff]

-- Given the above theorems it is easy to prove that the definition of denote_list is the equivalent to Regex.denote:
theorem denote_list_is_Regex.denote {α: Type} {σ: Type} (Φ: σ -> List α -> Prop) (r: Regex σ):
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
    rw [Regex.denote_symbol']
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

-- Helper theorems for proofs of functions that use denote_infix

theorem denote_infix_emptyset {α: Type} {σ: Type} (xs: List α) (Φ: σ -> List.InfixOf xs -> Prop):
  denote_infix Regex.emptyset xs Φ
  = Language.emptyset xs := by
  simp only [denote_infix, denote_infix, Language.emptyset]

theorem denote_infix_emptystr {α: Type} {σ: Type} (xs: List α) (Φ: σ -> List.InfixOf xs -> Prop):
  denote_infix Regex.emptystr xs Φ
  = Language.emptystr xs := by
  simp only [denote_infix, denote_infix, Language.emptystr]

theorem denote_infix_symbol {α: Type} {σ: Type} (xs: List α) (Φ: σ -> List.InfixOf xs -> Prop) (s: σ):
  denote_infix (Regex.symbol s) xs Φ
  = Φ s (List.InfixOf.self xs) := by
  simp only [denote_infix, denote_infix, List.InfixOf.self]

theorem denote_infix_or {α: Type} {σ: Type} (xs: List α) (Φ: σ -> List.InfixOf xs -> Prop) (p q: Regex σ):
  denote_infix (Regex.or p q) xs Φ
  = ((denote_infix p xs Φ) \/ (denote_infix q xs Φ)) := by
  simp only [denote_infix]

theorem denote_infix_concat_n {α: Type} {σ: Type} (xs: List α) (Φ: σ -> List.InfixOf xs -> Prop) (p q: Regex σ):
  denote_infix (Regex.concat p q) xs Φ
  = (∃ (n: Fin (xs.length + 1)),
       (denote_infix p (List.take n xs) (denote_symbol_lift_take n Φ))
    /\ (denote_infix q (List.drop n xs) (denote_symbol_lift_drop n Φ))) := by
  simp only [denote_infix]

theorem denote_infix_concat_n' {α: Type} {σ: Type} (xs: List α) (Φ: σ -> List.InfixOf xs -> Prop) (p q: Regex σ):
  denote_infix (Regex.concat p q) xs Φ
  = (∃ (n: Fin (xs.length + 1)),
       (denote_infix p (List.take n xs) (denote_symbol_lift_take n Φ))
    /\ (denote_infix q (List.drop n xs) (denote_symbol_lift_drop n Φ))) := by
  simp only [denote_infix]

theorem denote_infix_star_n {α: Type} {σ: Type} (xs: List α) (Φ: σ -> List.InfixOf xs -> Prop) (r: Regex σ):
  denote_infix (Regex.star r) xs Φ
  = (match xs with
    | [] => True
    | (x'::xs') =>
       ∃ (n: Fin xs.length),
         (denote_infix r (List.take (n + 1) (x'::xs')) (denote_symbol_lift_take (n + 1) Φ))
      /\ (denote_infix (Regex.star r) (List.drop (n + 1) (x'::xs')) (denote_symbol_lift_drop (n + 1) Φ))) := by
  cases xs with
  | nil =>
    simp [denote_infix]
  | cons x xs =>
    cases xs with
    | cons _ _ =>
      simp only [denote_infix]
    | nil =>
      simp only [denote_infix]
