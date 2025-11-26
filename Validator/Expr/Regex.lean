import Validator.Std.Hedge

import Validator.Expr.Pred
import Validator.Expr.Language

-- A regular expression is defined over a generic symbol
inductive Regex (σ: Type) where
  | emptyset
  | emptystr
  | symbol (s: σ)
  | or (p q: Regex σ)
  | concat (p q: Regex σ)
  | star (p: Regex σ)
  deriving DecidableEq, Ord, Repr, Hashable

instance [Ord α]: Ord (Regex α) := inferInstance

instance [Repr α]: Repr (Regex α) := inferInstance

instance [DecidableEq α]: DecidableEq (Regex α) := inferInstance

instance [DecidableEq α]: BEq (Regex α) := inferInstance

instance [Hashable α]: Hashable (Regex α) := inferInstance

def Regex.map (r: Regex α) (f: α -> β): Regex β :=
  match r with
  | emptyset => emptyset
  | emptystr => emptystr
  | symbol s => symbol (f s)
  | or r1 r2 => or (r1.map f) (r2.map f)
  | concat r1 r2 => concat (r1.map f) (r2.map f)
  | star r1 => star (r1.map f)

def Regex.first (r: Regex (α × β)): Regex α :=
  Regex.map r (fun (s, _) => s)

-- A regular expression is denoted as usual, expect that allow the user to inject the denotation of the generic symbol, dσ.
-- This allows us to handle generic predicates or even trees, without extending the original regular expression with new operators.
def Regex.denote {α: Type} {σ: Type} (dσ : σ -> List α -> Prop) (r: Regex σ): (xs: List α) -> Prop :=
  match r with
  | Regex.emptyset => Language.emptyset
  | Regex.emptystr => Language.emptystr
  | Regex.symbol s => dσ s
  | Regex.or p q => Language.or (denote dσ p) (denote dσ q)
  | Regex.concat p q => Language.concat_n (denote dσ p) (denote dσ q)
  | Regex.star p => Language.star_n (denote dσ p)

def Regex.nullable {σ: Type} (r: Regex σ): Bool :=
  match r with
  | Regex.emptyset => false
  | Regex.emptystr => true
  | Regex.symbol _ => false
  | Regex.or p q => Regex.nullable p || Regex.nullable q
  | Regex.concat p q => Regex.nullable p && Regex.nullable q
  | Regex.star _ => true

def Regex.unescapable (x: Regex σ): Bool :=
  match x with
  | Regex.emptyset => true
  | _ => false

def Regex.onlyif (cond: Prop) [dcond: Decidable cond] (x: Regex σ): Regex σ :=
  if cond then x else Regex.emptyset

def Regex.smartOr (x y: Regex σ): Regex σ :=
  match x with
  | Regex.emptyset => y
  | _ =>
    match y with
    | Regex.emptyset => x
    | _ => Regex.or x y

def Regex.smartConcat (x y: Regex σ): Regex σ :=
  match x with
  | Regex.emptyset => Regex.emptyset
  | Regex.emptystr => y
  | _ =>
    match y with
    | Regex.emptyset => Regex.emptyset
    | Regex.emptystr => x
    | _ => Regex.concat x y

def Regex.smartStar (x: Regex σ): Regex σ :=
  match x with
  | Regex.star _ => x
  | Regex.emptyset => Regex.emptystr
  | _ => Regex.star x

-- We prove that for each regular expression the denotation holds for the specific language definition:
-- * Regex.denote dσ Regex.emptyset = Language.emptyset
-- * Regex.denote dσ Regex.emptystr = Language.emptystr
-- * Regex.denote dσ (Regex.symbol s) = dσ s
-- * Regex.denote dσ (Regex.or p q) = Language.or (Regex.denote dσ p) (Regex.denote dσ q)
-- * Regex.denote dσ (Regex.concat p q) = Language.concat_n (Regex.denote dσ p) (Regex.denote dσ q)
-- * Regex.denote dσ (Regex.star r) = Language.star_n (Regex.denote dσ r)

theorem Regex.denote_emptyset {α: Type} {σ: Type} (denote_symbol: σ -> List α -> Prop):
  Regex.denote denote_symbol Regex.emptyset = Language.emptyset := by
  simp only [Regex.denote]

theorem Regex.denote_emptystr {α: Type} {σ: Type} (denote_symbol: σ -> List α -> Prop):
  Regex.denote denote_symbol Regex.emptystr = Language.emptystr := by
  simp only [Regex.denote]

theorem Regex.denote_symbol {α: Type} {σ: Type} (denote_symbol: σ -> List α -> Prop) (s: σ):
  Regex.denote denote_symbol (Regex.symbol s) = Language.symbol denote_symbol s := by
  simp only [Regex.denote]
  unfold Language.symbol
  rfl

theorem Regex.denote_symbol' {α: Type} {σ: Type} (denote_symbol: σ -> List α -> Prop) (s: σ):
  Regex.denote denote_symbol (Regex.symbol s) = denote_symbol s := by
  simp only [Regex.denote]

theorem Regex.denote_or {α: Type} {σ: Type} (denote_symbol: σ -> List α -> Prop) (p q: Regex σ):
  Regex.denote denote_symbol (Regex.or p q) = Language.or (Regex.denote denote_symbol p) (Regex.denote denote_symbol q) := by
  funext
  simp only [Regex.denote, Language.or]

theorem Regex.denote_concat_n {α: Type} {σ: Type} (denote_symbol: σ -> List α -> Prop) (p q: Regex σ):
  Regex.denote denote_symbol (Regex.concat p q) = Language.concat_n (Regex.denote denote_symbol p) (Regex.denote denote_symbol q) := by
  funext
  simp only [Regex.denote]

theorem Regex.denote_star_n' {α: Type} {σ: Type} (denote_symbol: σ -> List α -> Prop) (r: Regex σ) (xs: List α):
  Regex.denote denote_symbol (Regex.star r) xs <-> Language.star_n (Regex.denote denote_symbol r) xs := by
  simp only [Regex.denote]

theorem Regex.denote_star_n {α: Type} {σ: Type} (denote_symbol: σ -> List α -> Prop) (r: Regex σ):
  Regex.denote denote_symbol (Regex.star r) = Language.star_n (Regex.denote denote_symbol r) := by
  simp only [Regex.denote]

-- Here follows theorems for proving termination of Regex.denote_infix

theorem Regex.denote_infix_sizeOf_or_left {α: Type} {σ: Type} {p q: Regex σ} {xs: List α}:
  Prod.Lex (fun x1 x2 => x1 < x2) (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂) (xs.length, p) (xs.length, Regex.or p q) := by
  apply Prod.Lex.right
  simp only [Regex.or.sizeOf_spec]
  omega

theorem Regex.denote_infix_sizeOf_or_right {α: Type} {σ: Type} {p q: Regex σ} {xs: List α}:
  Prod.Lex (fun x1 x2 => x1 < x2) (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂) (xs.length, q) (xs.length, Regex.or p q) := by
  apply Prod.Lex.right
  simp only [Regex.or.sizeOf_spec]
  omega

theorem Regex.denote_infix_sizeOf_concat_left {α: Type} {σ: Type} {p q: Regex σ} {xs: List α}:
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

theorem Regex.denote_infix_sizeOf_concat_right {α: Type} {σ: Type} {p q: Regex σ} {xs: List α}:
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

theorem Regex.denote_infix_sizeOf_star_left {α: Type} {σ: Type} {p: Regex σ} {xs: List α}:
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

theorem Regex.denote_infix_sizeOf_star_right {α: Type} {σ: Type} {p: Regex σ} {x: α} {xs: List α}:
  Prod.Lex (fun x1 x2 => x1 < x2) (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂) ((List.drop (n + 1) (x::xs)).length, Regex.star p) ((x::xs).length, Regex.star p) := by
  simp only [List.drop_succ_cons, List.length_drop, List.length_cons]
  apply Prod.Lex.left
  omega

-- denote_symbol_lift_take and denote_symbol_lift_drop is used by Regex.denote_infix to lift
--   a denote_symbol function to work on an infix of the original infix:
-- * (denote_symbol: σ -> List.InfixOf xs -> Prop) -> (σ -> List.InfixOf (List.take n xs) -> Prop)
-- * (denote_symbol: σ -> List.InfixOf xs -> Prop) -> (σ -> List.InfixOf (List.drop n xs) -> Prop)
-- This works, because take and drop create infixes of a list and the infix of an infix is an infix.
-- We need these lifting functions to make the prove that Regex.denote_list = Regex.denote possible.
-- See Regex.denote_list_concat_n and Regex.denote_list_star_n for the exact detail.

def denote_symbol_lift_take (n: Nat) (denote_symbol: σ -> List.InfixOf xs -> Prop): (σ -> List.InfixOf (List.take n xs) -> Prop) :=
  fun (s: σ) (ys: List.InfixOf (List.take n xs)) =>
    denote_symbol s (List.InfixOf.mk ys.val (by apply List.list_infixof_take_is_infix))

def denote_symbol_lift_drop (n: Nat) (denote_symbol: σ -> List.InfixOf xs -> Prop): (σ -> List.InfixOf (List.drop n xs) -> Prop) :=
  fun (s: σ) (ys: List.InfixOf (List.drop n xs)) =>
    denote_symbol s (List.InfixOf.mk ys.val (by apply List.list_infixof_drop_is_infix))

-- Regex.denote_infix is an alternative version of Regex.denote that is later proven to be equivalent definitions.
-- The difference is that the denote_symbol function now has a relationship with the original input list, List.InfixOf.
-- This relationship is used for proving termination of regular expressions on trees.
-- The only other changes is that Regex.denote_infix contains unfolded versions of Language.or, Language.concat_n and Language.star_n.
def Regex.denote_infix
  {α: Type} {σ: Type}
  (x: Regex σ) (xs: List α) (dσ: σ -> List.InfixOf xs -> Prop): Prop :=
  match x with
  | Regex.emptyset => Language.emptyset xs
  | Regex.emptystr => Language.emptystr xs
  | Regex.symbol s => dσ s (List.InfixOf.self xs)
  | Regex.or y z =>
       (Regex.denote_infix y xs dσ)
    \/ (Regex.denote_infix z xs dσ)
  | Regex.concat y z =>
     ∃ (n: Fin (xs.length + 1)),
       (Regex.denote_infix y (List.take n xs) (denote_symbol_lift_take n dσ))
    /\ (Regex.denote_infix z (List.drop n xs) (denote_symbol_lift_drop n dσ))
  | Regex.star y =>
    match xs with
    | [] => True
    | (x'::xs') =>
       ∃ (n: Fin xs.length),
         (Regex.denote_infix y (List.take (n + 1) (x'::xs')) (denote_symbol_lift_take (n + 1) dσ))
      /\ (Regex.denote_infix (Regex.star y) (List.drop (n + 1) (x'::xs')) (denote_symbol_lift_drop (n + 1) dσ))
  termination_by (xs.length, x)
  decreasing_by
    · apply Regex.denote_infix_sizeOf_or_left
    · apply Regex.denote_infix_sizeOf_or_right
    · apply Regex.denote_infix_sizeOf_concat_left
    · apply Regex.denote_infix_sizeOf_concat_right
    · apply Regex.denote_infix_sizeOf_star_left
    · apply Regex.denote_infix_sizeOf_star_right

-- Regex.denote_list has the same type signature as Regex.denote, but uses Regex.denote_infix.
-- We will prove that Regex.denote_list = Regex.denote
def Regex.denote_list {α: Type} {σ: Type} (denote_symbol: σ -> List α -> Prop) (r: Regex σ) (xs: List α): Prop :=
  Regex.denote_infix r xs (fun s (xs': List.InfixOf xs) => denote_symbol s xs'.val)

-- We want to prove the correctness of our denote_list denotation function,
-- by proving it is equivalent to the original Regex.denote function:
-- * Regex.denote_list dσ r = Regex.denote dσ r
-- For this we need to prove the following helper theorems:
-- * Regex.denote_list dσ Regex.emptyset = Language.emptyset
-- * Regex.denote_list dσ Regex.emptystr = Language.emptystr
-- * Regex.denote_list dσ (Regex.symbol s) = dσ s
-- * Regex.denote_list dσ (Regex.or p q) = Language.or (Regex.denote_list dσ p) (Regex.denote_list dσ q)
-- * Regex.denote_list dσ (Regex.concat p q) = Language.concat_n (Regex.denote_list dσ p) (Regex.denote_list dσ q)
-- * Regex.denote_list dσ (Regex.star r) = Language.star_n (Regex.denote_list dσ r)

theorem Regex.denote_list_emptyset {α: Type} {σ: Type} (dσ: σ -> List α -> Prop):
  Regex.denote_list dσ Regex.emptyset
  = Language.emptyset := by
  funext xs
  simp only [Regex.denote_list, Regex.denote_infix, Language.emptyset]

theorem Regex.denote_list_emptystr {α: Type} {σ: Type} (dσ: σ -> List α -> Prop):
  Regex.denote_list dσ Regex.emptystr
  = Language.emptystr := by
  funext xs
  simp only [Regex.denote_list, Regex.denote_infix, Language.emptystr]

theorem Regex.denote_list_symbol {α: Type} {σ: Type} (dσ: σ -> List α -> Prop) (s: σ):
  Regex.denote_list dσ (Regex.symbol s)
  = dσ s := by
  funext xs
  simp only [Regex.denote_list, Regex.denote_infix, List.InfixOf.self]

theorem Regex.denote_list_or {α: Type} {σ: Type} (dσ: σ -> List α -> Prop) (p q: Regex σ):
  Regex.denote_list dσ (Regex.or p q)
  = Language.or (Regex.denote_list dσ p) (Regex.denote_list dσ q) := by
  unfold Language.or
  funext xs
  simp only [Regex.denote_list, Regex.denote_infix]

-- We need the lifting functions denote_symbol_lift_take and denote_symbol_lift_drop to prove denote_list_concat_n.
-- When we unfold the definitions of Regex.denote_list, Regex.denote_infix and Language.concat_n, we get the following goal:
-- ∃ n,
--   Regex.denote_infix p (List.take (↑n) xs) (denote_symbol_lift_take ↑n fun s xs' => dσ s ↑xs') ∧
--   Regex.denote_infix q (List.drop (↑n) xs) (denote_symbol_lift_drop ↑n fun s xs' => dσ s ↑xs')
-- =
-- ∃ n,
--   Regex.denote_infix p (List.take (↑n) xs) (fun s xs' => dσ s ↑xs') ∧
--   Regex.denote_infix q (List.drop (↑n) xs) (fun s xs' => dσ s ↑xs')
--
-- On closer inspection, we can fill in some of the types:
--
-- ∃ n,
--   Regex.denote_infix p (List.take (↑n) xs) (denote_symbol_lift_take ↑n fun s (xs': xs.InfixOf) => dσ s ↑xs') ∧
--   Regex.denote_infix q (List.drop (↑n) xs) (denote_symbol_lift_drop ↑n fun s (xs': xs.InfixOf) => dσ s ↑xs')
-- =
-- ∃ n,
--   Regex.denote_infix p (List.take (↑n) xs) (fun s (xs': (List.take (↑n) xs).InfixOf) => dσ s ↑xs') ∧
--   Regex.denote_infix q (List.drop (↑n) xs) (fun s (xs': (List.drop (↑n) xs).InfixOf) => dσ s ↑xs')
--
-- If we didn't have these lifting functions, then the two sides would have have been equal, except for the types of xs'.
-- The functions denote_symbol_lift_take and denote_symbol_lift_drop is used to make the types of xs' the same:
-- * denote_symbol_lift_take: (denote_symbol: σ -> List.InfixOf xs -> Prop) -> (σ -> List.InfixOf (List.take n xs) -> Prop)
-- * denote_symbol_lift_drop: (denote_symbol: σ -> List.InfixOf xs -> Prop) -> (σ -> List.InfixOf (List.drop n xs) -> Prop)
theorem Regex.denote_list_concat_n {α: Type} {σ: Type} (dσ: σ -> List α -> Prop) (p q: Regex σ):
  Regex.denote_list dσ (Regex.concat p q)
  = Language.concat_n (Regex.denote_list dσ p) (Regex.denote_list dσ q) := by
  funext xs
  simp only [Regex.denote_list, Regex.denote_infix, Language.concat_n]
  unfold denote_symbol_lift_drop
  unfold denote_symbol_lift_take
  unfold List.InfixOf.mk
  simp only

theorem Regex.denote_list_star_n_iff {α: Type} {σ: Type} (dσ: σ -> List α -> Prop) (r: Regex σ) (xs: List α):
  Regex.denote_list dσ (Regex.star r) xs
  <-> Language.star_n (Regex.denote_list dσ r) xs := by
  cases xs with
  | nil =>
    simp only [Regex.denote_list, Regex.denote_infix, Language.star_n]
  | cons x' xs' =>
    apply Iff.intro
    case mp =>
      intro h
      simp only [Regex.denote_list, Regex.denote_infix] at h
      simp only [Regex.denote_list, Language.star_n]
      obtain ⟨⟨n, hn⟩, ⟨hp, hq⟩⟩ := h
      exists ⟨n, hn⟩
      simp only at hp hq
      simp only
      apply And.intro hp
      rw [<- Regex.denote_list_star_n_iff]
      simp only [Regex.denote_list]
      exact hq
    case mpr =>
      intro h
      simp only [Language.star_n] at h
      obtain ⟨⟨n, hn⟩, ⟨hp, hq⟩⟩ := h
      simp only [Regex.denote_list]
      simp only [Regex.denote_infix]
      exists ⟨n, hn⟩
      simp only at hp hq
      simp only
      apply And.intro hp
      unfold denote_symbol_lift_drop
      simp only
      unfold List.InfixOf.mk
      rw [<- Regex.denote_list]
      rw [Regex.denote_list_star_n_iff]
      exact hq
  termination_by xs.length

-- Just like concat_n, star_n also splits the string, using take and drop.
-- This means it also requires the lifting functions: denote_symbol_lift_take and denote_symbol_lift_drop to make this proof possible.
-- See denote_list_concat_n for details.
theorem Regex.denote_list_star_n {α: Type} {σ: Type} (dσ: σ -> List α -> Prop) (r: Regex σ):
  Regex.denote_list dσ (Regex.star r)
  = Language.star_n (Regex.denote_list dσ r) := by
  funext xs
  rw [Regex.denote_list_star_n_iff]

-- Given the above theorems it is easy to prove that the definition of Regex.denote_list is the equivalent to Regex.denote:
theorem Regex.denote_list_is_Regex.denote {α: Type} {σ: Type} (dσ: σ -> List α -> Prop) (r: Regex σ):
  Regex.denote_list dσ r = Regex.denote dσ r := by
  induction r with
  | emptyset =>
    rw [Regex.denote_list_emptyset]
    rw [Regex.denote_emptyset]
  | emptystr =>
    rw [Regex.denote_list_emptystr]
    rw [Regex.denote_emptystr]
  | symbol s =>
    rw [Regex.denote_list_symbol]
    rw [Regex.denote_symbol']
  | or p q ihp ihq =>
    rw [Regex.denote_list_or]
    rw [Regex.denote_or]
    rw [ihp]
    rw [ihq]
  | concat p q ihp ihq =>
    rw [Regex.denote_list_concat_n]
    rw [Regex.denote_concat_n]
    rw [ihp]
    rw [ihq]
  | star p ihp =>
    rw [Regex.denote_list_star_n]
    rw [Regex.denote_star_n]
    rw [ihp]

-- Helper theorems for proofs of functions that use Regex.denote_infix

theorem Regex.denote_infix_emptyset {α: Type} {σ: Type} (xs: List α) (dσ: σ -> List.InfixOf xs -> Prop):
  Regex.denote_infix Regex.emptyset xs dσ
  = Language.emptyset xs := by
  simp only [Regex.denote_infix, Regex.denote_infix, Language.emptyset]

theorem Regex.denote_infix_emptystr {α: Type} {σ: Type} (xs: List α) (dσ: σ -> List.InfixOf xs -> Prop):
  Regex.denote_infix Regex.emptystr xs dσ
  = Language.emptystr xs := by
  simp only [Regex.denote_infix, Regex.denote_infix, Language.emptystr]

theorem Regex.denote_infix_symbol {α: Type} {σ: Type} (xs: List α) (dσ: σ -> List.InfixOf xs -> Prop) (s: σ):
  Regex.denote_infix (Regex.symbol s) xs dσ
  = dσ s (List.InfixOf.self xs) := by
  simp only [Regex.denote_infix, Regex.denote_infix, List.InfixOf.self]

theorem Regex.denote_infix_or {α: Type} {σ: Type} (xs: List α) (dσ: σ -> List.InfixOf xs -> Prop) (p q: Regex σ):
  Regex.denote_infix (Regex.or p q) xs dσ
  = ((Regex.denote_infix p xs dσ) \/ (Regex.denote_infix q xs dσ)) := by
  simp only [Regex.denote_infix]

theorem Regex.denote_infix_concat_n {α: Type} {σ: Type} (xs: List α) (dσ: σ -> List.InfixOf xs -> Prop) (p q: Regex σ):
  Regex.denote_infix (Regex.concat p q) xs dσ
  = (∃ (n: Fin (xs.length + 1)),
       (Regex.denote_infix p (List.take n xs) (denote_symbol_lift_take n dσ))
    /\ (Regex.denote_infix q (List.drop n xs) (denote_symbol_lift_drop n dσ))) := by
  simp only [Regex.denote_infix]

theorem Regex.denote_infix_concat_n' {α: Type} {σ: Type} (xs: List α) (dσ: σ -> List.InfixOf xs -> Prop) (p q: Regex σ):
  Regex.denote_infix (Regex.concat p q) xs dσ
  = (∃ (n: Fin (xs.length + 1)),
       (Regex.denote_infix p (List.take n xs) (denote_symbol_lift_take n dσ))
    /\ (Regex.denote_infix q (List.drop n xs) (denote_symbol_lift_drop n dσ))) := by
  simp only [Regex.denote_infix]

theorem Regex.denote_infix_star_n {α: Type} {σ: Type} (xs: List α) (dσ: σ -> List.InfixOf xs -> Prop) (r: Regex σ):
  Regex.denote_infix (Regex.star r) xs dσ
  = (match xs with
    | [] => True
    | (x'::xs') =>
       ∃ (n: Fin xs.length),
         (Regex.denote_infix r (List.take (n + 1) (x'::xs')) (denote_symbol_lift_take (n + 1) dσ))
      /\ (Regex.denote_infix (Regex.star r) (List.drop (n + 1) (x'::xs')) (denote_symbol_lift_drop (n + 1) dσ))) := by
  cases xs with
  | nil =>
    simp [Regex.denote_infix]
  | cons x xs =>
    cases xs with
    | cons _ _ =>
      simp only [Regex.denote_infix]
    | nil =>
      simp only [Regex.denote_infix]

def Regex.derive {σ: Type} {α: Type} (p: σ -> α -> Bool) (r: Regex σ) (a: α): Regex σ :=
  match r with
  | emptyset => emptyset
  | emptystr => emptyset
  | symbol s =>
    if p s a
    then emptystr
    else emptyset
  | or r1 r2 =>
    or (derive p r1 a) (derive p r2 a)
  | concat r1 r2 =>
    if nullable r1
    then or
      (concat (derive p r1 a) r2)
      (derive p r2 a)
    else
      (concat (derive p r1 a) r2)
  | star r1 =>
    concat (derive p r1 a) (star r1)

-- derive2 is the same as derive, except the answer to the predicate is already included in a tuple with the original symbol.
def Regex.derive2 {σ: Type} (r: Regex (σ × Bool)): Regex σ :=
  match r with
  | emptyset => emptyset
  | emptystr => emptyset
  | symbol (_, b) =>
    if b
    then emptystr
    else emptyset
  | or r1 r2 =>
    or (derive2 r1) (derive2 r2)
  | concat r1 r2 =>
    if nullable r1
    then
      or (concat (derive2 r1) (first r2)) (derive2 r2)
    else
      concat (derive2 r1) (first r2)
  | star r1 =>
      concat (derive2 r1) (star (first r1))

theorem map_first (p: σ -> α -> Bool) (r: Regex σ) (a: α):
  (r.map (fun s => (s, p s a))).first = r := by
  induction r with
  | emptyset =>
    simp only [Regex.map, Regex.first]
  | emptystr =>
    simp only [Regex.map, Regex.first]
  | symbol _ =>
    simp only [Regex.map, Regex.first]
  | or r1 r2 ih1 ih2 =>
    simp only [Regex.map, Regex.first]
    simp_all only [Regex.or.injEq]
    apply And.intro
    · exact ih1
    · exact ih2
  | concat r1 r2 ih1 ih2 =>
    simp only [Regex.map, Regex.first]
    simp_all only [Regex.concat.injEq]
    apply And.intro
    · exact ih1
    · exact ih2
  | star r1 ih1 =>
    simp only [Regex.map, Regex.first]
    simp_all only [Regex.star.injEq]
    exact ih1

theorem map_nullable (p: σ -> α -> Bool) (r: Regex σ) (a: α):
  (r.map (fun s => (s, p s a))).nullable = r.nullable := by
  induction r with
  | emptyset =>
    simp only [Regex.map, Regex.nullable]
  | emptystr =>
    simp only [Regex.map, Regex.nullable]
  | symbol _ =>
    simp only [Regex.map, Regex.nullable]
  | or r1 r2 ih1 ih2 =>
    simp only [Regex.map, Regex.nullable]
    simp_all only
  | concat r1 r2 ih1 ih2 =>
    simp only [Regex.map, Regex.nullable]
    simp_all only
  | star r1 ih1 =>
    simp only [Regex.map, Regex.nullable]

theorem Regex.derive_is_derive2 (p: σ -> α -> Bool) (r: Regex σ) (a: α):
  derive p r a = derive2 (map r (fun s => (s, p s a))) := by
  induction r with
  | emptyset =>
    simp only [Regex.derive, Regex.map, Regex.derive2]
  | emptystr =>
    simp only [Regex.derive, Regex.map, Regex.derive2]
  | symbol _ =>
    simp only [Regex.derive, Regex.map, Regex.derive2]
  | or r1 r2 ih1 ih2 =>
    simp only [Regex.derive, Regex.map, Regex.derive2]
    rw [<- ih1]
    rw [<- ih2]
  | concat r1 r2 ih1 ih2 =>
    simp only [Regex.derive, Regex.map, Regex.derive2]
    rw [<- ih1]
    rw [<- ih2]
    have h : (r2.map fun s => (s, p s a)).first = r2 := by
      apply map_first
    have h' : (r1.map fun s => (s, p s a)).nullable = r1.nullable := by
      apply map_nullable
    rw [h]
    rw [h']
  | star r1 ih1 =>
    simp only [Regex.derive, Regex.map, Regex.derive2]
    rw [<- ih1]
    have h : (r1.map fun s => (s, p s a)).first = r1 := by
      apply map_first
    rw [h]

def Regex.smartDerive2 {σ: Type} (r: Regex (σ × Bool)): Regex σ :=
  match r with
  | emptyset => emptyset
  | emptystr => emptyset
  | symbol (_, b) =>
    if b
    then emptystr
    else emptyset
  | or r1 r2 =>
    smartOr (derive2 r1) (derive2 r2)
  | concat r1 r2 =>
    if nullable r1
    then
      smartOr (smartConcat (derive2 r1) (first r2)) (derive2 r2)
    else
      smartConcat (derive2 r1) (first r2)
  | star r1 =>
      smartConcat (derive2 r1) (smartStar (first r1))
