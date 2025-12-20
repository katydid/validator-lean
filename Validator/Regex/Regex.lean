import Validator.Std.Vec

import Validator.Regex.Language

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

namespace Regex

-- A regular expression is denoted as usual, expect that allow the user to inject the denotation of the generic symbol, Φ.
-- This allows us to handle generic predicates or even trees, without extending the original regular expression with new operators.
def denote {α: Type} {σ: Type} (Φ : σ -> α -> Prop) (r: Regex σ): (xs: List α) -> Prop :=
  match r with
  | emptyset => Language.emptyset
  | emptystr => Language.emptystr
  | symbol s => Language.symbol_pred Φ s
  | or p q => Language.or (denote Φ p) (denote Φ q)
  | concat p q => Language.concat_n (denote Φ p) (denote Φ q)
  | star p => Language.star_n (denote Φ p)

def null {σ: Type} (r: Regex σ): Bool :=
  match r with
  | emptyset => false
  | emptystr => true
  | symbol _ => false
  | or p q => null p || null q
  | concat p q => null p && null q
  | star _ => true

def unescapable (x: Regex σ): Bool :=
  match x with
  | emptyset => true
  | _ => false

def onlyif (cond: Prop) [dcond: Decidable cond] (x: Regex σ): Regex σ :=
  if cond then x else emptyset

def denote_onlyif {α: Type} (Φ : σ -> α -> Prop) (condition: Prop) [dcond: Decidable condition] (r: Regex σ):
  denote Φ (onlyif condition r) = Language.onlyif condition (denote Φ r) := by
  unfold Language.onlyif
  unfold onlyif
  funext xs
  split_ifs
  case pos hc =>
    simp only [eq_iff_iff, iff_and_self]
    intro d
    assumption
  case neg hc =>
    simp only [eq_iff_iff]
    rw [denote]
    rw [Language.emptyset]
    simp only [false_iff, not_and]
    intro hc'
    contradiction

def derive {σ: Type} {α: Type} (Φ: σ -> α -> Bool) (r: Regex σ) (a: α): Regex σ :=
  match r with
  | emptyset => emptyset
  | emptystr => emptyset
  | symbol s => onlyif (Φ s a) emptystr
  | or r1 r2 => or (derive Φ r1 a) (derive Φ r2 a)
  | concat r1 r2 =>
    or
      (concat (derive Φ r1 a) r2)
      (onlyif (null r1) (derive Φ r2 a))
  | star r1 => concat (derive Φ r1 a) (star r1)

def derives (Φ: σ -> α -> Bool) (rs: Vec (Regex σ) l) (a: α): Vec (Regex σ) l :=
  Vec.map rs (fun r => derive Φ r a)

-- We prove that for each regular expression the denotation holds for the specific language definition:
-- * Regex.denote Φ Regex.emptyset = Language.emptyset
-- * Regex.denote Φ Regex.emptystr = Language.emptystr
-- * Regex.denote Φ (Regex.symbol s) = Φ s
-- * Regex.denote Φ (Regex.or p q) = Language.or (Regex.denote Φ p) (Regex.denote Φ q)
-- * Regex.denote Φ (Regex.concat p q) = Language.concat_n (Regex.denote Φ p) (Regex.denote Φ q)
-- * Regex.denote Φ (Regex.star r) = Language.star_n (Regex.denote Φ r)

theorem denote_emptyset {α: Type} {σ: Type} (Φ: σ -> α -> Prop):
  denote Φ emptyset = Language.emptyset := by
  simp only [denote]

theorem denote_emptystr {α: Type} {σ: Type} (Φ: σ -> α -> Prop):
  denote Φ emptystr = Language.emptystr := by
  simp only [denote]

theorem denote_symbol_pred {α: Type} {σ: Type} (Φ: σ -> α -> Prop) (s: σ):
  denote Φ (symbol s) = Language.symbol_pred Φ s := by
  simp only [denote]

theorem denote_or {α: Type} {σ: Type} (Φ: σ -> α -> Prop) (p q: Regex σ):
  denote Φ (or p q) = Language.or (denote Φ p) (denote Φ q) := by
  funext
  simp only [denote, Language.or]

theorem denote_concat_n {α: Type} {σ: Type} (Φ: σ -> α -> Prop) (p q: Regex σ):
  denote Φ (concat p q) = Language.concat_n (denote Φ p) (denote Φ q) := by
  funext
  simp only [denote]

theorem denote_star_n' {α: Type} {σ: Type} (Φ: σ -> α -> Prop) (r: Regex σ) (xs: List α):
  denote Φ (star r) xs <-> Language.star_n (denote Φ r) xs := by
  simp only [denote]

theorem denote_star_n {α: Type} {σ: Type} (Φ: σ -> α -> Prop) (r: Regex σ):
  denote Φ (star r) = Language.star_n (denote Φ r) := by
  simp only [denote]
