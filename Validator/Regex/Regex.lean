import Validator.Std.Vec

import Validator.Regex.Language

-- A regular expression is defined over a generic symbol
inductive Regex (σ: Type) where
  | emptyset
  | emptystr
  | symbol (s: σ)
  | or (r1 r2: Regex σ)
  | concat (r1 r2: Regex σ)
  | star (r1: Regex σ)
  deriving DecidableEq, Ord, Repr, Hashable

instance [Ord σ]: Ord (Regex σ) := inferInstance

instance [Repr σ]: Repr (Regex σ) := inferInstance

instance [DecidableEq σ]: DecidableEq (Regex σ) := inferInstance

instance [DecidableEq σ]: BEq (Regex σ) := inferInstance

instance [Hashable σ]: Hashable (Regex σ) := inferInstance

namespace Regex

-- A regular expression is denoted as usual, expect that allow the user to inject the denotation of the generic symbol, Φ.
-- This allows us to handle generic predicates or even trees, without extending the original regular expression with new operators.
def denote {α: Type} {σ: Type} (Φ : σ -> α -> Prop) (r: Regex σ): (xs: List α) -> Prop :=
  match r with
  | emptyset => Language.emptyset
  | emptystr => Language.emptystr
  | symbol s => Language.symbol Φ s
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

def map_derive (Φ: σ -> α -> Bool) (rs: Vec (Regex σ) l) (a: α): Vec (Regex σ) l :=
  Vec.map rs (fun r => derive Φ r a)

def fold_derive (Φ: σ -> α -> Bool) (r: Regex σ) (xs: List α): Regex σ :=
  (List.foldl (derive Φ) r) xs

def validate (Φ: σ -> α -> Bool) (r: Regex σ) (xs: List α): Bool :=
  null (fold_derive Φ r xs)

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

theorem denote_symbol {α: Type} {σ: Type} (Φ: σ -> α -> Prop) (s: σ):
  denote Φ (symbol s) = Language.symbol Φ s := by
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

-- Commutes proofs

theorem null_commutes {σ: Type} {α: Type} (Φ: σ -> α -> Prop) (r: Regex σ):
  ((null r) = true) = Language.null (denote Φ r) := by
  induction r with
  | emptyset =>
    unfold denote
    rw [Language.null_emptyset]
    unfold null
    apply Bool.false_eq_true
  | emptystr =>
    unfold denote
    rw [Language.null_emptystr]
    unfold null
    simp only
  | symbol p =>
    unfold denote
    rw [Language.null_symbol]
    unfold null
    apply Bool.false_eq_true
  | or p q ihp ihq =>
    unfold denote
    rw [Language.null_or]
    unfold null
    rw [<- ihp]
    rw [<- ihq]
    rw [Bool.or_eq_true]
  | concat p q ihp ihq =>
    unfold denote
    rw [Language.null_concat_n]
    unfold null
    rw [<- ihp]
    rw [<- ihq]
    rw [Bool.and_eq_true]
  | star r ih =>
    unfold denote
    rw [Language.null_star_n]
    unfold null
    simp only

theorem derive_commutes {σ: Type} {α: Type} (Φ: σ -> α -> Prop) [DecidableRel Φ] (r: Regex σ) (x: α):
  denote Φ (derive (fun s a => Φ s a) r x) = Language.derive (denote Φ r) x := by
  induction r with
  | emptyset =>
    simp only [denote, derive]
    rw [Language.derive_emptyset]
  | emptystr =>
    simp only [denote, derive]
    rw [Language.derive_emptystr]
  | symbol p =>
    simp only [denote]
    rw [Language.derive_symbol]
    unfold derive
    rw [denote_onlyif]
    simp only [denote]
    simp only [decide_eq_true_eq]
  | or p q ihp ihq =>
    simp only [denote, derive]
    rw [Language.derive_or]
    unfold Language.or
    rw [ihp]
    rw [ihq]
  | concat p q ihp ihq =>
    simp only [denote, derive]
    rw [Language.derive_concat_n]
    rw [<- ihp]
    rw [<- ihq]
    rw [denote_onlyif]
    congrm (Language.or (Language.concat_n (denote Φ (derive (fun s a => Φ s a) p x)) (denote Φ q)) ?_)
    rw [null_commutes]
  | star r ih =>
    simp only [denote, derive]
    rw [Language.derive_star_n]
    guard_target =
      Language.concat_n (denote Φ (derive (fun s a => Φ s a) r x)) (Language.star_n (denote Φ r))
      = Language.concat_n (Language.derive (denote Φ r) x) (Language.star_n (denote Φ r))
    congrm ((Language.concat_n ?_ (Language.star_n (denote Φ r))))
    guard_target = denote Φ (derive (fun s a => Φ s a) r x) = Language.derive (denote Φ r) x
    exact ih

theorem derive_commutesb {σ: Type} {α: Type} (Φ: σ -> α -> Bool) (r: Regex σ) (x: α):
  denote (fun s a => Φ s a) (derive (fun s a => Φ s a) r x) = Language.derive (denote (fun s a => Φ s a) r) x := by
  rw [<- derive_commutes]
  congr
  funext s a
  simp only [Bool.decide_eq_true]

theorem derives_commutes {α: Type} (Φ: σ -> α -> Prop) [DecidableRel Φ] (r: Regex σ) (xs: List α):
  denote Φ (fold_derive (fun s a => Φ s a) r xs) = Language.derives (denote Φ r) xs := by
  unfold fold_derive
  rw [Language.derives_foldl]
  induction xs generalizing r with
  | nil =>
    simp only [List.foldl_nil]
  | cons x xs ih =>
    simp only [List.foldl_cons]
    have h := derive_commutes Φ r x
    have ih' := ih (derive (fun s a => Φ s a) r x)
    rw [h] at ih'
    exact ih'

theorem validate_commutes {α: Type} (Φ: σ -> α -> Prop) [DecidableRel Φ] (r: Regex σ) (xs: List α):
  (validate (fun s a => Φ s a) r xs = true) = (denote Φ r) xs := by
  rw [<- Language.validate (denote Φ r) xs]
  unfold validate
  rw [<- derives_commutes]
  rw [<- null_commutes]

-- decidableDenote shows that the derivative algorithm is decidable
-- https://leanprover.zulipchat.com/#narrow/channel/270676-lean4/topic/restricting.20axioms
def decidableDenote (Φ: σ -> α -> Prop) [DecidableRel Φ] (r: Regex σ): DecidablePred (denote Φ r) :=
  fun xs => decidable_of_decidable_of_eq (validate_commutes Φ r xs)
