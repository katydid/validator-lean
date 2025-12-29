import Mathlib.Tactic.SimpRw

import Validator.Std.Hedge

import Validator.Regex.Room
import Validator.Hedge.Denote
import Validator.Hedge.Grammar
import Validator.Hedge.IfExpr

namespace Hedge.Grammar.Room

def derive {α: Type}
  (G: Grammar n φ) (Φ: φ -> α -> Bool)
  (r: Hedge.Grammar.Rule n φ) (x: Hedge.Node α): Hedge.Grammar.Rule n φ :=
  Regex.Room.derive (fun (symbol: Hedge.Grammar.Symbol n φ) =>
    match x with
    | Hedge.Node.mk label children =>
      let ifExpr: Hedge.Grammar.Symbol n φ := symbol
      let childr: Hedge.Grammar.Rule n φ := Hedge.Grammar.evalif G Φ ifExpr label
      let dchildr: Hedge.Grammar.Rule n φ := List.foldl (derive G Φ) childr children
      Hedge.Grammar.Rule.null dchildr
  ) r

theorem unapply_hedge_param_and_flip
  (G: Grammar n φ) (Φ: φ -> α -> Bool) (x: Hedge.Node α):
  (fun (symbol: Hedge.Grammar.Symbol n φ) =>
    match x with
    | Hedge.Node.mk label children =>
      let ifExpr: Hedge.Grammar.Symbol n φ := symbol
      let childr: Hedge.Grammar.Rule n φ := Hedge.Grammar.evalif G Φ ifExpr label
      let dchildr: Hedge.Grammar.Rule n φ := List.foldl (derive G Φ) childr children
      Hedge.Grammar.Rule.null dchildr
  )
  =
  (flip fun (symbol: Hedge.Grammar.Symbol n φ) (x': Hedge.Node α) =>
    match x' with
    | Hedge.Node.mk label children =>
      let ifExpr: Hedge.Grammar.Symbol n φ := symbol
      let childr: Hedge.Grammar.Rule n φ := Hedge.Grammar.evalif G Φ ifExpr label
      let dchildr: Hedge.Grammar.Rule n φ := List.foldl (derive G Φ) childr children
      Hedge.Grammar.Rule.null dchildr
  ) x := by
  rfl

theorem derive_emptyset {α: Type} (G: Grammar n φ) (Φ: φ -> α -> Bool) (a: Hedge.Node α):
  Hedge.Grammar.Room.derive G Φ Regex.emptyset a = Regex.emptyset := by
  unfold derive
  rw [unapply_hedge_param_and_flip]
  rw [Regex.Room.derive_emptyset]

theorem derive_emptystr {α: Type} (G: Grammar n φ) (Φ: φ -> α -> Bool) (a: Hedge.Node α):
  Hedge.Grammar.Room.derive G Φ Regex.emptystr a = Regex.emptyset := by
  unfold derive
  rw [unapply_hedge_param_and_flip]
  rw [Regex.Room.derive_emptystr]

theorem derive_symbol {α: Type} (G: Grammar n φ) (Φ: φ -> α -> Bool) (a: Hedge.Node α):
  Hedge.Grammar.Room.derive G Φ (Regex.symbol s) a
    = Regex.onlyif (
        ( match a with
          | Node.mk label children =>
            (List.foldl (derive G Φ) (G.evalif Φ s label) children).null
        ) = true)
        Regex.emptystr := by
  unfold derive
  rw [unapply_hedge_param_and_flip]
  rw [Regex.Room.derive_symbol]

theorem derive_or {α: Type} (G: Grammar n φ) (Φ: φ -> α -> Bool) (r1 r2: Rule n φ) (a: Hedge.Node α):
  Hedge.Grammar.Room.derive G Φ (Regex.or r1 r2) a
  = Regex.or (Hedge.Grammar.Room.derive G Φ r1 a) (Hedge.Grammar.Room.derive G Φ r2 a) := by
  unfold derive
  rw [unapply_hedge_param_and_flip]
  rw [Regex.Room.derive_or]

theorem derive_concat {α: Type} (G: Grammar n φ) (Φ: φ -> α -> Bool) (r1 r2: Rule n φ) (a: Hedge.Node α):
  Hedge.Grammar.Room.derive G Φ (Regex.concat r1 r2) a
    = Regex.or
      (Regex.concat (Hedge.Grammar.Room.derive G Φ r1 a) r2)
      (Regex.onlyif (Regex.null r1) (Hedge.Grammar.Room.derive G Φ r2 a)) := by
  unfold derive
  rw [unapply_hedge_param_and_flip]
  rw [Regex.Room.derive_concat]

theorem derive_star {α: Type} (G: Grammar n φ) (Φ: φ -> α -> Bool) (r1: Rule n φ) (a: Hedge.Node α):
  Hedge.Grammar.Room.derive G Φ (Regex.star r1) a
  = Regex.concat (Hedge.Grammar.Room.derive G Φ r1 a) (Regex.star r1) := by
  unfold derive
  rw [unapply_hedge_param_and_flip]
  rw [Regex.Room.derive_star]

theorem and_start {α: Type} (G: Hedge.Grammar n φ) (Φ: φ -> α -> Bool) (label: α) (children: Hedge α):
  ((List.foldl (derive G Φ) (if Φ p label = true then G.lookup ref else Regex.emptyset) children).null = true)
  = ((Φ p label = true) /\ ((List.foldl (derive G Φ) (G.lookup ref) children).null = true)) := by
  generalize (Φ p label) = pred
  generalize (G.lookup ref) = r
  split_ifs
  case pos h =>
    simp_all only [true_and]
  case neg h =>
    simp_all only [Bool.not_eq_true, Bool.false_eq_true, false_and, eq_iff_iff, iff_false]
    subst h
    induction children with
    | nil =>
      simp only [Rule.null, List.foldl_nil, Regex.null]
    | cons x xs ih =>
      simp only [List.foldl_cons]
      rw [derive_emptyset]
      rw [ih]

theorem derive_denote_symbol_is_onlyif {α: Type} (G: Hedge.Grammar n φ) (Φ: φ -> α -> Bool) (label: α) (children: Hedge α):
  Regex.Language.derive
    (Rule.denote G (fun s a => Φ s a = true)
      (Regex.symbol (pred, ref))
    )
    (Node.mk label children)
  =
    Regex.Language.onlyif
      (Φ pred label = true ∧ Rule.denote G (fun s a => Φ s a = true) (G.lookup ref) children)
    Regex.Language.emptystr
  := by
  funext xs
  rw [Hedge.Grammar.denote_symbol]
  rw [Hedge.Language.derive_iff_tree]
  simp only [Bool.decide_eq_true]

theorem derive_commutes_symbol {α: Type}
  (G: Hedge.Grammar n φ)
  (Φ: φ -> α -> Bool)
  (pred: φ)
  (ref: Ref n)
  (x4: Hedge.Node α)
  (xs: Hedge α)
  (ihr:
    ∀ (r: Hedge.Grammar.Rule n φ) (x3: Hedge.Node.DescendantOf x4) (xs: Hedge α),
        Hedge.Grammar.Rule.denote G (fun p a => Φ p a) (Hedge.Grammar.Room.derive G Φ r x3.val) xs
    <-> Regex.Language.derive (Hedge.Grammar.Rule.denote G (fun p a => Φ p a) r) x3.val xs
  )
  :
  Rule.denote G (fun s a => Φ s a = true) (derive G Φ (Regex.symbol (pred, ref)) x4) xs =
  Regex.Language.derive (Rule.denote G (fun s a => Φ s a = true) (Regex.symbol (pred, ref))) x4 xs := by
  cases x4 with
  | mk label children =>

  rw [derive_denote_symbol_is_onlyif]

  rw [derive_symbol]
  simp only
  rw [Hedge.Grammar.denote_onlyif]

  rw [Hedge.Grammar.denote_emptystr]
  congr

  simp only [evalif]
  simp only [and_start]
  congr

  generalize G.lookup ref = r
  induction children generalizing r with
  | nil =>
    simp only [List.foldl_nil]
    rw [Hedge.Grammar.denote_nil_is_null]
  | cons x2 xs ihxs =>
    simp only [List.foldl]
    rw [ihxs]
    · have hchild := Node.Descendant.mkFirstChild_eq label x2 xs
      have ihr := ihr (r := r) (x3 := hchild.val) (xs := xs)
      cases hchild with
      | mk hdes heq =>
      rw [<- heq]
      rw [ihr]
      rfl
    · intro r' x3 xs'
      have hcons := Node.Descendant.consFirstChild_eq x2 x3
      have ihr := ihr r' hcons.val xs'
      cases hcons with
      | mk hdes heq =>
      rw [<- heq]
      simp at ihr
      rw [ihr]
      rfl

theorem revert_param (f g: α -> β):
  f = g -> ∀ x, f x = g x := by
  intro a x
  subst a
  simp_all only

theorem derive_commutesb_iff {α: Type} (G: Hedge.Grammar n φ) (Φ: φ -> α -> Bool) (r: Hedge.Grammar.Rule n φ) (x: Hedge.Node α) (xs: Hedge α):
  Hedge.Grammar.Rule.denote G (fun s a => Φ s a) (Hedge.Grammar.Room.derive G Φ r x) xs
  <-> Regex.Language.derive (Hedge.Grammar.Rule.denote G (fun s a => Φ s a) r) x xs := by
  rw [<- eq_iff_iff]
  apply revert_param
  induction r with
  | emptyset =>
    rw [derive_emptyset]
    rw [Hedge.Grammar.denote_emptyset]
    rw [Regex.Language.derive_emptyset]
  | emptystr =>
    rw [derive_emptystr]
    rw [Hedge.Grammar.denote_emptystr]
    rw [Hedge.Grammar.denote_emptyset]
    rw [Regex.Language.derive_emptystr]
  | symbol s =>
    funext xs
    cases s with
    | mk pred ref =>
    let ihr :=
      fun (r: Hedge.Grammar.Rule n φ) (x7: Hedge.Node.DescendantOf x) (xs: Hedge α) =>
        derive_commutesb_iff G Φ r x7 xs
    rw [derive_commutes_symbol (ihr := ihr) (x4 := x)]
  | or r1 r2 ih1 ih2 =>
    rw [derive_or]
    rw [Hedge.Grammar.denote_or]
    rw [Hedge.Grammar.denote_or]
    rw [Regex.Language.derive_or]
    rw [ih1]
    rw [ih2]
  | concat r1 r2 ih1 ih2 =>
    rw [derive_concat]
    rw [Hedge.Grammar.denote_concat_n]
    rw [Hedge.Grammar.denote_or]
    rw [Hedge.Grammar.denote_concat_n]
    rw [Hedge.Grammar.denote_onlyif]
    rw [Regex.Language.derive_concat_n]
    rw [<- ih1]
    rw [<- ih2]
    congr
    apply Hedge.Grammar.null_commutes
  | star r1 ih1 =>
    rw [derive_star]
    rw [Hedge.Grammar.denote_star_n]
    rw [Hedge.Grammar.denote_concat_n]
    rw [Hedge.Grammar.denote_star_n]
    rw [Regex.Language.derive_star_n]
    rw [ih1]
  termination_by x
  decreasing_by
    apply Hedge.Node.DescendantOf.sizeOf

theorem derive_commutesb {α: Type}
  (G: Hedge.Grammar n φ)
  (Φ: φ -> α -> Bool)
  (r: Hedge.Grammar.Rule n φ)
  (x: Hedge.Node α):
  Hedge.Grammar.Rule.denote G (fun s a => Φ s a) (Hedge.Grammar.Room.derive G Φ r x)
  = Regex.Language.derive (Hedge.Grammar.Rule.denote G (fun s a => Φ s a) r) x := by
  funext xs
  rw [derive_commutesb_iff]
