import Validator.Expr.Expr
import Validator.Expr.Pred
import Validator.Expr.Language

namespace Denote

def denote {α: Type} [BEq α] (r: Expr α): Language.Lang α :=
  match r with
  | Expr.emptyset => Language.emptyset
  | Expr.epsilon => Language.emptystr
  | Expr.tree p childrenExpr => Language.tree (Pred.eval p) (denote childrenExpr)
  | Expr.or x y => Language.or (denote x) (denote y)
  | Expr.concat x y => Language.concat (denote x) (denote y)
  | Expr.star x => Language.star (denote x)

def denote_onlyif {α: Type} [BEq α] (condition: Prop) [dcond: Decidable condition] (x: Expr α):
  denote (Expr.onlyif condition x) = Language.onlyif condition (denote x) := by
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
    rw [Language.emptyset]
    simp only [false_iff, not_and]
    intro hc'
    contradiction

theorem null_commutes {α: Type} [BEq α] (x: Expr α):
  ((Expr.nullable x) = true) = Language.null (denote x) := by
  induction x with
  | emptyset =>
    unfold denote
    rw [Language.null_emptyset]
    unfold Expr.nullable
    apply Bool.false_eq_true
  | epsilon =>
    unfold denote
    rw [Language.null_emptystr]
    unfold Expr.nullable
    simp only
  | tree p children =>
    unfold denote
    rw [Language.null_tree]
    unfold Expr.nullable
    apply Bool.false_eq_true
  | or p q ihp ihq =>
    unfold denote
    rw [Language.null_or]
    unfold Expr.nullable
    rw [<- ihp]
    rw [<- ihq]
    rw [Bool.or_eq_true]
  | concat p q ihp ihq =>
    unfold denote
    rw [Language.null_concat]
    unfold Expr.nullable
    rw [<- ihp]
    rw [<- ihq]
    rw [Bool.and_eq_true]
  | star r ih =>
    unfold denote
    rw [Language.null_star]
    unfold Expr.nullable
    simp only
