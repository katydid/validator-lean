import Validator.Std.Hedge
import Validator.Regex.Language

namespace Hedge.Language

open List (
  append_assoc
  append_eq_nil_iff
  append_nil
  cons
  cons_append
  cons.injEq
  foldl_nil
  nil
  nil_append
  nil_eq
  singleton_append
)

-- Definitions

def Lang (α: Type): Type := Regex.Language.Langs (Hedge.Node α)

def tree {α: Type} (φ: α -> Bool) (R: Lang α): Lang α :=
  fun xs => ∃ label children, xs = [Hedge.Node.mk label children] /\ φ label /\ R children

example: Lang Nat := (tree (fun x => x = 1) (Regex.Language.or (tree (fun x => x = 1) Regex.Language.emptystr) Regex.Language.emptyset))

theorem null_iff_tree {α: Type} {p: α -> Bool} {children: Lang α}:
  Regex.Language.null (tree p children) <-> False :=
  Iff.intro nofun nofun

theorem null_tree {α: Type} {p: α -> Bool} {children: Lang α}:
  Regex.Language.null (tree p children) = False := by
  rw [null_iff_tree]

theorem derive_iff_tree {α: Type} {p: α -> Bool} {childlang: Lang α} {label: α} {children: Hedge α} {xs: Hedge α}:
  (Regex.Language.derive (tree p childlang) (Hedge.Node.mk label children)) xs <->
  (Regex.Language.onlyif (p label /\ childlang children) Regex.Language.emptystr) xs := by
  simp only [Regex.Language.derive, Regex.Language.derives, singleton_append]
  simp only [Regex.Language.onlyif, Regex.Language.emptystr]
  refine Iff.intro ?toFun ?invFun
  case toFun =>
    unfold tree
    simp only [cons.injEq, Hedge.Node.mk.injEq]
    intro ⟨ label', children', ⟨ ⟨ hlabel', hchildren' ⟩, hxs ⟩ , hif ⟩
    subst_vars
    simp only [and_true]
    exact hif
  case invFun =>
    intro ⟨ hif , hxs  ⟩
    unfold tree
    exists label
    exists children
    rw [hxs]
    simp only [true_and]
    exact hif

-- Hedge.Language.derive (Hedge.Language.tree p.eval (Denote.denote children)) a
theorem derive_tree {α: Type} {p: α -> Bool} {childlang: Lang α} {label: α} {children: Hedge α}:
  (Regex.Language.derive (tree p childlang) (Hedge.Node.mk label children)) =
  (Regex.Language.onlyif (p label /\ childlang children) Regex.Language.emptystr) := by
  funext
  rw [derive_iff_tree]
