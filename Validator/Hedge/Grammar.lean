import Validator.Std.Hedge
import Validator.Std.List
import Validator.Std.Vec

import Validator.Pred.AnyEq
import Validator.Regex.Regex
import Validator.Regex.Elem
import Validator.Regex.Language
import Validator.Hedge.Types
import Validator.Hedge.Language

namespace Hedge.Grammar

def lookup {n: Nat} {φ: Type}
  (G: Grammar n φ) (ref: Fin n): Rule n φ :=
  Vec.get G.prods ref

def singleton (x: Rule 0 φ): Grammar 0 φ  :=
  Grammar.mk x #vec[]

def emptyset: Grammar 0 φ :=
  singleton Regex.emptyset

def emptystr: Grammar 0 φ :=
  singleton Regex.emptystr

def Rule.null (r: Rule n φ): Bool :=
  Regex.null r

def null (G: Grammar n φ): Bool :=
  Rule.null G.start

theorem Rule.denote_decreasing {x: Hedge.Node α} {xs: Hedge α} (h: x ∈ xs):
  sizeOf x.getChildren < sizeOf xs := by
  cases x with
  | mk label children =>
  simp only [Hedge.Node.getChildren]
  have h := Hedge.elem_is_leq_sizeOf h
  simp only [Hedge.Node.mk.sizeOf_spec] at h
  simp +arith only at h
  omega

def Rule.denote {α: Type}
  (G: Grammar n φ) (Φ: φ -> α -> Bool)
  (r: Hedge.Grammar.Rule n φ) (xs: Hedge α): Prop :=
  Regex.Elem.denote_elem r xs (fun (pred, ref) x' =>
    match x' with
    | Subtype.mk x _hx =>
        Φ pred x.getLabel
        /\ Rule.denote G Φ (G.lookup ref) x.getChildren
  )
  termination_by xs
  decreasing_by exact (Rule.denote_decreasing _hx)

def denote {α: Type} (G: Grammar n φ) (Φ: φ -> α -> Bool) (xs: Hedge α): Prop :=
  Rule.denote G Φ G.start xs

example : Grammar 5 (AnyEq.Pred String) := Grammar.mk
  -- start := ("html", Html)
  (start := Regex.symbol (AnyEq.Pred.eq "html", 0))
  -- production rules
  (prods := #vec[
    -- Html -> ("head", Head) · ("body", Body)
    Regex.concat
      (Regex.symbol (AnyEq.Pred.eq "head", 1))
      (Regex.symbol (AnyEq.Pred.eq "body", 2))
    -- Head -> ("title", Text) | ε
    , Regex.or
      (Regex.symbol (AnyEq.Pred.eq "title", 3))
      Regex.emptystr
    -- Body -> ("p", Text)*
    , Regex.star (Regex.symbol (AnyEq.Pred.eq "p", 3))
    -- Text -> (., Empty)
    , Regex.symbol (AnyEq.Pred.any, 4)
    -- Empty -> ε
    , Regex.emptystr
  ])

private def example_grammar: Grammar 1 (AnyEq.Pred Char) :=
  Grammar.mk
    (Regex.or Regex.emptystr (Regex.symbol (AnyEq.Pred.eq 'a', 0)))
    #vec[Regex.emptystr]

#guard
  example_grammar.lookup (Fin.mk 0 (by omega))
  = Regex.emptystr

theorem simp_denote_rule_iff {α: Type} (G: Grammar n φ) (Φ: φ -> α -> Bool) (r: Rule n φ) (xs: Hedge α):
  (Regex.Elem.denote_elem r xs (fun (pred, ref) x' =>
    match x' with
    | Subtype.mk x _hx =>
        Φ pred x.getLabel
        /\ Rule.denote G Φ (G.lookup ref) x.getChildren
  )) =
  (Regex.Elem.denote_elem r xs (fun (pred, ref) y =>
    ∃ x: Hedge.Node α, y.val = x /\ Φ pred x.getLabel /\ Rule.denote G Φ (G.lookup ref) x.getChildren
  )) := by
  congr
  ext s x'
  rw [<- eq_iff_iff]
  have ⟨pred, ref⟩ := s
  simp only
  obtain ⟨x', hx'⟩ := x'
  simp only
  simp only [↓existsAndEq, true_and]

theorem simp_denote_rule {α: Type} (G: Grammar n φ) (Φ: φ -> α -> Bool) (r: Rule n φ) (xs: Hedge α):
  Rule.denote G Φ r xs =
  Regex.Elem.denote_elem r xs (fun (pred, ref) x' =>
    ∃ label children, x'.val = Hedge.Node.mk label children /\ Φ pred label /\ Rule.denote G Φ (G.lookup ref) children
  ) := by
  nth_rewrite 1 [Rule.denote]
  rw [simp_denote_rule_iff]
  congr
  ext s xs'
  obtain ⟨pred, ref⟩ := s
  simp only
  apply Iff.intro
  case mp =>
    intro h
    obtain ⟨x, hxs, h⟩ := h
    cases x with
    | mk label children =>
    exists label, children
  case mpr =>
    intro h
    obtain ⟨label, children, hxs, h⟩ := h
    exists Hedge.Node.mk label children

theorem Rule.denote_emptyset {α: Type} {G: Grammar n φ} {Φ: φ -> α -> Bool}:
  Rule.denote G Φ Regex.emptyset = Regex.Language.emptyset := by
  unfold Regex.Language.emptyset
  funext xs
  unfold Rule.denote
  simp [Regex.Elem.denote_elem_emptyset]

theorem Rule.denote_emptystr {α: Type} {G: Grammar n φ} {Φ: φ -> α -> Bool}:
  Rule.denote G Φ Regex.emptystr = Regex.Language.emptystr := by
  unfold Regex.Language.emptystr
  funext xs
  unfold Rule.denote
  simp [Regex.Elem.denote_elem_emptystr]

theorem denote_rule_symbol_iff {n: Nat} {α: Type} {φ: Type}
  {G: Grammar n φ} {Φ: φ -> α -> Bool} {p: φ}
  {ref: Ref n} {xs: Hedge α}:
  Rule.denote G Φ (Regex.symbol (p, ref)) xs
  <-> Hedge.Language.tree (Φ p) (Rule.denote G Φ (G.lookup ref)) xs := by
  cases xs with
  | nil =>
    unfold Hedge.Language.tree
    unfold Rule.denote
    simp [Regex.Elem.denote_elem_symbol]
    simp only [Regex.Language.symbol]
    simp only [Subtype.exists, List.not_mem_nil, IsEmpty.exists_iff, exists_false,
      not_false_eq_true]
  | cons x xs =>
    cases xs with
    | cons x' xs' =>
      unfold Hedge.Language.tree
      unfold Rule.denote
      simp [Regex.Elem.denote_elem_symbol]
      simp [List.ElemOf.selfs]
      simp only [Regex.Language.symbol]
      simp only [List.cons.injEq, reduceCtorEq, and_false, false_and, nonempty_subtype,
        List.mem_cons, exists_or_eq_left, exists_const, not_false_eq_true]
    | nil =>
      unfold Hedge.Language.tree
      apply Iff.intro
      case mp =>
        intro h
        unfold Rule.denote at h
        simp only [Regex.Elem.denote_elem_symbol] at h
        simp only [List.ElemOf.selfs] at h
        obtain ⟨hx, hg⟩ := h
        cases x with
        | mk label children =>
        exists label, children
        apply And.intro (by rfl)
        simp [List.ElemOf.mk] at hg
        obtain ⟨hg1, hg2⟩ := hg
        simp only [List.ElemOf] at hx
        cases hx with
        | mk x hx =>
        simp only at *
        simp only [Subtype.mk.injEq] at hg1
        subst_vars
        clear hx
        simp only [Hedge.Node.getLabel, Hedge.Node.getChildren] at *
        exact hg2
      case mpr =>
        intro h
        obtain ⟨label, children, hx, hp, hg⟩ := h
        cases x with
        | mk label' children' =>
        simp at hx
        obtain ⟨hl, hc⟩ := hx
        rw [hl, hc] at *
        clear hl hc label' children'
        rw [Rule.denote]
        simp only [Regex.Elem.denote_elem_symbol]
        simp only [List.ElemOf.selfs, List.ElemOf.mk, Subtype.coe_eta, List.attach_cons,
          List.attach_nil, List.map_nil, List.map_cons]
        simp only [Regex.Language.symbol, List.cons.injEq, and_true, exists_eq_left']
        simp only [Hedge.Node.getLabel, Hedge.Node.getChildren]
        exact And.intro hp hg

theorem Rule.denote_symbol {n: Nat} {α: Type} {φ: Type}
  {G: Grammar n φ} {Φ: φ -> α -> Bool} {p: φ} {ref: Ref n}:
  Rule.denote G Φ (Regex.symbol (p, ref))
  = Hedge.Language.tree (Φ p) (Rule.denote G Φ (G.lookup ref)) := by
  funext xs
  rw [denote_rule_symbol_iff]

theorem Rule.denote_or {n: Nat} {α: Type}
  {G: Grammar n φ} {Φ: φ -> α -> Bool} {r1 r2: Rule n φ}:
  Rule.denote G Φ (Regex.or r1 r2)
  = Regex.Language.or (Rule.denote G Φ r1) (Rule.denote G Φ r2) := by
  funext xs
  unfold Regex.Language.or
  unfold Rule.denote
  simp [Regex.Elem.denote_elem_or]

theorem Rule.denote_concat_n {n: Nat} {α: Type}
  {G: Grammar n φ} {Φ: φ -> α -> Bool} {r1 r2: Rule n φ}:
  Rule.denote G Φ (Regex.concat r1 r2)
  = Regex.Language.concat_n (Rule.denote G Φ r1) (Rule.denote G Φ r2) := by
  funext xs
  unfold Regex.Language.concat_n
  unfold Rule.denote
  simp only [Regex.Elem.denote_elem_concat_n]
  rfl

theorem Rule.denote_concat {n: Nat} {α: Type}
  {G: Grammar n φ} {Φ: φ -> α -> Bool} {r1 r2: Rule n φ}:
  Rule.denote G Φ (Regex.concat r1 r2)
  = Regex.Language.concat_append (Rule.denote G Φ r1) (Rule.denote G Φ r2) := by
  rw [Rule.denote_concat_n]
  funext xs
  rw [Regex.Language.concat_n_is_concat]

theorem denote_rule_star_n_iff {n: Nat} {α: Type}
  {G: Grammar n φ} {Φ: φ -> α -> Bool} {r: Rule n φ} (xs: Hedge α):
  Rule.denote G Φ (Regex.star r) xs
  <->
  Regex.Language.star_n (Rule.denote G Φ r) xs := by
  rw [<- eq_iff_iff]
  unfold Regex.Language.star_n
  unfold Rule.denote
  rw [Regex.Elem.denote_elem_star_n]
  simp only
  cases xs with
  | nil =>
    rfl
  | cons x xs =>
    simp only
    congr
    ext n
    rw [<- eq_iff_iff]
    unfold Regex.Elem.denote_symbol_lift_take
    unfold Regex.Elem.denote_symbol_lift_drop
    congr
    simp only
    simp only [List.ElemOf.mk]
    simp
    rw [<- denote_rule_star_n_iff]
    rw [Rule.denote]
  termination_by xs.length
  decreasing_by
    obtain ⟨n, hn⟩ := n
    apply List.list_length_drop_lt_cons

theorem Rule.denote_star_n {n: Nat} {α: Type}
  {G: Grammar n φ} {Φ: φ -> α -> Bool} {r: Rule n φ}:
  Rule.denote G Φ (Regex.star r)
  =
  Regex.Language.star_n (Rule.denote G Φ r) := by
  funext xs
  rw [denote_rule_star_n_iff]

theorem Rule.denote_star {n: Nat} {α: Type}
  {G: Grammar n φ} {Φ: φ -> α -> Bool} {r: Rule n φ}:
  Rule.denote G Φ (Regex.star r)
  =
  Regex.Language.star_append (Rule.denote G Φ r) := by
  funext xs
  rw [denote_rule_star_n_iff]
  rw [Regex.Language.star_append_is_star_n]

def Rule.denote_onlyif {α: Type}
  (condition: Prop) [dcond: Decidable condition]
  (G: Grammar n φ) {Φ: φ -> α -> Bool} (x: Rule n φ):
  denote G Φ (Regex.onlyif condition x) = Regex.Language.onlyif condition (denote G Φ x) := by
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
    rw [Rule.denote, Regex.Elem.denote_elem]
    simp only [Regex.Language.emptyset, false_iff, not_and]
    intro hc'
    contradiction

theorem Rule.null_commutes {α: Type}
  (G: Grammar n φ) (Φ: φ -> α -> Bool) (x: Rule n φ):
  ((Rule.null x) = true) = Regex.Language.null (denote G Φ x) := by
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
    rw [denote_concat]
    rw [Regex.Language.null_concat_append]
    unfold Regex.null
    rw [<- ihp]
    rw [<- ihq]
    unfold Regex.null
    rw [Bool.and_eq_true]
  | star r ih =>
    rw [denote_star]
    rw [Regex.Language.null_star_append]
    unfold Regex.null
    simp only
