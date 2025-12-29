import Validator.Hedge.Grammar
import Validator.Hedge.Denote

namespace Hedge.Grammar.Elem

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
  (G: Hedge.Grammar n φ) (Φ: φ -> α -> Bool)
  (r: Hedge.Grammar.Rule n φ) (xs: Hedge α): Prop :=
  Regex.Elem.denote_elem r xs (fun (pred, ref) x' =>
    match x' with
    | Subtype.mk x _hx =>
        Φ pred x.getLabel
        /\ Rule.denote G Φ (G.lookup ref) x.getChildren
  )
  termination_by xs
  decreasing_by exact (Rule.denote_decreasing _hx)

def denote {α: Type} (G: Hedge.Grammar n φ) (Φ: φ -> α -> Bool) (xs: Hedge α): Prop :=
  Hedge.Grammar.Elem.Rule.denote G Φ G.start xs

theorem simp_denote_rule_iff {α: Type} (G: Hedge.Grammar n φ) (Φ: φ -> α -> Bool) (r: Hedge.Grammar.Rule n φ) (xs: Hedge α):
  (Regex.Elem.denote_elem r xs (fun (pred, ref) x' =>
    match x' with
    | Subtype.mk x _hx =>
        Φ pred x.getLabel
        /\ Hedge.Grammar.Elem.Rule.denote G Φ (G.lookup ref) x.getChildren
  )) =
  (Regex.Elem.denote_elem r xs (fun (pred, ref) y =>
    ∃ x: Hedge.Node α, y.val = x /\ Φ pred x.getLabel /\ Hedge.Grammar.Elem.Rule.denote G Φ (G.lookup ref) x.getChildren
  )) := by
  congr
  ext s x'
  rw [<- eq_iff_iff]
  have ⟨pred, ref⟩ := s
  simp only
  obtain ⟨x', hx'⟩ := x'
  simp only
  simp only [↓existsAndEq, true_and]

theorem simp_denote_rule {α: Type} (G: Hedge.Grammar n φ) (Φ: φ -> α -> Bool) (r: Hedge.Grammar.Rule n φ) (xs: Hedge α):
  Hedge.Grammar.Elem.Rule.denote G Φ r xs =
  Regex.Elem.denote_elem r xs (fun (pred, ref) x' =>
    ∃ label children, x'.val = Hedge.Node.mk label children /\ Φ pred label /\ Hedge.Grammar.Elem.Rule.denote G Φ (G.lookup ref) children
  ) := by
  nth_rewrite 1 [Hedge.Grammar.Elem.Rule.denote]
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

theorem Rule.denote_emptyset {α: Type} {G: Hedge.Grammar n φ} {Φ: φ -> α -> Bool}:
  Hedge.Grammar.Elem.Rule.denote G Φ Regex.emptyset = Regex.Language.emptyset := by
  unfold Regex.Language.emptyset
  funext xs
  unfold Hedge.Grammar.Elem.Rule.denote
  simp [Regex.Elem.denote_elem_emptyset]

theorem Rule.denote_emptystr {α: Type} {G: Hedge.Grammar n φ} {Φ: φ -> α -> Bool}:
  Hedge.Grammar.Elem.Rule.denote G Φ Regex.emptystr = Regex.Language.emptystr := by
  unfold Regex.Language.emptystr
  funext xs
  unfold Hedge.Grammar.Elem.Rule.denote
  simp [Regex.Elem.denote_elem_emptystr]

theorem denote_rule_symbol_iff {n: Nat} {α: Type} {φ: Type}
  {G: Hedge.Grammar n φ} {Φ: φ -> α -> Bool} {p: φ}
  {ref: Hedge.Grammar.Ref n} {xs: Hedge α}:
  Hedge.Grammar.Elem.Rule.denote G Φ (Regex.symbol (p, ref)) xs
  <-> Hedge.Language.tree (Φ p) (Hedge.Grammar.Elem.Rule.denote G Φ (G.lookup ref)) xs := by
  cases xs with
  | nil =>
    unfold Hedge.Language.tree
    unfold Hedge.Grammar.Elem.Rule.denote
    simp [Regex.Elem.denote_elem_symbol]
    simp only [Regex.Language.symbol]
    simp only [Subtype.exists, List.not_mem_nil, IsEmpty.exists_iff, exists_false,
      not_false_eq_true]
  | cons x xs =>
    cases xs with
    | cons x' xs' =>
      unfold Hedge.Language.tree
      unfold Hedge.Grammar.Elem.Rule.denote
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
        unfold Hedge.Grammar.Elem.Rule.denote at h
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
        rw [Hedge.Grammar.Elem.Rule.denote]
        simp only [Regex.Elem.denote_elem_symbol]
        simp only [List.ElemOf.selfs, List.ElemOf.mk, Subtype.coe_eta, List.attach_cons,
          List.attach_nil, List.map_nil, List.map_cons]
        simp only [Regex.Language.symbol, List.cons.injEq, and_true, exists_eq_left']
        simp only [Hedge.Node.getLabel, Hedge.Node.getChildren]
        exact And.intro hp hg

theorem Rule.denote_symbol {n: Nat} {α: Type} {φ: Type}
  {G: Hedge.Grammar n φ} {Φ: φ -> α -> Bool} {p: φ} {ref: Hedge.Grammar.Ref n}:
  Hedge.Grammar.Elem.Rule.denote G Φ (Regex.symbol (p, ref))
  = Hedge.Language.tree (Φ p) (Hedge.Grammar.Elem.Rule.denote G Φ (G.lookup ref)) := by
  funext xs
  rw [denote_rule_symbol_iff]

theorem Rule.denote_or {n: Nat} {α: Type}
  {G: Hedge.Grammar n φ} {Φ: φ -> α -> Bool} {r1 r2: Hedge.Grammar.Rule n φ}:
  Hedge.Grammar.Elem.Rule.denote G Φ (Regex.or r1 r2)
  = Regex.Language.or (Hedge.Grammar.Elem.Rule.denote G Φ r1) (Hedge.Grammar.Elem.Rule.denote G Φ r2) := by
  funext xs
  unfold Regex.Language.or
  unfold Hedge.Grammar.Elem.Rule.denote
  simp [Regex.Elem.denote_elem_or]

theorem Rule.denote_concat_n {n: Nat} {α: Type}
  {G: Hedge.Grammar n φ} {Φ: φ -> α -> Bool} {r1 r2: Hedge.Grammar.Rule n φ}:
  Hedge.Grammar.Elem.Rule.denote G Φ (Regex.concat r1 r2)
  = Regex.Language.concat_n (Hedge.Grammar.Elem.Rule.denote G Φ r1) (Hedge.Grammar.Elem.Rule.denote G Φ r2) := by
  funext xs
  unfold Regex.Language.concat_n
  unfold Hedge.Grammar.Elem.Rule.denote
  simp only [Regex.Elem.denote_elem_concat_n]
  rfl

theorem Rule.denote_concat {n: Nat} {α: Type}
  {G: Hedge.Grammar n φ} {Φ: φ -> α -> Bool} {r1 r2: Hedge.Grammar.Rule n φ}:
  Hedge.Grammar.Elem.Rule.denote G Φ (Regex.concat r1 r2)
  = Regex.Language.concat_append (Hedge.Grammar.Elem.Rule.denote G Φ r1) (Hedge.Grammar.Elem.Rule.denote G Φ r2) := by
  rw [Rule.denote_concat_n]
  funext xs
  rw [Regex.Language.concat_n_is_concat]

theorem denote_star_n_iff {n: Nat} {α: Type}
  {G: Hedge.Grammar n φ} {Φ: φ -> α -> Bool} {r: Hedge.Grammar.Rule n φ} (xs: Hedge α):
  Hedge.Grammar.Elem.Rule.denote G Φ (Regex.star r) xs
  <->
  Regex.Language.star_n (Hedge.Grammar.Elem.Rule.denote G Φ r) xs := by
  rw [<- eq_iff_iff]
  unfold Regex.Language.star_n
  unfold Hedge.Grammar.Elem.Rule.denote
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
    rw [<- denote_star_n_iff]
    rw [Hedge.Grammar.Elem.Rule.denote]
  termination_by xs.length
  decreasing_by
    obtain ⟨n, hn⟩ := n
    apply List.list_length_drop_lt_cons

theorem Rule.denote_star_n {n: Nat} {α: Type}
  {G: Hedge.Grammar n φ} {Φ: φ -> α -> Bool} {r: Hedge.Grammar.Rule n φ}:
  Hedge.Grammar.Elem.Rule.denote G Φ (Regex.star r)
  =
  Regex.Language.star_n (Hedge.Grammar.Elem.Rule.denote G Φ r) := by
  funext xs
  rw [Hedge.Grammar.Elem.denote_star_n_iff]

theorem Rule.denote_star {n: Nat} {α: Type}
  {G: Hedge.Grammar n φ} {Φ: φ -> α -> Bool} {r: Hedge.Grammar.Rule n φ}:
  Hedge.Grammar.Elem.Rule.denote G Φ (Regex.star r)
  =
  Regex.Language.star_append (Hedge.Grammar.Elem.Rule.denote G Φ r) := by
  funext xs
  rw [Hedge.Grammar.Elem.denote_star_n_iff]
  rw [Regex.Language.star_append_is_star_n]

def Rule.denote_onlyif {α: Type}
  (condition: Prop) [dcond: Decidable condition]
  (G: Hedge.Grammar n φ) {Φ: φ -> α -> Bool} (x: Hedge.Grammar.Rule n φ):
  Hedge.Grammar.Elem.Rule.denote G Φ (Regex.onlyif condition x) = Regex.Language.onlyif condition (Hedge.Grammar.Elem.Rule.denote G Φ x) := by
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
    rw [Hedge.Grammar.Elem.Rule.denote, Regex.Elem.denote_elem]
    simp only [Regex.Language.emptyset, false_iff, not_and]
    intro hc'
    contradiction

theorem Rule.null_commutes {α: Type}
  (G: Hedge.Grammar n φ) (Φ: φ -> α -> Bool) (x: Hedge.Grammar.Rule n φ):
  ((Hedge.Grammar.Rule.null x) = true) = Regex.Language.null (Hedge.Grammar.Elem.Rule.denote G Φ x) := by
  unfold Hedge.Grammar.Rule.null
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
