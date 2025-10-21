import Validator.Std.Hedge

import Validator.Expr.Pred
import Validator.Expr.Regex
import Validator.Expr.Language

-- ## Definition 3.2.3: Regular Hedge Grammar
--   𝐺 = (𝑁, 𝑇, 𝑆, 𝑃)
--   𝑁 a finite set of non-terminals
--   𝑇 a finite set of terminals
--   𝑆 the start symbol of a regular hedge grammar is a regular expression comprising pairs of nonterminals and terminals (a regular expression over N × T)
--   𝑃 a set of production rules of a regular hedge grammar are of the form X → r such that r is a regular expression over N × T.

abbrev Ref μ := Fin μ -- non-terminal

abbrev Rule (μ: Nat) (α: Type) (Φ: (α: Type) -> Type) :=
  Regex (Φ α × Ref μ)

structure Grammar (μ: Nat) (α: Type) (Φ: (α: Type) -> Type) where
  start: Rule μ α Φ
  prods: Vector (Rule μ α Φ) μ

def Grammar.lookup {μ: Nat} {α: Type} {Φ: (α: Type) -> Type}
  (g: Grammar μ α Φ) (ref: Fin μ): Rule μ α Φ :=
  Vector.get g.prods ref

example : Grammar 5 String Pred := Grammar.mk
  -- start := ("html", Html)
  (start := Regex.symbol (Pred.eq "html", 0))
  -- production rules
  (prods := #v[
    -- Html -> ("head", Head) · ("body", Body)
    Regex.concat
      (Regex.symbol (Pred.eq "head", 1))
      (Regex.symbol (Pred.eq "body", 2))
    -- Head -> ("title", Text) | ε
    , Regex.or
      (Regex.symbol (Pred.eq "title", 3))
      Regex.emptystr
    -- Body -> ("p", Text)*
    , Regex.star (Regex.symbol (Pred.eq "p", 3))
    -- Text -> (., Empty)
    , Regex.symbol (Pred.any, 4)
    -- Empty -> ε
    , Regex.emptystr
  ])

def denote_rule {α: Type} [BEq α] (g: Grammar μ α Pred) (r: Rule μ α Pred) (xs: Hedge α): Prop :=
  Regex.denote_infix r xs (fun (pred, ref) xs' =>
    match xs' with
    | Subtype.mk [x] _hx =>
        Pred.eval pred x.getLabel
        /\ denote_rule g (g.lookup ref) x.getChildren
    | _ => False
  )
  termination_by xs
  decreasing_by
    cases x with
    | mk label children =>
    simp only [Hedge.Node.getChildren]
    have h := List.list_infix_is_leq_sizeOf _hx
    simp only [List.cons.sizeOf_spec, List.nil.sizeOf_spec, Hedge.Node.mk.sizeOf_spec] at h
    simp +arith only at h
    omega

def Grammar.denote {α: Type} [BEq α] (g: Grammar μ α Pred) (xs: Hedge α): Prop :=
  denote_rule g g.start xs

theorem simp_denote_rule' {α: Type} [BEq α] (g: Grammar μ α Pred) (r: Rule μ α Pred) (xs: Hedge α):
  (Regex.denote_infix r xs (fun (pred, ref) xs' =>
    match xs' with
    | Subtype.mk [x] _hx =>
        Pred.eval pred x.getLabel
        /\ denote_rule g (g.lookup ref) x.getChildren
    | _ => False
  )) =
  (Regex.denote_infix r xs (fun (pred, ref) xs' =>
    ∃ x: Hedge.Node α, xs'.val = [x] /\ Pred.eval pred x.getLabel /\ denote_rule g (g.lookup ref) x.getChildren
  )) := by
  congr
  ext s xs'
  rw [<- eq_iff_iff]
  have ⟨pred, ref⟩ := s
  simp only
  obtain ⟨xs', hxs'⟩ := xs'
  simp only
  cases xs' with
  | nil =>
    simp
  | cons x xs' =>
    cases xs' with
    | cons _ _ =>
      simp
    | nil =>
      simp

theorem simp_denote_rule {α: Type} [BEq α] (g: Grammar μ α Pred) (r: Rule μ α Pred) (xs: Hedge α):
  denote_rule g r xs =
  Regex.denote_infix r xs (fun (pred, ref) xs' =>
    ∃ label children, xs'.val = [Hedge.Node.mk label children] /\ Pred.eval pred label /\ denote_rule g (g.lookup ref) children
  ) := by
  nth_rewrite 1 [denote_rule]
  rw [simp_denote_rule']
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

theorem Grammar.denote_rule_emptyset {α: Type} [BEq α] {g: Grammar μ α Pred}:
  denote_rule g Regex.emptyset = Language.emptyset := by
  unfold Language.emptyset
  funext xs
  unfold denote_rule
  simp [Regex.denote_infix_emptyset]

theorem Grammar.denote_rule_emptystr {α: Type} [BEq α] {g: Grammar μ α Pred}:
  denote_rule g Regex.emptystr = Language.emptystr := by
  unfold Language.emptystr
  funext xs
  unfold denote_rule
  simp [Regex.denote_infix_emptystr]

theorem denote_rule_symbol' {μ: Nat} {α: Type} [BEq α]
  {g: Grammar μ α Pred} {pred: Pred α} {ref: Ref μ} {xs: Hedge α}:
  denote_rule g (Regex.symbol (pred, ref)) xs
  <-> Language.tree (Pred.eval pred) (denote_rule g (g.lookup ref)) xs := by
  cases xs with
  | nil =>
    unfold Language.tree
    unfold denote_rule
    simp [Regex.denote_infix_symbol]
  | cons x xs =>
    cases xs with
    | cons x' xs' =>
      unfold Language.tree
      unfold denote_rule
      simp [Regex.denote_infix_symbol]
      simp [List.InfixOf.self]
    | nil =>
      unfold Language.tree
      unfold denote_rule
      simp [Regex.denote_infix_symbol]
      simp [List.InfixOf.self]
      apply Iff.intro
      case mp h =>
        intro h
        obtain ⟨hp, hg⟩ := h
        cases x with
        | mk label children =>
        exists label, children
        apply And.intro (by rfl)
        simp [Hedge.Node.getLabel] at hp
        simp [Hedge.Node.getChildren] at hg
        apply And.intro hp
        rw [<- denote_rule]
        exact hg
      case mpr h =>
        intro h
        obtain ⟨label, children, hx, hp, hg⟩ := h
        cases x with
        | mk label' children' =>
        simp at hx
        obtain ⟨hl, hc⟩ := hx
        rw [hl, hc] at *
        clear hl hc label' children'
        simp [Hedge.Node.getChildren, Hedge.Node.getLabel]
        rw [<- denote_rule] at hg
        apply And.intro hp hg

theorem Grammar.denote_rule_symbol {μ: Nat} {α: Type} [BEq α]
  {g: Grammar μ α Pred} {pred: Pred α} {ref: Ref μ}:
  denote_rule g (Regex.symbol (pred, ref))
  = Language.tree (Pred.eval pred) (denote_rule g (g.lookup ref)) := by
  funext xs
  rw [denote_rule_symbol']

theorem Grammar.denote_rule_or {μ: Nat} {α: Type} [BEq α]
  {g: Grammar μ α Pred} {p q: Rule μ α Pred}:
  denote_rule g (Regex.or p q)
  = Language.or (denote_rule g p) (denote_rule g q) := by
  funext xs
  unfold Language.or
  unfold denote_rule
  simp [Regex.denote_infix_or]

theorem Grammar.denote_rule_concat_n {μ: Nat} {α: Type} [BEq α]
  {g: Grammar μ α Pred} {p q: Rule μ α Pred}:
  denote_rule g (Regex.concat p q)
  = Language.concat_n (denote_rule g p) (denote_rule g q) := by
  funext xs
  unfold Language.concat_n
  unfold denote_rule
  simp only [Regex.denote_infix_concat_n]
  congr
  ext n
  rw [<- eq_iff_iff]
  unfold denote_symbol_lift_take
  unfold denote_symbol_lift_drop
  congr
  next =>
    simp only
    ext s ys
    unfold List.InfixOf.mk
    obtain ⟨ys, hys⟩ := ys
    simp only
    cases ys with
    | nil =>
      simp
    | cons y ys =>
      cases ys with
      | nil =>
        simp
      | cons _ _ =>
        simp
  next =>
    simp only
    ext s ys
    unfold List.InfixOf.mk
    obtain ⟨ys, hys⟩ := ys
    simp only
    cases ys with
    | nil =>
      simp
    | cons y ys =>
      cases ys with
      | nil =>
        simp
      | cons _ _ =>
        simp

theorem denote_rule_star_n' {μ: Nat} {α: Type} [BEq α]
  {g: Grammar μ α Pred} {r: Rule μ α Pred} (xs: Hedge α):
  denote_rule g (Regex.star r) xs
  <->
  Language.star_n (denote_rule g r) xs := by
  rw [<- eq_iff_iff]
  unfold Language.star_n
  unfold denote_rule
  cases xs with
  | nil =>
    simp [Regex.denote_infix_star_n]
  | cons x xs =>
    simp only
    rw [Regex.denote_infix_star_n]
    simp only
    congr
    ext n
    rw [<- eq_iff_iff]
    unfold denote_symbol_lift_take
    unfold denote_symbol_lift_drop
    congr
    next =>
      ext s ys
      rw [<- eq_iff_iff]
      simp only
      unfold List.InfixOf.mk
      obtain ⟨ys, hys⟩ := ys
      simp only
      cases ys with
      | nil =>
        simp
      | cons y ys =>
        cases ys with
        | nil =>
          simp
        | cons _ _ =>
          simp
    next =>
      simp only
      unfold List.InfixOf.mk
      simp
      rw [<- denote_rule_star_n']
      rw [denote_rule]
      rw [<- eq_iff_iff]
      congr
      ext s ys
      obtain ⟨ys, hys⟩ := ys
      simp only
      cases ys with
      | nil =>
        simp
      | cons y ys =>
        cases ys with
        | nil =>
          simp
        | cons _ _ =>
          simp
  termination_by xs.length
  decreasing_by
    obtain ⟨n, hn⟩ := n
    apply List.list_length_drop_lt_cons

theorem Grammar.denote_rule_star_n {μ: Nat} {α: Type} [BEq α]
  {g: Grammar μ α Pred} {r: Rule μ α Pred}:
  denote_rule g (Regex.star r)
  =
  Language.star_n (denote_rule g r) := by
  funext xs
  rw [denote_rule_star_n']
