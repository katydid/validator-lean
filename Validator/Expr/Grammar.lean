import Mathlib.Data.Vector.Snoc

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

abbrev Rules (μ: Nat) (α: Type) (Φ: (α: Type) -> Type) (ν: Nat) :=
  List.Vector (Rule μ α Φ) ν

def hashVector [Hashable α] (xs: List.Vector α n): UInt64 :=
  hash xs.toList

instance (α: Type) (n: Nat) [Hashable α] : Hashable (List.Vector α n) where
  hash := hashVector

def hashRules {μ: Nat} {α: Type} {Φ: (α: Type) -> Type} {ν: Nat} [Hashable α] [Hashable (Φ α)] (xs: Rules μ α Φ ν): UInt64 :=
  hash xs.toList

instance (μ: Nat) (α: Type) (Φ: (α: Type) -> Type) (ν: Nat) [Hashable α] [Hashable (Φ α)] : Hashable (Rules μ α Φ ν) where
  hash := hashRules

structure Grammar (μ: Nat) (α: Type) (Φ: (α: Type) -> Type) where
  start: Rule μ α Φ
  prods: Vector (Rule μ α Φ) μ

def Grammar.lookup {μ: Nat} {α: Type} {Φ: (α: Type) -> Type}
  (g: Grammar μ α Φ) (ref: Fin μ): Rule μ α Φ :=
  Vector.get g.prods ref

def Grammar.singleton (x: Rule 0 α Φ): Grammar 0 α Φ  :=
  Grammar.mk x #v[]

def Grammar.emptyset: Grammar 0 α Φ :=
  Grammar.mk Regex.emptyset #v[]

def Grammar.emptystr: Grammar 0 α Φ :=
  Grammar.mk Regex.emptystr #v[]

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

def example_grammar: Grammar 1 Char Pred :=
  Grammar.mk
    (Regex.or Regex.emptystr (Regex.symbol (Pred.eq 'a', 0)))
    #v[Regex.emptystr]

#guard
  example_grammar.lookup (Fin.mk 0 (by omega))
  = Regex.emptystr

theorem Rule.denote_decreasing {x: Hedge.Node α} {xs: Hedge α} (h: List.IsInfix [x] xs):
  sizeOf x.getChildren < sizeOf xs := by
  cases x with
  | mk label children =>
  simp only [Hedge.Node.getChildren]
  have h := List.list_infix_is_leq_sizeOf h
  simp only [List.cons.sizeOf_spec, List.nil.sizeOf_spec, Hedge.Node.mk.sizeOf_spec] at h
  simp +arith only at h
  omega

def Rule.denote {α: Type} [BEq α] (g: Grammar μ α Pred) (r: Rule μ α Pred) (xs: Hedge α): Prop :=
  Regex.denote_infix r xs (fun (pred, ref) xs' =>
    match xs' with
    | Subtype.mk [x] _hx =>
        Pred.eval pred x.getLabel
        /\ Rule.denote g (g.lookup ref) x.getChildren
    | _ => False
  )
  termination_by xs
  decreasing_by exact (Rule.denote_decreasing _hx)

def Grammar.denote {α: Type} [BEq α] (g: Grammar μ α Pred) (xs: Hedge α): Prop :=
  Rule.denote g g.start xs

theorem simp_denote_rule' {α: Type} [BEq α] (g: Grammar μ α Pred) (r: Rule μ α Pred) (xs: Hedge α):
  (Regex.denote_infix r xs (fun (pred, ref) xs' =>
    match xs' with
    | Subtype.mk [x] _hx =>
        Pred.eval pred x.getLabel
        /\ Rule.denote g (g.lookup ref) x.getChildren
    | _ => False
  )) =
  (Regex.denote_infix r xs (fun (pred, ref) xs' =>
    ∃ x: Hedge.Node α, xs'.val = [x] /\ Pred.eval pred x.getLabel /\ Rule.denote g (g.lookup ref) x.getChildren
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
  Rule.denote g r xs =
  Regex.denote_infix r xs (fun (pred, ref) xs' =>
    ∃ label children, xs'.val = [Hedge.Node.mk label children] /\ Pred.eval pred label /\ Rule.denote g (g.lookup ref) children
  ) := by
  nth_rewrite 1 [Rule.denote]
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

theorem Rule.denote_emptyset {α: Type} [BEq α] {g: Grammar μ α Pred}:
  Rule.denote g Regex.emptyset = Language.emptyset := by
  unfold Language.emptyset
  funext xs
  unfold Rule.denote
  simp [Regex.denote_infix_emptyset]

theorem Rule.denote_emptystr {α: Type} [BEq α] {g: Grammar μ α Pred}:
  Rule.denote g Regex.emptystr = Language.emptystr := by
  unfold Language.emptystr
  funext xs
  unfold Rule.denote
  simp [Regex.denote_infix_emptystr]

theorem denote_rule_symbol' {μ: Nat} {α: Type} [BEq α]
  {g: Grammar μ α Pred} {pred: Pred α} {ref: Ref μ} {xs: Hedge α}:
  Rule.denote g (Regex.symbol (pred, ref)) xs
  <-> Language.tree (Pred.eval pred) (Rule.denote g (g.lookup ref)) xs := by
  cases xs with
  | nil =>
    unfold Language.tree
    unfold Rule.denote
    simp [Regex.denote_infix_symbol]
  | cons x xs =>
    cases xs with
    | cons x' xs' =>
      unfold Language.tree
      unfold Rule.denote
      simp [Regex.denote_infix_symbol]
      simp [List.InfixOf.self]
    | nil =>
      unfold Language.tree
      unfold Rule.denote
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
        rw [<- Rule.denote]
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
        rw [<- Rule.denote] at hg
        apply And.intro hp hg

theorem Rule.denote_symbol {μ: Nat} {α: Type} [BEq α]
  {g: Grammar μ α Pred} {pred: Pred α} {ref: Ref μ}:
  Rule.denote g (Regex.symbol (pred, ref))
  = Language.tree (Pred.eval pred) (Rule.denote g (g.lookup ref)) := by
  funext xs
  rw [denote_rule_symbol']

theorem Rule.denote_or {μ: Nat} {α: Type} [BEq α]
  {g: Grammar μ α Pred} {p q: Rule μ α Pred}:
  Rule.denote g (Regex.or p q)
  = Language.or (Rule.denote g p) (Rule.denote g q) := by
  funext xs
  unfold Language.or
  unfold Rule.denote
  simp [Regex.denote_infix_or]

theorem Rule.denote_concat_n {μ: Nat} {α: Type} [BEq α]
  {g: Grammar μ α Pred} {p q: Rule μ α Pred}:
  Rule.denote g (Regex.concat p q)
  = Language.concat_n (Rule.denote g p) (Rule.denote g q) := by
  funext xs
  unfold Language.concat_n
  unfold Rule.denote
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

theorem Rule.denote_concat {μ: Nat} {α: Type} [BEq α]
  {g: Grammar μ α Pred} {p q: Rule μ α Pred}:
  Rule.denote g (Regex.concat p q)
  = Language.concat (Rule.denote g p) (Rule.denote g q) := by
  rw [Rule.denote_concat_n]
  funext xs
  rw [Language.concat_is_concat_n]

theorem denote_rule_star_n' {μ: Nat} {α: Type} [BEq α]
  {g: Grammar μ α Pred} {r: Rule μ α Pred} (xs: Hedge α):
  Rule.denote g (Regex.star r) xs
  <->
  Language.star_n (Rule.denote g r) xs := by
  rw [<- eq_iff_iff]
  unfold Language.star_n
  unfold Rule.denote
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
      rw [Rule.denote]
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

theorem Rule.denote_star_n {μ: Nat} {α: Type} [BEq α]
  {g: Grammar μ α Pred} {r: Rule μ α Pred}:
  Rule.denote g (Regex.star r)
  =
  Language.star_n (Rule.denote g r) := by
  funext xs
  rw [denote_rule_star_n']

theorem Rule.denote_star {μ: Nat} {α: Type} [BEq α]
  {g: Grammar μ α Pred} {r: Rule μ α Pred}:
  Rule.denote g (Regex.star r)
  =
  Language.star (Rule.denote g r) := by
  funext xs
  rw [denote_rule_star_n']
  rw [Language.star_is_star_n]

def Rule.denote_onlyif {α: Type} [BEq α] (condition: Prop) [dcond: Decidable condition] (g: Grammar μ α Pred) (x: Rule μ α Pred):
  denote g (Regex.onlyif condition x) = Language.onlyif condition (denote g x) := by
  unfold Language.onlyif
  unfold Regex.onlyif
  funext xs
  split_ifs
  case pos hc =>
    simp only [eq_iff_iff, iff_and_self]
    intro d
    assumption
  case neg hc =>
    simp only [eq_iff_iff]
    rw [Rule.denote, Regex.denote_infix]
    simp only [Language.emptyset, false_iff, not_and]
    intro hc'
    contradiction

def Rule.nullable (r: Rule μ α Φ): Bool :=
  Regex.nullable r

def Grammar.nullable (g: Grammar μ α Φ): Bool :=
  Rule.nullable g.start

theorem Rule.null_commutes {α: Type} [BEq α] (g: Grammar μ α Pred) (x: Rule μ α Pred):
  ((Rule.nullable x) = true) = Language.null (denote g x) := by
  induction x with
  | emptyset =>
    rw [denote_emptyset]
    rw [Language.null_emptyset]
    unfold Rule.nullable
    unfold Regex.nullable
    apply Bool.false_eq_true
  | emptystr =>
    rw [denote_emptystr]
    rw [Language.null_emptystr]
    unfold Rule.nullable
    unfold Regex.nullable
    simp only
  | symbol s =>
    obtain ⟨p, children⟩ := s
    rw [denote_symbol]
    rw [Language.null_tree]
    unfold Rule.nullable
    unfold Regex.nullable
    apply Bool.false_eq_true
  | or p q ihp ihq =>
    rw [denote_or]
    rw [Language.null_or]
    unfold Rule.nullable
    unfold Regex.nullable
    rw [<- ihp]
    rw [<- ihq]
    unfold Rule.nullable
    unfold Regex.nullable
    rw [Bool.or_eq_true]
  | concat p q ihp ihq =>
    rw [denote_concat]
    rw [Language.null_concat]
    unfold Rule.nullable
    unfold Regex.nullable
    rw [<- ihp]
    rw [<- ihq]
    unfold Rule.nullable
    unfold Regex.nullable
    rw [Bool.and_eq_true]
  | star r ih =>
    rw [denote_star]
    rw [Language.null_star]
    unfold Rule.nullable
    unfold Regex.nullable
    simp only
