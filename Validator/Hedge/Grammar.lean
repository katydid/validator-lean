import Validator.Std.Vec
import Validator.Std.Hedge

import Validator.Expr.Pred
import Validator.Regex.Regex
import Validator.Regex.Language
import Validator.Hedge.Language

-- ## Definition 3.2.3: Regular Hedge Grammar
--   𝐺 = (𝑁, 𝑇, 𝑆, 𝑃)
--   𝑁 a finite set of non-terminals
--   𝑇 a finite set of terminals
--   𝑆 the start symbol of a regular hedge grammar is a regular expression comprising pairs of nonterminals and terminals (a regular expression over N × T)
--   𝑃 a set of production rules of a regular hedge grammar are of the form X → r such that r is a regular expression over N × T.

-- n = the number of non-terminals
abbrev Ref (n: Nat) := Fin n -- non-terminal

abbrev Rule (n: Nat) (φ: Type) :=
  Regex (φ × Ref n)

abbrev Rules (n: Nat) (φ: Type) (l: Nat) :=
  Vec (Rule n φ) l

def hashVector [Hashable α] (xs: Vec α n): UInt64 :=
  hash xs.toList

instance (α: Type) (n: Nat) [Hashable α] : Hashable (Vec α n) where
  hash := hashVector

def hashRules {n: Nat} {φ: Type} {l: Nat} [Hashable φ] (xs: Rules n φ l): UInt64 :=
  hash xs.toList

instance (n: Nat) (φ: Type) (l: Nat) [Hashable φ] : Hashable (Rules n φ l) where
  hash := hashRules

structure Grammar (n: Nat) (φ: Type) where
  start: Rule n φ
  prods: Vec (Rule n φ) n

def Grammar.lookup {n: Nat} {φ: Type}
  (G: Grammar n φ) (ref: Fin n): Rule n φ :=
  Vec.get G.prods ref

def Grammar.singleton (x: Rule 0 φ): Grammar 0 φ  :=
  Grammar.mk x #vec[]

def Grammar.emptyset: Grammar 0 φ :=
  Grammar.mk Regex.emptyset #vec[]

def Grammar.emptystr: Grammar 0 φ :=
  Grammar.mk Regex.emptystr #vec[]

example : Grammar 5 (Pred String) := Grammar.mk
  -- start := ("html", Html)
  (start := Regex.symbol (Pred.eq "html", 0))
  -- production rules
  (prods := #vec[
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

def example_grammar: Grammar 1 (Pred Char) :=
  Grammar.mk
    (Regex.or Regex.emptystr (Regex.symbol (Pred.eq 'a', 0)))
    #vec[Regex.emptystr]

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

def Rule.denote {α: Type}
  (G: Grammar n φ) (Φ: φ -> α -> Bool)
  (r: Rule n φ) (xs: Hedge α): Prop :=
  Regex.denote_infix r xs (fun (pred, ref) xs' =>
    match xs' with
    | Subtype.mk [x] _hx =>
        Φ pred x.getLabel
        /\ Rule.denote G Φ (G.lookup ref) x.getChildren
    | _ => False
  )
  termination_by xs
  decreasing_by exact (Rule.denote_decreasing _hx)

def Grammar.denote {α: Type} (G: Grammar n φ) (Φ: φ -> α -> Bool) (xs: Hedge α): Prop :=
  Rule.denote G Φ G.start xs

theorem simp_denote_rule' {α: Type} (G: Grammar n φ) (Φ: φ -> α -> Bool) (r: Rule n φ) (xs: Hedge α):
  (Regex.denote_infix r xs (fun (pred, ref) xs' =>
    match xs' with
    | Subtype.mk [x] _hx =>
        Φ pred x.getLabel
        /\ Rule.denote G Φ (G.lookup ref) x.getChildren
    | _ => False
  )) =
  (Regex.denote_infix r xs (fun (pred, ref) xs' =>
    ∃ x: Hedge.Node α, xs'.val = [x] /\ Φ pred x.getLabel /\ Rule.denote G Φ (G.lookup ref) x.getChildren
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

theorem simp_denote_rule {α: Type} (G: Grammar n φ) (Φ: φ -> α -> Bool) (r: Rule n φ) (xs: Hedge α):
  Rule.denote G Φ r xs =
  Regex.denote_infix r xs (fun (pred, ref) xs' =>
    ∃ label children, xs'.val = [Hedge.Node.mk label children] /\ Φ pred label /\ Rule.denote G Φ (G.lookup ref) children
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

theorem Rule.denote_emptyset {α: Type} {G: Grammar n φ} {Φ: φ -> α -> Bool}:
  Rule.denote G Φ Regex.emptyset = Regex.Language.emptyset := by
  unfold Regex.Language.emptyset
  funext xs
  unfold Rule.denote
  simp [Regex.denote_infix_emptyset]

theorem Rule.denote_emptystr {α: Type} {G: Grammar n φ} {Φ: φ -> α -> Bool}:
  Rule.denote G Φ Regex.emptystr = Regex.Language.emptystr := by
  unfold Regex.Language.emptystr
  funext xs
  unfold Rule.denote
  simp [Regex.denote_infix_emptystr]

theorem denote_rule_symbol' {n: Nat} {α: Type} {φ: Type}
  {G: Grammar n φ} {Φ: φ -> α -> Bool} {p: φ}
  {ref: Ref n} {xs: Hedge α}:
  Rule.denote G Φ (Regex.symbol (p, ref)) xs
  <-> Hedge.Language.tree (Φ p) (Rule.denote G Φ (G.lookup ref)) xs := by
  cases xs with
  | nil =>
    unfold Hedge.Language.tree
    unfold Rule.denote
    simp [Regex.denote_infix_symbol]
  | cons x xs =>
    cases xs with
    | cons x' xs' =>
      unfold Hedge.Language.tree
      unfold Rule.denote
      simp [Regex.denote_infix_symbol]
      simp [List.InfixOf.self]
    | nil =>
      unfold Hedge.Language.tree
      unfold Rule.denote
      simp [Regex.denote_infix_symbol]
      simp [List.InfixOf.self]
      apply Iff.intro
      case mp =>
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
      case mpr =>
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

theorem Rule.denote_symbol {n: Nat} {α: Type} {φ: Type}
  {G: Grammar n φ} {Φ: φ -> α -> Bool} {p: φ} {ref: Ref n}:
  Rule.denote G Φ (Regex.symbol (p, ref))
  = Hedge.Language.tree (Φ p) (Rule.denote G Φ (G.lookup ref)) := by
  funext xs
  rw [denote_rule_symbol']

theorem Rule.denote_or {n: Nat} {α: Type}
  {G: Grammar n φ} {Φ: φ -> α -> Bool} {r1 r2: Rule n φ}:
  Rule.denote G Φ (Regex.or r1 r2)
  = Regex.Language.or (Rule.denote G Φ r1) (Rule.denote G Φ r2) := by
  funext xs
  unfold Regex.Language.or
  unfold Rule.denote
  simp [Regex.denote_infix_or]

theorem Rule.denote_concat_n {n: Nat} {α: Type}
  {G: Grammar n φ} {Φ: φ -> α -> Bool} {r1 r2: Rule n φ}:
  Rule.denote G Φ (Regex.concat r1 r2)
  = Regex.Language.concat_n (Rule.denote G Φ r1) (Rule.denote G Φ r2) := by
  funext xs
  unfold Regex.Language.concat_n
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

theorem Rule.denote_concat {n: Nat} {α: Type}
  {G: Grammar n φ} {Φ: φ -> α -> Bool} {r1 r2: Rule n φ}:
  Rule.denote G Φ (Regex.concat r1 r2)
  = Regex.Language.concat (Rule.denote G Φ r1) (Rule.denote G Φ r2) := by
  rw [Rule.denote_concat_n]
  funext xs
  rw [Regex.Language.concat_n_is_concat]

theorem denote_rule_star_n' {n: Nat} {α: Type}
  {G: Grammar n φ} {Φ: φ -> α -> Bool} {r: Rule n φ} (xs: Hedge α):
  Rule.denote G Φ (Regex.star r) xs
  <->
  Regex.Language.star_n (Rule.denote G Φ r) xs := by
  rw [<- eq_iff_iff]
  unfold Regex.Language.star_n
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

theorem Rule.denote_star_n {n: Nat} {α: Type}
  {G: Grammar n φ} {Φ: φ -> α -> Bool} {r: Rule n φ}:
  Rule.denote G Φ (Regex.star r)
  =
  Regex.Language.star_n (Rule.denote G Φ r) := by
  funext xs
  rw [denote_rule_star_n']

theorem Rule.denote_star {n: Nat} {α: Type}
  {G: Grammar n φ} {Φ: φ -> α -> Bool} {r: Rule n φ}:
  Rule.denote G Φ (Regex.star r)
  =
  Regex.Language.star (Rule.denote G Φ r) := by
  funext xs
  rw [denote_rule_star_n']
  rw [Regex.Language.star_is_star_n]

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
    rw [Rule.denote, Regex.denote_infix]
    simp only [Regex.Language.emptyset, false_iff, not_and]
    intro hc'
    contradiction

def Rule.nullable (r: Rule n φ): Bool :=
  Regex.nullable r

def Grammar.nullable (G: Grammar n φ): Bool :=
  Rule.nullable G.start

theorem Rule.null_commutes {α: Type}
  (G: Grammar n φ) (Φ: φ -> α -> Bool) (x: Rule n φ):
  ((Rule.nullable x) = true) = Regex.Language.null (denote G Φ x) := by
  induction x with
  | emptyset =>
    rw [denote_emptyset]
    rw [Regex.Language.null_emptyset]
    unfold Rule.nullable
    unfold Regex.nullable
    apply Bool.false_eq_true
  | emptystr =>
    rw [denote_emptystr]
    rw [Regex.Language.null_emptystr]
    unfold Rule.nullable
    unfold Regex.nullable
    simp only
  | symbol s =>
    obtain ⟨p, children⟩ := s
    rw [denote_symbol]
    rw [Hedge.Language.null_tree]
    unfold Rule.nullable
    unfold Regex.nullable
    apply Bool.false_eq_true
  | or p q ihp ihq =>
    rw [denote_or]
    rw [Regex.Language.null_or]
    unfold Rule.nullable
    unfold Regex.nullable
    rw [<- ihp]
    rw [<- ihq]
    unfold Rule.nullable
    unfold Regex.nullable
    rw [Bool.or_eq_true]
  | concat p q ihp ihq =>
    rw [denote_concat]
    rw [Regex.Language.null_concat]
    unfold Rule.nullable
    unfold Regex.nullable
    rw [<- ihp]
    rw [<- ihq]
    unfold Rule.nullable
    unfold Regex.nullable
    rw [Bool.and_eq_true]
  | star r ih =>
    rw [denote_star]
    rw [Regex.Language.null_star]
    unfold Rule.nullable
    unfold Regex.nullable
    simp only
