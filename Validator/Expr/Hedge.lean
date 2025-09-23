import Validator.Std.ParseTree
import Validator.Std.Slice

import Validator.Expr.Pred
import Validator.Expr.Language

inductive Regex α where
  | emptyset
  | emptystr
  | symbol (s: α)
  | or (y z: Regex α)
  | concat (y z: Regex α)
  | star (y: Regex α)
  deriving DecidableEq, Hashable

-- ## Definition 3.2.3: Regular Hedge Grammar
--   𝐺 = (𝑁 , 𝑇 , 𝑆, 𝑃)
--   𝑁 a finite set of non-terminals
--   𝑇 a finite set of terminals
--   𝑆 is regular expression over 𝑇 (𝑁)
--   𝑃 a set of production rules of the form 𝑋 → 𝑎(𝑟)
--   where 𝑋 ∈ 𝑁
--     𝑎 ∈ 𝑇
--     𝑟 is a regular expression over 𝑁

abbrev Ref μ := Fin μ

structure Grammar μ α where
  -- 𝑆 is regular expression over 𝑇 (𝑁)
  -- Pred over α are the terminals 𝑇.
  -- Ref μ are the non terminals.
  start: Regex (Pred α × Ref μ)
  -- 𝑃 a set of production rules of the form 𝑋 → 𝑎(𝑟)
  -- X is a Nat smaller than μ to garauntee the success of lookups as index in the Vector.
  -- a is a Predicate over T or rather an alphabet α.
  refs: Vector (Pred α × Regex (Ref μ)) μ

def Grammar.lookup (g: Grammar μ α) (ref: Fin μ): Pred α × Regex (Ref μ) :=
  Vector.get g.refs ref

def denote_regex {α: Type} {σ: Type} (denote_symbol: σ -> List α -> Prop) (r: Regex σ): (as: List α) -> Prop :=
  match r with
  | Regex.emptyset => fun _ => False
  | Regex.emptystr => fun as => as = []
  | Regex.symbol s => Language.symbol denote_symbol s
  | Regex.or y z => Language.or (denote_regex denote_symbol y) (denote_regex denote_symbol z)
  | Regex.concat y z => Language.concat_n (denote_regex denote_symbol y) (denote_regex denote_symbol z)
  | Regex.star y => Language.star (denote_regex denote_symbol y)

theorem denote_regex_emptyset {α: Type} {σ: Type} (denote_symbol: σ -> List α -> Prop):
  denote_regex denote_symbol Regex.emptyset = Language.emptyset := by
  unfold Language.emptyset
  simp [denote_regex]

theorem denote_regex_emptystr {α: Type} {σ: Type} (denote_symbol: σ -> List α -> Prop):
  denote_regex denote_symbol Regex.emptystr = Language.emptystr := by
  unfold Language.emptystr
  simp [denote_regex]

theorem denote_regex_symbol {α: Type} {σ: Type} (denote_symbol: σ -> List α -> Prop) (s: σ):
  denote_regex denote_symbol (Regex.symbol s) = Language.symbol denote_symbol s := by
  simp [denote_regex]

theorem denote_regex_symbol' {α: Type} {σ: Type} (denote_symbol: σ -> List α -> Prop) (s: σ):
  denote_regex denote_symbol (Regex.symbol s) = denote_symbol s := by
  simp [denote_regex]
  unfold Language.symbol
  funext
  rfl

theorem denote_regex_or {α: Type} {σ: Type} (denote_symbol: σ -> List α -> Prop) (x y: Regex σ):
  denote_regex denote_symbol (Regex.or x y) = Language.or (denote_regex denote_symbol x) (denote_regex denote_symbol y) := by
  unfold Language.or
  funext
  simp [denote_regex]

theorem denote_regex_concat_n {α: Type} [BEq α] (denote_symbol: σ -> List α -> Prop) (x y: Regex σ):
  denote_regex denote_symbol (Regex.concat x y) = Language.concat_n (denote_regex denote_symbol x) (denote_regex denote_symbol y) := by
  funext
  simp [denote_regex]

theorem denote_regex_star' {α: Type} [BEq α] (denote_symbol: σ -> List α -> Prop) (y: Regex σ) (as: List α):
  denote_regex denote_symbol (Regex.star y) as <-> Language.star (denote_regex denote_symbol y) as := by
  simp [denote_regex]

theorem denote_regex_star {α: Type} [BEq α] (denote_symbol: σ -> List α -> Prop) (y: Regex σ):
  denote_regex denote_symbol (Regex.star y) = Language.star (denote_regex denote_symbol y) := by
  funext xs
  rw [denote_regex_star']

def denote_forest {α: Type} [BEq α] (g: Grammar μ α) (x: Regex (Ref μ)) (as: ParseForest α) : Prop :=
  match x with
  | Regex.emptyset => False
  | Regex.emptystr => as = []
  | Regex.symbol s =>
    match as with
    | [ParseTree.mk label children] =>
      match g.lookup s with
      | (p', x') => Pred.eval p' label /\ denote_forest g x' children
    | _ => False
  | Regex.or y z => (denote_forest g y as) \/ (denote_forest g z as)
  | Regex.concat y z => ∃ n,
    denote_forest g y (List.take n as) /\ denote_forest g z (List.drop n as)
  | Regex.star y =>
    match as with
    | [] => True
    | (a'::as') => ∃ n,
        (denote_forest g y (a'::(List.take n as')))
        /\ (denote_forest g x (List.drop n as'))
  termination_by (as, x)
  decreasing_by
  · apply Prod.Lex.left
    simp
    omega
  · apply Prod.Lex.right
    simp
    omega
  · apply Prod.Lex.right
    simp
  · have h := ParseTree.ParseForest.sizeOf_take n as
    cases h with
    | inl h =>
      rw [h]
      apply Prod.Lex.right
      simp [Regex.concat.sizeOf_spec]
      omega
    | inr h =>
      apply Prod.Lex.left
      assumption
  · have h := ParseTree.ParseForest.sizeOf_drop n as
    cases h with
    | inl h =>
      rw [h]
      apply Prod.Lex.right
      simp [Regex.concat.sizeOf_spec]
    | inr h =>
      apply Prod.Lex.left
      assumption
  · have h := ParseTree.ParseForest.sizeOf_take n as'
    cases h with
    | inl h =>
      rw [h]
      apply Prod.Lex.right
      simp [Regex.star.sizeOf_spec]
    | inr h =>
      apply Prod.Lex.left
      simp
      assumption
  · have h := ParseTree.ParseForest.sizeOf_drop n as'
    cases h with
    | inl h =>
      rw [h]
      apply Prod.Lex.left
      simp
    | inr h =>
      apply Prod.Lex.left
      simp
      omega

def denote_regex' {α: Type} {σ: Type} (x: Regex σ) (denote_symbol: σ -> List α -> Prop) (xs: List α): Prop :=
  match x with
  | Regex.emptyset => False
  | Regex.emptystr => xs.isEmpty
  | Regex.symbol s => denote_symbol s xs
  | Regex.or y z => (denote_regex' y denote_symbol xs) \/ (denote_regex' z denote_symbol xs)
  | Regex.concat y z => ∃ (n: Nat), (denote_regex' y denote_symbol (List.take n xs)) /\ (denote_regex' z denote_symbol (List.drop n xs))
  | Regex.star y =>
    match xs with
    | [] => True
    | (x'::xs') =>
      ∃ (n: Nat), (denote_regex' y denote_symbol (List.take (n + 1) (x'::xs'))) /\ (denote_regex' (Regex.star y) denote_symbol (List.drop (n + 1) (x'::xs')))
  termination_by (xs.length, x)
  decreasing_by
  · apply Prod.Lex.right
    simp only [Regex.or.sizeOf_spec]
    omega
  · apply Prod.Lex.right
    simp only [Regex.or.sizeOf_spec]
    omega
  · by_cases (List.take n xs = xs)
    case pos h =>
      rw [h]
      apply Prod.Lex.right
      simp only [Regex.concat.sizeOf_spec]
      omega
    case neg h =>
      apply Prod.Lex.left
      exact List.list_length_neq_take h
  · by_cases (List.drop n xs = xs)
    case pos h =>
      rw [h]
      apply Prod.Lex.right
      simp only [Regex.concat.sizeOf_spec]
      omega
    case neg h =>
      apply Prod.Lex.left
      exact List.list_length_neq_drop h
  · by_cases ((List.take (n + 1) (x'::xs')) = (x'::xs'))
    case pos h =>
      rw [h]
      apply Prod.Lex.right
      simp only [Regex.star.sizeOf_spec]
      omega
    case neg h =>
      apply Prod.Lex.left
      exact List.list_length_neq_take h
  · by_cases ((List.drop (n + 1) (x'::xs')) = (x'::xs'))
    case pos h =>
      rw [h]
      apply Prod.Lex.left
      simp at h
      have h' := List.list_drop_neq_cons (n := n) (xs := xs') (x := x')
      contradiction
    case neg h =>
      apply Prod.Lex.left
      exact List.list_length_neq_drop h

theorem denote_forest_emptyset {α: Type} [BEq α] (g: Grammar μ α):
  denote_forest g Regex.emptyset = Language.emptyset := by
  unfold Language.emptyset
  funext
  simp [denote_forest]

theorem denote_forest_emptystr {α: Type} [BEq α] (g: Grammar μ α):
  denote_forest g Regex.emptystr = Language.emptystr := by
  unfold Language.emptystr
  funext
  simp [denote_forest]

theorem denote_forest_tree {α: Type} [BEq α] {g: Grammar μ α}:
  denote_forest g (Regex.symbol r) = Language.tree (Pred.eval (g.lookup r).1) (denote_forest g (g.lookup r).2) := by
  unfold Language.tree
  funext
  rename_i as
  cases as with
  | nil =>
    simp [denote_forest]
  | cons a as =>
    cases as with
    | nil =>
      cases a with
      | mk label children =>
      simp only [List.cons.injEq, ParseTree.mk.injEq, and_true, existsAndEq, exists_eq_left']
      simp [denote_forest]
    | cons b as =>
      simp [denote_forest]

theorem denote_forest_or {α: Type} [BEq α] (g: Grammar μ α) (x y: Regex (Ref μ)):
  denote_forest g (Regex.or x y) = Language.or (denote_forest g x) (denote_forest g y) := by
  unfold Language.or
  funext
  simp [denote_forest]

theorem denote_forest_concat_n {α: Type} [BEq α] (g: Grammar μ α) (x y: Regex (Ref μ)):
  denote_forest g (Regex.concat x y) = Language.concat_n (denote_forest g x) (denote_forest g y) := by
  unfold Language.concat_n
  funext
  simp [denote_forest]

theorem denote_forest_star' {α: Type} [BEq α] (g: Grammar μ α) (x: Regex (Ref μ)) (as: ParseForest α):
  denote_forest g (Regex.star x) as <-> Language.star (denote_forest g x) as:= by
  apply Iff.intro
  case mp =>
    intro h
    cases as with
    | nil =>
      apply Language.star.zero
    | cons a as =>
      simp [denote_forest] at h
      cases h with
      | intro n h =>
      cases h with
      | intro h1 h2 =>
      apply Language.star.more a (List.take n as) (List.drop n as)
      · simp
      · exact h1
      · rw [<- denote_forest_star']
        exact h2
  case mpr =>
    intro h
    cases as with
    | nil =>
      simp [denote_forest]
    | cons a as =>
      simp [denote_forest]
      cases h with
      | more a1 as1 as2 _ hxy h1 h2  =>
        cases hxy
        exists List.length as1
        simp
        apply And.intro h1
        rw [denote_forest_star']
        exact h2
  termination_by as
  decreasing_by
    · have h' := List.list_drop_exists n tail
      cases h' with
      | intro ys h' =>
      nth_rewrite 2 [h']
      simp only [List.cons.sizeOf_spec, gt_iff_lt]
      have h'' := List.list_sizeOf_prepend (List.drop n tail) ys
      omega
    · rename_i j1 j2 j3 j4 j5 j6 j7 j8 j9 _j10
      cases j4
      rw [<- j6]
      apply List.list_sizeOf_cons

theorem denote_forest_star {α: Type} [BEq α] (g: Grammar μ α) (x: Regex (Ref μ)):
  denote_forest g (Regex.star x) = Language.star (denote_forest g x) := by
  funext xs
  rw [denote_forest_star']

def denote_ref_forest {α: Type} [BEq α] (g: Grammar μ α) (p: Pred α) (x: Regex (Ref μ)) (as: List (ParseTree α)): Prop :=
  match as with
  | [ParseTree.mk label children] =>
    Pred.eval p label /\ denote_forest g x children
  | _ => False

def denote_start_ref_forest {α: Type} [BEq α] (g: Grammar μ α) (x: Regex (Pred α × Ref μ)) (as: ParseForest α): Prop :=
  denote_regex (fun (p, r) as' =>
    denote_ref_forest g p (Regex.symbol r) as'
  ) x as

theorem denote_start_ref_forest_emptyset {α: Type} [BEq α] {g: Grammar μ α}:
  denote_start_ref_forest g Regex.emptyset = Language.emptyset := by
  unfold Language.emptyset
  funext
  simp [denote_start_ref_forest, denote_regex]

theorem denote_start_ref_forest_emptystr {α: Type} [BEq α] {g: Grammar μ α}:
  denote_start_ref_forest g Regex.emptystr = Language.emptystr := by
  unfold Language.emptystr
  funext
  simp [denote_start_ref_forest, denote_regex]

theorem denote_start_ref_forest_tree' {α: Type} [BEq α] {g: Grammar μ α} (x: Pred α × Ref μ) (as: ParseForest α):
  denote_start_ref_forest g (Regex.symbol x) as <->
    ∃ label children, as = [ParseTree.mk label children]
    /\ Pred.eval x.1 label
    /\ denote_forest g (Regex.symbol x.2) children := by
  cases as with
  | nil =>
    simp [denote_start_ref_forest, denote_regex, Language.symbol, denote_ref_forest]
  | cons a as =>
    cases as with
    | nil =>
      cases a with
      | mk label children =>
        simp [denote_start_ref_forest, denote_regex, Language.symbol, denote_ref_forest]
    | cons a' as =>
      simp [denote_start_ref_forest, denote_regex, Language.symbol, denote_ref_forest]

theorem denote_start_ref_forest_tree {α: Type} [BEq α] {g: Grammar μ α} (x: Pred α × Ref μ):
  denote_start_ref_forest g (Regex.symbol x) =
    fun as => ∃ label children, as = [ParseTree.mk label children]
    /\ Pred.eval x.1 label
    /\ denote_forest g (Regex.symbol x.2) children := by
  funext
  rw [denote_start_ref_forest_tree']

def denote_regex_sliceof {α: Type} {xs': List α} {σ: Type} (x: Regex σ) (denote_symbol: σ -> SliceOf xs' -> Prop) (xs: SliceOf xs'): Prop :=
  match x with
  | Regex.emptyset => False
  | Regex.emptystr => xs.isEmpty
  | Regex.symbol s => denote_symbol s xs
  | Regex.or y z =>
       (denote_regex_sliceof y denote_symbol xs)
    \/ (denote_regex_sliceof z denote_symbol xs)
  | Regex.concat y z =>
     ∃ (n: Fin (xs.length + 1)),
       (denote_regex_sliceof y denote_symbol (SliceOf.take n xs))
    /\ (denote_regex_sliceof z denote_symbol (SliceOf.drop n xs))
  | Regex.star y =>
    match hxs: xs.nonEmpty with
    | Option.none => True
    | Option.some xxs => (
        ∃ (n: Fin (xxs.val.length + 1)),
          (denote_regex_sliceof y denote_symbol (SliceOf.take_succ n xxs.val (by omega)))
        /\ (denote_regex_sliceof (Regex.star y) denote_symbol (SliceOf.drop_succ n xxs.val (by omega)))
      )
  termination_by (xs.length, x)
  decreasing_by
    · apply Prod.Lex.right
      simp
      omega
    · apply Prod.Lex.right
      simp
    · cases xs with
      | mk o l h =>
      simp only [SliceOf.take, SliceOf.length]
      by_cases (n >= l)
      case pos h' =>
        rw [Nat.min_eq_right h']
        apply Prod.Lex.right
        simp only [Regex.concat.sizeOf_spec]
        omega
      case neg h' =>
        apply Prod.Lex.left
        omega
    · cases xs with
      | mk o l h =>
      simp only [SliceOf.drop, SliceOf.length]
      by_cases (l - n = l)
      case pos h' =>
        rw [h']
        apply Prod.Lex.right
        simp only [Regex.concat.sizeOf_spec]
        omega
      case neg h' =>
        apply Prod.Lex.left
        omega
    · cases xs with
      | mk o l h =>
      simp only [SliceOf.take_succ, SliceOf.length, SliceOf.take]
      cases xxs with
      | mk xs' hxs' =>
      cases n with
      | mk n hn =>
      cases xs' with
      | mk offset length prop =>
      simp only [SliceOf.length] at hxs'
      simp only [SliceOf.length] at hn
      simp only [SliceOf.nonEmpty] at hxs
      cases l with
      | zero =>
        simp only [reduceCtorEq] at hxs
      | succ l =>
        simp only [Option.some.injEq, Subtype.mk.injEq, SliceOf.mk.injEq] at hxs
        obtain ⟨hxs, ho, hl⟩ := hxs
        subst_vars
        simp only
        rw [show min (n + 1) (l + 1) = if n + 1 ≤ l + 1 then n + 1 else l + 1 from rfl]
        simp +arith only at *
        by_cases (n = l)
        case pos h'' =>
          rw [h'']
          simp
          apply Prod.Lex.right
          simp only [Regex.star.sizeOf_spec]
          omega
        case neg h'' =>
          split_ifs
          · apply Prod.Lex.left
            omega
          · apply Prod.Lex.right
            simp only [Regex.star.sizeOf_spec]
            omega
    · cases xs with
      | mk o l h =>
      simp only [SliceOf.drop_succ, SliceOf.length, SliceOf.drop]
      cases xxs with
      | mk xs' hxs' =>
      cases n with
      | mk n hn =>
      cases xs' with
      | mk offset length prop =>
      simp only [SliceOf.length] at hxs'
      simp only [SliceOf.length] at hn
      simp only [SliceOf.nonEmpty] at hxs
      cases l with
      | zero =>
        simp only [reduceCtorEq] at hxs
      | succ l =>
        simp only [Option.some.injEq, Subtype.mk.injEq, SliceOf.mk.injEq] at hxs
        obtain ⟨hxs, ho, hl⟩ := hxs
        subst_vars
        simp only
        apply Prod.Lex.left
        omega

def denote_ref_regex {α: Type} [BEq α] (g: Grammar μ α) (p: Pred α) (x: Regex (Ref μ)) (as: ParseForest α): Prop :=
  match as with
  | [tree] =>
      Pred.eval p tree.getLabel
      /\ denote_regex_sliceof x (fun ref sliceOfChildren =>
          match g.lookup ref with
          | (p', x') => denote_ref_regex g p' x' (SliceOf.val sliceOfChildren)
        ) (SliceOf.mk' tree.getChildren)
  | _ => False
  termination_by as
  decreasing_by
    simp only [List.cons.sizeOf_spec, List.nil.sizeOf_spec, gt_iff_lt]
    cases tree with
    | mk label children =>
    simp only [ParseTree.getChildren] at sliceOfChildren
    simp only [SliceOf.val, ParseTree.getChildren]
    cases sliceOfChildren with
    | mk offset len prop =>
    simp only [ParseTree.mk.sizeOf_spec]
    have h : sizeOf (List.take len (List.drop offset children)) <= sizeOf children := by
      apply List.list_sizeOf_take_drop_le
    omega

def denote_start_ref_regex {α: Type} [BEq α] (g: Grammar μ α) (x: Regex (Pred α × Ref μ)) (as: ParseForest α): Prop :=
  denote_regex (fun (p, r) as' =>
    denote_ref_regex g p (Regex.symbol r) as'
  ) x as

theorem denote_start_ref_regex_emptyset {α: Type} [BEq α] {g: Grammar μ α}:
  denote_start_ref_regex g Regex.emptyset = Language.emptyset := by
  unfold Language.emptyset
  funext
  simp [denote_start_ref_regex, denote_regex]

theorem denote_start_ref_regex_emptystr {α: Type} [BEq α] {g: Grammar μ α}:
  denote_start_ref_regex g Regex.emptystr = Language.emptystr := by
  unfold Language.emptystr
  funext
  simp [denote_start_ref_regex, denote_regex]
