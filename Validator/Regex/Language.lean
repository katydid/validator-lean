import Mathlib.Tactic.Linarith -- split_ands

namespace Regex.Language

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

def Langs (α: Type): Type := List α -> Prop

def emptyset : Langs α :=
  fun _ => False

def universal {α: Type} : Langs α :=
  fun _ => True

def emptystr {α: Type} : Langs α :=
  fun xs => xs = []

def char {α: Type} (x : α): Langs α :=
  fun xs => xs = [x]

def pred {α: Type} (p : α -> Bool): Langs α :=
  fun xs => ∃ x, xs = [x] /\ p x

def symbol {α: Type} (Φ: σ -> α -> Prop) (s: σ): Langs α :=
  fun xs => ∃ x, xs = [x] /\ Φ s x

def any {α: Type}: Langs α :=
  fun xs => ∃ x, xs = [x]

-- onlyif is used as an and to make derive char not require an if statement
-- (derive (char c) a) w <-> (onlyif (a = c) emptystr)
def onlyif {α: Type} (cond : Prop) (P : Langs α) : Langs α :=
  fun xs => cond /\ P xs

def or {α: Type} (P : Langs α) (Q : Langs α) : Langs α :=
  fun xs => P xs \/ Q xs

def and {α: Type} (P : Langs α) (Q : Langs α) : Langs α :=
  fun xs => P xs /\ Q xs

def concat_append {α: Type} (P : Langs α) (Q : Langs α) : Langs α :=
  fun (xs : List α) =>
    ∃ (xs1 : List α) (xs2 : List α), P xs1 /\ Q xs2 /\ xs = (xs1 ++ xs2)

-- alternative definition of concat
def concat_n {α: Type} (P : Langs α) (Q : Langs α) : Langs α :=
  fun (xs : List α) =>
    ∃ n: Fin (xs.length + 1), P (List.take n xs) /\ Q (List.drop n xs)

inductive star_append {α: Type} (R: Langs α): Langs α where
  | zero: star_append R []
  | more: ∀ (x: α) (xs1 xs2 xs: List α),
    xs = (x::xs1) ++ xs2
    -> R (x::xs1)
    -> star_append R xs2
    -> star_append R xs

-- alternative definition of star
def star_n {α: Type} (R: Langs α) (xs: List α): Prop :=
  match xs with
  | [] => True
  | (x'::xs') =>
    ∃ (n: Fin xs.length),
      R (List.take (n + 1) (x'::xs')) /\
      (star_n R (List.drop (n + 1) (x'::xs')))
  termination_by xs.length
  decreasing_by
    obtain ⟨n, hn⟩ := n
    simp
    omega

def not {α: Type} (R: Langs α): Langs α :=
  fun xs => (Not (R xs))

-- attribute [simp] allows these definitions to be unfolded when using the simp tactic.
attribute [simp] universal emptyset emptystr char onlyif or and concat_append

example: Langs α := universal
example: Langs α := emptystr
example: Langs α := (or emptystr universal)
example: Langs α := (and emptystr universal)
example: Langs α := emptyset
example: Langs α := (star_append emptyset)
example: Langs Char := char 'a'
example: Langs Char := char 'b'
example: Langs Char := (or (char 'a') emptyset)
example: Langs Char := (and (char 'a') (char 'b'))
example: Langs Nat := (and (char 1) (char 2))
example: Langs Nat := (onlyif True (char 2))
example: Langs Nat := (concat_append (char 1) (char 2))
example: Langs Nat := (pred (fun x => x = 1))

def null {α: Type} (R: Langs α): Prop :=
  R []

def derives {α: Type} (R: Langs α) (xs: List α): Langs α :=
  λ ys => R (xs ++ ys)

def derive {α: Type} (R: Langs α) (x: α): Langs α :=
  derives R [x]

def derive' {α: Type} (R: Langs α) (x: α): Langs α :=
  fun (xs: List α) => R (x :: xs)

attribute [simp] null derive derives derive'

theorem derive_is_derive' {α: Type} (R: Langs α) (x: α):
  derive R x = derive' R x :=
  rfl

theorem derives_empty_list {α: Type} (R: Langs α):
  derives R [] = R :=
  rfl

theorem derives_strings {α: Type} (R: Langs α) (xs ys: List α):
  derives R (xs ++ ys) = derives (derives R xs) ys :=
  match xs with
  | [] => rfl
  | (x :: xs) => derives_strings (derive R x) xs ys

theorem derives_step {α: Type} (R: Langs α) (x: α) (xs: List α):
  derives R (x :: xs) = derives (derive R x) xs := by
  simp only [derive]
  rw [<- derives_strings]
  congr

theorem null_derives {α: Type} (R: Langs α) (xs: List α):
  (null ∘ derives R) xs = R xs := by
  unfold derives
  unfold null
  simp only [Function.comp_apply]
  simp only [append_nil]

theorem validate {α: Type} (R: Langs α) (xs: List α):
  null (derives R xs) = R xs := by
  unfold derives
  unfold null
  simp only [append_nil]

theorem derives_foldl (R: Langs α) (xs: List α):
  (derives R) xs = (List.foldl derive R) xs := by
  revert R
  induction xs with
  | nil =>
    unfold derives
    simp only [nil_append, foldl_nil, implies_true]
  | cons x xs ih =>
    simp
    intro R
    rw [derives_step]
    rw [ih (derive R x)]
    simp only [derive]

-- Theorems: null

theorem null_emptyset {α: Type}:
  @null α emptyset = False :=
  rfl

theorem null_iff_emptyset {α: Type}:
  @null α emptyset <-> False := by
  rw [null_emptyset]

theorem not_null_if_emptyset {α: Type}:
  @null α emptyset -> False :=
  null_iff_emptyset.mp

theorem null_universal {α: Type}:
  @null α universal = True :=
  rfl

theorem null_iff_emptystr {α: Type}:
  @null α emptystr <-> True :=
  Iff.intro
    (fun _ => True.intro)
    (fun _ => rfl)

theorem null_if_emptystr {α: Type}:
  @null α emptystr :=
  rfl

theorem null_emptystr {α: Type}:
  @null α emptystr = True := by
  rw [null_iff_emptystr]

theorem null_iff_any {α: Type}:
  @null α any <-> False :=
  Iff.intro nofun nofun

theorem not_null_if_any {α: Type}:
  @null α any -> False :=
  nofun

theorem null_any {α: Type}:
  @null α any = False := by
  rw [null_iff_any]

theorem null_iff_char {α: Type} {c: α}:
  null (char c) <-> False :=
  Iff.intro nofun nofun

theorem not_null_if_char {α: Type} {c: α}:
  null (char c) -> False :=
  nofun

theorem null_char {α: Type} {c: α}:
  null (char c) = False := by
  rw [null_iff_char]

theorem null_iff_pred {α: Type} {p: α -> Bool}:
  null (pred p) <-> False :=
  Iff.intro nofun nofun

theorem not_null_if_pred {α: Type} {p: α -> Bool}:
  null (pred p) -> False :=
  nofun

theorem null_pred {α: Type} {p: α -> Bool}:
  null (pred p) = False := by
  rw [null_iff_pred]

theorem null_iff_symbol {σ: Type} {α: Type} {Φ: σ -> α -> Prop} {s: σ}:
  null (symbol Φ s) <-> False :=
  Iff.intro nofun nofun

theorem not_null_if_symbol {σ: Type} {α: Type} {Φ: σ -> α -> Prop} {s: σ}:
  null (symbol Φ s) -> False :=
  nofun

theorem null_symbol {σ: Type} {α: Type} {Φ: σ -> α -> Prop} {s: σ}:
  null (symbol Φ s) = False := by
  rw [null_iff_symbol]

theorem null_or {α: Type} {P Q: Langs α}:
  null (or P Q) = ((null P) \/ (null Q)) :=
  rfl

theorem null_iff_or {α: Type} {P Q: Langs α}:
  null (or P Q) <-> ((null P) \/ (null Q)) := by
  rw [null_or]

theorem null_and {α: Type} {P Q: Langs α}:
  null (and P Q) = ((null P) /\ (null Q)) :=
  rfl

theorem null_iff_concat_append {α: Type} {P Q: Langs α}:
  null (concat_append P Q) <-> ((null P) /\ (null Q)) := by
  refine Iff.intro ?toFun ?invFun
  case toFun =>
    intro ⟨x, y, hx, hy, hxy⟩
    simp only [nil_eq, append_eq_nil_iff] at hxy
    simp only [hxy] at hx hy
    exact ⟨hx, hy⟩
  case invFun =>
    exact fun ⟨x, y⟩ => ⟨[], [], x, y, rfl⟩

theorem null_concat_append {α: Type} {P Q: Langs α}:
  null (concat_append P Q) = ((null P) /\ (null Q)) := by
  rw [null_iff_concat_append]

theorem null_iff_concat_n {α: Type} {P Q: Langs α}:
  null (concat_n P Q) <-> ((null P) /\ (null Q)) := by
  refine Iff.intro ?toFun ?invFun
  case toFun =>
    intro ⟨⟨n, hn⟩, hp, hq⟩
    simp at hn
    subst hn
    simp only [List.take] at hp
    simp only [List.drop] at hq
    exact And.intro hp hq
  case invFun =>
    intro ⟨hp, hq⟩
    unfold concat_n
    simp only [null, List.length_nil, Nat.reduceAdd, Fin.val_eq_zero, List.take_nil, List.drop_nil,
      exists_const]
    exact And.intro hp hq

theorem null_concat_n {α: Type} {P Q: Langs α}:
  null (concat_n P Q) = ((null P) /\ (null Q)) := by
  rw [null_iff_concat_n]

theorem null_if_star_append {α: Type} {R: Langs α}:
  null (star_append R) :=
  star_append.zero

theorem null_iff_star_append {α: Type} {R: Langs α}:
  null (star_append R) <-> True :=
  Iff.intro
    (fun _ => True.intro)
    (fun _ => star_append.zero)

theorem null_star_append {α: Type} {R: Langs α}:
  null (star_append R) = True := by
  rw [null_iff_star_append]

theorem null_iff_star_n {α: Type} {R: Langs α}:
  null (star_n R) <-> True :=
  Iff.intro
    (fun _ => True.intro)
    (fun _ => by
      unfold null
      simp only [star_n]
    )

theorem null_star_n {α: Type} {R: Langs α}:
  null (star_n R) = True := by
  rw [null_iff_star_n]

theorem null_not {α: Type} {R: Langs α}:
  null (not R) = null (Not ∘ R) :=
  rfl

theorem null_iff_not {α: Type} {R: Langs α}:
  null (not R) <-> null (Not ∘ R) := by
  rw [null_not]

-- Theorems: derive

theorem derive_emptyset {α: Type} {a: α}:
  (derive emptyset a) = emptyset :=
  rfl

theorem derive_universal {α: Type} {a: α}:
  (derive universal a) = universal :=
  rfl

theorem derive_iff_emptystr {α: Type} {a: α} {w: List α}:
  (derive emptystr a) w <-> emptyset w :=
  Iff.intro nofun nofun

theorem derive_emptystr {α: Type} {a: α}:
  (derive emptystr a) = emptyset := by
  funext
  rw [derive_iff_emptystr]

theorem derive_iff_char {α: Type} [DecidableEq α] {a: α} {c: α} {w: List α}:
  (derive (char c) a) w <-> (onlyif (a = c) emptystr) w := by
  refine Iff.intro ?toFun ?invFun
  case toFun =>
    intro D
    cases D with | refl =>
    exact ⟨ rfl, rfl ⟩
  case invFun =>
    intro ⟨ H1 , H2  ⟩
    cases H1 with | refl =>
    cases H2 with | refl =>
    exact rfl

theorem derive_char {α: Type} [DecidableEq α] {a: α} {c: α}:
  (derive (char c) a) = (onlyif (a = c) emptystr) := by
  funext
  rw [derive_iff_char]

theorem derive_iff_pred {α: Type} {p: α -> Bool} {x: α} {xs: List α}:
  (derive (pred p) x) xs <-> (onlyif (p x) emptystr) xs := by
  simp only [derive, derives, singleton_append]
  simp only [onlyif, emptystr]
  refine Iff.intro ?toFun ?invFun
  case toFun =>
    intro D
    match D with
    | Exists.intro x' D =>
    simp only [cons.injEq] at D
    match D with
    | And.intro (And.intro hxx' hxs) hpx =>
    rw [<- hxx'] at hpx
    exact And.intro hpx hxs
  case invFun =>
    intro ⟨ hpx , hxs  ⟩
    unfold pred
    exists x
    simp only [cons.injEq, true_and]
    exact And.intro hxs hpx

theorem derive_pred {α: Type} {p: α -> Bool} {x: α}:
  (derive (pred p) x) = (onlyif (p x) emptystr) := by
  funext
  rw [derive_iff_pred]

theorem derive_or {α: Type} {a: α} {P Q: Langs α}:
  (derive (or P Q) a) = (or (derive P a) (derive Q a)) :=
  rfl

theorem derive_and {α: Type} {a: α} {P Q: Langs α}:
  (derive (and P Q) a) = (and (derive P a) (derive Q a)) :=
  rfl

theorem derive_onlyif {α: Type} {a: α} {s: Prop} {P: Langs α}:
  (derive (onlyif s P) a) = (onlyif s (derive P a)) :=
  rfl

theorem derive_iff_concat_append {α: Type} {x: α} {P Q: Langs α} {xs: List α}:
  (derive (concat_append P Q) x) xs <->
    (or (concat_append (derive P x) Q) (onlyif (null P) (derive Q x))) xs := by
  refine Iff.intro ?toFun ?invFun
  case toFun =>
    simp only [Language.or, Language.concat_append, derive, derives, null, onlyif]
    intro d
    guard_hyp d: ∃ x_1 y, P x_1 ∧ Q y ∧ [x] ++ xs = x_1 ++ y
    guard_target = (∃ x_1 y, P ([x] ++ x_1) ∧ Q y ∧ xs = x_1 ++ y) ∨ P [] ∧ Q ([x] ++ xs)
    match d with
    | Exists.intro ps (Exists.intro qs (And.intro hp (And.intro hq hs))) =>
    guard_hyp hp : P ps
    guard_hyp hq : Q qs
    guard_hyp hs : [x] ++ xs = ps ++ qs
    match ps with
    | nil =>
      guard_hyp hp : P []
      guard_hyp hq : Q qs
      refine Or.inr ?r
      guard_target = P [] ∧ Q ([x] ++ xs)
      rw [nil_append] at hs
      rw [hs]
      exact And.intro hp hq
    | cons p ps =>
      guard_hyp hp : P (p :: ps)
      guard_hyp hq : Q qs
      guard_hyp hs : [x] ++ xs = p :: ps ++ qs
      refine Or.inl ?l
      guard_target = ∃ x_1 y, P ([x] ++ x_1) ∧ Q y ∧ xs = x_1 ++ y
      simp only [cons_append, cons.injEq] at hs
      match hs with
      | And.intro hpx hs =>
        rw [hpx]
        rw [nil_append] at hs
        rw [hs]
        guard_hyp hs : xs = ps ++ qs
        guard_target = ∃ x y, P ([p] ++ x) ∧ Q y ∧ ps ++ qs = x ++ y
        exact Exists.intro ps (Exists.intro qs (And.intro hp (And.intro hq rfl)))
  case invFun =>
    simp only [Language.or, Language.concat_append, derive, derives, null, onlyif]
    intro e
    guard_hyp e : (∃ x_1 y, P ([x] ++ x_1) ∧ Q y ∧ xs = x_1 ++ y) ∨ P [] ∧ Q ([x] ++ xs)
    guard_target = ∃ x_1 y, P x_1 ∧ Q y ∧ [x] ++ xs = x_1 ++ y
    match e with
    | Or.inl e =>
      guard_hyp e: ∃ x_1 y, P ([x] ++ x_1) ∧ Q y ∧ xs = x_1 ++ y
      guard_target = ∃ x_1 y, P x_1 ∧ Q y ∧ [x] ++ xs = x_1 ++ y
      match e with
      | Exists.intro ps (Exists.intro qs (And.intro hp (And.intro hq hs))) =>
        guard_hyp hp: P ([x] ++ ps)
        guard_hyp hq: Q qs
        guard_hyp hs: xs = ps ++ qs
        rw [hs]
        guard_target = ∃ x_1 y, P x_1 ∧ Q y ∧ [x] ++ (ps ++ qs) = x_1 ++ y
        exact Exists.intro ([x] ++ ps) (Exists.intro qs (And.intro hp (And.intro hq rfl)))
    | Or.inr e =>
      guard_hyp e : P [] ∧ Q ([x] ++ xs)
      guard_target = ∃ x_1 y, P x_1 ∧ Q y ∧ [x] ++ xs = x_1 ++ y
      match e with
      | And.intro hp hq =>
        exact Exists.intro [] (Exists.intro (x :: xs) (And.intro hp (And.intro hq rfl)))

theorem derive_concat_append {α: Type} {x: α} {P Q: Langs α}:
  (derive (concat_append P Q) x) =
    (or (concat_append (derive P x) Q) (onlyif (null P) (derive Q x))) := by
  funext
  rw [derive_iff_concat_append]

theorem derive_iff_star_append {α: Type} {x: α} {R: Langs α} {xs: List α}:
  (derive (star_append R) x) xs <-> (concat_append (derive R x) (star_append R)) xs := by
  refine Iff.intro ?toFun ?invFun
  case toFun =>
    intro deriveStar
    unfold derive at deriveStar
    unfold derives at deriveStar
    cases deriveStar with
    | more x' xs1 xs2 _ hxs Rxxs1 starRxs2 =>
      unfold concat_append
      exists xs1
      exists xs2
      simp only [cons_append, cons.injEq] at hxs
      cases hxs with
      | intro hxs1 hxs2 =>
      rw [hxs1]
      split_ands
      · exact Rxxs1
      · exact starRxs2
      · exact hxs2
  case invFun =>
    intro concatDerive
    unfold concat_append at concatDerive
    cases concatDerive with
    | intro xs1 concatDerive =>
    cases concatDerive with
    | intro xs2 concatDerive =>
    cases concatDerive with
    | intro deriveRxxs1 concatDerive =>
    cases concatDerive with
    | intro starRxs2 hxs =>
    unfold derive
    unfold derives
    refine star_append.more x xs1 xs2 ?hxs ?e ?f ?g
    · rw [hxs]
      simp only [cons_append, nil_append]
    · apply deriveRxxs1
    · exact starRxs2

theorem derive_star_append {α: Type} {x: α} {R: Langs α}:
  (derive (star_append R) x) = (concat_append (derive R x) (star_append R)) := by
  funext
  rw [derive_iff_star_append]

theorem derive_not {α: Type} {x: α} {R: Langs α}:
  (derive (not R) x) = Not ∘ (derive R x) :=
  rfl

theorem derive_iff_not {α: Type} {x: α} {R: Langs α} {xs: List α}:
  (derive (not R) x) xs <-> Not ((derive R x) xs) := by
  rw [derive_not]
  rfl

-- Theorems: simplification rules

theorem simp_concat_append_emptyset_l_is_emptyset (r: Langs α):
  concat_append emptyset r = emptyset := by
  unfold concat_append
  simp only [emptyset, false_and, exists_const]
  rfl

theorem simp_concat_append_emptyset_r_is_emptyset (r: Langs α):
  concat_append r emptyset = emptyset := by
  unfold concat_append
  simp only [emptyset, false_and, and_false, exists_const]
  rfl

theorem simp_concat_append_emptystr_l_is_r (r: Langs α):
  concat_append emptystr r = r := by
  unfold concat_append
  simp only [emptystr, exists_and_left, exists_eq_left, nil_append, exists_eq_right']

theorem simp_concat_append_emptystr_r_is_l (r: Langs α):
  concat_append r emptystr = r := by
  unfold concat_append
  simp only [emptystr, exists_and_left, exists_eq_left, append_nil, exists_eq_right']

theorem simp_concat_append_assoc (r s t: Langs α):
  concat_append (concat_append r s) t = concat_append r (concat_append s t) := by
  unfold concat_append
  funext xs
  simp only [eq_iff_iff]
  apply Iff.intro
  case mp =>
    intro h
    match h with
    | Exists.intro xs1
        (Exists.intro xs2
          (And.intro
            (Exists.intro xs3
              (Exists.intro xs4
                (And.intro rxs3
                  (And.intro sxs4 xs1split))))
            (And.intro txs2 xssplit))) =>
    clear h
    exists xs3
    exists (xs4 ++ xs2)
    split_ands
    · exact rxs3
    · exists xs4
      exists xs2
    · rw [xs1split] at xssplit
      simp only [append_assoc] at xssplit
      exact xssplit
  case mpr =>
    intro h
    match h with
    | Exists.intro xs1
        (Exists.intro xs2
          (And.intro rxs1
            (And.intro
              (Exists.intro xs3
                (Exists.intro xs4
                  (And.intro sxs3
                    (And.intro txs4 xs2split)
                )))
              xssplit))) =>
    clear h
    exists (xs1 ++ xs3)
    exists xs4
    split_ands
    · exists xs1
      exists xs3
    · exact txs4
    · rw [xs2split] at xssplit
      simp only [append_assoc]
      exact xssplit

-- class Associative found in Init/Core.lean in namespace Std
-- It is used by the ac_rfl tactic.
instance IsAssociative_concat_append {α: Type}: Std.Associative (@concat_append α) :=
  { assoc := @simp_concat_append_assoc α }

-- Test that ac_rfl uses the instance of Std.Associative
example (r s t: Langs α):
  concat_append (concat_append r s) t = concat_append r (concat_append s t) := by
  ac_rfl

instance IsLawfulIdentity_concat_append {α: Type} : Std.LawfulIdentity (@concat_append α) (@emptystr α) where
  left_id := simp_concat_append_emptystr_l_is_r
  right_id := simp_concat_append_emptystr_r_is_l

-- Test ac_rfl uses the instance of LawfulIdentity
example (r: Langs α):
  concat_append emptystr r = r := by
  ac_rfl

-- Test ac_nf tactic
example (r s: Langs α) (H: s = r):
  concat_append emptystr r = s := by
  ac_nf
  rw [H]

theorem concat_n_iff_concat:
  concat_n P Q xs <-> concat_append P Q xs := by
  apply Iff.intro
  case mp =>
    intro h
    cases h with
    | intro n h =>
    cases h with
    | intro hx hy =>
    exists (List.take n xs)
    exists (List.drop n xs)
    apply And.intro hx
    apply And.intro hy
    simp only [List.take_append_drop]
  case mpr =>
    intro h
    cases h with
    | intro xs h =>
    cases h with
    | intro ys h =>
    cases h with
    | intro hx h =>
    cases h with
    | intro hy hxsys =>
    rw [hxsys]
    unfold concat_n
    exists (Fin.mk (List.length xs) (by
      simp only [List.length_append]
      omega
    ))
    simp only [List.take_left', List.drop_left']
    apply And.intro hx hy

theorem concat_n_is_concat:
  concat_n P Q = concat_append P Q := by
  funext xs
  rw [concat_n_iff_concat]

theorem derive_iff_concat_n {α: Type} {x: α} {P Q: Langs α} {xs: List α}:
  (derive (concat_n P Q) x) xs <->
    (or (concat_n (derive P x) Q) (onlyif (null P) (derive Q x))) xs := by
  repeat rw [concat_n_is_concat]
  rw [derive_iff_concat_append]

theorem derive_concat_n {α: Type} {x: α} {P Q: Langs α}:
  (derive (concat_n P Q) x) =
    (or (concat_n (derive P x) Q) (onlyif (null P) (derive Q x))) := by
  funext
  rw [derive_iff_concat_n]

theorem star_append_is_star_n:
  star_n P xs <-> star_append P xs := by
  apply Iff.intro
  case mp =>
    intro h
    unfold star_n at h
    cases xs with
    | nil =>
      apply star_append.zero
    | cons x xs =>
      simp at h
      obtain ⟨⟨n, hn⟩, ⟨hp, hq⟩⟩ := h
      simp at hp hq
      apply star_append.more x (List.take n xs) (List.drop n xs)
      · rw [cons_append]
        simp
      · assumption
      · apply star_append_is_star_n.mp hq
  case mpr =>
    intro h
    cases xs with
    | nil =>
      unfold star_n
      simp
    | cons x xs =>
      unfold star_n
      cases h with
      | more x xs1 xs2 _ hxs hp hq =>
        simp at hxs
        obtain ⟨hx, hxs⟩ := hxs
        subst_vars
        exists (Fin.mk xs1.length (by
          simp
          omega
        ))
        simp
        apply And.intro hp
        apply star_append_is_star_n.mpr hq
  termination_by xs.length

theorem simp_or_emptyset_l_is_r (r: Langs α):
  or emptyset r = r := by
  unfold or
  simp only [emptyset, false_or]

theorem simp_or_emptyset_r_is_l (r: Langs α):
  or r emptyset = r := by
  unfold or
  simp only [emptyset, or_false]

theorem simp_or_universal_l_is_universal (r: Langs α):
  or universal r = universal := by
  unfold or
  simp only [universal, true_or]
  rfl

theorem simp_or_universal_r_is_universal (r: Langs α):
  or r universal = universal := by
  unfold or
  simp only [universal, or_true]
  rfl

theorem simp_or_null_l_emptystr_is_l
  (r: Langs α)
  (nullr: null r):
  or r emptystr = r := by
  unfold or
  simp only [emptystr]
  unfold null at nullr
  funext xs
  simp only [eq_iff_iff, or_iff_left_iff_imp]
  intro hxs
  rw [hxs]
  exact nullr

theorem simp_or_emptystr_null_r_is_r
  (r: Langs α)
  (nullr: null r):
  or emptystr r = r := by
  unfold or
  simp only [emptystr]
  unfold null at nullr
  funext xs
  simp only [eq_iff_iff, or_iff_right_iff_imp]
  intro hxs
  rw [hxs]
  exact nullr

theorem simp_or_idemp (r: Langs α):
  or r r = r := by
  unfold or
  funext xs
  apply or_self

theorem simp_or_comm (r s: Langs α):
  or r s = or s r := by
  unfold or
  funext xs
  simp only [eq_iff_iff]
  apply Iff.intro
  case mp =>
    intro h
    match h with
    | Or.inl h =>
      exact Or.inr h
    | Or.inr h =>
      exact Or.inl h
  case mpr =>
    intro h
    match h with
    | Or.inl h =>
      exact Or.inr h
    | Or.inr h =>
      exact Or.inl h

theorem simp_or_assoc (r s t: Langs α):
  or (or r s) t = or r (or s t) := by
  unfold or
  funext xs
  simp only [eq_iff_iff]
  apply Iff.intro
  · case mp =>
    intro h
    cases h with
    | inl h =>
      cases h with
      | inl h =>
        left
        exact h
      | inr h =>
        right
        left
        exact h
    | inr h =>
      right
      right
      exact h
  · case mpr =>
    intro h
    cases h with
    | inl h =>
      left
      left
      exact h
    | inr h =>
      cases h with
      | inl h =>
        left
        right
        exact h
      | inr h =>
        right
        exact h

-- class Associative found in Init/Core.lean in namespace Std
-- It is used by the ac_rfl tactic.
instance IsAssociative_or {α: Type}: Std.Associative (@or α) :=
  { assoc := @simp_or_assoc α }

-- class Commutative found in Init/Core.lean in namespace Std
-- It is used by the ac_rfl tactic.
instance IsCommutative_or {α: Type}: Std.Commutative (@or α) :=
  { comm := @simp_or_comm α }

-- class IdempotentOp found in Init/Core.lean in namespace Std
-- It is used by the ac_rfl tactic.
instance IsIdempotentOp_or {α: Type}: Std.IdempotentOp (@or α) :=
  { idempotent := simp_or_idemp }

instance IsLawfulCommIdentity_or {α: Type} : Std.LawfulCommIdentity (@or α) (@emptyset α) where
  right_id r := simp_or_emptyset_r_is_l r

-- Test that ac_rfl uses the instance of Std.LawfulCommIdentity
example (r: Langs α):
  or r emptyset = r := by
  ac_rfl

-- Test that ac_rfl uses the instance of Std.Commutative
example (r s: Langs α):
  or r s = or s r := by
  ac_rfl

-- Test that ac_rfl uses the instance of Std.Associative
example (r s t: Langs α):
  or (or r s) t = or r (or s t) := by
  ac_rfl

-- Test that ac_rfl uses the instance of Std.IdempotentOp
example (r: Langs α):
  or (or r r) r = r := by
  ac_rfl

-- Test that ac_rfl uses both the instances of Std.Associative and Std.Commutative
example (a b c d : Langs α):
  (or a (or b (or c d))) = (or d (or (or b c) a)) := by ac_rfl

-- Test that ac_rfl uses both the instances of Std.Associative and Std.Commutative and Std.IdempotentOp
example (a b c d : Langs α):
  (or a (or b (or c d))) = (or a (or d (or (or b c) a))) := by ac_rfl

-- Test ac_nf tactic
example (r s: Langs α) (H: s = r):
  or emptyset (or r s) = (or r r) := by
  ac_nf
  rw [H]
  ac_rfl

theorem simp_and_emptyset_l_is_emptyset (r: Langs α):
  and emptyset r = emptyset := by
  unfold and
  simp only [emptyset, false_and]
  rfl

theorem simp_and_emptyset_r_is_emptyset (r: Langs α):
  and r emptyset = emptyset := by
  unfold and
  simp only [emptyset, and_false]
  rfl

theorem simp_and_universal_l_is_r (r: Langs α):
  and universal r = r := by
  unfold and
  simp only [universal, true_and]

theorem simp_and_universal_r_is_l (r: Langs α):
  and r universal = r := by
  unfold and
  simp only [universal, and_true]

theorem simp_and_null_l_emptystr_is_emptystr
  (r: Langs α)
  (nullr: null r):
  and r emptystr = emptystr := by
  funext xs
  simp only [and, emptystr, eq_iff_iff, and_iff_right_iff_imp]
  intro hxs
  rw [hxs]
  exact nullr

theorem simp_and_emptystr_null_r_is_emptystr
  (r: Langs α)
  (nullr: null r):
  and emptystr r = emptystr := by
  funext xs
  simp only [null] at nullr
  simp only [and, emptystr, eq_iff_iff, and_iff_left_iff_imp]
  intro hxs
  rw [hxs]
  exact nullr

theorem simp_and_not_null_l_emptystr_is_emptyset
  (r: Langs α)
  (notnullr: Not (null r)):
  and r emptystr = emptyset := by
  funext xs
  simp only [and, emptystr, emptyset, eq_iff_iff, iff_false, not_and]
  intro hr hxs
  rw [hxs] at hr
  contradiction

theorem simp_and_emptystr_not_null_r_is_emptyset
  (r: Langs α)
  (notnullr: Not (null r)):
  and emptystr r = emptyset := by
  funext xs
  simp only [and, emptystr, emptyset, eq_iff_iff, iff_false, not_and]
  intro hxs
  rw [hxs]
  exact notnullr

theorem simp_and_idemp (r: Langs α):
  and r r = r := by
  unfold and
  funext xs
  simp only [eq_iff_iff]
  apply Iff.intro
  case mp =>
    intro h
    cases h
    assumption
  case mpr =>
    intro h
    exact And.intro h h

theorem simp_and_comm (r s: Langs α):
  and r s = and s r := by
  unfold and
  funext xs
  simp only [eq_iff_iff]
  apply Iff.intro
  case mp =>
    intro h
    cases h with
    | intro hr hs =>
      exact And.intro hs hr
  case mpr =>
    intro h
    cases h with
    | intro hs hr =>
      exact And.intro hr hs

theorem simp_and_assoc (r s t: Langs α):
  and (and r s) t = and r (and s t) := by
  unfold and
  funext xs
  simp only [eq_iff_iff]
  apply Iff.intro
  case mp =>
    intro h
    match h with
    | And.intro (And.intro h1 h2) h3 =>
    exact And.intro h1 (And.intro h2 h3)
  case mpr =>
    intro h
    match h with
    | And.intro h1 (And.intro h2 h3) =>
    exact And.intro (And.intro h1 h2) h3

-- class Associative found in Init/Core.lean in namespace Std
-- It is used by the ac_rfl tactic.
instance IsAssociative_and {α: Type}: Std.Associative (@and α) :=
  { assoc := @simp_and_assoc α }

-- class Commutative found in Init/Core.lean in namespace Std
-- It is used by the ac_rfl tactic.
instance IsCommutative_and {α: Type}: Std.Commutative (@and α) :=
  { comm := @simp_and_comm α }

-- class IdempotentOp found in Init/Core.lean in namespace Std
-- It is used by the ac_rfl tactic.
instance IsIdempotentOp_and {α: Type}: Std.IdempotentOp (@and α) :=
  { idempotent := simp_and_idemp }

instance IsLawfulCommIdentity_and {α: Type} : Std.LawfulCommIdentity (@and α) (@universal α) where
  right_id r := simp_and_universal_r_is_l r

-- Test that ac_rfl uses the instance of Std.LawfulCommIdentity
example (r: Langs α):
  and r universal = r := by
  ac_rfl

-- Test that ac_rfl uses the instance of Std.Commutative
example (r s: Langs α):
  and r s = and s r := by
  ac_rfl

-- Test that ac_rfl uses the instance of Std.Associative
example (r s t: Langs α):
  and (and r s) t = and r (and s t) := by
  ac_rfl

-- Test that ac_rfl uses the instance of Std.IdempotentOp
example (r: Langs α):
  and r (and r r) = r := by
  ac_rfl

-- Test that ac_rfl uses both the instances of Std.Associative and Std.Commutative
example (a b c d : Langs α):
  (and a (and b (and c d))) = (and d (and (and b c) a)) := by ac_rfl

-- Test that ac_rfl uses both the instances of Std.Associative and Std.Commutative and Std.IdempotentOp
example (a b c d : Langs α):
  (and a (and b (and c d))) = (and d (and d (and (and b c) a))) := by ac_rfl

theorem not_not_intro' {p : Prop} (h : p) : ¬ ¬ p :=
  fun hn : (p -> False) => hn h

theorem simp_not_not_is_double_negation
  (r: Langs α) [DecidablePred r]:
  not (not r) = r := by
  unfold not
  funext xs
  simp only [eq_iff_iff]
  exact Decidable.not_not

theorem simp_not_and_demorgen
  (r s: Langs α) (xs: List α) [Decidable (r xs)] [Decidable (s xs)]:
  not (and r s) xs = or (not r) (not s) xs := by
  unfold and
  unfold or
  unfold not
  simp only [eq_iff_iff]
  exact Decidable.not_and_iff_not_or_not

theorem simp_not_or_demorgen (r s: Langs α):
  not (or r s) = and (not r) (not s) := by
  unfold not
  unfold or
  unfold and
  simp only [not_or]

theorem simp_and_not_emptystr_l_not_null_r_is_r
  (r: Langs α)
  (notnullr: Not (null r)):
  and (not emptystr) r = r := by
  funext xs
  simp only [and, not, emptystr, eq_iff_iff, and_iff_right_iff_imp]
  intro hr hxs
  rw [hxs] at hr
  contradiction

theorem simp_and_not_null_l_not_emptystr_r_is_l
  (r: Langs α)
  (notnullr: Not (null r)):
  and r (not emptystr) = r := by
  funext xs
  simp only [null] at notnullr
  simp only [and, not, emptystr, eq_iff_iff, and_iff_left_iff_imp]
  intro hr hxs
  rw [hxs] at hr
  contradiction

theorem simp_one_r_implies_star_append_r (r: Langs α) (xs: List α):
  r xs -> star_append r xs := by
  intro h
  cases xs
  · exact star_append.zero
  · case cons x xs =>
    apply star_append.more x xs []
    · simp only [append_nil]
    · exact h
    · exact star_append.zero

theorem simp_star_append_concat_append_star_append_implies_star_append (r: Langs α) (xs: List α):
  concat_append (star_append r) (star_append r) xs -> star_append r xs := by
  intro h
  cases h with
  | intro xs1 h =>
  cases h with
  | intro xs2 h =>
  cases h with
  | intro starrxs1 h =>
  cases h with
  | intro starrxs2 xssplit =>
  rw [xssplit]
  clear xssplit
  induction starrxs1 with
  | zero =>
    simp only [nil_append]
    exact starrxs2
  | more x xs11 xs12 _ xs1split rxxs11 starrxs12 ih =>
    rename_i xs1
    rw [xs1split]
    apply star_append.more x xs11 (xs12 ++ xs2)
    simp only [cons_append, append_assoc]
    exact rxxs11
    exact ih

theorem simp_star_append_implies_star_append_concat_append_star_append (r: Langs α) (xs: List α):
  star_append r xs -> concat_append (star_append r) (star_append r) xs  := by
  intro h
  cases h with
  | zero =>
    unfold concat_append
    exists []
    exists []
    split_ands
    · exact star_append.zero
    · exact star_append.zero
    · simp only [append_nil]
  | more x xs1 xs2 _ xssplit rxxs1 starrxs2 =>
    unfold concat_append
    exists (x::xs1)
    exists xs2
    split_ands
    · refine star_append.more x xs1 [] _ ?_ ?_ ?_
      · simp only [append_nil]
      · exact rxxs1
      · exact star_append.zero
    · exact starrxs2
    · rw [xssplit]

theorem simp_star_append_concat_append_star_append_is_star_append (r: Langs α):
  concat_append (star_append r) (star_append r) = star_append r := by
  unfold concat_append
  funext xs
  simp only [eq_iff_iff]
  apply Iff.intro
  case mp =>
    apply simp_star_append_concat_append_star_append_implies_star_append
  case mpr =>
    apply simp_star_append_implies_star_append_concat_append_star_append

theorem simp_star_append_star_append_is_star_append (r: Langs α):
  star_append (star_append r) = star_append r := by
  funext xs
  simp only [eq_iff_iff]
  apply Iff.intro
  case mp =>
    intro h
    induction h with
    | zero =>
      exact star_append.zero
    | more x xs1 xs2 _ xssplit starrxxs1 starstarrxs2 ih =>
      rename_i xss
      rw [xssplit]
      rw [<- simp_star_append_concat_append_star_append_is_star_append]
      unfold concat_append
      exists (x::xs1)
      exists xs2
  case mpr =>
    intro h
    induction h with
    | zero =>
      exact star_append.zero
    | more x xs1 xs2 _ xssplit rxxs1 starrxs2 ih =>
      rename_i xss
      apply star_append.more x xs1 xs2
      · exact xssplit
      · apply simp_one_r_implies_star_append_r
        exact rxxs1
      · exact ih

theorem simp_star_append_emptystr_is_emptystr {α: Type}:
  star_append (@emptystr α) = (@emptystr α) := by
  funext xs
  simp only [emptystr, eq_iff_iff]
  apply Iff.intro
  case mp =>
    intro h
    cases h
    case zero =>
      rfl
    case more x xs1 xs2 hemptystr hstar hsplit =>
      nomatch hemptystr
  case mpr =>
    intro h
    rw [h]
    exact star_append.zero

theorem simp_star_append_emptyset_is_emptystr {α: Type}:
  star_append (@emptyset α) = (@emptystr α) := by
  funext xs
  simp only [emptystr, eq_iff_iff]
  apply Iff.intro
  case mp =>
    intro h
    cases h
    case zero =>
      rfl
    case more x xs1 xs2 hemptystr hstar hsplit =>
      nomatch hemptystr
  case mpr =>
    intro h
    rw [h]
    exact star_append.zero

theorem simp_star_append_any_is_universal {α: Type}:
  star_append (@any α) = @universal α := by
  funext xs
  simp only [universal, eq_iff_iff]
  apply Iff.intro
  case mp =>
    intro h
    exact True.intro
  case mpr =>
    intro h
    induction xs with
    | nil =>
      exact star_append.zero
    | cons x xs ih =>
      apply star_append.more x [] xs
      · simp only [singleton_append]
      · unfold any
        exists x
      · exact ih

def onlyif_true {cond: Prop} {l: List α -> Prop} (condIsTrue: cond):
  Language.onlyif cond l = l := by
  unfold Language.onlyif
  funext xs
  simp only [eq_iff_iff, and_iff_right_iff_imp]
  intro p
  assumption

def onlyif_false {cond: Prop} {l: List α -> Prop} (condIsFalse: ¬cond):
  Language.onlyif cond l = Language.emptyset := by
  funext xs
  rw [eq_iff_iff]
  apply Iff.intro
  case mp =>
    intro h
    cases h
    case intro condIsTrue lxs =>
    contradiction
  case mpr =>
    intro h
    nomatch h

theorem simp_or_concat_append_left_distrib (a b c : Langs α) : concat_append a (or b c) = or (concat_append a b) (concat_append a c) := by
  unfold or
  unfold concat_append
  funext xs
  simp only
  simp only [eq_iff_iff]
  simp only [exists_and_left]
  apply Iff.intro
  · case mp =>
    intro H
    cases H with
    | intro xs1 H =>
    cases H with
    | intro axs1 H =>
    cases H with
    | intro x H =>
    cases H with
    | intro bc H =>
    cases bc with
    | inl Hb =>
      apply Or.inl
      exists xs1
      apply And.intro
      exact axs1
      exists x
    | inr Hc =>
      apply Or.inr
      exists xs1
      apply And.intro
      exact axs1
      exists x
  . case mpr =>
    intro H
    cases H with
    | inl H =>
      cases H with
      | intro xs1 H =>
      cases H with
      | intro axs1 H =>
      cases H with
      | intro x H =>
      cases H with
      | intro Hb H =>
      exists xs1
      apply And.intro
      exact axs1
      exists x
      apply And.intro
      apply Or.inl
      exact Hb
      exact H
    | inr H =>
      cases H with
      | intro xs1 H =>
      cases H with
      | intro axs1 H =>
      cases H with
      | intro x H =>
      cases H with
      | intro Hc H =>
      exists xs1
      apply And.intro
      exact axs1
      exists x
      apply And.intro
      apply Or.inr
      exact Hc
      exact H

theorem simp_or_concat_append_right_distrib (a b c : Langs α) : concat_append (or a b) c = or (concat_append a c) (concat_append b c) := by
  unfold or
  unfold concat_append
  funext xs
  simp only [eq_iff_iff]
  apply Iff.intro
  · case mp =>
    intro H
    cases H with
    | intro xs1 H =>
    cases H with
    | intro xs2 H =>
    cases H with
    | intro Hab H =>
    cases H with
    | intro Hc H =>
    cases Hab with
    | inl Ha =>
      apply Or.inl
      exists xs1
      exists xs2
    | inr Hb =>
      apply Or.inr
      exists xs1
      exists xs2
  · case mpr =>
    intro H
    cases H with
    | inl H =>
      cases H with
      | intro xs1 H =>
      cases H with
      | intro xs2 H =>
      cases H with
      | intro Ha H =>
      cases H with
      | intro Hc H =>
      exists xs1
      exists xs2
      apply And.intro
      · apply Or.inl
        exact Ha
      · apply And.intro
        · exact Hc
        · exact H
    | inr H =>
      cases H with
      | intro xs1 H =>
      cases H with
      | intro xs2 H =>
      cases H with
      | intro Hb H =>
      cases H with
      | intro Hc H =>
      exists xs1
      exists xs2
      apply And.intro
      · apply Or.inr
        exact Hb
      · apply And.intro
        · exact Hc
        · exact H

theorem simp_or_and_left_distrib (a b c : Langs α) : and a (or b c) = or (and a b) (and a c) := by
  unfold and
  unfold or
  funext xs
  simp only [eq_iff_iff]
  apply Iff.intro
  · case mp =>
    intro H
    cases H with
    | intro Ha Hbc =>
    cases Hbc with
    | inl Hb =>
      apply Or.inl
      apply And.intro Ha Hb
    | inr Hc =>
      apply Or.inr
      apply And.intro Ha Hc
  · case mpr =>
    intro H
    cases H with
    | inl Hab =>
      cases Hab with
      | intro Ha Hb =>
        apply And.intro
        exact Ha
        apply Or.inl
        exact Hb
    | inr Hac =>
      cases Hac with
      | intro Ha Hc =>
        apply And.intro
        exact Ha
        apply Or.inr
        exact Hc

theorem simp_or_and_right_distrib (a b c : Langs α) : and (or a b) c = or (and a c) (and b c) := by
  unfold and
  unfold or
  funext xs
  simp only [eq_iff_iff]
  apply Iff.intro
  · case mp =>
    intro H
    cases H with
    | intro Hab Hc =>
    cases Hab with
    | inl Ha =>
      apply Or.inl
      apply And.intro Ha Hc
    | inr Hb =>
      apply Or.inr
      apply And.intro Hb Hc
  · case mpr =>
    intro H
    cases H with
    | inl Hac =>
      cases Hac with
      | intro Ha Hc =>
        apply And.intro
        apply Or.inl
        exact Ha
        exact Hc
    | inr Hbc =>
      cases Hbc with
      | intro Hb Hc =>
        apply And.intro
        apply Or.inr
        exact Hb
        exact Hc

theorem simp_and_or_left_distrib (a b c : Langs α) : or a (and b c) = and (or a b) (or a c) := by
  unfold and
  unfold or
  funext xs
  simp only [eq_iff_iff]
  apply Iff.intro
  · case mp =>
    intro H
    cases H with
    | inl H =>
      apply And.intro
      · apply Or.inl H
      · apply Or.inl H
    | inr H =>
      cases H with
      | intro Hb Hc =>
      apply And.intro
      · apply Or.inr Hb
      · apply Or.inr Hc
  · case mpr =>
    intro H
    cases H with
    | intro Hab Hac =>
    cases Hab with
    | inl Ha =>
      apply Or.inl Ha
    | inr Hb =>
      cases Hac with
      | inl Ha =>
        apply Or.inl Ha
      | inr Hc =>
        apply Or.inr
        apply And.intro Hb Hc

theorem simp_and_or_right_distrib (a b c : Langs α) : or (and a b) c = and (or a c) (or b c) := by
  unfold and
  unfold or
  funext xs
  simp only [eq_iff_iff]
  apply Iff.intro
  · case mp =>
    intro H
    cases H with
    | inl h => simp_all only [true_or, and_self]
    | inr h_1 => simp_all only [or_true, and_self]
  · case mpr =>
    intro H
    cases H with
    | intro Hleft Hright =>
    cases Hleft with
    | inl h =>
      cases Hright with
      | inl h_1 => simp_all only [and_self, true_or]
      | inr h_2 => simp_all only [true_and, or_true]
    | inr h_1 =>
      cases Hright with
      | inl h => simp_all only [and_true, or_true]
      | inr h_2 => simp_all only [or_true]

theorem simp_or_star_append_any_l_is_star_append_any (r: Langs α):
  or (star_append any) r = (star_append any) := by
  rw [simp_star_append_any_is_universal]
  rw [simp_or_universal_l_is_universal]

theorem simp_or_star_append_any_r_is_star_append_any (r: Langs α):
  or r (star_append any) = (star_append any) := by
  rw [simp_star_append_any_is_universal]
  rw [simp_or_universal_r_is_universal]
