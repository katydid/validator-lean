import Lean.Elab.Tactic

import Mathlib.Tactic.NthRewrite

import Validator.Std.List
import Validator.Std.Slice

-- ParseTree is a Labelled Tree.
inductive ParseTree (α: Type) where
  | mk (label: α) (children: List (ParseTree α))
  deriving BEq, Ord, Repr, Hashable

abbrev ParseForest α := List (ParseTree α)

namespace ParseTree

instance [Ord α]: LE (ParseTree α) where
  le x y := (Ord.compare x y).isLE

instance [Ord α]: LT (ParseTree α) where
  lt x y := (Ord.compare x y).isLT

def getLabel (t: ParseTree α): α :=
  match t with
  | ParseTree.mk l _ => l

def getChildren (t: ParseTree α): ParseForest α :=
  match t with
  | ParseTree.mk _ c => c

def getAttachedChildren (t: ParseTree α): List {x // x ∈ t.getChildren} :=
  match t with
  | ParseTree.mk _ c => c.attach

mutual
def hasDecEq [DecidableEq α]: (a b : ParseTree α) → Decidable (Eq a b)
  | ParseTree.mk la as, ParseTree.mk lb bs =>
    match decEq la lb with
    | isFalse nlab => isFalse (by
        simp only [ParseTree.mk.injEq, not_and]
        intro h
        contradiction
      )
    | isTrue hlab =>
      match ParseTree.hasDecEqs as bs with
      | isFalse nabs => isFalse (by
          simp only [ParseTree.mk.injEq, not_and]
          intro _ hab
          contradiction
        )
      | isTrue habs => isTrue (by
          rw [hlab]
          rw [habs]
        )
def hasDecEqs [DecidableEq α]: (as bs : ParseForest α) → Decidable (Eq as bs)
  | [], [] => isTrue rfl
  | (a::as), [] => isFalse (by
      intro h
      contradiction
    )
  | [], (b::bs) => isFalse (by
      intro h
      contradiction
    )
  | (a::as), (b::bs) =>
    match ParseTree.hasDecEq a b with
    | isFalse nab => isFalse (by
        simp only [List.cons.injEq, not_and]
        intro _ hab
        contradiction
      )
    | isTrue hab =>
      match ParseTree.hasDecEqs as bs with
      | isFalse nabs => isFalse (fun h => List.noConfusion h (fun _ habs => absurd habs nabs))
      | isTrue habs => isTrue (hab ▸ habs ▸ rfl)
end

instance[DecidableEq α] : DecidableEq (ParseTree α) := hasDecEq

local elab "simp_sizeOf" : tactic => do
  Lean.Elab.Tactic.evalTactic (<- `(tactic|
    simp only [ParseTree.mk.sizeOf_spec, List.cons.sizeOf_spec, List.nil.sizeOf_spec, Subtype.mk.sizeOf_spec])
  )

private theorem lt_plus (x y z: Nat):
  y < z -> x + y < x + z := by
  simp

theorem take_eq_self_iff (x : List α) {n : Nat} : x.take n = x ↔ x.length ≤ n :=
  ⟨fun h ↦ by rw [← h]; simp, List.take_of_length_le⟩

theorem ParseForest.sizeOf_take (n: Nat) (xs: ParseForest α):
  List.take n xs = xs \/ sizeOf (List.take n xs) < sizeOf xs := by
  rw [take_eq_self_iff]
  by_cases (List.length xs > n)
  case pos h =>
    apply Or.inr
    induction n generalizing xs with
    | zero =>
      simp only [List.take]
      simp_sizeOf
      cases xs with
      | nil =>
        simp only [List.length_nil, gt_iff_lt, Nat.lt_irrefl] at h
      | cons x xs =>
        simp_sizeOf
        cases x
        simp_sizeOf
        omega
    | succ n' ih =>
      cases xs with
      | nil =>
        simp at h
      | cons x xs =>
        simp only [List.take]
        simp_sizeOf
        simp only [List.length_cons, gt_iff_lt, Nat.add_lt_add_iff_right] at h
        apply lt_plus
        apply ih
        exact h
  case neg h =>
    simp only [gt_iff_lt, Nat.not_lt] at h
    apply Or.inl
    assumption

theorem ParseForest.sizeOf_drop (n: Nat) (xs: ParseForest α):
  List.drop n xs = xs \/ sizeOf (List.drop n xs) < sizeOf xs := by
  have h := List.list_drop_exists (xs := xs) (n := n)
  cases h with
  | intro ys h =>
  nth_rewrite 2 [h]
  nth_rewrite 4 [h]
  cases ys with
  | nil =>
    simp only [List.nil_append, Nat.lt_irrefl, or_false]
  | cons y ys =>
    apply Or.inr
    apply List.list_sizeOf_cons

theorem le (a b: Nat):
  a <= b <-> a = b \/ a < b := by
  apply Iff.intro
  case mp =>
    intro h
    omega
  case mpr =>
    intro h
    cases h with
    | inl h =>
      rw [h]
    | inr h =>
      omega
