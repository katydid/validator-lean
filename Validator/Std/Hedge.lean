import Lean.Elab.Tactic

import Mathlib.Tactic.NthRewrite
import Mathlib.Tactic.RewriteSearch

import Validator.Std.List

inductive Hedge.Node (α: Type) where
  | mk (label: α) (children: List (Hedge.Node α))
  deriving BEq, Ord, Repr, Hashable

abbrev Hedge α := List (Hedge.Node α)

namespace Hedge

def node {α: Type} (label: α) (children: Hedge α): Hedge.Node α :=
  Hedge.Node.mk label children

example: Hedge String := [
  node "html" [
    node "head" [
      node "title" [node "My Title" []]
    ],
    node "body" [
      node "p" [node "First Paragraph" []],
      node "p" [node "Second Paragraph" []]
    ]
  ]
]

example: Hedge String := [
  node "html" [
    node "head" [],
    node "body" []
  ]
]

def Node.text (s: String) (children: Hedge (Option String)):
  Hedge.Node (Option String) :=
  node (Option.some s) children
def Node.elem (children: Hedge (Option String)):
  Hedge.Node (Option String) :=
  node Option.none children

example: Hedge (Option String) := [
  Node.text "Subject" [Node.text "hello" []],
  Node.text "From"    [Node.text "me@mail.org" []],
  Node.text "To"      [Node.elem [Node.text "you@mail.com" []]],
  Node.text "Attachments" [
    Node.elem [
      Node.text "Filename" [Node.text "first.md" []],
      Node.text "Contents" [Node.text "remember" []],
    ],
    Node.elem [
      Node.text "Filename" [Node.text "next.txt" []],
      Node.text "Contents" [Node.text "to reply" []],
    ]
  ]
]

-- Node is a Labelled Tree.

instance [Ord α]: LE (Node α) where
  le x y := (Ord.compare x y).isLE

instance [Ord α]: LT (Node α) where
  lt x y := (Ord.compare x y).isLT

def Node.getLabel (t: Node α): α :=
  match t with
  | Node.mk l _ => l

def Node.getChildren (t: Node α): Hedge α :=
  match t with
  | Node.mk _ c => c

def getAttachedChildren (t: Hedge.Node α): List {x // x ∈ t.getChildren} :=
  match t with
  | Node.mk _ c => c.attach

mutual
def Node.hasDecEq [DecidableEq α]: (a b : Node α) → Decidable (Eq a b)
  | Node.mk la as, Node.mk lb bs =>
    match decEq la lb with
    | isFalse nlab => isFalse (by
        simp only [Node.mk.injEq, not_and]
        intro h
        contradiction
      )
    | isTrue hlab =>
      match Node.hasDecEqs as bs with
      | isFalse nabs => isFalse (by
          simp only [Node.mk.injEq, not_and]
          intro _ hab
          contradiction
        )
      | isTrue habs => isTrue (by
          rw [hlab]
          rw [habs]
        )
def Node.hasDecEqs [DecidableEq α]: (as bs : Hedge α) → Decidable (Eq as bs)
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
    match Node.hasDecEq a b with
    | isFalse nab => isFalse (by
        simp only [List.cons.injEq, not_and]
        intro _ hab
        contradiction
      )
    | isTrue hab =>
      match Node.hasDecEqs as bs with
      | isFalse nabs => isFalse (fun h => List.noConfusion h (fun _ habs => absurd habs nabs))
      | isTrue habs => isTrue (hab ▸ habs ▸ rfl)
end

instance[DecidableEq α] : DecidableEq (Node α) := Node.hasDecEq

local elab "simp_sizeOf" : tactic => do
  Lean.Elab.Tactic.evalTactic (<- `(tactic|
    simp only [Node.mk.sizeOf_spec, List.cons.sizeOf_spec, List.nil.sizeOf_spec, Subtype.mk.sizeOf_spec])
  )

private theorem lt_plus (x y z: Nat):
  y < z -> x + y < x + z := by
  simp

theorem take_eq_self_iff (xs : List α) {n : Nat} : xs.take n = xs ↔ xs.length ≤ n :=
  ⟨fun h ↦ by rw [← h]; simp; omega, List.take_of_length_le⟩

theorem sizeOf_take (n: Nat) (xs: Hedge α):
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

theorem sizeOf_take_lt_n {xs: Hedge α}
  (hlen: n < List.length xs):
  sizeOf (List.take n xs) < sizeOf xs := by
  have h := sizeOf_take n xs
  cases h with
  | inl hh =>
    rw [List.list_take_eq_self_iff] at hh
    omega
  | inr hh =>
    exact hh

theorem sizeOf_drop (n: Nat) (xs: Hedge α):
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
      omega
    | inr h =>
      omega

theorem elem_is_leq_sizeOf {α: Type} [SizeOf α] {x: Hedge.Node α} {ys: Hedge α}:
  x ∈ ys ->
  sizeOf x <= sizeOf ys := by
  intro h
  induction h with
  | head =>
    simp only [List.cons.sizeOf_spec]
    omega
  | tail =>
    simp only [List.cons.sizeOf_spec]
    omega
