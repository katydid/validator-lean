import Lean.Elab.Tactic

import Mathlib.Tactic.NthRewrite
import Mathlib.Tactic.RewriteSearch

import Validator.Std.List

inductive Hedge.Node (α: Type) where
  | mk (label: α) (children: List (Hedge.Node α))
  deriving BEq, Ord, Repr, Hashable

abbrev Hedge α := List (Hedge.Node α)

namespace Hedge

-- Node is a Labelled Tree.

instance [Ord α]: LE (Node α) where
  le x y := (Ord.compare x y).isLE

instance [Ord α]: LT (Node α) where
  lt x y := (Ord.compare x y).isLT

def Node.getLabel (t: Node α): α :=
  match t with
  | Node.mk l _ => l

def Node.getLabels (t: Node α): List α :=
  match t with
  | Node.mk l children => l :: List.flatMap Node.getLabels children

def Node.getChildren (t: Node α): Hedge α :=
  match t with
  | Node.mk _ c => c

def getAttachedChildren (t: Hedge.Node α): List {x // x ∈ t.getChildren} :=
  match t with
  | Node.mk _ c => c.attach

def node {α: Type} (label: α) (children: Hedge α): Hedge.Node α :=
  Hedge.Node.mk label children

abbrev LabelElem (x: α) (xs: Hedge α) := x ∈ List.flatMap Node.getLabels xs

abbrev LabelIn {α: Type} (xs: Hedge α) := {
    a: α
    // LabelElem a xs
  }

def LabelIn.mk {α: Type} (y: α) (xs: Hedge α) (property : LabelElem y xs) : LabelIn xs :=
  (Subtype.mk y property)

def LabelIn.self {α: Type} (x: Hedge.Node α) : LabelIn [x] :=
  (Subtype.mk x.getLabel (by
    cases x with
    | mk label children =>
    simp only [LabelElem, List.flatMap_cons, Node.getLabels, List.flatMap_nil, List.append_nil, Node.getLabel,
      List.mem_cons, List.mem_flatMap, true_or]
  ))

def Node.getDescendants (t: Hedge.Node α): Hedge α :=
  match t with
  | Node.mk _ children => children ++ List.flatMap Node.getDescendants children

abbrev Node.Descendant (child: Hedge.Node α) (ancestor: Hedge.Node α) := child ∈ ancestor.getDescendants

abbrev Node.DescendantOf {α: Type} (ancestor: Hedge.Node α) := {
    child: Hedge.Node α
    // Descendant child ancestor
  }

def Node.Descendant.mkFirstChild (parentLabel: α) (x: Hedge.Node α) (siblings: Hedge α): (Node.mk parentLabel (x :: siblings)).DescendantOf := by
  refine (Subtype.mk x ?_)
  unfold Node.Descendant
  unfold Node.getDescendants
  simp only [List.flatMap_cons, List.cons_append, List.mem_cons, List.mem_append, List.mem_flatMap,
    true_or]

def Node.Descendant.mkFirstChild_eq (parentLabel: α) (x: Hedge.Node α) (siblings: Hedge α):
  {
    descendant: (Node.mk parentLabel (x :: siblings)).DescendantOf
    // descendant.val = x
  } := by
  refine (Subtype.mk (Subtype.mk x ?_) ?_)
  · unfold Node.Descendant
    unfold Node.getDescendants
    simp only [List.flatMap_cons, List.cons_append, List.mem_cons, List.mem_append, List.mem_flatMap,
      true_or]
  · simp only

def Node.Descendant.consFirstChild
  (firstchild: Hedge.Node α) (h: (Node.mk label xs).DescendantOf):
  (Node.mk label (firstchild :: xs)).DescendantOf := by
  unfold Node.DescendantOf at *
  unfold Node.Descendant at *
  unfold Node.getDescendants at *
  obtain ⟨child, h⟩ := h
  refine (Subtype.mk child ?_)
  simp
  simp at h
  apply Or.inr
  cases h
  · apply Or.inl
    assumption
  · apply Or.inr
    apply Or.inr
    assumption

def Node.Descendant.consFirstChild_eq
  (firstchild: Hedge.Node α) (h: (Node.mk label xs).DescendantOf):
  {
    descendant: (Node.mk label (firstchild :: xs)).DescendantOf
    // descendant.val = h.val
  } := by
  obtain ⟨child, h⟩ := h
  unfold Node.Descendant at *
  simp only
  refine (Subtype.mk (Subtype.mk child ?_) ?_)
  · unfold Node.Descendant
    unfold Node.getDescendants at *
    simp
    simp at h
    apply Or.inr
    cases h
    · apply Or.inl
      assumption
    · apply Or.inr
      apply Or.inr
      assumption
  · simp

def Node.getFirstChild (x: Hedge.Node α): Option (Hedge.Node α) :=
  match x with
  | Node.mk _ (y::_ys) => Option.some y
  | _ => Option.none

abbrev Node.FirstChild (child: Hedge.Node α) (parent: Hedge.Node α) :=
  Option.some child = Node.getFirstChild parent

abbrev Node.FirstChildOf {α: Type} (parent: Hedge.Node α) := {
    child: Hedge.Node α
    // Node.FirstChild child parent
  }

def Node.FirstChild.mk
  (parentLabel: α) (firstchild: Hedge.Node α) (siblings: Hedge α):
  (Node.mk parentLabel (firstchild :: siblings)).FirstChildOf := by
  refine (Subtype.mk firstchild ?_)
  unfold Node.FirstChild
  unfold Node.getFirstChild
  simp only

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

theorem labelin_take_is_labelelem {xs: Hedge α} (y: Hedge.LabelIn (List.take n xs)):
  LabelElem y.val xs := by
  obtain ⟨y, hy⟩ := y
  simp only
  rw [List.list_take_drop_n n xs]
  unfold LabelElem at *
  unfold List.flatMap
  rw [List.map_append]
  rw [List.flatten_append]
  rw [List.mem_append]
  exact Or.inl hy

theorem labelin_drop_is_labelelem {xs: Hedge α} (y: Hedge.LabelIn (List.drop n xs)):
  LabelElem y.val xs := by
  obtain ⟨y, hy⟩ := y
  simp only
  rw [List.list_take_drop_n n xs]
  unfold LabelElem at *
  unfold List.flatMap
  rw [List.map_append]
  rw [List.flatten_append]
  rw [List.mem_append]
  exact Or.inr hy

private theorem Hedge.Node.sizeOf_lt_cons_child {α: Type} (label: α) (x1: Hedge.Node α) (x2: Hedge.Node α) (xs: Hedge α):
  sizeOf x1 < sizeOf (Hedge.Node.mk label xs)
  -> sizeOf x1 < sizeOf (Hedge.Node.mk label (x2 :: xs)) := by
  simp
  intro h
  omega

private theorem Hedge.Node.sizeOf_lt_cons_siblings {α: Type} (label: α) (x1: Hedge.Node α) (x2: Hedge.Node α) (xs: Hedge α):
  sizeOf x1 < sizeOf x2
  -> sizeOf x1 < sizeOf (Hedge.Node.mk label (x2 :: xs)) := by
  simp
  intro h
  omega

theorem Node.sizeOf_children
  {α : Type}
  (child : Node α)
  (label : α)
  (children : List (Node α))
  (h : child ∈ children)
  : sizeOf child < sizeOf (Hedge.Node.mk label children) := by
  induction children with
  | nil =>
    simp at h
  | cons x xs ih =>
    simp at h
    cases h with
    | inl h =>
      rw [h]
      simp
      omega
    | inr h =>
      apply Hedge.Node.sizeOf_lt_cons_child
      apply ih
      assumption

theorem Node.sizeOf_grandchildren
  {α : Type}
  (child : Node α)
  (label : α)
  (children : List (Node α))
  (h : child ∈ List.flatMap Hedge.Node.getDescendants children)
  : sizeOf child < sizeOf (Hedge.Node.mk label children) := by
  cases hchildren: children with
  | nil =>
    subst hchildren
    simp at h
  | cons firstchild children =>
    subst hchildren
    simp only [List.flatMap_cons, List.mem_append] at h
    cases h with
    | inl h =>
      unfold getDescendants at h
      cases hfirstchild: firstchild with
      | mk firstchildlabel firstgranchildren =>
      apply Hedge.Node.sizeOf_lt_cons_siblings
      subst hfirstchild
      simp only [List.mem_append] at h
      cases h with
      | inl h =>
        apply Node.sizeOf_children
        assumption
      | inr h =>
        apply Node.sizeOf_grandchildren
        exact h
    | inr h =>
      apply Hedge.Node.sizeOf_lt_cons_child
      apply Node.sizeOf_grandchildren
      assumption
  termination_by children
  decreasing_by
    · subst hfirstchild
      subst hchildren
      simp
      omega
    · subst hchildren
      simp
      omega

theorem Node.DescendantOf.sizeOf
  (x: Hedge.Node α)
  (d : x.DescendantOf): sizeOf d.val < sizeOf x := by
  unfold DescendantOf at d
  unfold Descendant at d
  obtain ⟨d, h⟩ := d
  simp only
  obtain ⟨label, children⟩ := x
  unfold getDescendants at h
  simp only [List.mem_append] at h
  cases h with
  | inl h =>
    apply Node.sizeOf_children
    assumption
  | inr h =>
    apply Node.sizeOf_grandchildren
    assumption
