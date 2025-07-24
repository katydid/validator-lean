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

mutual
def ParseTree.hasDecEq [DecidableEq α]: (a b : ParseTree α) → Decidable (Eq a b)
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
def ParseTree.hasDecEqs [DecidableEq α]: (as bs : ParseForest α) → Decidable (Eq as bs)
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

instance[DecidableEq α] : DecidableEq (ParseTree α) := ParseTree.hasDecEq
