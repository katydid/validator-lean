import Validator.Parser.Token

-- ParseTree is a Labelled Tree.
inductive ParseTree where
  | mk (label: Token) (children: List ParseTree)
  deriving BEq, Ord, Repr, Hashable

namespace ParseTree

def node (s: String) (children: List ParseTree): ParseTree :=
  ParseTree.mk (Token.string s) children

def str (s: String): ParseTree :=
  ParseTree.mk (Token.string s) []

def getLabel (t: ParseTree): Token :=
  match t with
  | ParseTree.mk l _ => l

def getChildren (t: ParseTree): List ParseTree :=
  match t with
  | ParseTree.mk _ c => c

mutual
def ParseTree.hasDecEq : (a b : ParseTree) → Decidable (Eq a b)
  | ParseTree.mk la as, ParseTree.mk lb bs =>
    match decEq la lb with
    | isFalse nlab => isFalse (by
        simp only [ParseTree.mk.injEq, List.cons.injEq, not_and]
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
def ParseTree.hasDecEqs : (as bs : List ParseTree) → Decidable (Eq as bs)
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
        simp only [ParseTree.mk.injEq, List.cons.injEq, not_and]
        intro _ hab
        contradiction
      )
    | isTrue hab =>
      match ParseTree.hasDecEqs as bs with
      | isFalse nabs => isFalse (fun h => List.noConfusion h (fun _ habs => absurd habs nabs))
      | isTrue habs => isTrue (hab ▸ habs ▸ rfl)
end

instance : DecidableEq ParseTree := ParseTree.hasDecEq
