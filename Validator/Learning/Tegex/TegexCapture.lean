-- Based on algorithm from Regular Expression Sub-Matching using Partial Derivatives - Martin Sulzmann and Kenny Zhuo Ming Lu
-- Thank you Keegan Perry for simplifying and explaining the original to me.

import Validator.Parser.Token
import Validator.Parser.ParseTree

import Validator.Learning.Tegex.Tegex

namespace TegexCapture

-- neutralize replaces all chars with emptyset.
-- This way the expression will stay nullable and not change based on derivative input.
-- This makes it possible to keep all the capture groups inside for later extraction.
def neutralize (x: Tegex): Tegex :=
  match x with
  | Tegex.emptyset => Tegex.emptyset
  | Tegex.epsilon => Tegex.epsilon
  | Tegex.matched tok childExpr => Tegex.matched tok (neutralize childExpr)
  | Tegex.tree _ _ => Tegex.emptyset
  | Tegex.or y z => Tegex.smartOr (neutralize y) (neutralize z)
  | Tegex.concat y z => Tegex.concat (neutralize y) (neutralize z)
  | Tegex.star y => Tegex.star (neutralize y)
  | Tegex.group id y => Tegex.group id (neutralize y)

partial def derive (x: Tegex) (tree: ParseTree): Tegex :=
  match x with
  | Tegex.emptyset => Tegex.emptyset
  | Tegex.epsilon => Tegex.emptyset
  | Tegex.matched _ _ => Tegex.emptyset
  | Tegex.tree tok' childExpr =>
    match tree with
    | ParseTree.mk tok children =>
      if tok' = tok
      then
        let dchild := List.foldl derive childExpr children
        if dchild.nullable
        then Tegex.matched tok' dchild
        else Tegex.emptyset
      else Tegex.emptyset
  | Tegex.or y z => Tegex.smartOr (derive y tree) (derive z tree)
  | Tegex.concat y z =>
    if Tegex.nullable y
    then Tegex.smartOr
      (Tegex.smartConcat (derive y tree) z)
      -- A difference from the usual derive algorithm:
      -- Instead of (derive z tree), we write:
      (Tegex.smartConcat (neutralize y) (derive z tree))
    else Tegex.concat (derive y tree) z
  | Tegex.star y => Tegex.smartConcat (derive y tree) x
  -- group is the new operator compared to Expr.
  -- We store the input tree in the expression.
  | Tegex.group n y =>
    Tegex.group n (derive y tree)

def extract (x: Tegex): List ParseTree :=
  match x with
  -- should never be encountered, since emptyset is not nullable.
  | Tegex.emptyset => []
  | Tegex.epsilon => []
  -- should never be encountered, since char is not nullable.
  | Tegex.tree _ _ => []
  | Tegex.matched tok childExpr => [ParseTree.mk tok (extract childExpr)]
  | Tegex.or y z =>
    -- Under POSIX semantics, we prefer matching the left alternative.
    if y.nullable
    then extract y
    else extract z
  | Tegex.concat y z =>
    extract y ++ extract z
    -- Groups under a star are ignored.
    -- Recursively extracting under the star causes empty captures to be reported, which we do not want under POSIX semantics.
  | Tegex.star _ => []
    -- ignore group, this group will be extracted later by extractGroups.
  | Tegex.group _ y => extract y

def extractGroups (x: Tegex): List (Nat × List ParseTree) :=
  match x with
  -- should never be encountered, since emptyset is not nullable.
  | Tegex.emptyset => []
  | Tegex.epsilon => []
  -- should never be encountered, since tree is not nullable.
  | Tegex.tree _ _ => []
  | Tegex.matched _ childExpr => extractGroups childExpr
  | Tegex.or y z =>
    -- Under POSIX semantics, we prefer matching the left alternative.
    if y.nullable
    then extractGroups y
    else extractGroups z
  | Tegex.concat y z =>
    extractGroups y ++ extractGroups z
    -- Groups under a star are ignored.
    -- Recursively extracting under the star causes empty captures to be reported, which we do not want under POSIX semantics.
  | Tegex.star _ => []
    -- extract the string
  | Tegex.group id y => (id, extract y) :: extractGroups y

def captures (x: Tegex) (forest: List ParseTree): Option (List (Nat × List ParseTree)) :=
  let dx := List.foldl derive x forest
  if dx.nullable
  then Option.some (extractGroups dx)
  else Option.none

def capture (name: Nat) (x: Tegex) (forest: List ParseTree): Option (List ParseTree) :=
  match captures x forest with
  | Option.none => Option.none
  | Option.some cs =>
  let forests := List.filterMap
    (fun (name', forest) =>
      if name = name'
      then Option.some forest
      else Option.none
    ) cs
  List.head? (List.reverse (List.mergeSort forests (le := fun x y => (Ord.compare x y).isLE)))

def Tegex.char (c: Char): Tegex :=
  (Tegex.tree (Token.string (String.mk [c])) Tegex.epsilon)

def treeString (s: String): List ParseTree :=
  match s with
  | String.mk cs =>
    List.map (fun c => ParseTree.mk (Token.string (String.mk [c])) []) cs

#guard capture 1 (Tegex.concat (Tegex.concat
    (Tegex.star (Tegex.char 'a'))
    (Tegex.group 1 (Tegex.char 'b')))
    (Tegex.star (Tegex.char 'a'))
  )
  (treeString "aaabaaa") =
  Option.some (treeString "b")

#guard capture 1 (Tegex.concat (Tegex.concat
    (Tegex.star (Tegex.char 'a'))
    (Tegex.group 1 (Tegex.star (Tegex.char 'b'))))
    (Tegex.star (Tegex.char 'a'))
  )
  (treeString "aaabbbaaa") =
  Option.some (treeString "bbb")

#guard capture 1 (Tegex.concat (Tegex.concat
    (Tegex.star (Tegex.char 'a'))
    (Tegex.group 1
      (Tegex.or
        (Tegex.star (Tegex.char 'b'))
        (Tegex.star (Tegex.char 'c'))
      )
    ))
    (Tegex.star (Tegex.char 'a'))
  )
  (treeString "aaacccaaa") =
  Option.some (treeString "ccc")

#guard capture 1 (Tegex.concat (Tegex.concat
    (Tegex.star (Tegex.char 'a'))
    (Tegex.group 1
      (Tegex.or
        (Tegex.star (Tegex.char 'b'))
        (Tegex.concat (Tegex.char 'b') (Tegex.star (Tegex.char 'c')))
      )
    ))
    (Tegex.star (Tegex.char 'a'))
  )
  (treeString "aaabccaaa") =
  Option.some (treeString "bcc")

#guard capture 1 (Tegex.concat (Tegex.concat
    (Tegex.star (Tegex.char 'a'))
    (Tegex.group 1 (Tegex.char 'b')))
    (Tegex.star (Tegex.char 'a'))
  )
  [
    ParseTree.mk (Token.string "a") [],
    ParseTree.mk (Token.string "a") [],
    ParseTree.mk (Token.string "a") [],
    ParseTree.mk (Token.string "b") [],
    ParseTree.mk (Token.string "a") [],
    ParseTree.mk (Token.string "a") [],
    ParseTree.mk (Token.string "a") []
  ] =
  Option.some [
    ParseTree.mk (Token.string "b") []
  ]

#guard capture 1
    (Tegex.group 1 (Tegex.tree (Token.string "b")
      (Tegex.tree (Token.string "c") Tegex.epsilon))
    )
  [
    ParseTree.mk (Token.string "b") [
      ParseTree.mk (Token.string "c") [],
    ],
  ] =
  Option.some [
    ParseTree.mk (Token.string "b") [
      ParseTree.mk (Token.string "c") []
    ]
  ]

#guard capture 1
    (Tegex.tree (Token.string "b")
      (Tegex.group 1 (Tegex.tree (Token.string "c") Tegex.epsilon))
    )
  [
    ParseTree.mk (Token.string "b") [
      ParseTree.mk (Token.string "c") [],
    ],
  ] = Option.some [
    ParseTree.mk (Token.string "c") []
  ]

#guard capture 1 (Tegex.concat (Tegex.concat
    (Tegex.star (Tegex.char 'a'))
    (Tegex.tree (Token.string "b")
      (Tegex.concat (Tegex.concat
        (Tegex.star (Tegex.char 'a'))
        (Tegex.group 1 (Tegex.char 'c')))
        (Tegex.star (Tegex.char 'a'))
      )
    ))
    (Tegex.star (Tegex.char 'a'))
  )
  [
    ParseTree.mk (Token.string "a") [],
    ParseTree.mk (Token.string "a") [],
    ParseTree.mk (Token.string "a") [],
    ParseTree.mk (Token.string "b") [
      ParseTree.mk (Token.string "a") [],
      ParseTree.mk (Token.string "a") [],
      ParseTree.mk (Token.string "a") [],
      ParseTree.mk (Token.string "c") [],
      ParseTree.mk (Token.string "a") [],
      ParseTree.mk (Token.string "a") [],
      ParseTree.mk (Token.string "a") [],
    ],
    ParseTree.mk (Token.string "a") [],
    ParseTree.mk (Token.string "a") [],
    ParseTree.mk (Token.string "a") []
  ] =
  Option.some [
    ParseTree.mk (Token.string "c") []
  ]
