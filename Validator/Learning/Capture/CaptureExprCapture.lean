-- This extends the algorithm in https://github.com/katydid/regex-deriv-lean/blob/main/RegexDeriv/Group/Capture/CaptureRegexCapture.lean
-- It extends the algorithm to implement capturing on ParseTrees.

import Validator.Parser.Token
import Validator.Parser.ParseTree

import Validator.Learning.Capture.CaptureExpr

namespace CaptureExprCapture

-- neutralize replaces all tree operators with emptyset.
-- It is used when deriving concat.
-- This way we do not lose capture information on nullable expressions.
def neutralize (x: CaptureExpr): CaptureExpr :=
  match x with
  | CaptureExpr.emptyset => CaptureExpr.emptyset
  | CaptureExpr.epsilon => CaptureExpr.epsilon
  -- matched is handled exactly the same as epsilon, by simply preserving itself and the matched tok and childExpr.
  | CaptureExpr.matched tok childExpr => CaptureExpr.matched tok (neutralize childExpr)
  | CaptureExpr.tree _ _ => CaptureExpr.emptyset
  | CaptureExpr.or y z => CaptureExpr.smartOr (neutralize y) (neutralize z)
  | CaptureExpr.concat y z => CaptureExpr.concat (neutralize y) (neutralize z)
  | CaptureExpr.star y => CaptureExpr.star (neutralize y)
  | CaptureExpr.group id y => CaptureExpr.group id (neutralize y)

partial def derive (x: CaptureExpr) (tree: ParseTree): CaptureExpr :=
  match x with
  | CaptureExpr.emptyset => CaptureExpr.emptyset
  | CaptureExpr.epsilon => CaptureExpr.emptyset
  -- remember matched is just epsilon, so has the same derivative.
  | CaptureExpr.matched _ _ => CaptureExpr.emptyset
  | CaptureExpr.tree tok' childExpr =>
    match tree with
    | ParseTree.mk tok children =>
      if tok' = tok
      then
        let dchild := List.foldl derive childExpr children
        if dchild.nullable
        -- instead of epsilon we return the token matched and the derivative of children with the captured characters.
        then CaptureExpr.matched tok' dchild
        else CaptureExpr.emptyset
      else CaptureExpr.emptyset
  | CaptureExpr.or y z => CaptureExpr.smartOr (derive y tree) (derive z tree)
  | CaptureExpr.concat y z =>
    if CaptureExpr.nullable y
    then CaptureExpr.smartOr
      (CaptureExpr.smartConcat (derive y tree) z)
      -- A difference from the usual derive algorithm:
      -- To preserve the capture information in the nullable expression y,
      -- instead of (derive z tree), we write:
      (CaptureExpr.smartConcat (neutralize y) (derive z tree))
    else CaptureExpr.concat (derive y tree) z
  | CaptureExpr.star y => CaptureExpr.smartConcat (derive y tree) x
  | CaptureExpr.group n y =>
    CaptureExpr.group n (derive y tree)

-- extract extracts a single forest for the whole expression.
-- This based on extractGroups, but only returns one captured forest.
def extract (x: CaptureExpr): List ParseTree :=
  match x with
  | CaptureExpr.emptyset => []
  | CaptureExpr.epsilon => []
  | CaptureExpr.tree _ _ => []
  -- matched returns the matched token and extracts the matched children from the child expression.
  | CaptureExpr.matched tok childExpr => [ParseTree.mk tok (extract childExpr)]
  | CaptureExpr.or y z =>
    -- Under POSIX semantics, we prefer matching the left alternative.
    if y.nullable
    then extract y
    else extract z
  | CaptureExpr.concat y z =>
    extract y ++ extract z
    -- Groups under a star are ignored.
    -- Recursively extracting under the star causes empty captures to be reported, which we do not want under POSIX semantics.
  | CaptureExpr.star _ => []
    -- Ignore group, this group will be extracted later by extractGroups.
  | CaptureExpr.group _ y => extract y

-- extractGroups returns the captured forest for each group.
def extractGroups (includePath: Bool) (x: CaptureExpr): List (Nat × List ParseTree) :=
  match x with
  | CaptureExpr.emptyset => []
  | CaptureExpr.epsilon => []
  | CaptureExpr.tree _ _ => []
  -- There may be groups in the childExpr that needs to be extracted.
  | CaptureExpr.matched tok childExpr =>
    if includePath
    then List.map (fun (id, children) => (id, [ParseTree.mk tok children])) (extractGroups includePath childExpr)
    else extractGroups includePath childExpr
  | CaptureExpr.or y z =>
    if y.nullable
    then extractGroups includePath y
    else extractGroups includePath z
  | CaptureExpr.concat y z =>
    extractGroups includePath y ++ extractGroups includePath z
  | CaptureExpr.star _ => []
    -- extract the forest for the single group id
  | CaptureExpr.group id y => (id, extract y) :: extractGroups includePath y

-- captures returns all captured forests for all groups.
def captures (includePath: Bool) (x: CaptureExpr) (forest: List ParseTree): Option (List (Nat × List ParseTree)) :=
  let dx := List.foldl derive x forest
  if dx.nullable
  then Option.some (extractGroups includePath dx)
  else Option.none

-- capture only returns the longest capture for a specific group.
def capture (name: Nat) (x: CaptureExpr) (forest: List ParseTree) (includePath: Bool := false): Option (List ParseTree) :=
  match captures includePath x forest with
  | Option.none => Option.none
  | Option.some cs =>
  let forests := List.filterMap
    (fun (name', forest) =>
      if name = name'
      then Option.some forest
      else Option.none
    ) cs
  List.head? (List.reverse (List.mergeSort forests (le := fun x y => (Ord.compare x y).isLE)))

-- capturePath includes the path of the captured tree.
def capturePath (name: Nat) (x: CaptureExpr) (forest: List ParseTree): Option (List ParseTree) :=
  capture name x forest (includePath := true)

def CaptureExpr.char (c: Char): CaptureExpr :=
  (CaptureExpr.tree (Token.string (String.mk [c])) CaptureExpr.epsilon)

def treeString (s: String): List ParseTree :=
  match s with
  | String.mk cs =>
    List.map (fun c => ParseTree.mk (Token.string (String.mk [c])) []) cs

#guard capture 1 (CaptureExpr.concat (CaptureExpr.concat
    (CaptureExpr.star (CaptureExpr.char 'a'))
    (CaptureExpr.group 1 (CaptureExpr.char 'b')))
    (CaptureExpr.star (CaptureExpr.char 'a'))
  )
  (treeString "aaabaaa") =
  Option.some (treeString "b")

#guard capture 1 (CaptureExpr.concat (CaptureExpr.concat
    (CaptureExpr.star (CaptureExpr.char 'a'))
    (CaptureExpr.group 1 (CaptureExpr.star (CaptureExpr.char 'b'))))
    (CaptureExpr.star (CaptureExpr.char 'a'))
  )
  (treeString "aaabbbaaa") =
  Option.some (treeString "bbb")

#guard capture 1 (CaptureExpr.concat (CaptureExpr.concat
    (CaptureExpr.star (CaptureExpr.char 'a'))
    (CaptureExpr.group 1
      (CaptureExpr.or
        (CaptureExpr.star (CaptureExpr.char 'b'))
        (CaptureExpr.star (CaptureExpr.char 'c'))
      )
    ))
    (CaptureExpr.star (CaptureExpr.char 'a'))
  )
  (treeString "aaacccaaa") =
  Option.some (treeString "ccc")

#guard capture 1 (CaptureExpr.concat (CaptureExpr.concat
    (CaptureExpr.star (CaptureExpr.char 'a'))
    (CaptureExpr.group 1
      (CaptureExpr.or
        (CaptureExpr.star (CaptureExpr.char 'b'))
        (CaptureExpr.concat (CaptureExpr.char 'b') (CaptureExpr.star (CaptureExpr.char 'c')))
      )
    ))
    (CaptureExpr.star (CaptureExpr.char 'a'))
  )
  (treeString "aaabccaaa") =
  Option.some (treeString "bcc")

#guard capture 1 (CaptureExpr.concat (CaptureExpr.concat
    (CaptureExpr.star (CaptureExpr.char 'a'))
    (CaptureExpr.group 1 (CaptureExpr.char 'b')))
    (CaptureExpr.star (CaptureExpr.char 'a'))
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
    (CaptureExpr.group 1 (CaptureExpr.tree (Token.string "b")
      (CaptureExpr.tree (Token.string "c") CaptureExpr.epsilon))
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
    (CaptureExpr.tree (Token.string "b")
      (CaptureExpr.group 1 (CaptureExpr.tree (Token.string "c") CaptureExpr.epsilon))
    )
  [
    ParseTree.mk (Token.string "b") [
      ParseTree.mk (Token.string "c") [],
    ],
  ] = Option.some [
    ParseTree.mk (Token.string "c") []
  ]

#guard capturePath 1
    (CaptureExpr.tree (Token.string "b")
      (CaptureExpr.group 1 (CaptureExpr.tree (Token.string "c") CaptureExpr.epsilon))
    )
  [
    ParseTree.mk (Token.string "b") [
      ParseTree.mk (Token.string "c") [],
    ],
  ] = Option.some [
    ParseTree.mk (Token.string "b") [
      ParseTree.mk (Token.string "c") []
    ]
  ]

#guard capture 1 (CaptureExpr.concat (CaptureExpr.concat
    (CaptureExpr.star (CaptureExpr.char 'a'))
    (CaptureExpr.tree (Token.string "b")
      (CaptureExpr.concat (CaptureExpr.concat
        (CaptureExpr.star (CaptureExpr.char 'a'))
        (CaptureExpr.group 1 (CaptureExpr.char 'c')))
        (CaptureExpr.star (CaptureExpr.char 'a'))
      )
    ))
    (CaptureExpr.star (CaptureExpr.char 'a'))
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

#guard capturePath 1 (CaptureExpr.concat (CaptureExpr.concat
    (CaptureExpr.star (CaptureExpr.char 'a'))
    (CaptureExpr.tree (Token.string "b")
      (CaptureExpr.concat (CaptureExpr.concat
        (CaptureExpr.star (CaptureExpr.char 'a'))
        (CaptureExpr.group 1 (CaptureExpr.char 'c')))
        (CaptureExpr.star (CaptureExpr.char 'a'))
      )
    ))
    (CaptureExpr.star (CaptureExpr.char 'a'))
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
  ] = Option.some [
    ParseTree.mk (Token.string "b") [
      ParseTree.mk (Token.string "c") []
    ]
  ]
