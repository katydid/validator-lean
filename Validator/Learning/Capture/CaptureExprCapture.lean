-- This extends the algorithm in https://github.com/katydid/regex-deriv-lean/blob/main/RegexDeriv/Group/Capture/CaptureRegexCapture.lean
-- It extends the algorithm to implement capturing on ParseTrees.

import Validator.Std.ParseTree
import Validator.Parser.Token
import Validator.Parser.TokenTree

import Validator.Expr.Pred
import Validator.Expr.TokenPred

import Validator.Capturer.CaptureExpr
import Validator.Capturer.CaptureExtract

namespace CaptureExprCapture

partial def derive [DecidableEq α] (x: CaptureExpr α) (tree: ParseTree α): CaptureExpr α :=
  match x with
  | CaptureExpr.emptyset => CaptureExpr.emptyset
  | CaptureExpr.epsilon => CaptureExpr.emptyset
  -- remember matched is just epsilon, so has the same derivative.
  | CaptureExpr.matched _ _ => CaptureExpr.emptyset
  | CaptureExpr.tree pred childExpr =>
    match tree with
    | ParseTree.mk tok children =>
      if Pred.eval pred tok
      then
        let dchild := List.foldl derive childExpr children
        if dchild.nullable
        -- instead of epsilon we return the token matched and the derivative of children with the captured characters.
        then CaptureExpr.matched tok dchild
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
      (CaptureExpr.smartConcat (CaptureExpr.neutralize y) (derive z tree))
    else CaptureExpr.smartConcat (derive y tree) z
  | CaptureExpr.star y => CaptureExpr.smartConcat (derive y tree) x
  | CaptureExpr.group n y =>
    CaptureExpr.smartGroup n (derive y tree)

-- captures returns all captured forests for all groups.
def captures [DecidableEq α] (includePath: Bool) (x: CaptureExpr α) (forest: ParseForest α): Option (List (Nat × ParseForest α)) :=
  let dx := List.foldl derive x forest
  if dx.nullable
  then Option.some (CaptureExtract.extractGroups includePath dx)
  else Option.none

-- capture only returns the longest capture for a specific group.
def capture
  [DecidableEq α] [Ord α]
  (id: Nat) (x: CaptureExpr α) (forest: ParseForest α) (includePath: Bool := false): Option (ParseForest α) :=
  match captures includePath x forest with
  | Option.none => Option.none
  | Option.some cs =>
  let forests := List.filterMap
    (fun (id', forest) =>
      if id = id'
      then Option.some forest
      else Option.none
    ) cs
  List.head? (List.reverse (List.mergeSort forests (le := fun x y => (Ord.compare x y).isLE)))

-- capturePath includes the path of the captured tree.
def capturePath
  [DecidableEq α] [Ord α]
  (id: Nat) (x: CaptureExpr α) (forest: ParseForest α): Option (ParseForest α) :=
  capture id x forest (includePath := true)

def CaptureExpr.char (c: Char): CaptureExpr Token :=
  (CaptureExpr.tree (TokenPred.eqStr (String.mk [c])) CaptureExpr.epsilon)

def treeString (s: String): TokenForest :=
  match s with
  | String.mk cs =>
    List.map (fun c => TokenTree.mk (Token.string (String.mk [c])) []) cs

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
    (CaptureExpr.group 1 (CaptureExpr.tree (TokenPred.eqStr "b")
      (CaptureExpr.tree (TokenPred.eqStr "c") CaptureExpr.epsilon))
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
    (CaptureExpr.tree (TokenPred.eqStr "b")
      (CaptureExpr.group 1 (CaptureExpr.tree (TokenPred.eqStr "c") CaptureExpr.epsilon))
    )
  [
    ParseTree.mk (Token.string "b") [
      ParseTree.mk (Token.string "c") [],
    ],
  ] = Option.some [
    ParseTree.mk (Token.string "c") []
  ]

#guard capturePath 1
    (CaptureExpr.tree (TokenPred.eqStr "b")
      (CaptureExpr.group 1 (CaptureExpr.tree (TokenPred.eqStr "c") CaptureExpr.epsilon))
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
    (CaptureExpr.tree (TokenPred.eqStr "b")
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
    (CaptureExpr.tree (TokenPred.eqStr "b")
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
