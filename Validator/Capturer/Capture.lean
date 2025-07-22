import Validator.Std.Except

import Validator.Parser.Token
import Validator.Parser.ParseTree

import Validator.Capturer.CaptureEnter
import Validator.Capturer.CaptureExpr
import Validator.Capturer.CaptureExtract
import Validator.Capturer.CaptureIfExpr
import Validator.Capturer.CaptureLeave
import Validator.Capturer.CaptureM

import Validator.Capturer.Inst.TreeParserLogCaptureM

namespace Capture

def deriveEnter [CaptureM m] (xs: List CaptureExpr): m (List CaptureExpr) := do
  let token <- Parser.token
  let enters := CaptureEnter.deriveEnter xs
  return CaptureIfExpr.evals enters token

def deriveLeave
  [CaptureM m]
  (xs: List CaptureExpr) (label: Token) (dchildxs: List CaptureExpr): m (List CaptureExpr) :=
  CaptureLeave.deriveLeave xs (List.map (fun dchildx =>
    if CaptureExpr.nullable dchildx
    then CaptureExpr.matched label dchildx
    else CaptureExpr.emptyset
  ) dchildxs)

def deriveValue [CaptureM m] (xs: List CaptureExpr) (label: Token): m (List CaptureExpr) := do
  deriveLeave xs label (<- deriveEnter xs)

partial def derive [CaptureM m] (xs: List CaptureExpr): m (List CaptureExpr) := do
  if List.all xs CaptureExpr.unescapable then
    Parser.skip; return xs
  match <- Parser.next with
  | Hint.field =>
    let childxs <- deriveEnter xs
    let token <- Parser.token
    let dchildxs: List CaptureExpr <-
      match <- Parser.next with
      | Hint.value => deriveValue childxs (<- Parser.token)
      | Hint.enter => derive childxs
      | hint => throw s!"unexpected {hint}"
    let xsLeave <- deriveLeave xs token dchildxs
    derive xsLeave
  | Hint.value =>
    let token <- Parser.token
    deriveValue xs token >>= derive
  | Hint.enter =>
    let dchildxs <- derive xs
    derive dchildxs
  | Hint.leave => return xs
  | Hint.eof => return xs

-- captures returns all captured forests for all groups.
def captures [CaptureM m] (includePath: Bool) (x: CaptureExpr): m (List (Nat × List ParseTree)) := do
  let dxs <- derive [x]
  match dxs with
  | [dx] =>
    if dx.nullable
    then return (CaptureExtract.extractGroups includePath dx)
    else throw "no match"
  | _ =>
    throw "wtf"

-- capture only returns the longest capture for a specific group.
def capture (name: Nat) (x: CaptureExpr) (forest: List ParseTree) (includePath: Bool := false): Except String (List ParseTree) := do
  let (_logs, dx) := TreeParserLogCaptureM.run' (captures includePath x) forest
  match dx with
  | Except.error err => Except.error err
  | Except.ok cs =>
    let forests := List.filterMap
      (fun (name', forest) =>
        if name = name'
        then Option.some forest
        else Option.none
      ) cs
    match List.head? (List.reverse (List.mergeSort forests (le := fun x y => (Ord.compare x y).isLE))) with
    | Option.some k => return k
    | Option.none => throw "unknown group"

-- capturePath includes the path of the captured tree.
def capturePath (name: Nat) (x: CaptureExpr) (forest: List ParseTree): Except String (List ParseTree) :=
  capture name x forest (includePath := true)

def CaptureExpr.char (c: Char): CaptureExpr :=
  (CaptureExpr.tree (Pred.eqStr (String.mk [c])) CaptureExpr.epsilon)

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
  Except.ok (treeString "b")

#guard capture 1 (CaptureExpr.concat (CaptureExpr.concat
    (CaptureExpr.star (CaptureExpr.char 'a'))
    (CaptureExpr.group 1 (CaptureExpr.star (CaptureExpr.char 'b'))))
    (CaptureExpr.star (CaptureExpr.char 'a'))
  )
  (treeString "aaabbbaaa") =
  Except.ok (treeString "bbb")

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
  Except.ok (treeString "ccc")

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
  Except.ok (treeString "bcc")

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
  Except.ok [
    ParseTree.mk (Token.string "b") []
  ]

#guard capture 1
    (CaptureExpr.group 1 (CaptureExpr.tree (Pred.eqStr "b")
      (CaptureExpr.tree (Pred.eqStr "c") CaptureExpr.epsilon))
    )
  [
    ParseTree.mk (Token.string "b") [
      ParseTree.mk (Token.string "c") [],
    ],
  ] =
  Except.ok [
    ParseTree.mk (Token.string "b") [
      ParseTree.mk (Token.string "c") []
    ]
  ]

#guard capture 1
    (CaptureExpr.tree (Pred.eqStr "b")
      (CaptureExpr.group 1 (CaptureExpr.tree (Pred.eqStr "c") CaptureExpr.epsilon))
    )
  [
    ParseTree.mk (Token.string "b") [
      ParseTree.mk (Token.string "c") [],
    ],
  ] = Except.ok [
    ParseTree.mk (Token.string "c") []
  ]

#guard capturePath 1
    (CaptureExpr.tree (Pred.eqStr "b")
      (CaptureExpr.group 1 (CaptureExpr.tree (Pred.eqStr "c") CaptureExpr.epsilon))
    )
  [
    ParseTree.mk (Token.string "b") [
      ParseTree.mk (Token.string "c") [],
    ],
  ] = Except.ok [
    ParseTree.mk (Token.string "b") [
      ParseTree.mk (Token.string "c") []
    ]
  ]

#guard capture 1 (CaptureExpr.concat (CaptureExpr.concat
    (CaptureExpr.star (CaptureExpr.char 'a'))
    (CaptureExpr.tree (Pred.eqStr "b")
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
  Except.ok [
    ParseTree.mk (Token.string "c") []
  ]

#guard capturePath 1 (CaptureExpr.concat (CaptureExpr.concat
    (CaptureExpr.star (CaptureExpr.char 'a'))
    (CaptureExpr.tree (Pred.eqStr "b")
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
  ] = Except.ok [
    ParseTree.mk (Token.string "b") [
      ParseTree.mk (Token.string "c") []
    ]
  ]
