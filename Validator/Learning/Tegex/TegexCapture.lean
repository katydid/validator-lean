-- Based on algorithm from Regular Expression Sub-Matching using Partial Derivatives - Martin Sulzmann and Kenny Zhuo Ming Lu
-- Thank you Keegan Perry for simplifying and explaining the original to me.

import Validator.Learning.Tegex.Tegex

namespace TegexCapture

-- neutralize replaces all chars with emptyset.
-- This way the expression will stay nullable and not change based on derivative input.
-- This makes it possible to keep all the capture groups inside for later extraction.
def neutralize (x: Tegex): Tegex :=
  match x with
  | Tegex.emptyset => Tegex.emptyset
  | Tegex.epsilon => Tegex.epsilon
  | Tegex.matched c => Tegex.matched c
  | Tegex.char _ => Tegex.emptyset
  | Tegex.or y z => Tegex.smartOr (neutralize y) (neutralize z)
  | Tegex.concat y z => Tegex.concat (neutralize y) (neutralize z)
  | Tegex.star y => Tegex.star (neutralize y)
  | Tegex.group id y => Tegex.group id (neutralize y)

partial def derive (x: Tegex) (char: Char): Tegex :=
  match x with
  | Tegex.emptyset => Tegex.emptyset
  | Tegex.epsilon => Tegex.emptyset
  | Tegex.matched _ => Tegex.emptyset
  | Tegex.char char' =>
    if char' = char
    then Tegex.matched char
    else Tegex.emptyset
  | Tegex.or y z => Tegex.smartOr (derive y char) (derive z char)
  | Tegex.concat y z =>
    if Tegex.nullable y
    then Tegex.smartOr
      (Tegex.smartConcat (derive y char) z)
      -- A difference from the usual derive algorithm:
      -- Instead of (derive z tree), we write:
      (Tegex.smartConcat (neutralize y) (derive z char))
    else Tegex.concat (derive y char) z
  | Tegex.star y => Tegex.smartConcat (derive y char) x
  -- group is the new operator compared to Expr.
  -- We store the input tree in the expression.
  | Tegex.group n y =>
    Tegex.group n (derive y char)

def extract (x: Tegex): List Char :=
  match x with
  -- should never be encountered, since emptyset is not nullable.
  | Tegex.emptyset => []
  | Tegex.epsilon => []
  -- should never be encountered, since char is not nullable.
  | Tegex.char _ => []
  | Tegex.matched c => [c]
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

def extractGroups (x: Tegex): List (Nat × List Char) :=
  match x with
  -- should never be encountered, since emptyset is not nullable.
  | Tegex.emptyset => []
  | Tegex.epsilon => []
  -- should never be encountered, since char is not nullable.
  | Tegex.char _ => []
  | Tegex.matched _ => []
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

def captures (x: Tegex) (chars: List Char): Option (List (Nat × List Char)) :=
  let dx := List.foldl derive x chars
  if dx.nullable
  then Option.some (extractGroups dx)
  else Option.none

def capture (name: Nat) (x: Tegex) (input: String): Option String :=
  match input with
  | String.mk chars =>
  match captures x chars with
  | Option.none => Option.none
  | Option.some cs =>
  let strs := List.filterMap
    (fun (name', str) =>
      if name = name'
      then Option.some (String.mk str)
      else Option.none
    ) cs
  List.head? (List.reverse (List.mergeSort strs))

#guard capture 1 (Tegex.concat (Tegex.concat
    (Tegex.star (Tegex.char 'a'))
    (Tegex.group 1 (Tegex.char 'b')))
    (Tegex.star (Tegex.char 'a'))
  )
  "aaabaaa" =
  Option.some "b"

#guard capture 1 (Tegex.concat (Tegex.concat
    (Tegex.star (Tegex.char 'a'))
    (Tegex.group 1 (Tegex.star (Tegex.char 'b'))))
    (Tegex.star (Tegex.char 'a'))
  )
  "aaabbbaaa" =
  Option.some "bbb"

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
  "aaacccaaa" =
  Option.some "ccc"

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
  "aaabccaaa" =
  Option.some "bcc"
