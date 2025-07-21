-- Based on algorithm from Regular Expression Sub-Matching using Partial Derivatives - Martin Sulzmann and Kenny Zhuo Ming Lu
-- Thank you Keegan Perry for simplifying and explaining the original to me.

import Validator.Learning.Cegex.Cegex

namespace CegexCapture

-- neutralize replaces all chars with emptyset.
-- This way the expression will stay nullable and not change based on derivative input.
-- This makes it possible to keep all the capture groups inside for later extraction.
def neutralize (x: Cegex): Cegex :=
  match x with
  | Cegex.emptyset => Cegex.emptyset
  | Cegex.epsilon => Cegex.epsilon
  | Cegex.matched c => Cegex.matched c
  | Cegex.char _ => Cegex.emptyset
  | Cegex.or y z => Cegex.smartOr (neutralize y) (neutralize z)
  | Cegex.concat y z => Cegex.concat (neutralize y) (neutralize z)
  | Cegex.star y => Cegex.star (neutralize y)
  | Cegex.group id y => Cegex.group id (neutralize y)

partial def derive (x: Cegex) (char: Char): Cegex :=
  match x with
  | Cegex.emptyset => Cegex.emptyset
  | Cegex.epsilon => Cegex.emptyset
  | Cegex.matched _ => Cegex.emptyset
  | Cegex.char char' =>
    if char' = char
    then Cegex.matched char
    else Cegex.emptyset
  | Cegex.or y z => Cegex.smartOr (derive y char) (derive z char)
  | Cegex.concat y z =>
    if Cegex.nullable y
    then Cegex.smartOr
      (Cegex.smartConcat (derive y char) z)
      -- A difference from the usual derive algorithm:
      -- Instead of (derive z tree), we write:
      (Cegex.smartConcat (neutralize y) (derive z char))
    else Cegex.concat (derive y char) z
  | Cegex.star y => Cegex.smartConcat (derive y char) x
  -- group is the new operator compared to Expr.
  -- We store the input tree in the expression.
  | Cegex.group n y =>
    Cegex.group n (derive y char)

def extract (x: Cegex): List Char :=
  match x with
  -- should never be encountered, since emptyset is not nullable.
  | Cegex.emptyset => []
  | Cegex.epsilon => []
  -- should never be encountered, since char is not nullable.
  | Cegex.char _ => []
  | Cegex.matched c => [c]
  | Cegex.or y z =>
    -- Under POSIX semantics, we prefer matching the left alternative.
    if y.nullable
    then extract y
    else extract z
  | Cegex.concat y z =>
    extract y ++ extract z
    -- Groups under a star are ignored.
    -- Recursively extracting under the star causes empty captures to be reported, which we do not want under POSIX semantics.
  | Cegex.star _ => []
    -- ignore group, this group will be extracted later by extractGroups.
  | Cegex.group _ y => extract y

def extractGroups (x: Cegex): List (Nat × List Char) :=
  match x with
  -- should never be encountered, since emptyset is not nullable.
  | Cegex.emptyset => []
  | Cegex.epsilon => []
  -- should never be encountered, since char is not nullable.
  | Cegex.char _ => []
  | Cegex.matched _ => []
  | Cegex.or y z =>
    -- Under POSIX semantics, we prefer matching the left alternative.
    if y.nullable
    then extractGroups y
    else extractGroups z
  | Cegex.concat y z =>
    extractGroups y ++ extractGroups z
    -- Groups under a star are ignored.
    -- Recursively extracting under the star causes empty captures to be reported, which we do not want under POSIX semantics.
  | Cegex.star _ => []
    -- extract the string
  | Cegex.group id y => (id, extract y) :: extractGroups y

def captures (x: Cegex) (chars: List Char): Option (List (Nat × List Char)) :=
  let dx := List.foldl derive x chars
  if dx.nullable
  then Option.some (extractGroups dx)
  else Option.none

def capture (name: Nat) (x: Cegex) (input: String): Option String :=
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

#guard capture 1 (Cegex.concat (Cegex.concat
    (Cegex.star (Cegex.char 'a'))
    (Cegex.group 1 (Cegex.char 'b')))
    (Cegex.star (Cegex.char 'a'))
  )
  "aaabaaa" =
  Option.some "b"

#guard capture 1 (Cegex.concat (Cegex.concat
    (Cegex.star (Cegex.char 'a'))
    (Cegex.group 1 (Cegex.star (Cegex.char 'b'))))
    (Cegex.star (Cegex.char 'a'))
  )
  "aaabbbaaa" =
  Option.some "bbb"

#guard capture 1 (Cegex.concat (Cegex.concat
    (Cegex.star (Cegex.char 'a'))
    (Cegex.group 1
      (Cegex.or
        (Cegex.star (Cegex.char 'b'))
        (Cegex.star (Cegex.char 'c'))
      )
    ))
    (Cegex.star (Cegex.char 'a'))
  )
  "aaacccaaa" =
  Option.some "ccc"

#guard capture 1 (Cegex.concat (Cegex.concat
    (Cegex.star (Cegex.char 'a'))
    (Cegex.group 1
      (Cegex.or
        (Cegex.star (Cegex.char 'b'))
        (Cegex.concat (Cegex.char 'b') (Cegex.star (Cegex.char 'c')))
      )
    ))
    (Cegex.star (Cegex.char 'a'))
  )
  "aaabccaaa" =
  Option.some "bcc"
