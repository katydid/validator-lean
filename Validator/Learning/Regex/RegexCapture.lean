-- This algorithm is from Regular Expression Sub-Matching using Partial Derivatives - Martin Sulzmann and Kenny Zhuo Ming Lu

-- Thank you Keegan Perry for simplifying and explaining this to me.
import Validator.Learning.Regex.Regex

namespace RegexCapture

-- neutralize replaces all chars with emptyset.
-- This way the expression will stay nullable and not change based on derivative input.
-- This makes it possible to keep all the capture groups inside for later extraction.
def neutralize (x: Regex): Regex :=
  match x with
  | Regex.emptyset => Regex.emptyset
  | Regex.epsilon => Regex.epsilon
  | Regex.char _ => Regex.emptyset
  | Regex.or y z => Regex.smartOr (neutralize y) (neutralize z)
  | Regex.concat y z => Regex.concat (neutralize y) (neutralize z)
  | Regex.star y => Regex.star (neutralize y)
  | Regex.group id c y => Regex.group id c (neutralize y)

partial def derive (x: Regex) (char: Char): Regex :=
  match x with
  | Regex.emptyset => Regex.emptyset
  | Regex.epsilon => Regex.emptyset
  | Regex.char char' =>
    if char' = char
    then Regex.epsilon
    else Regex.emptyset
  | Regex.or y z => Regex.smartOr (derive y char) (derive z char)
  | Regex.concat y z =>
    if Regex.nullable y
    then Regex.smartOr
      (Regex.smartConcat (derive y char) z)
      -- A difference from the usual derive algorithm:
      -- Instead of (derive z tree), we write:
      (Regex.smartConcat (neutralize y) (derive z char))
    else Regex.concat (derive y char) z
  | Regex.star y => Regex.smartConcat (derive y char) x
  -- group is the new operator compared to Expr.
  -- We store the input tree in the expression.
  | Regex.group n chars y =>
    Regex.group n (char :: chars) (derive y char)

def extract (x: Regex): List (Nat × List Char) :=
  match x with
  -- should never be encountered, since emptyset is not nullable.
  | Regex.emptyset => []
  | Regex.epsilon => []
  -- should never be encountered, since char is not nullable.
  | Regex.char _ => []
  | Regex.or y z =>
    -- Under POSIX semantics, we prefer matching the left alternative.
    if y.nullable
    then extract y
    else extract z
  | Regex.concat y z =>
    extract y ++ extract z
    -- Groups under a star are ignored.
    -- Recursively extracting under the star causes empty captures to be reported, which we do not want under POSIX semantics.
  | Regex.star _ => []
  | Regex.group id c y => (id, c) :: extract y

def captures (x: Regex) (chars: List Char): Option (List (Nat × List Char)) :=
  let dx := List.foldl derive x chars
  if dx.nullable
  then Option.some (extract dx)
  else Option.none

def capture (name: Nat) (x: Regex) (input: String): Option String :=
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

#guard capture 1 (Regex.concat (Regex.concat
    (Regex.star (Regex.char 'a'))
    (Regex.group 1 [] (Regex.char 'b')))
    (Regex.star (Regex.char 'a'))
  )
  "aaabaaa" =
  Option.some "b"

#guard capture 1 (Regex.concat (Regex.concat
    (Regex.star (Regex.char 'a'))
    (Regex.group 1 [] (Regex.star (Regex.char 'b'))))
    (Regex.star (Regex.char 'a'))
  )
  "aaabbbaaa" =
  Option.some "bbb"

#guard capture 1 (Regex.concat (Regex.concat
    (Regex.star (Regex.char 'a'))
    (Regex.group 1 []
      (Regex.or
        (Regex.star (Regex.char 'b'))
        (Regex.star (Regex.char 'c'))
      )
    ))
    (Regex.star (Regex.char 'a'))
  )
  "aaacccaaa" =
  Option.some "ccc"
