-- Regex includes capturing groups
inductive Regex where
  | emptyset
  | epsilon
  | char (c: Char)
  | or (y z: Regex)
  | concat (y z: Regex)
  | star (y: Regex)
  -- group is the only new operator compared to a Regex without capturing groups.
  | group (id: Nat) (capture: List Char) (x: Regex)
  deriving DecidableEq, Ord, Repr, Hashable

def Regex.nullable (x: Regex): Bool :=
  match x with
  | Regex.emptyset => false
  | Regex.epsilon => true
  | Regex.char _ => false
  | Regex.or y z => nullable y || nullable z
  | Regex.concat y z => nullable y && nullable z
  | Regex.star _ => true
  -- The group is nullable if its embedded expression is nullable.
  | Regex.group _ _ y => nullable y

def Regex.unescapable (x: Regex): Bool :=
  match x with
  | Regex.emptyset => true
  | _ => false

-- smartOr is a smart constructor for the or operator.
def Regex.smartOr (x y: Regex): Regex :=
  match x with
  | Regex.emptyset => y
  | _ =>
    match y with
    | Regex.emptyset => x
    | _ => Regex.or x y

-- smartConcat is a smart constructor for the concat operator.
def Regex.smartConcat (x y: Regex): Regex :=
  match x with
  | Regex.emptyset => Regex.emptyset
  | _ =>
    match y with
    | Regex.emptyset => Regex.emptyset
    | _ => Regex.concat x y

-- smartStar is a smart constructor for the star operator.
def Regex.smartStar (x: Regex): Regex :=
  match x with
  | Regex.star _ => x
  | _ => Regex.star x
