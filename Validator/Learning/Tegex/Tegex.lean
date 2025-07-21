-- Tegex includes capturing groups
inductive Tegex where
  | emptyset
  | epsilon
  | matched (c: Char)
  | char (c: Char)
  | or (y z: Tegex)
  | concat (y z: Tegex)
  | star (y: Tegex)
  -- group is the only new operator compared to a Tegex without capturing groups.
  | group (id: Nat) (x: Tegex)
  deriving DecidableEq, Ord, Repr, Hashable

def Tegex.nullable (x: Tegex): Bool :=
  match x with
  | Tegex.emptyset => false
  | Tegex.epsilon => true
  | Tegex.matched _ => true
  | Tegex.char _ => false
  | Tegex.or y z => nullable y || nullable z
  | Tegex.concat y z => nullable y && nullable z
  | Tegex.star _ => true
  -- The group is nullable if its embedded expression is nullable.
  | Tegex.group _ y => nullable y

def Tegex.unescapable (x: Tegex): Bool :=
  match x with
  | Tegex.emptyset => true
  | _ => false

-- smartOr is a smart constructor for the or operator.
def Tegex.smartOr (x y: Tegex): Tegex :=
  match x with
  | Tegex.emptyset => y
  | _ =>
    match y with
    | Tegex.emptyset => x
    | _ => Tegex.or x y

-- smartConcat is a smart constructor for the concat operator.
def Tegex.smartConcat (x y: Tegex): Tegex :=
  match x with
  | Tegex.emptyset => Tegex.emptyset
  | _ =>
    match y with
    | Tegex.emptyset => Tegex.emptyset
    | _ => Tegex.concat x y

-- smartStar is a smart constructor for the star operator.
def Tegex.smartStar (x: Tegex): Tegex :=
  match x with
  | Tegex.star _ => x
  | _ => Tegex.star x
