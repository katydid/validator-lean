-- Cegex includes capturing groups
inductive Cegex where
  | emptyset
  | epsilon
  -- NEW: matched operator
  | matched (c: Char)
  | char (c: Char)
  | or (y z: Cegex)
  | concat (y z: Cegex)
  | star (y: Cegex)
  -- group is the only new operator compared to a Cegex without capturing groups.
  | group (id: Nat) (x: Cegex)
  deriving DecidableEq, Ord, Repr, Hashable

def Cegex.nullable (x: Cegex): Bool :=
  match x with
  | Cegex.emptyset => false
  | Cegex.epsilon => true
  | Cegex.matched _ => true
  | Cegex.char _ => false
  | Cegex.or y z => nullable y || nullable z
  | Cegex.concat y z => nullable y && nullable z
  | Cegex.star _ => true
  -- The group is nullable if its embedded expression is nullable.
  | Cegex.group _ y => nullable y

def Cegex.unescapable (x: Cegex): Bool :=
  match x with
  | Cegex.emptyset => true
  | _ => false

-- smartOr is a smart constructor for the or operator.
def Cegex.smartOr (x y: Cegex): Cegex :=
  match x with
  | Cegex.emptyset => y
  | _ =>
    match y with
    | Cegex.emptyset => x
    | _ => Cegex.or x y

-- smartConcat is a smart constructor for the concat operator.
def Cegex.smartConcat (x y: Cegex): Cegex :=
  match x with
  | Cegex.emptyset => Cegex.emptyset
  | _ =>
    match y with
    | Cegex.emptyset => Cegex.emptyset
    | _ => Cegex.concat x y

-- smartStar is a smart constructor for the star operator.
def Cegex.smartStar (x: Cegex): Cegex :=
  match x with
  | Cegex.star _ => x
  | _ => Cegex.star x
