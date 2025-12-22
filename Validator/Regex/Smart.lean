import Validator.Std.Vec

import Validator.Regex.Regex
import Validator.Regex.Point

namespace Regex.Smart

def or (x y: Regex σ): Regex σ :=
  match x with
  | Regex.emptyset => y
  | _ =>
    match y with
    | Regex.emptyset => x
    | _ => Regex.or x y

def concat (x y: Regex σ): Regex σ :=
  match x with
  | Regex.emptyset => Regex.emptyset
  | Regex.emptystr => y
  | _ =>
    match y with
    | Regex.emptyset => Regex.emptyset
    | Regex.emptystr => x
    | _ => Regex.concat x y

def star (x: Regex σ): Regex σ :=
  match x with
  | Regex.star _ => x
  | Regex.emptyset => Regex.emptystr
  | _ => Regex.star x

def derive {σ: Type} {α: Type} (Φ: σ -> α -> Bool) (r: Regex σ) (a: α): Regex σ :=
  match r with
  | Regex.emptyset => Regex.emptyset
  | Regex.emptystr => Regex.emptyset
  | Regex.symbol s => Regex.onlyif (Φ s a) Regex.emptystr
  | Regex.or r1 r2 => or (derive Φ r1 a) (derive Φ r2 a)
  | Regex.concat r1 r2 =>
    or
      (concat (derive Φ r1 a) r2)
      (Regex.onlyif (Regex.null r1) (derive Φ r2 a))
  | Regex.star r1 => concat (derive Φ r1 a) (star r1)

def derive_point {σ: Type} (r: Regex (σ × Bool)): Regex σ :=
  match r with
  | Regex.emptyset => Regex.emptyset
  | Regex.emptystr => Regex.emptyset
  | Regex.symbol (_, b) => Regex.onlyif b Regex.emptystr
  | Regex.or r1 r2 => or (derive_point r1) (derive_point r2)
  | Regex.concat r1 r2 =>
    or
      (concat (derive_point r1) (Regex.Point.first r2))
      (Regex.onlyif (Regex.null r1) (derive_point r2))
  | Regex.star r1 =>
      concat (derive_point r1) (star (Regex.Point.first r1))

def derive_points (rs: Vec (Regex (σ × Bool)) l): Vec (Regex σ) l :=
  Vec.map rs (fun r => derive_point r)
