import Validator.Expr.Expr

namespace Smart

def or (x y: Expr): Expr :=
  match x with
  | Expr.emptyset => y
  | _ =>
    match y with
    | Expr.emptyset => x
    | _ => Expr.or x y

def concat (x y: Expr): Expr :=
  match x with
  | Expr.emptyset => Expr.emptyset
  | Expr.epsilon => y
  | _ =>
    match y with
    | Expr.emptyset => Expr.emptyset
    | Expr.epsilon => x
    | _ => Expr.concat x y

def star (x: Expr): Expr :=
  match x with
  | Expr.star _ => x
  | Expr.emptyset => Expr.epsilon
  | _ => Expr.star x
