import Std

import Validator.Std.Vec

import Validator.Expr.Regex

namespace BalancedContextFreeGrammar

abbrev Ref n := Fin n

-- Balanced Context Free Grammars have the restriction that each non-terminal cannot represent any regular expression,
-- but only regular expressions that are surrounded by a start and end terminal.
structure Rule (n: Nat) (φ: Type) where
  enter: φ
  child: Regex (Ref n)
  leave: φ

abbrev RegexRule (n: Nat) (φ: Type) := Regex (φ ⊕ (Ref n))

def Rule.toRegex {n: Nat} {φ: Type}
  (r: Rule n φ): RegexRule n φ :=
  (Regex.concat
    (Regex.symbol (Sum.inl r.enter))
    (Regex.concat
      (Regex.map r.child Sum.inr)
      (Regex.symbol (Sum.inl r.leave))
    )
  )

abbrev Rules (n: Nat) (φ: Type) := { xs: List (Rule n φ) // xs.length > 0 }

structure BCFG (n: Nat) (φ: Type) where
  start: { s: List (Ref n) // s.length > 0 }
  prods: Vec (Rules n φ) n

def union_rules {n: Nat} {φ: Type}
  (xs: Rules n φ): RegexRule n φ :=
  match xs with
  | Subtype.mk xs hxs =>
  match xs with
  | [] => by contradiction
  | [x] => x.toRegex
  | (x::xs) => List.foldl Regex.or x.toRegex (List.map Rule.toRegex xs)

def BCFG.getStart
  {n: Nat} {φ: Type}
  (G: BCFG n φ): RegexRule n φ :=
  match G.start with
  | Subtype.mk s hs =>
  match s with
  | [] => by contradiction
  | (x::xs) =>
    let xs' := (List.map (fun x' => Regex.symbol (Sum.inr x'))) xs
    List.foldl Regex.or (Regex.symbol (Sum.inr x)) xs'

def BCFG.lookup {n: Nat} {φ: Type}
  (g: BCFG n φ) (ref: Fin n): RegexRule n φ :=
  union_rules (Vec.get g.prods ref)

def nullable {n: Nat} {φ: Type} (r: RegexRule n φ): Bool :=
  Regex.nullable r

partial def derive {n: Nat}
  (G: BCFG n φ) (Φ: φ -> α -> Bool)
  (r: RegexRule n φ) (a: α): RegexRule n φ :=
  match r with
  | Regex.emptyset => Regex.emptyset
  | Regex.emptystr => Regex.emptyset
  | Regex.symbol (Sum.inl p) =>
    if Φ p a
    then Regex.emptystr
    else Regex.emptyset
  | Regex.symbol (Sum.inr ref) =>
    derive G Φ (G.lookup ref) a
  | Regex.or r1 r2 =>
    Regex.or (derive G Φ r1 a) (derive G Φ r2 a)
  | Regex.concat r1 r2 =>
    if nullable r1
    then Regex.or
      (Regex.concat (derive G Φ r1 a) r2)
      (derive G Φ r2 a)
    else
      (Regex.concat (derive G Φ r1 a) r2)
  | Regex.star r1 =>
    Regex.concat (derive G Φ r1 a) (Regex.star r1)
