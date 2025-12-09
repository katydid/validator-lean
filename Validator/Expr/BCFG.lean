import Std

import Validator.Std.Vec

import Validator.Expr.Regex
import Validator.Expr.Pred

namespace BalancedContextFreeGrammar

abbrev Ref n := Fin n

-- Balanced Context Free Grammars have the restriction that each non-terminal cannot represent any regular expression,
-- but only regular expressions that are surrounded by a start and end terminal.
structure Rule (n: Nat) (α: Type) (Φ: (α: Type) -> Type) where
  enter: Φ α
  child: Regex (Ref n)
  leave: Φ α

abbrev RegexRule (n: Nat) (α: Type) (Φ: (α: Type) -> Type) := Regex ((Φ α) ⊕ (Ref n))

def Rule.toRegex {n: Nat} {α: Type} {Φ: (α: Type) -> Type}
  (r: Rule n α Φ): RegexRule n α Φ :=
  (Regex.concat
    (Regex.symbol (Sum.inl r.enter))
    (Regex.concat
      (Regex.map r.child Sum.inr)
      (Regex.symbol (Sum.inl r.leave))
    )
  )

abbrev Rules (n: Nat) (α: Type) (Φ: (α: Type) -> Type) := { xs: List (Rule n α Φ) // xs.length > 0 }

structure BCFG (n: Nat) (α: Type) (Φ: (α: Type) -> Type) where
  start: { s: List (Ref n) // s.length > 0 }
  prods: Vec (Rules n α Φ) n

def union_rules {n: Nat} {α: Type} {Φ: (α: Type) -> Type}
  (xs: Rules n α Φ): RegexRule n α Φ :=
  match xs with
  | Subtype.mk xs hxs =>
  match xs with
  | [] => by contradiction
  | [x] => x.toRegex
  | (x::xs) => List.foldl Regex.or x.toRegex (List.map Rule.toRegex xs)

def BCFG.getStart
  {n: Nat} {α: Type} {Φ: (α: Type) -> Type}
  (g: BCFG n α Φ): RegexRule n α Φ :=
  match g.start with
  | Subtype.mk s hs =>
  match s with
  | [] => by contradiction
  | (x::xs) =>
    let xs' := (List.map (fun x' => Regex.symbol (Sum.inr x'))) xs
    List.foldl Regex.or (Regex.symbol (Sum.inr x)) xs'

def BCFG.lookup {n: Nat} {α: Type} {Φ: (α: Type) -> Type}
  (g: BCFG n α Φ) (ref: Fin n): RegexRule n α Φ :=
  union_rules (Vec.get g.prods ref)

def nullable {n: Nat} {α: Type} {Φ: (α: Type) -> Type} (r: RegexRule n α Φ): Bool :=
  Regex.nullable r

partial def derive {n: Nat} {α: Type} [DecidableEq α] [BEq α]
  (g: BCFG n α Pred) (r: RegexRule n α Pred) (a: α): RegexRule n α Pred :=
  match r with
  | Regex.emptyset => Regex.emptyset
  | Regex.emptystr => Regex.emptyset
  | Regex.symbol (Sum.inl p) =>
    if Pred.eval p a
    then Regex.emptystr
    else Regex.emptyset
  | Regex.symbol (Sum.inr ref) =>
    derive g (g.lookup ref) a
  | Regex.or r1 r2 =>
    Regex.or (derive g r1 a) (derive g r2 a)
  | Regex.concat r1 r2 =>
    if nullable r1
    then Regex.or
      (Regex.concat (derive g r1 a) r2)
      (derive g r2 a)
    else
      (Regex.concat (derive g r1 a) r2)
  | Regex.star r1 =>
    Regex.concat (derive g r1 a) (Regex.star r1)
