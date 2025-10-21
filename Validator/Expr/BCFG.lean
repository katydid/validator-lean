import Std

import Validator.Expr.Regex
import Validator.Expr.Pred

namespace BalancedContextFreeGrammar

abbrev Ref μ := Fin μ

-- Balanced Context Free Grammars have the restriction that each non-terminal cannot represent any regular expression,
-- but only regular expressions that are surrounded by a start and end terminal.
structure Rule (μ: Nat) (α: Type) (Φ: (α: Type) -> Type) where
  enter: Φ α
  child: Regex (Ref μ)
  leave: Φ α

abbrev RegexRule (μ: Nat) (α: Type) (Φ: (α: Type) -> Type) := Regex ((Φ α) ⊕ (Ref μ))

def Rule.toRegex {μ: Nat} {α: Type} {Φ: (α: Type) -> Type}
  (r: Rule μ α Φ): RegexRule μ α Φ :=
  (Regex.concat
    (Regex.symbol (Sum.inl r.enter))
    (Regex.concat
      (Regex.map r.child Sum.inr)
      (Regex.symbol (Sum.inl r.leave))
    )
  )

abbrev Rules (μ: Nat) (α: Type) (Φ: (α: Type) -> Type) := { xs: List (Rule μ α Φ) // xs.length > 0 }

structure BCFG (μ: Nat) (α: Type) (Φ: (α: Type) -> Type) where
  start: { s: List (Ref μ) // s.length > 0 }
  prods: Vector (Rules μ α Φ) μ

def union_rules {μ: Nat} {α: Type} {Φ: (α: Type) -> Type}
  (xs: Rules μ α Φ): RegexRule μ α Φ :=
  match xs with
  | Subtype.mk xs hxs =>
  match xs with
  | [] => by contradiction
  | [x] => x.toRegex
  | (x::xs) => List.foldl Regex.or x.toRegex (List.map Rule.toRegex xs)

def BCFG.getStart
  {μ: Nat} {α: Type} {Φ: (α: Type) -> Type}
  (g: BCFG μ α Φ): RegexRule μ α Φ :=
  match g.start with
  | Subtype.mk s hs =>
  match s with
  | [] => by contradiction
  | (x::xs) =>
    let xs' := (List.map (fun x' => Regex.symbol (Sum.inr x'))) xs
    List.foldl Regex.or (Regex.symbol (Sum.inr x)) xs'

def BCFG.lookup {μ: Nat} {α: Type} {Φ: (α: Type) -> Type}
  (g: BCFG μ α Φ) (ref: Fin μ): RegexRule μ α Φ :=
  union_rules (Vector.get g.prods ref)

def nullable {μ: Nat} {α: Type} {Φ: (α: Type) -> Type} (r: RegexRule μ α Φ): Bool :=
  Regex.nullable r

partial def derive {μ: Nat} {α: Type} [DecidableEq α] [BEq α]
  (g: BCFG μ α Pred) (r: RegexRule μ α Pred) (a: α): RegexRule μ α Pred :=
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
