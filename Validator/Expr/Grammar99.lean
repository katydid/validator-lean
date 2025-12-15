import Validator.Std.Hedge
import Validator.Std.Vec

import Validator.Expr.Grammar
import Validator.Expr.Pred
import Validator.Expr.Regex
import Validator.Expr.Language

-- Definition of a regular hedge grammar according to http://www.xml.gr.jp/relax/hedge_nice.html
-- A regular hedge grammar (RHG) is a 5-tuple <Σ, X, N, P,rf >, where:
--     Σ is a finite set of symbols,
--     X is a finite set of variables,
--     N is a finite set of non-terminals,
--     P is a finite set of production rules, each of which takes one of the two forms as below:
--         n → x, where n is a non-terminal in N, and x is a variable in X,
--         n → a <r>, where n is a non-terminal in N, a is a symbol in Σ, and r is a regular expression comprising non-terminals,
--     rf is a regular expression comprising non-terminals.

structure Grammar99 (n: Nat) (φ: Type) where
  start: Regex (Ref n)
  prods: Vec (φ × Regex (Ref n)) n

def Grammar99.lookup (g: Grammar99 n φ) (ref: Fin n): φ × Regex (Ref n) :=
  Vec.get g.prods ref

def Grammar99.denote_prod {α: Type}
  (g: Grammar99 n φ) (Φ: φ -> α -> Prop) [DecidableRel Φ]
  (pred: φ) (r: Regex (Ref n)) (xs: Hedge α): Prop :=
  match xs with
  | [Hedge.Node.mk label children] =>
    Φ pred label /\
    Regex.denote_infix r children (fun ref xs' =>
      match (g.lookup ref) with
      | (pred', r') =>
        Grammar99.denote_prod g Φ pred' r' xs'
    )
  | _ => False
  termination_by xs
  decreasing_by
    obtain ⟨xs, hxs⟩ := xs'
    have h := List.list_infix_is_leq_sizeOf hxs
    simp +arith only
    simp only [List.cons.sizeOf_spec, List.nil.sizeOf_spec, Hedge.Node.mk.sizeOf_spec]
    omega

def Grammar99.denote_start {α: Type}
  (g: Grammar99 n φ) (Φ: φ -> α -> Prop) [DecidableRel Φ]
  (r: Regex (Ref n)) (xs: Hedge α): Prop :=
  Regex.denote_infix r xs (fun ref xs' =>
    match (g.lookup ref) with
    | (pred', r') =>
      Grammar99.denote_prod g Φ pred' r' xs'
  )

def Grammar99.denote {α: Type}
  (g: Grammar99 n φ) (Φ: φ -> α -> Prop) [DecidableRel Φ]
  (xs: Hedge α): Prop :=
  Grammar99.denote_start g Φ g.start xs

namespace Grammar99

def convert99'
  (g99: Grammar99 n φ)
  (r: Regex (Ref n)): Rule n φ :=
  match r with
  | Regex.emptyset => Regex.emptyset
  | Regex.emptystr => Regex.emptystr
  | Regex.symbol ref => Regex.symbol ((g99.lookup ref).1, ref)
  | Regex.or p q => Regex.or (convert99' g99 p) (convert99' g99 q)
  | Regex.concat p q => Regex.concat (convert99' g99 p) (convert99' g99 q)
  | Regex.star p => Regex.star (convert99' g99 p)

def convert99 (g99: Grammar99 n φ): Grammar n φ :=
  match g99 with
  | Grammar99.mk start prods =>
    Grammar.mk (convert99' g99 start) (Vec.map prods (fun (_, rref) => convert99' g99 rref))

def convert' (g: Grammar n φ) (r: Regex (φ × Ref n)): Regex (Ref n) :=
  match r with
  | Regex.emptyset => Regex.emptyset
  | Regex.emptystr => Regex.emptystr
  | Regex.symbol (_, ref) => Regex.symbol ref
  | Regex.or p q => Regex.or (convert' g p) (convert' g q)
  | Regex.concat p q => Regex.concat (convert' g p) (convert' g q)
  | Regex.star p => Regex.star (convert' g p)
