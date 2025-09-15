import Validator.Expr.Expr

namespace Compress

inductive Index where
 | val (n: Nat)
 | emptyset -- emptyset is unescapable, so it gets a special index

def indexOf [DecidableEq α] (xs: Exprs μ α) (y: (Expr μ α)): Except String Index :=
  match y with
  | Expr.emptyset => Except.ok Index.emptyset
  | _ =>
    match List.idxOf? y xs with
    | Option.none => Except.error "indexOf: unable to find expression"
    | Option.some idx => Except.ok (Index.val idx)

def ofIndex' (xs: Exprs μ α) (index: Nat): Except String (Expr μ α) :=
  match xs with
  | [] => Except.error "index overflow"
  | (x::xs') =>
    match index with
    | 0 => Except.ok x
    | (n' + 1) => ofIndex' xs' n'

def ofIndex (xs: Exprs μ α) (index: Index): Except String (Expr μ α) :=
  match index with
  | Index.emptyset => Except.ok Expr.emptyset
  | Index.val n =>
    ofIndex' xs n

-- Indices represents compressed indexes
-- that resulted from compressing a list of expressions.
-- This can be used to expanded to a list of expressions.
inductive Indices where
  | mk (indices: List Index)

-- compress compresses a list of expressions.
def compress [DecidableEq α] (xs: Exprs μ α): Except String ((Exprs μ α) × Indices) := do
  -- sort to increase chance of cache hit
  -- TODO: let sxs := List.mergeSort xs
  -- remove duplicates
  let sxs' := List.eraseReps xs
  -- remove unescapable expressions, currently only emptyset
  let sxs'': Exprs μ α := List.erase sxs' Expr.emptyset
  -- find all indexes of the original expressions in the compressed expressions
  let indexes: List Index <- List.mapM (indexOf sxs'') xs
  return (sxs'', Indices.mk indexes)

def compressM [DecidableEq α] [Monad m] [MonadExcept String m] (xs: Exprs μ α): m ((Exprs μ α) × Indices) := do
  MonadExcept.ofExcept (compress xs)

-- expand expands a list of expressions.
def expand (indices: Indices) (xs: Exprs μ α): Except String (Exprs μ α) :=
  match indices with
  | Indices.mk indexes =>
    List.mapM (ofIndex xs) indexes

def expandM [Monad m] [MonadExcept String m] (indices: Indices) (xs: Exprs μ α): m (Exprs μ α) :=
  MonadExcept.ofExcept (expand indices xs)
