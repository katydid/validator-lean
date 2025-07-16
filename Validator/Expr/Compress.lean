import Validator.Expr.Expr

namespace Compress

inductive Index where
 | val (n: Nat)
 | emptyset -- emptyset is unescapable, so it gets a special index

def indexOf (xs: List Expr) (y: Expr): Except String Index :=
  match y with
  | Expr.emptyset => Except.ok Index.emptyset
  | _ =>
    match List.idxOf? y xs with
    | Option.none => Except.error "indexOf: unable to find expression"
    | Option.some idx => Except.ok (Index.val idx)

def ofIndex' (xs: List Expr) (index: Nat): Except String Expr :=
  match xs with
  | [] => Except.error "index overflow"
  | (x::xs') =>
    match index with
    | 0 => Except.ok x
    | (n' + 1) => ofIndex' xs' n'

def ofIndex (xs: List Expr) (index: Index): Except String Expr :=
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
def compress (xs: List Expr): Except String ((List Expr) × Indices) := do
  -- sort to increase chance of cache hit
  -- TODO: let sxs := List.mergeSort xs
  -- remove duplicates
  let sxs' := List.eraseReps xs
  -- remove unescapable expressions, currently only emptyset
  let sxs'': List Expr := List.erase sxs' Expr.emptyset
  -- find all indexes of the original expressions in the compressed expressions
  let indexes: List Index <- List.mapM (indexOf sxs'') xs
  return (sxs'', Indices.mk indexes)

def compressM [Monad m] [MonadExcept String m] (xs: List Expr): m ((List Expr) × Indices) := do
  match compress xs with
  | Except.ok k => return k
  | Except.error err => throw err

-- expand expands a list of expressions.
def expand (indices: Indices) (xs: List Expr): Except String (List Expr) :=
  match indices with
  | Indices.mk indexes =>
    List.mapM (ofIndex xs) indexes

def expandM [Monad m] [MonadExcept String m] (indices: Indices) (xs: List Expr): m (List Expr) :=
  match expand indices xs with
  | Except.ok k => return k
  | Except.error err => throw err
