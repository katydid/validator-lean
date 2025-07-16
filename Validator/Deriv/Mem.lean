import Std

import Validator.Expr.Expr
import Validator.Expr.IfExpr

import Validator.Deriv.Enter
import Validator.Deriv.Leave

namespace Mem

private def memoizeM {α: Type u} {β: Type u}
  [Monad m] [Hashable α] [BEq α] [LawfulBEq α]
  (memoized: Std.ExtHashMap α β) (calculate: α -> m β) (key: α) : m (β × Std.ExtHashMap α β) := do
  match memoized.get? key with
  | Option.none =>
    let newvalue <- calculate key
    return (newvalue, memoized.insert key newvalue)
  | Option.some value =>
    return (value, memoized)

def MemEnter := Std.ExtHashMap (List Expr) (List IfExpr)
def MemLeave := Std.ExtHashMap (List Expr × List Bool) (List Expr)

def enters
  (xs: List Expr) (mem: MemEnter): Id (List IfExpr × MemEnter) :=
  memoizeM mem Enter.enters xs

private def leavesUncurried [Monad m] [MonadExcept String m] (xsns: (List Expr) × (List Bool)): m (List Expr) :=
  match xsns with
  | ( xs, ns ) => Leave.leaves xs ns

def leaves [Monad m] [MonadExcept String m] (xs: List Expr) (ns: List Bool) (mem: MemLeave): m ((List Expr) × MemLeave) := do
  memoizeM mem leavesUncurried (xs, ns)

instance : Enter.DeriveEnters (StateM MemEnter) where
  deriveEnters := enters

instance : Leave.DeriveLeaves (StateT MemLeave (Except String)) where
  deriveLeaves := leaves
