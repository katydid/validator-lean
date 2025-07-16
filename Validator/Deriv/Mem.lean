import Std

import Validator.Expr.Expr
import Validator.Expr.IfExpr

import Validator.Deriv.Enter
import Validator.Deriv.Leave

private def memoizeM {α: Type u} {β: Type u}
  [Monad m] [Hashable α] [BEq α] [LawfulBEq α]
  (memoized: Std.ExtHashMap α β) (calculate: α -> m β) (key: α) : m (β × Std.ExtHashMap α β) := do
  match memoized.get? key with
  | Option.none =>
    let newvalue <- calculate key
    return (newvalue, memoized.insert key newvalue)
  | Option.some value =>
    return (value, memoized)

private def MemEnter := Std.ExtHashMap (List Expr) (List IfExpr)
private def MemLeave := Std.ExtHashMap (List Expr × List Bool) (List Expr)
def Mem := (MemEnter × MemLeave)

def Mem.mk: Mem :=
  (Std.ExtHashMap.emptyWithCapacity, Std.ExtHashMap.emptyWithCapacity)

def enters
  (xs: List Expr) (mem: Mem): Id (List IfExpr × Mem) := do
  match mem with
  | ( memE, memL ) =>
    let (ifExprs, memE') <- memoizeM memE Enter.enters xs
    return (ifExprs, ( memE', memL ))

private def leavesUncurried [Monad m] [MonadExcept String m] (xsns: (List Expr) × (List Bool)): m (List Expr) :=
  match xsns with
  | ( xs, ns ) => Leave.leaves xs ns

def leaves [Monad m] [MonadExcept String m] (xs: List Expr) (ns: List Bool) (mem: Mem): m ((List Expr) × Mem) := do
  match mem with
  | ⟨ memE, memL ⟩ =>
    let (deriveLeave, memL') <- memoizeM memL leavesUncurried (xs, ns)
    return (deriveLeave, ( memE, memL' ))

instance : Enter.DeriveEnters (StateM Mem) where
  deriveEnters := enters

instance : Leave.DeriveLeaves (StateT Mem (Except String)) where
  deriveLeaves := leaves
