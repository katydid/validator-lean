import Validator.Parser.Parser
import Validator.Parser.LTree

import Validator.Deriv.Enter
import Validator.Deriv.Leave
import Validator.Deriv.Mem

-- Env is the derivative validator environment.
-- Executing the derivative algorithm requires:
--   a pull based Parser
--   a deriveEnter and deriveLeave function that could optionally be memoized.
--   the possibility of returning an error.
class Env (m: Type -> Type u)
  [Monad m]
  [MonadExcept String m]
  [Parser m]
  [Enter.DeriveEnters m]
  [Leave.DeriveLeaves m]

abbrev EnvLTreeExcept := StateT LTree.LTreeParser (Except String)

instance : Enter.DeriveEnters EnvLTreeExcept where
  deriveEnters xs := return Enter.enters xs

instance : Leave.DeriveLeaves EnvLTreeExcept where
  deriveLeaves xs ns := Leave.leaves xs ns

instance : Env EnvLTreeExcept where
  -- all instances have been created, so no implementations are required here

structure EnvLTreeState where
  parser: LTree.LTreeParser
  enter: Mem.MemEnter
  leave: Mem.MemLeave

abbrev EnvLTreeMem := StateT EnvLTreeState (Except String)

-- TODO: find better way to write exactly the same code for each method.
-- There has to be shorter way to lift accross these monads.
instance : Parser EnvLTreeMem where
  next := do
    let s <- get
    match StateT.run LTree.next s.parser with
    | Except.ok (res, parser') =>
      set (EnvLTreeState.mk parser' s.enter s.leave)
      return res
    | Except.error err =>
      throw err
  skip := do
    let s <- get
    match StateT.run LTree.skip s.parser with
    | Except.ok (res, parser') =>
      set (EnvLTreeState.mk parser' s.enter s.leave)
      return res
    | Except.error err =>
      throw err
  token := do
    let s <- get
    match StateT.run LTree.token s.parser with
    | Except.ok (res, parser') =>
      set (EnvLTreeState.mk parser' s.enter s.leave)
      return res
    | Except.error err =>
      throw err

instance : Enter.DeriveEnters EnvLTreeMem where
  deriveEnters xs := do
    let s <- get
    match StateT.run (m := Id) (Mem.enters xs) s.enter with
    | (res, enter') =>
      set (EnvLTreeState.mk s.parser enter' s.leave)
      return res

instance : Leave.DeriveLeaves EnvLTreeMem where
  deriveLeaves xs ns := do
    let s <- get
    match StateT.run (Mem.leaves xs ns) s.leave with
    | Except.ok (res, leave') =>
      set (EnvLTreeState.mk s.parser s.enter leave')
      return res
    | Except.error err =>
      throw err

instance : Env EnvLTreeMem where
  -- all instances have been created, so no implementations are required here
