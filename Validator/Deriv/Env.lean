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
-- Tagless final class inspired by https://jproyo.github.io/posts/2019-03-17-tagless-final-haskell/
class Env (m: Type -> Type u) extends
  Monad m,
  MonadExcept String m,
  Parser m,
  Enter.DeriveEnters m,
  Leave.DeriveLeaves m

namespace Env

abbrev LTreeExcept m := StateT LTree.LTreeParser (Except String) m

instance : Enter.DeriveEnters LTreeExcept where
  deriveEnters xs := return Enter.enters xs

instance : Leave.DeriveLeaves LTreeExcept where
  deriveLeaves xs ns := Leave.leaves xs ns

instance : Env LTreeExcept where
  -- all instances have been created, so no implementations are required here

structure LTreeState where
  parser: LTree.LTreeParser
  enter: Mem.MemEnter
  leave: Mem.MemLeave

abbrev LTreeMem := StateT LTreeState (Except String)

-- TODO: find better way to write exactly the same code for each method.
-- There has to be shorter way to lift accross these monads.
instance : Parser LTreeMem where
  next := do
    let s <- get
    match StateT.run LTree.next s.parser with
    | Except.ok (res, parser') =>
      set (LTreeState.mk parser' s.enter s.leave)
      return res
    | Except.error err =>
      throw err
  skip := do
    let s <- get
    match StateT.run LTree.skip s.parser with
    | Except.ok (res, parser') =>
      set (LTreeState.mk parser' s.enter s.leave)
      return res
    | Except.error err =>
      throw err
  token := do
    let s <- get
    match StateT.run LTree.token s.parser with
    | Except.ok (res, parser') =>
      set (LTreeState.mk parser' s.enter s.leave)
      return res
    | Except.error err =>
      throw err

instance : Enter.DeriveEnters LTreeMem where
  deriveEnters xs := do
    let s <- get
    match StateT.run (m := Id) (Mem.enters xs) s.enter with
    | (res, enter') =>
      set (LTreeState.mk s.parser enter' s.leave)
      return res

instance : Leave.DeriveLeaves LTreeMem where
  deriveLeaves xs ns := do
    let s <- get
    match StateT.run (Mem.leaves xs ns) s.leave with
    | Except.ok (res, leave') =>
      set (LTreeState.mk s.parser s.enter leave')
      return res
    | Except.error err =>
      throw err

instance : Env LTreeMem where
  -- all instances have been created, so no implementations are required here
