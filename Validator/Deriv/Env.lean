import Validator.Parser.Parser
import Validator.Parser.ParseTree

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

abbrev ETreeParser := EStateM String ParseTree.TreeParser

instance : Enter.DeriveEnters ETreeParser where
  deriveEnters xs := return Enter.enters xs

instance : Leave.DeriveLeaves ETreeParser where
  deriveLeaves xs ns := Leave.leaves xs ns

instance : Env ETreeParser where
  -- all instances have been created, so no implementations are required here

def ETreeParser.run (x: ETreeParser α) (t: ParseTree): Except String α :=
  match EStateM.run x (ParseTree.TreeParser.mk' t) with
  | EStateM.Result.ok k _ => Except.ok k
  | EStateM.Result.error err _ => Except.error err

structure TreeState where
  parser: ParseTree.TreeParser
  enter: Mem.MemEnter
  leave: Mem.MemLeave

abbrev TreeMem := EStateM String TreeState

def TreeMem.mk (p: ParseTree.TreeParser): TreeState :=
  TreeState.mk p Std.ExtHashMap.emptyWithCapacity Std.ExtHashMap.emptyWithCapacity

-- TODO: find better way to write exactly the same code for each method.
-- There has to be shorter way to lift accross these monads.
instance : Parser TreeMem where
  next := do
    let s <- get
    match StateT.run ParseTree.next s.parser with
    | Except.ok (res, parser') =>
      set (TreeState.mk parser' s.enter s.leave)
      return res
    | Except.error err =>
      throw err
  skip := do
    let s <- get
    match StateT.run ParseTree.skip s.parser with
    | Except.ok (res, parser') =>
      set (TreeState.mk parser' s.enter s.leave)
      return res
    | Except.error err =>
      throw err
  token := do
    let s <- get
    match StateT.run ParseTree.token s.parser with
    | Except.ok (res, parser') =>
      set (TreeState.mk parser' s.enter s.leave)
      return res
    | Except.error err =>
      throw err

instance : Enter.DeriveEnters TreeMem where
  deriveEnters xs := do
    let s <- get
    match StateT.run (m := Id) (Mem.enters xs) s.enter with
    | (res, enter') =>
      set (TreeState.mk s.parser enter' s.leave)
      return res

instance : Leave.DeriveLeaves TreeMem where
  deriveLeaves xs ns := do
    let s <- get
    match StateT.run (Mem.leaves xs ns) s.leave with
    | Except.ok (res, leave') =>
      set (TreeState.mk s.parser s.enter leave')
      return res
    | Except.error err =>
      throw err

instance : Env TreeMem where
  -- all instances have been created, so no implementations are required here

def TreeMem.run (x: TreeMem α) (t: ParseTree): Except String α :=
  match EStateM.run x (TreeMem.mk (ParseTree.TreeParser.mk' t)) with
  | EStateM.Result.ok k _ => Except.ok k
  | EStateM.Result.error err _ => Except.error err
