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

abbrev TreeParserState α := EStateM String ParseTree.TreeParser α

instance : Enter.DeriveEnters TreeParserState where
  deriveEnters xs := return Enter.enters xs

instance : Leave.DeriveLeaves TreeParserState where
  deriveLeaves xs ns := Leave.leaves xs ns

instance : Env TreeParserState where
  -- all instances have been created, so no implementations are required here

structure TreeParserAndMem where
  parser: ParseTree.TreeParser
  enter: Mem.MemEnter
  leave: Mem.MemLeave

abbrev TreeParserStateWithMem α := EStateM String TreeParserAndMem α

def TreeParserStateWithMem.mk (p: ParseTree.TreeParser): TreeParserAndMem :=
  TreeParserAndMem.mk p Std.ExtHashMap.emptyWithCapacity Std.ExtHashMap.emptyWithCapacity

-- TODO: find better way to write exactly the same code for each method.
-- There has to be shorter way to lift accross these monads.
instance : Parser TreeParserStateWithMem where
  next := do
    let s <- get
    match StateT.run ParseTree.next s.parser with
    | Except.ok (res, parser') =>
      set (TreeParserAndMem.mk parser' s.enter s.leave)
      return res
    | Except.error err =>
      throw err
  skip := do
    let s <- get
    match StateT.run ParseTree.skip s.parser with
    | Except.ok (res, parser') =>
      set (TreeParserAndMem.mk parser' s.enter s.leave)
      return res
    | Except.error err =>
      throw err
  token := do
    let s <- get
    match StateT.run ParseTree.token s.parser with
    | Except.ok (res, parser') =>
      set (TreeParserAndMem.mk parser' s.enter s.leave)
      return res
    | Except.error err =>
      throw err

instance : Enter.DeriveEnters TreeParserStateWithMem where
  deriveEnters xs := do
    let s <- get
    match StateT.run (m := Id) (Mem.enters xs) s.enter with
    | (res, enter') =>
      set (TreeParserAndMem.mk s.parser enter' s.leave)
      return res

instance : Leave.DeriveLeaves TreeParserStateWithMem where
  deriveLeaves xs ns := do
    let s <- get
    match StateT.run (Mem.leaves xs ns) s.leave with
    | Except.ok (res, leave') =>
      set (TreeParserAndMem.mk s.parser s.enter leave')
      return res
    | Except.error err =>
      throw err

instance : Env TreeParserStateWithMem where
  -- all instances have been created, so no implementations are required here

def TreeParserState.run (x: TreeParserState α) (t: ParseTree): Except String α :=
  match EStateM.run x (ParseTree.TreeParser.mk t) with
  | EStateM.Result.ok k _ => Except.ok k
  | EStateM.Result.error err _ => Except.error err

def TreeParserStateWithMem.run (f: TreeParserStateWithMem α) (t: ParseTree): Except String α :=
  match EStateM.run f (TreeParserStateWithMem.mk (ParseTree.TreeParser.mk t)) with
  | EStateM.Result.ok k _ => Except.ok k
  | EStateM.Result.error err _ => Except.error err
