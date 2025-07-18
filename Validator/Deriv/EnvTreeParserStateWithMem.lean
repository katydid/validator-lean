import Validator.Std.Debug

import Validator.Deriv.Env
import Validator.Deriv.MemEnter
import Validator.Deriv.MemLeave

namespace EnvTreeParserStateWithMem

structure TreeParserAndMem where
  parser: ParseTree.TreeParser
  enter: MemEnter.EnterMap
  leave: MemLeave.LeaveMap

abbrev TreeParserStateWithMem α := EStateM String TreeParserAndMem α

def TreeParserStateWithMem.mk (p: ParseTree.TreeParser): TreeParserAndMem :=
  TreeParserAndMem.mk p MemEnter.EnterMap.mk MemLeave.LeaveMap.mk

instance : Debug TreeParserStateWithMem where
  debug (_line: String) := return ()

instance: MonadStateOf ParseTree.TreeParser TreeParserStateWithMem where
  get : TreeParserStateWithMem ParseTree.TreeParser := do
    let s <- EStateM.get
    return s.parser
  set : ParseTree.TreeParser → TreeParserStateWithMem PUnit :=
    fun parser => do
      let s <- EStateM.get
      EStateM.set (TreeParserAndMem.mk parser s.enter s.leave)
  modifyGet {α: Type}: (ParseTree.TreeParser → Prod α ParseTree.TreeParser) → TreeParserStateWithMem α :=
    fun f => do
      let s <- EStateM.get
      let (res, parser) := f s.parser
      EStateM.set (TreeParserAndMem.mk parser s.enter s.leave)
      return res

instance
  [Monad TreeParserStateWithMem] -- EStateM is monad
  [Debug TreeParserStateWithMem] -- Debug instance is declared above
  [MonadExcept String TreeParserStateWithMem] -- EStateM String is MonadExcept String
  [MonadStateOf ParseTree.TreeParser TreeParserStateWithMem] -- MonadStateOf ParseTree.TreeParser is declared above
  : Parser TreeParserStateWithMem where -- This should just follow, but apparently we need to spell it out
  next := Parser.next
  skip := Parser.skip
  token := Parser.token

instance : MemEnter.MemEnter TreeParserStateWithMem where
  getEnter : TreeParserStateWithMem MemEnter.EnterMap := do
    let s <- EStateM.get
    return s.enter
  setEnter : MemEnter.EnterMap → TreeParserStateWithMem PUnit :=
    fun enter => do
      let s <- EStateM.get
      set (TreeParserAndMem.mk s.parser enter s.leave)

-- This should just follow from the instance declared in MemEnter, but we spell it out just in case.
instance : Enter.DeriveEnters TreeParserStateWithMem where
  deriveEnters (xs: List Expr): TreeParserStateWithMem (List IfExpr) := MemEnter.enter xs

instance : MemLeave.MemLeave TreeParserStateWithMem where
  getLeave : TreeParserStateWithMem MemLeave.LeaveMap := do
    let s <- EStateM.get
    return s.leave
  setLeave : MemLeave.LeaveMap → TreeParserStateWithMem PUnit :=
    fun leave => do
      let s <- EStateM.get
      set (TreeParserAndMem.mk s.parser s.enter leave)

-- This should just follow from the instance declared in MemLeave, but we spell it out just in case.
instance : Leave.DeriveLeaves TreeParserStateWithMem where
  deriveLeaves (xs: List Expr) (ns: List Bool): TreeParserStateWithMem (List Expr) := MemLeave.leave xs ns

instance : Env TreeParserStateWithMem where
  -- all instances have been created, so no implementations are required here

def run (f: TreeParserStateWithMem α) (t: ParseTree): Except String α :=
  match EStateM.run f (TreeParserStateWithMem.mk (ParseTree.TreeParser.mk t)) with
  | EStateM.Result.ok k _ => Except.ok k
  | EStateM.Result.error err _ => Except.error err

def run' (f: TreeParserStateWithMem α) (t: ParseTree): EStateM.Result String (MemEnter.EnterMap × MemLeave.LeaveMap) α :=
  match EStateM.run f (TreeParserStateWithMem.mk (ParseTree.TreeParser.mk t)) with
  | EStateM.Result.ok res s => EStateM.Result.ok res (s.enter, s.leave)
  | EStateM.Result.error err s => EStateM.Result.error err (s.enter, s.leave)
