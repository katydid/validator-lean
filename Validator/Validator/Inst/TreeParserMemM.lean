import Validator.Std.Debug

import Validator.Parser.ParseTree
import Validator.Parser.TreeParser

import Validator.Memoize.MemEnter
import Validator.Memoize.MemLeave

import Validator.Validator.ValidateM

namespace TreeParserMemM

structure TreeParserAndMem where
  parser: TreeParser.TreeParser
  enter: MemEnter.EnterMap
  leave: MemLeave.LeaveMap

abbrev TreeParserMemM α := EStateM String TreeParserAndMem α

def TreeParserMemM.mk (p: TreeParser.TreeParser): TreeParserAndMem :=
  TreeParserAndMem.mk p MemEnter.EnterMap.mk MemLeave.LeaveMap.mk

instance : Debug TreeParserMemM where
  debug (_line: String) := return ()

instance: MonadStateOf TreeParser.TreeParser TreeParserMemM where
  get : TreeParserMemM TreeParser.TreeParser := do
    let s <- EStateM.get
    return s.parser
  set : TreeParser.TreeParser → TreeParserMemM PUnit :=
    fun parser => do
      let s <- EStateM.get
      EStateM.set (TreeParserAndMem.mk parser s.enter s.leave)
  modifyGet {α: Type}: (TreeParser.TreeParser → Prod α TreeParser.TreeParser) → TreeParserMemM α :=
    fun f => do
      let s <- EStateM.get
      let (res, parser) := f s.parser
      EStateM.set (TreeParserAndMem.mk parser s.enter s.leave)
      return res

instance
  [Monad TreeParserMemM] -- EStateM is monad
  [Debug TreeParserMemM] -- Debug instance is declared above
  [MonadExcept String TreeParserMemM] -- EStateM String is MonadExcept String
  [MonadStateOf TreeParser.TreeParser TreeParserMemM] -- MonadStateOf ParseTree.TreeParser is declared above
  : Parser TreeParserMemM where -- This should just follow, but apparently we need to spell it out
  next := Parser.next
  skip := Parser.skip
  token := Parser.token

instance : MemEnter.MemEnter TreeParserMemM where
  getEnter : TreeParserMemM MemEnter.EnterMap := do
    let s <- EStateM.get
    return s.enter
  setEnter : MemEnter.EnterMap → TreeParserMemM PUnit :=
    fun enter => do
      let s <- EStateM.get
      set (TreeParserAndMem.mk s.parser enter s.leave)

-- This should just follow from the instance declared in MemEnter, but we spell it out just in case.
instance : Enter.DeriveEnter TreeParserMemM where
  deriveEnter (xs: List Expr): TreeParserMemM (List IfExpr) := MemEnter.deriveEnter xs

instance : MemLeave.MemLeave TreeParserMemM where
  getLeave : TreeParserMemM MemLeave.LeaveMap := do
    let s <- EStateM.get
    return s.leave
  setLeave : MemLeave.LeaveMap → TreeParserMemM PUnit :=
    fun leave => do
      let s <- EStateM.get
      set (TreeParserAndMem.mk s.parser s.enter leave)

-- This should just follow from the instance declared in MemLeave, but we spell it out just in case.
instance : Leave.DeriveLeave TreeParserMemM where
  deriveLeave (xs: List Expr) (ns: List Bool): TreeParserMemM (List Expr) := MemLeave.deriveLeave xs ns

instance : ValidateM TreeParserMemM where
  -- all instances have been created, so no implementations are required here

def run (f: TreeParserMemM α) (t: ParseTree): Except String α :=
  match EStateM.run f (TreeParserMemM.mk (TreeParser.TreeParser.mk t)) with
  | EStateM.Result.ok k _ => Except.ok k
  | EStateM.Result.error err _ => Except.error err

def run' (f: TreeParserMemM α) (t: ParseTree): EStateM.Result String (MemEnter.EnterMap × MemLeave.LeaveMap) α :=
  match EStateM.run f (TreeParserMemM.mk (TreeParser.TreeParser.mk t)) with
  | EStateM.Result.ok res s => EStateM.Result.ok res (s.enter, s.leave)
  | EStateM.Result.error err s => EStateM.Result.error err (s.enter, s.leave)
