import Validator.Std.Debug

import Validator.Parser.ParseTree
import Validator.Parser.TreeParser

import Validator.Env.Env
import Validator.Memoize.MemEnter
import Validator.Memoize.MemLeave

namespace EnvTreeParserIO

structure TreeParserAndMem where
  parser: TreeParser.TreeParser
  enter: MemEnter.EnterMap
  leave: MemLeave.LeaveMap

abbrev TreeParserIO (α: Type) := StateT TreeParserAndMem (EIO String) α

def TreeParserIO.mk (p: TreeParser.TreeParser): TreeParserAndMem :=
  TreeParserAndMem.mk p MemEnter.EnterMap.mk MemLeave.LeaveMap.mk

def EIO.println [ToString α] (x: α): EIO String Unit :=
  IO.toEIO (fun x => "ERROR: " ++ x.toString) (IO.println x)

instance : Debug TreeParserIO where
  debug (line: String) := StateT.lift (EIO.println line)

instance: MonadStateOf TreeParser.TreeParser TreeParserIO where
  get : TreeParserIO TreeParser.TreeParser := do
    let s <- StateT.get
    return s.parser
  set : TreeParser.TreeParser → TreeParserIO PUnit :=
    fun parser => do
      let s <- StateT.get
      set (TreeParserAndMem.mk parser s.enter s.leave)
  modifyGet {α: Type}: (TreeParser.TreeParser → Prod α TreeParser.TreeParser) → TreeParserIO α :=
    fun f => do
      let s <- StateT.get
      let (res, parser) := f s.parser
      set (TreeParserAndMem.mk parser s.enter s.leave)
      return res

instance
  [Monad TreeParserIO] -- EStateM is monad
  [Debug TreeParserIO] -- Debug instance is declared above
  [MonadExcept String TreeParserIO] -- EStateM String is MonadExcept String
  [MonadStateOf TreeParser.TreeParser TreeParserIO] -- MonadStateOf ParseTree.TreeParser is declared above
  : Parser TreeParserIO where -- This should just follow, but apparently we need to spell it out
  next := Parser.next
  skip := Parser.skip
  token := Parser.token

instance : MemEnter.MemEnter TreeParserIO where
  getEnter : TreeParserIO MemEnter.EnterMap := do
    let s <- StateT.get
    return s.enter
  setEnter : MemEnter.EnterMap → TreeParserIO PUnit :=
    fun enter => do
      let s <- StateT.get
      set (TreeParserAndMem.mk s.parser enter s.leave)

-- This should just follow from the instance declared in MemEnter, but we spell it out just in case.
instance : Enter.DeriveEnter TreeParserIO where
  deriveEnter (xs: List Expr): TreeParserIO (List IfExpr) := MemEnter.deriveEnter xs

instance : MemLeave.MemLeave TreeParserIO where
  getLeave : TreeParserIO MemLeave.LeaveMap := do
    let s <- StateT.get
    return s.leave
  setLeave : MemLeave.LeaveMap → TreeParserIO PUnit :=
    fun leave => do
      let s <- StateT.get
      set (TreeParserAndMem.mk s.parser s.enter leave)

-- This should just follow from the instance declared in MemLeave, but we spell it out just in case.
instance : Leave.DeriveLeave TreeParserIO where
  deriveLeave (xs: List Expr) (ns: List Bool): TreeParserIO (List Expr) := MemLeave.deriveLeave xs ns

instance : Env TreeParserIO where
  -- all instances have been created, so no implementations are required here

def run (f: TreeParserIO α) (t: ParseTree): EIO String α :=
  StateT.run' f (TreeParserIO.mk (TreeParser.TreeParser.mk t))

-- runTwice is used to check if the cache was hit on the second run
def runTwice [DecidableEq α] (f: TreeParserIO α) (t: ParseTree): EIO String α := do
  let initial := TreeParserIO.mk (TreeParser.TreeParser.mk t)
  let (res1, updated) <- StateT.run f initial
  _ <- EIO.println "start second run"
  let res2 <- StateT.run' f (TreeParserAndMem.mk (TreeParser.TreeParser.mk t) updated.enter updated.leave)
  if res1 ≠ res2
  then throw "memoization changed result"
  else return res1
