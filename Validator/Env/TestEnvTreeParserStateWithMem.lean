import Validator.Std.Debug

import Validator.Memoize.MemEnter
import Validator.Memoize.MemLeave

import Validator.Env.EnvTreeParserStateWithMem
import Validator.Env.EnvM

namespace TestEnvTreeParserStateWithMem

structure TreeParserAndMemTest where
  parser: TreeParser.TreeParser
  enter: MemEnter.EnterMap
  leave: MemLeave.LeaveMap

open EnvTreeParserStateWithMem

abbrev TreeParserStateWithMemTest α := EStateM String TreeParserAndMemTest α

def TreeParserStateWithMemTest.mk (p: TreeParser.TreeParser): TreeParserAndMemTest :=
  TreeParserAndMemTest.mk p MemEnter.EnterMap.mk MemLeave.LeaveMap.mk

instance : Debug TreeParserStateWithMemTest where
  debug (_line: String) := return ()

instance: MonadStateOf TreeParser.TreeParser TreeParserStateWithMemTest where
  get : TreeParserStateWithMemTest TreeParser.TreeParser := do
    let s <- EStateM.get
    return s.parser
  set : TreeParser.TreeParser → TreeParserStateWithMemTest PUnit :=
    fun parser => do
      let s <- EStateM.get
      EStateM.set (TreeParserAndMemTest.mk parser s.enter s.leave)
  modifyGet {α: Type}: (TreeParser.TreeParser → Prod α TreeParser.TreeParser) → TreeParserStateWithMemTest α :=
    fun f => do
      let s <- EStateM.get
      let (res, parser) := f s.parser
      EStateM.set (TreeParserAndMemTest.mk parser s.enter s.leave)
      return res

instance
  [Monad TreeParserStateWithMemTest] -- EStateM is monad
  [Debug TreeParserStateWithMemTest] -- Debug instance is declared above
  [MonadExcept String TreeParserStateWithMemTest] -- EStateM String is MonadExcept String
  [MonadStateOf TreeParser.TreeParser TreeParserStateWithMemTest] -- MonadStateOf ParseTree.TreeParser is declared above
  : Parser TreeParserStateWithMemTest where -- This should just follow, but apparently we need to spell it out
  next := Parser.next
  skip := Parser.skip
  token := Parser.token

instance : MemEnter.MemEnter TreeParserStateWithMemTest where
  getEnter : TreeParserStateWithMemTest MemEnter.EnterMap := do
    let s <- EStateM.get
    return s.enter
  setEnter : MemEnter.EnterMap → TreeParserStateWithMemTest PUnit :=
    fun enter => do
      let s <- EStateM.get
      set (TreeParserAndMemTest.mk s.parser enter s.leave)

-- This should just follow from the instance declared in MemEnter, but we spell it out just in case.
instance : Enter.DeriveEnter TreeParserStateWithMemTest where
  deriveEnter (xs: List Expr): TreeParserStateWithMemTest (List IfExpr) := do
    let memoized <- MemEnter.MemEnter.getEnter
    match memoized.get? xs with
    | Option.none =>
      throw "test cache miss"
    | Option.some value =>
      Debug.debug "test cache hit"
      return value

instance : MemLeave.MemLeave TreeParserStateWithMemTest where
  getLeave : TreeParserStateWithMemTest MemLeave.LeaveMap := do
    let s <- EStateM.get
    return s.leave
  setLeave : MemLeave.LeaveMap → TreeParserStateWithMemTest PUnit :=
    fun leave => do
      let s <- EStateM.get
      set (TreeParserAndMemTest.mk s.parser s.enter leave)

-- This should just follow from the instance declared in MemLeave, but we spell it out just in case.
instance : Leave.DeriveLeave TreeParserStateWithMemTest where
  deriveLeave (xs: List Expr) (ns: List Bool): TreeParserStateWithMemTest (List Expr) := do
    let memoized <- MemLeave.MemLeave.getLeave
    match memoized.get? (xs, ns) with
    | Option.none =>
      throw "test cache miss"
    | Option.some value =>
      Debug.debug "test cache hit"
      return value

instance : EnvM TreeParserStateWithMemTest where
  -- all instances have been created, so no implementations are required here

def run (f: TreeParserStateWithMemTest α) (t: ParseTree): Except String α :=
  match EStateM.run f (TreeParserStateWithMemTest.mk (TreeParser.TreeParser.mk t)) with
  | EStateM.Result.ok k _ => Except.ok k
  | EStateM.Result.error err _ => Except.error err

def run' (f: TreeParserStateWithMemTest α) (t: ParseTree) (e: MemEnter.EnterMap) (l: MemLeave.LeaveMap): EStateM.Result String (MemEnter.EnterMap × MemLeave.LeaveMap) α :=
  match EStateM.run f (TreeParserAndMemTest.mk (TreeParser.TreeParser.mk t) e l) with
  | EStateM.Result.ok res s => EStateM.Result.ok res (s.enter, s.leave)
  | EStateM.Result.error err s => EStateM.Result.error err (s.enter, s.leave)
