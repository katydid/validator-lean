import Validator.Std.Debug

import Validator.Memoize.MemEnter
import Validator.Memoize.MemLeave

import Validator.Validator.Inst.TreeParserMemM
import Validator.Validator.ValidateM

namespace TreeParserMemTestM

structure State where
  parser: TreeParser.TreeParser
  enter: MemEnter.EnterMap
  leave: MemLeave.LeaveMap
  logs: List String

abbrev Impl α := EStateM String State α

def Impl.mk (p: TreeParser.TreeParser): State :=
  State.mk p MemEnter.EnterMap.mk MemLeave.LeaveMap.mk []

instance : Debug Impl where
  debug (line: String) := do
    let s <- EStateM.get
    set (State.mk s.parser s.enter s.leave (s.logs ++ [line]))
    return ()

instance: MonadStateOf TreeParser.TreeParser Impl where
  get : Impl TreeParser.TreeParser := do
    let s <- EStateM.get
    return s.parser
  set : TreeParser.TreeParser → Impl PUnit :=
    fun parser => do
      let s <- EStateM.get
      EStateM.set (State.mk parser s.enter s.leave s.logs)
  modifyGet {α: Type}: (TreeParser.TreeParser → Prod α TreeParser.TreeParser) → Impl α :=
    fun f => do
      let s <- EStateM.get
      let (res, parser) := f s.parser
      EStateM.set (State.mk parser s.enter s.leave s.logs)
      return res

instance
  [Monad Impl] -- EStateM is monad
  [Debug Impl] -- Debug instance is declared above
  [MonadExcept String Impl] -- EStateM String is MonadExcept String
  [MonadStateOf TreeParser.TreeParser Impl] -- MonadStateOf ParseTree.TreeParser is declared above
  : Parser Impl where -- This should just follow, but apparently we need to spell it out
  next := Parser.next
  skip := Parser.skip
  token := Parser.token

instance : MemEnter.MemEnter Impl where
  getEnter : Impl MemEnter.EnterMap := do
    let s <- EStateM.get
    return s.enter
  setEnter : MemEnter.EnterMap → Impl PUnit :=
    fun enter => do
      let s <- EStateM.get
      set (State.mk s.parser enter s.leave s.logs)

-- This should just follow from the instance declared in MemEnter, but we spell it out just in case.
instance : Enter.DeriveEnter Impl where
  deriveEnter (xs: List Expr): Impl (List IfExpr) := do
    let memoized <- MemEnter.MemEnter.getEnter
    match memoized.get? xs with
    | Option.none =>
      throw "test cache miss"
    | Option.some value =>
      Debug.debug "test cache hit"
      return value

instance : MemLeave.MemLeave Impl where
  getLeave : Impl MemLeave.LeaveMap := do
    let s <- EStateM.get
    return s.leave
  setLeave : MemLeave.LeaveMap → Impl PUnit :=
    fun leave => do
      let s <- EStateM.get
      set (State.mk s.parser s.enter leave s.logs)

-- This should just follow from the instance declared in MemLeave, but we spell it out just in case.
instance : Leave.DeriveLeave Impl where
  deriveLeave (xs: List Expr) (ns: List Bool): Impl (List Expr) := do
    let memoized <- MemLeave.MemLeave.getLeave
    match memoized.get? (xs, ns) with
    | Option.none =>
      throw "test cache miss"
    | Option.some value =>
      Debug.debug "test cache hit"
      return value

instance : ValidateM Impl where
  -- all instances have been created, so no implementations are required here

def runPopulatedMem (f: Impl α) (t: ParseTree) (e: MemEnter.EnterMap) (l: MemLeave.LeaveMap): EStateM.Result String State α :=
  EStateM.run f (State.mk (TreeParser.TreeParser.mk t) e l [])

def run' (f: Impl α) (t: ParseTree): Except String α :=
  match EStateM.run f (Impl.mk (TreeParser.TreeParser.mk t)) with
  | EStateM.Result.ok k _ => Except.ok k
  | EStateM.Result.error err _ => Except.error err
