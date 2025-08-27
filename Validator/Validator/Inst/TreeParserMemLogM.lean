import Validator.Std.Debug

import Validator.Std.ParseTree
import Validator.Parser.TreeParser

import Validator.Memoize.MemEnter
import Validator.Memoize.MemLeave

import Validator.Validator.ValidateM

namespace TreeParserMemLogM

structure State (α: Type) [DecidableEq α] [Hashable α] where
  parser: TreeParser.ParserState α
  enter: MemEnter.EnterMap α
  leave: MemLeave.LeaveMap α
  logs : List String

abbrev Impl α [DecidableEq α] [Hashable α] β := EStateM String (State α) β

def Impl.mk [DecidableEq α] [Hashable α] (p: TreeParser.ParserState α): State α :=
  State.mk p MemEnter.EnterMap.mk MemLeave.LeaveMap.mk []

instance [DecidableEq α] [Hashable α]: Debug (Impl α) where
  debug (line: String) := do
    let s <- EStateM.get
    set (State.mk s.parser s.enter s.leave (s.logs ++ [line]))
    return ()

instance [DecidableEq α] [Hashable α]: MonadStateOf (TreeParser.ParserState α) (Impl α) where
  get : Impl α (TreeParser.ParserState α) := do
    let s <- EStateM.get
    return s.parser
  set : TreeParser.ParserState α → Impl α PUnit :=
    fun parser => do
      let s <- EStateM.get
      EStateM.set (State.mk parser s.enter s.leave s.logs)
  modifyGet {β: Type}: (TreeParser.ParserState α → Prod β (TreeParser.ParserState α)) → Impl α β :=
    fun f => do
      let s <- EStateM.get
      let (res, parser) := f s.parser
      EStateM.set (State.mk parser s.enter s.leave s.logs)
      return res

instance
  [DecidableEq α]
  [Hashable α]
  [Monad (Impl α)] -- EStateM is monad
  [Debug (Impl α)] -- Debug instance is declared above
  [MonadExcept String (Impl α)] -- EStateM String is MonadExcept String
  [MonadStateOf (TreeParser.ParserState α) (Impl α)] -- MonadStateOf ParseTree.TreeParser is declared above
  : Parser (Impl α) α where -- This should just follow, but apparently we need to spell it out
  next := Parser.next
  skip := Parser.skip
  token := Parser.token

instance [DecidableEq α] [Hashable α]: MemEnter.MemEnter (Impl α) α where
  getEnter : Impl α (MemEnter.EnterMap α) := do
    let s <- EStateM.get
    return s.enter
  setEnter : MemEnter.EnterMap α → Impl α PUnit :=
    fun enter => do
      let s <- EStateM.get
      set (State.mk s.parser enter s.leave s.logs)

-- This should just follow from the instance declared in MemEnter, but we spell it out just in case.
instance [DecidableEq α] [Hashable α]: Enter.DeriveEnter (Impl α) α where
  deriveEnter (xs: Exprs α): Impl α (IfExprs α) := MemEnter.deriveEnter xs

instance [DecidableEq α] [Hashable α]: MemLeave.MemLeave (Impl α) α where
  getLeave : Impl α (MemLeave.LeaveMap α) := do
    let s <- EStateM.get
    return s.leave
  setLeave : MemLeave.LeaveMap α → Impl α PUnit :=
    fun leave => do
      let s <- EStateM.get
      set (State.mk s.parser s.enter leave s.logs)

-- This should just follow from the instance declared in MemLeave, but we spell it out just in case.
instance [DecidableEq α] [Hashable α]: Leave.DeriveLeave (Impl α) α where
  deriveLeave (xs: Exprs α) (ns: List Bool): Impl α (Exprs α) := MemLeave.deriveLeave xs ns

instance [DecidableEq α] [Hashable α]: ValidateM (Impl α) α where
  -- all instances have been created, so no implementations are required here

def run [DecidableEq α] [Hashable α] (f: Impl α β) (t: ParseTree α): EStateM.Result String (State α) β :=
  EStateM.run f (Impl.mk (TreeParser.ParserState.mk' t))

def run' [DecidableEq α] [Hashable α] (f: Impl α β) (t: ParseTree α): (List String × (Except String β)) :=
  match EStateM.run f (Impl.mk (TreeParser.ParserState.mk' t)) with
  | EStateM.Result.ok res s => (s.logs, Except.ok res)
  | EStateM.Result.error err s => (s.logs, Except.error err)

def runPopulatedMem [DecidableEq α] [Hashable α] (f: Impl α β) (t: ParseTree α) (e: MemEnter.EnterMap α) (l: MemLeave.LeaveMap α): EStateM.Result String (State α) β :=
  EStateM.run f (State.mk (TreeParser.ParserState.mk' t) e l [])
