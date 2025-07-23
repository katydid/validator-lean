import Validator.Std.Debug

import Validator.Parser.ParseTree
import Validator.Parser.TreeParser

import Validator.Memoize.MemEnter
import Validator.Memoize.MemLeave

import Validator.Validator.ValidateM

namespace TreeParserIO

structure State (α: Type) [DecidableEq α] [Hashable α] where
  parser: TreeParser.TreeParser α
  enter: MemEnter.EnterMap α
  leave: MemLeave.LeaveMap α

abbrev Impl α [DecidableEq α] [Hashable α] β := StateT (State α) (EIO String) β

def Impl.mk [DecidableEq α] [Hashable α] (p: TreeParser.TreeParser α): State α :=
  State.mk p MemEnter.EnterMap.mk MemLeave.LeaveMap.mk

def EIO.println [ToString α] (x: α): EIO String Unit :=
  IO.toEIO (fun x => "ERROR: " ++ x.toString) (IO.println x)

instance [DecidableEq α] [Hashable α] : Debug (Impl α) where
  debug (line: String) := StateT.lift (EIO.println line)

instance [DecidableEq α] [Hashable α]: MonadStateOf (TreeParser.TreeParser α) (Impl α) where
  get : Impl α (TreeParser.TreeParser α) := do
    let s <- StateT.get
    return s.parser
  set : TreeParser.TreeParser α → Impl α PUnit :=
    fun parser => do
      let s <- StateT.get
      set (State.mk parser s.enter s.leave)
  modifyGet {β: Type}: (TreeParser.TreeParser α → Prod β (TreeParser.TreeParser α)) → Impl α β :=
    fun f => do
      let s <- StateT.get
      let (res, parser) := f s.parser
      set (State.mk parser s.enter s.leave)
      return res

instance
  [DecidableEq α]
  [Hashable α]
  [Monad (Impl α)] -- EStateM is monad
  [Debug (Impl α)] -- Debug instance is declared above
  [MonadExcept String (Impl α)] -- EStateM String is MonadExcept String
  [MonadStateOf (TreeParser.TreeParser α) (Impl α)] -- MonadStateOf ParseTree.TreeParser is declared above
  : Parser (Impl α) α where -- This should just follow, but apparently we need to spell it out
  next := Parser.next
  skip := Parser.skip
  token := Parser.token

instance [DecidableEq α] [Hashable α]: MemEnter.MemEnter (Impl α) α where
  getEnter : Impl α (MemEnter.EnterMap α) := do
    let s <- StateT.get
    return s.enter
  setEnter : MemEnter.EnterMap α → Impl α PUnit :=
    fun enter => do
      let s <- StateT.get
      set (State.mk s.parser enter s.leave)

-- This should just follow from the instance declared in MemEnter, but we spell it out just in case.
instance [DecidableEq α] [Hashable α]: Enter.DeriveEnter (Impl α) α where
  deriveEnter (xs: Exprs α): Impl α (IfExprs α) := MemEnter.deriveEnter xs

instance [DecidableEq α] [Hashable α]: MemLeave.MemLeave (Impl α) α where
  getLeave : Impl α (MemLeave.LeaveMap α) := do
    let s <- StateT.get
    return s.leave
  setLeave : MemLeave.LeaveMap α → Impl α PUnit :=
    fun leave => do
      let s <- StateT.get
      set (State.mk s.parser s.enter leave)

-- This should just follow from the instance declared in MemLeave, but we spell it out just in case.
instance [DecidableEq α] [Hashable α]: Leave.DeriveLeave (Impl α) α where
  deriveLeave (xs: Exprs α) (ns: List Bool): Impl α (Exprs α) := MemLeave.deriveLeave xs ns

instance [DecidableEq α] [Hashable α]: ValidateM (Impl α) α where
  -- all instances have been created, so no implementations are required here

def run' [DecidableEq α] [Hashable α] (f: Impl α β) (t: ParseTree α): EIO String β :=
  StateT.run' f (Impl.mk (TreeParser.TreeParser.mk t))
