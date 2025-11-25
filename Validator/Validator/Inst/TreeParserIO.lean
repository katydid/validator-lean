import Validator.Std.Debug

import Validator.Std.Hedge
import Validator.Parser.TreeParser

import Validator.Memoize.MemEnter
import Validator.Memoize.MemLeave

import Validator.Validator.ValidateM

namespace TreeParserIO

structure State (n: Nat) (α: Type) [DecidableEq α] [Hashable α] where
  parser: TreeParser.ParserState α
  enter: MemEnter.EnterMap n α
  leave: MemLeave.LeaveMap n α

abbrev Impl n α [DecidableEq α] [Hashable α] β := StateT (State n α) (EIO String) β

def Impl.mk [DecidableEq α] [Hashable α] (p: TreeParser.ParserState α): State n α :=
  State.mk p MemEnter.EnterMap.mk MemLeave.LeaveMap.mk

def EIO.println [ToString α] (x: α): EIO String Unit :=
  IO.toEIO (fun x => "ERROR: " ++ x.toString) (IO.println x)

instance [DecidableEq α] [Hashable α] : Debug (Impl n α) where
  debug (line: String) := StateT.lift (EIO.println line)

instance [DecidableEq α] [Hashable α]: MonadStateOf (TreeParser.ParserState α) (Impl n α) where
  get : Impl n α (TreeParser.ParserState α) := do
    let s <- StateT.get
    return s.parser
  set : TreeParser.ParserState α → Impl n α PUnit :=
    fun parser => do
      let s <- StateT.get
      set (State.mk parser s.enter s.leave)
  modifyGet {β: Type}: (TreeParser.ParserState α → Prod β (TreeParser.ParserState α)) → Impl n α β :=
    fun f => do
      let s <- StateT.get
      let (res, parser) := f s.parser
      set (State.mk parser s.enter s.leave)
      return res

instance
  [DecidableEq α]
  [Hashable α]
  [Monad (Impl n α)] -- EStateM is monad
  [Debug (Impl n α)] -- Debug instance is declared above
  [MonadExcept String (Impl n α)] -- EStateM String is MonadExcept String
  [MonadStateOf (TreeParser.ParserState α) (Impl n α)] -- MonadStateOf Hedge.Node.TreeParser is declared above
  : Parser (Impl n α) α where -- This should just follow, but apparently we need to spell it out
  next := Parser.next
  skip := Parser.skip
  token := Parser.token

instance [DecidableEq α] [Hashable α]: MemEnter (Impl n α) n α where
  getEnter : Impl n α (MemEnter.EnterMap n α) := do
    let s <- StateT.get
    return s.enter
  setEnter : MemEnter.EnterMap n α → Impl n α PUnit :=
    fun enter => do
      let s <- StateT.get
      set (State.mk s.parser enter s.leave)

-- This should just follow from the instance declared in MemEnter, but we spell it out just in case.
instance [DecidableEq α] [Hashable α]: Enter.DeriveEnter (Impl n α) n α where
  deriveEnter {l: Nat} (xs: Rules n (Pred α) l): Impl n α (IfExprs n α (Symbol.nums xs)) := MemEnter.deriveEnter xs

instance [DecidableEq α] [Hashable α]: MemLeave (Impl n α) n α where
  getLeave : Impl n α (MemLeave.LeaveMap n α) := do
    let s <- StateT.get
    return s.leave
  setLeave : MemLeave.LeaveMap n α → Impl n α PUnit :=
    fun leave => do
      let s <- StateT.get
      set (State.mk s.parser s.enter leave)

-- This should just follow from the instance declared in MemLeave, but we spell it out just in case.
instance [DecidableEq α] [Hashable α]: Leave.DeriveLeaveM (Impl n α) n α where
  deriveLeaveM {l: Nat} (xs: Rules n (Pred α) l) (ns: List.Vector Bool (Symbol.nums xs)): Impl n α (Rules n (Pred α) l) := MemLeave.deriveLeaveM xs ns

instance [DecidableEq α] [Hashable α]: ValidateM (Impl n α) n α where
  -- all instances have been created, so no implementations are required here

def run' [DecidableEq α] [Hashable α] (f: Impl n α β) (t: Hedge.Node α): EIO String β :=
  StateT.run' f (Impl.mk (TreeParser.ParserState.mk' t))
