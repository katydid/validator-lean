import Validator.Std.Debug
import Validator.Std.Hedge
import Validator.Std.Vec

import Validator.Parser.TreeParser

import Validator.Memoize.MemEnter
import Validator.Memoize.MemLeave

import Validator.Validator.ValidateM

namespace TreeParserIO

structure State (n: Nat) (φ: Type) (α: Type) [DecidableEq φ] [Hashable φ] where
  parser: TreeParser.ParserState α
  enter: MemEnter.EnterMap n φ
  leave: MemLeave.LeaveMap n φ

abbrev Impl n φ α [DecidableEq φ] [Hashable φ] β := StateT (State n φ α) (EIO String) β

def Impl.mk [DecidableEq φ] [Hashable φ] (p: TreeParser.ParserState α): State n φ α :=
  State.mk p MemEnter.EnterMap.mk MemLeave.LeaveMap.mk

def EIO.println [ToString α] (x: α): EIO String Unit :=
  IO.toEIO (fun x => "ERROR: " ++ x.toString) (IO.println x)

instance [DecidableEq φ] [Hashable φ] : Debug (Impl n φ α) where
  debug (line: String) := StateT.lift (EIO.println line)

instance [DecidableEq φ] [Hashable φ]: MonadStateOf (TreeParser.ParserState α) (Impl n φ α) where
  get : Impl n φ α (TreeParser.ParserState α) := do
    let s <- StateT.get
    return s.parser
  set : TreeParser.ParserState α → Impl n φ α PUnit :=
    fun parser => do
      let s <- StateT.get
      set (State.mk parser s.enter s.leave)
  modifyGet {β: Type}: (TreeParser.ParserState α → Prod β (TreeParser.ParserState α)) → Impl n φ α β :=
    fun f => do
      let s <- StateT.get
      let (res, parser) := f s.parser
      set (State.mk parser s.enter s.leave)
      return res

instance
  [DecidableEq φ]
  [Hashable φ]
  [Monad (Impl n φ α)] -- EStateM is monad
  [Debug (Impl n φ α)] -- Debug instance is declared above
  [MonadExcept String (Impl n φ α)] -- EStateM String is MonadExcept String
  [MonadStateOf (TreeParser.ParserState α) (Impl n φ α)] -- MonadStateOf Hedge.Node.TreeParser is declared above
  : Parser (Impl n φ α) α where -- This should just follow, but apparently we need to spell it out
  next := Parser.next
  skip := Parser.skip
  token := Parser.token

instance [DecidableEq φ] [Hashable φ]: MemEnter (Impl n φ α) n φ where
  getEnter : Impl n φ α (MemEnter.EnterMap n φ) := do
    let s <- StateT.get
    return s.enter
  setEnter : MemEnter.EnterMap n φ → Impl n φ α PUnit :=
    fun enter => do
      let s <- StateT.get
      set (State.mk s.parser enter s.leave)

-- This should just follow from the instance declared in MemEnter, but we spell it out just in case.
instance [DecidableEq φ] [Hashable φ]: Enter.DeriveEnter (Impl n φ α) (Symbol n φ) where
  deriveEnter {l: Nat} (xs: Rules n φ l): Impl n φ α (IfExprs n φ (Symbol.nums xs)) := MemEnter.deriveEnter xs

instance [DecidableEq φ] [Hashable φ]: MemLeave (Impl n φ α) n φ where
  getLeave : Impl n φ α (MemLeave.LeaveMap n φ) := do
    let s <- StateT.get
    return s.leave
  setLeave : MemLeave.LeaveMap n φ → Impl n φ α PUnit :=
    fun leave => do
      let s <- StateT.get
      set (State.mk s.parser s.enter leave)

-- This should just follow from the instance declared in MemLeave, but we spell it out just in case.
instance [DecidableEq φ] [Hashable φ]: LeaveSmart.DeriveLeaveM (Impl n φ α) (Symbol n φ) where
  deriveLeaveM {l: Nat} (xs: Rules n φ l) (ns: Vec Bool (Symbol.nums xs)): Impl n φ α (Rules n φ l) := MemLeave.deriveLeaveM xs ns

instance [DecidableEq φ] [Hashable φ]: ValidateM (Impl n φ α) (Symbol n φ) α where
  -- all instances have been created, so no implementations are required here

def run' [DecidableEq φ] [Hashable φ] (f: Impl n φ α β) (t: Hedge.Node α): EIO String β :=
  StateT.run' f (Impl.mk (TreeParser.ParserState.mk' t))
