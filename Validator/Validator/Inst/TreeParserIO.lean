import Validator.Std.Debug
import Validator.Std.Hedge
import Validator.Std.Vec

import Validator.Hedge.Grammar
import Validator.Hedge.IfExpr

import Validator.Parser.TreeParser

import Validator.Regex.EnterMem
import Validator.Regex.LeaveMem

import Validator.Validator.ValidateM

namespace TreeParserIO

structure State (n: Nat) (φ: Type) (α: Type) [DecidableEq φ] [Hashable φ] where
  parser: TreeParser.ParserState α
  enter: Regex.EnterMem.EnterMap (Hedge.Grammar.Symbol n φ)
  leave: Regex.LeaveMem.LeaveMap (Hedge.Grammar.Symbol n φ)

abbrev Impl n φ α [DecidableEq φ] [Hashable φ] β := StateT (State n φ α) (EIO String) β

def Impl.mk [DecidableEq φ] [Hashable φ] (p: TreeParser.ParserState α): State n φ α :=
  State.mk p Regex.EnterMem.EnterMap.mk Regex.LeaveMem.LeaveMap.mk

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

instance [DecidableEq φ] [Hashable φ]: EnterMem (Impl n φ α) (Hedge.Grammar.Symbol n φ) where
  getEnter : Impl n φ α (Regex.EnterMem.EnterMap (Hedge.Grammar.Symbol n φ)) := do
    let s <- StateT.get
    return s.enter
  setEnter : Regex.EnterMem.EnterMap (Hedge.Grammar.Symbol n φ) → Impl n φ α PUnit :=
    fun enter => do
      let s <- StateT.get
      set (State.mk s.parser enter s.leave)

-- This should just follow from the instance declared in EnterMem, but we spell it out just in case.
instance [DecidableEq φ] [Hashable φ]: Regex.Enter.DeriveEnter (Impl n φ α) (Hedge.Grammar.Symbol n φ) where
  deriveEnter {l: Nat} (xs: Hedge.Grammar.Rules n φ l): Impl n φ α (Hedge.Grammar.Symbols n φ (Regex.Symbol.nums xs)) := Regex.EnterMem.deriveEnter xs

instance [DecidableEq φ] [Hashable φ]: LeaveMem (Impl n φ α) (Hedge.Grammar.Symbol n φ) where
  getLeave : Impl n φ α (Regex.LeaveMem.LeaveMap (Hedge.Grammar.Symbol n φ)) := do
    let s <- StateT.get
    return s.leave
  setLeave : Regex.LeaveMem.LeaveMap (Hedge.Grammar.Symbol n φ) → Impl n φ α PUnit :=
    fun leave => do
      let s <- StateT.get
      set (State.mk s.parser s.enter leave)

-- This should just follow from the instance declared in LeaveMem, but we spell it out just in case.
instance [DecidableEq φ] [Hashable φ]: Regex.Leave.DeriveLeaveM (Impl n φ α) (Hedge.Grammar.Symbol n φ) where
  deriveLeaveM {l: Nat} (xs: Hedge.Grammar.Rules n φ l) (ns: Vec Bool (Regex.Symbol.nums xs)): Impl n φ α (Hedge.Grammar.Rules n φ l) := Regex.LeaveMem.deriveLeaveM xs ns

instance [DecidableEq φ] [Hashable φ]: ValidateM (Impl n φ α) (Hedge.Grammar.Symbol n φ) α where
  -- all instances have been created, so no implementations are required here

def run' [DecidableEq φ] [Hashable φ] (f: Impl n φ α β) (t: Hedge.Node α): EIO String β :=
  StateT.run' f (Impl.mk (TreeParser.ParserState.mk' t))
