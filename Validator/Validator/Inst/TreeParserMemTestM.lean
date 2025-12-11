import Validator.Std.Debug
import Validator.Std.Vec

import Validator.Memoize.MemEnter
import Validator.Memoize.MemLeave

import Validator.Validator.Inst.TreeParserMemM
import Validator.Validator.ValidateM

namespace TreeParserMemTestM

structure State (n: Nat) (α: Type) [DecidableEq α] [Hashable α] where
  parser: TreeParser.ParserState α
  enter: MemEnter.EnterMap n α
  leave: MemLeave.LeaveMap n α
  logs: List String

abbrev Impl n (α: Type) [DecidableEq α] [Hashable α] β := EStateM String (State n α) β

def Impl.mk [DecidableEq α] [Hashable α] (p: TreeParser.ParserState α): State n α :=
  State.mk p MemEnter.EnterMap.mk MemLeave.LeaveMap.mk []

instance [DecidableEq α] [Hashable α]: Debug (Impl n α) where
  debug (line: String) := do
    let s <- EStateM.get
    set (State.mk s.parser s.enter s.leave (s.logs ++ [line]))
    return ()

instance [DecidableEq α] [Hashable α]: MonadStateOf (TreeParser.ParserState α) (Impl n α) where
  get : Impl n α (TreeParser.ParserState α) := do
    let s <- EStateM.get
    return s.parser
  set : TreeParser.ParserState α → Impl n α PUnit :=
    fun parser => do
      let s <- EStateM.get
      EStateM.set (State.mk parser s.enter s.leave s.logs)
  modifyGet {β: Type}: (TreeParser.ParserState α → Prod β (TreeParser.ParserState α)) → Impl n α β :=
    fun f => do
      let s <- EStateM.get
      let (res, parser) := f s.parser
      EStateM.set (State.mk parser s.enter s.leave s.logs)
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
    let s <- EStateM.get
    return s.enter
  setEnter : MemEnter.EnterMap n α → Impl n α PUnit :=
    fun enter => do
      let s <- EStateM.get
      set (State.mk s.parser enter s.leave s.logs)

-- This should just follow from the instance declared in MemEnter, but we spell it out just in case.
instance [DecidableEq α] [Hashable α]: Enter.DeriveEnter (Impl n α) n α where
  deriveEnter {l: Nat} (xs: Rules n (Pred α) l): Impl n α (IfExprs n α (Symbol.nums xs)) := do
    let memoized <- MemEnter.getEnter
    match MemEnter.get? memoized xs with
    | Option.none =>
      throw "test cache miss"
    | Option.some value =>
      Debug.debug "test cache hit"
      return value

instance [DecidableEq α] [Hashable α]: MemLeave (Impl n α) n α where
  getLeave : Impl n α (MemLeave.LeaveMap n α) := do
    let s <- EStateM.get
    return s.leave
  setLeave : MemLeave.LeaveMap n α → Impl n α PUnit :=
    fun leave => do
      let s <- EStateM.get
      set (State.mk s.parser s.enter leave s.logs)

-- This should just follow from the instance declared in MemLeave, but we spell it out just in case.
instance [DecidableEq α] [Hashable α]: Leave.DeriveLeaveM (Impl n α) n α where
  deriveLeaveM {l: Nat} (xs: Rules n (Pred α) l) (ns: Vec Bool (Symbol.nums xs)): Impl n α (Rules n (Pred α) l) := do
    let memoized <- MemLeave.getLeave
    match MemLeave.get? memoized ⟨xs, ns⟩ with
    | Option.none =>
      throw "test cache miss"
    | Option.some value =>
      Debug.debug "test cache hit"
      return value

instance [DecidableEq α] [Hashable α]: ValidateM (Impl n α) n α where
  -- all instances have been created, so no implementations are required here

def runPopulatedMem
  [DecidableEq α] [Hashable α]
  (f: Impl n α β) (t: Hedge.Node α) (e: MemEnter.EnterMap n α) (l: MemLeave.LeaveMap n α): EStateM.Result String (State n α) β :=
  EStateM.run f (State.mk (TreeParser.ParserState.mk' t) e l [])

def run'
  [DecidableEq α] [Hashable α]
  (f: Impl n α β) (t: Hedge.Node α): Except String β :=
  match EStateM.run f (Impl.mk (TreeParser.ParserState.mk' t)) with
  | EStateM.Result.ok k _ => Except.ok k
  | EStateM.Result.error err _ => Except.error err
