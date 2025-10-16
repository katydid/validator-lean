import Validator.Std.Debug

import Validator.Memoize.MemEnter
import Validator.Memoize.MemLeave

import Validator.Validator.Inst.TreeParserMemM
import Validator.Validator.ValidateM

namespace TreeParserMemTestM

structure State (μ: Nat) (α: Type) [DecidableEq α] [Hashable α] where
  parser: TreeParser.ParserState α
  enter: MemEnter.EnterMap μ α
  leave: MemLeave.LeaveMap μ α
  logs: List String

abbrev Impl μ (α: Type) [DecidableEq α] [Hashable α] β := EStateM String (State μ α) β

def Impl.mk [DecidableEq α] [Hashable α] (p: TreeParser.ParserState α): State μ α :=
  State.mk p MemEnter.EnterMap.mk MemLeave.LeaveMap.mk []

instance [DecidableEq α] [Hashable α]: Debug (Impl μ α) where
  debug (line: String) := do
    let s <- EStateM.get
    set (State.mk s.parser s.enter s.leave (s.logs ++ [line]))
    return ()

instance [DecidableEq α] [Hashable α]: MonadStateOf (TreeParser.ParserState α) (Impl μ α) where
  get : Impl μ α (TreeParser.ParserState α) := do
    let s <- EStateM.get
    return s.parser
  set : TreeParser.ParserState α → Impl μ α PUnit :=
    fun parser => do
      let s <- EStateM.get
      EStateM.set (State.mk parser s.enter s.leave s.logs)
  modifyGet {β: Type}: (TreeParser.ParserState α → Prod β (TreeParser.ParserState α)) → Impl μ α β :=
    fun f => do
      let s <- EStateM.get
      let (res, parser) := f s.parser
      EStateM.set (State.mk parser s.enter s.leave s.logs)
      return res

instance
  [DecidableEq α]
  [Hashable α]
  [Monad (Impl μ α)] -- EStateM is monad
  [Debug (Impl μ α)] -- Debug instance is declared above
  [MonadExcept String (Impl μ α)] -- EStateM String is MonadExcept String
  [MonadStateOf (TreeParser.ParserState α) (Impl μ α)] -- MonadStateOf Hedge.Node.TreeParser is declared above
  : Parser (Impl μ α) α where -- This should just follow, but apparently we need to spell it out
  next := Parser.next
  skip := Parser.skip
  token := Parser.token

instance [DecidableEq α] [Hashable α]: MemEnter (Impl μ α) μ α where
  getEnter : Impl μ α (MemEnter.EnterMap μ α) := do
    let s <- EStateM.get
    return s.enter
  setEnter : MemEnter.EnterMap μ α → Impl μ α PUnit :=
    fun enter => do
      let s <- EStateM.get
      set (State.mk s.parser enter s.leave s.logs)

-- This should just follow from the instance declared in MemEnter, but we spell it out just in case.
instance [DecidableEq α] [Hashable α]: Enter.DeriveEnter (Impl μ α) μ α where
  deriveEnter (xs: Exprs μ α): Impl μ α (IfExprs μ α) := do
    let memoized <- MemEnter.getEnter
    match memoized.get? xs with
    | Option.none =>
      throw "test cache miss"
    | Option.some value =>
      Debug.debug "test cache hit"
      return value

instance [DecidableEq α] [Hashable α]: MemLeave (Impl μ α) μ α where
  getLeave : Impl μ α (MemLeave.LeaveMap μ α) := do
    let s <- EStateM.get
    return s.leave
  setLeave : MemLeave.LeaveMap μ α → Impl μ α PUnit :=
    fun leave => do
      let s <- EStateM.get
      set (State.mk s.parser s.enter leave s.logs)

-- This should just follow from the instance declared in MemLeave, but we spell it out just in case.
instance [DecidableEq α] [Hashable α]: Leave.DeriveLeaveM (Impl μ α) μ α where
  deriveLeaveM (xs: Exprs μ α) (ns: List Bool): Impl μ α (Exprs μ α) := do
    let memoized <- MemLeave.getLeave
    match memoized.get? (xs, ns) with
    | Option.none =>
      throw "test cache miss"
    | Option.some value =>
      Debug.debug "test cache hit"
      return value

instance [DecidableEq α] [Hashable α]: ValidateM (Impl μ α) μ α  where
  -- all instances have been created, so no implementations are required here

def runPopulatedMem
  [DecidableEq α] [Hashable α]
  (f: Impl μ α β) (t: Hedge.Node α) (e: MemEnter.EnterMap μ α) (l: MemLeave.LeaveMap μ α): EStateM.Result String (State μ α) β :=
  EStateM.run f (State.mk (TreeParser.ParserState.mk' t) e l [])

def run'
  [DecidableEq α] [Hashable α]
  (f: Impl μ α β) (t: Hedge.Node α): Except String β :=
  match EStateM.run f (Impl.mk (TreeParser.ParserState.mk' t)) with
  | EStateM.Result.ok k _ => Except.ok k
  | EStateM.Result.error err _ => Except.error err
