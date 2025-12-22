import Validator.Std.Debug
import Validator.Std.Vec

import Validator.Memoize.MemEnter
import Validator.Memoize.MemLeave

import Validator.Validator.Inst.TreeParserMemM
import Validator.Validator.ValidateM

namespace TreeParserMemTestM

structure State (n: Nat) (φ: Type) (α: Type) [DecidableEq φ] [Hashable φ] where
  parser: TreeParser.ParserState α
  enter: MemEnter.EnterMap n φ
  leave: MemLeave.LeaveMap n φ
  logs: List String

abbrev Impl n (φ: Type) (α: Type) [DecidableEq φ] [Hashable φ] β := EStateM String (State n φ α) β

def Impl.mk [DecidableEq φ] [Hashable φ] (p: TreeParser.ParserState α): State n φ α :=
  State.mk p MemEnter.EnterMap.mk MemLeave.LeaveMap.mk []

instance [DecidableEq φ] [Hashable φ]: Debug (Impl n φ α) where
  debug (line: String) := do
    let s <- EStateM.get
    set (State.mk s.parser s.enter s.leave (s.logs ++ [line]))
    return ()

instance [DecidableEq φ] [Hashable φ]: MonadStateOf (TreeParser.ParserState α) (Impl n φ α) where
  get : Impl n φ α (TreeParser.ParserState α) := do
    let s <- EStateM.get
    return s.parser
  set : TreeParser.ParserState α → Impl n φ α PUnit :=
    fun parser => do
      let s <- EStateM.get
      EStateM.set (State.mk parser s.enter s.leave s.logs)
  modifyGet {β: Type}: (TreeParser.ParserState α → Prod β (TreeParser.ParserState α)) → Impl n φ α β :=
    fun f => do
      let s <- EStateM.get
      let (res, parser) := f s.parser
      EStateM.set (State.mk parser s.enter s.leave s.logs)
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
    let s <- EStateM.get
    return s.enter
  setEnter : MemEnter.EnterMap n φ → Impl n φ α PUnit :=
    fun enter => do
      let s <- EStateM.get
      set (State.mk s.parser enter s.leave s.logs)

-- This should just follow from the instance declared in MemEnter, but we spell it out just in case.
instance [DecidableEq φ] [Hashable φ]: Enter.DeriveEnter (Impl n φ α) (Symbol n φ) where
  deriveEnter {l: Nat} (xs: Rules n φ l): Impl n φ α (IfExprs n φ (Symbol.nums xs)) := do
    let memoized <- MemEnter.getEnter
    match MemEnter.get? memoized xs with
    | Option.none =>
      throw "test cache miss"
    | Option.some value =>
      Debug.debug "test cache hit"
      return value

instance [DecidableEq φ] [Hashable φ]: MemLeave (Impl n φ α) n φ where
  getLeave : Impl n φ α (MemLeave.LeaveMap n φ) := do
    let s <- EStateM.get
    return s.leave
  setLeave : MemLeave.LeaveMap n φ → Impl n φ α PUnit :=
    fun leave => do
      let s <- EStateM.get
      set (State.mk s.parser s.enter leave s.logs)

-- This should just follow from the instance declared in MemLeave, but we spell it out just in case.
instance [DecidableEq φ] [Hashable φ]: LeaveSmart.DeriveLeaveM (Impl n φ α) (Symbol n φ) where
  deriveLeaveM {l: Nat} (xs: Rules n φ l) (ns: Vec Bool (Symbol.nums xs)): Impl n φ α (Rules n φ l) := do
    let memoized <- MemLeave.getLeave
    match MemLeave.get? memoized ⟨xs, ns⟩ with
    | Option.none =>
      throw "test cache miss"
    | Option.some value =>
      Debug.debug "test cache hit"
      return value

instance [DecidableEq φ] [Hashable φ]: ValidateM (Impl n φ α) (Symbol n φ) α where
  -- all instances have been created, so no implementations are required here

def runPopulatedMem
  [DecidableEq φ] [Hashable φ]
  (f: Impl n φ α β) (t: Hedge.Node α) (e: MemEnter.EnterMap n φ) (l: MemLeave.LeaveMap n φ): EStateM.Result String (State n φ α) β :=
  EStateM.run f (State.mk (TreeParser.ParserState.mk' t) e l [])

def run'
  [DecidableEq φ] [Hashable φ]
  (f: Impl n φ α β) (t: Hedge.Node α): Except String β :=
  match EStateM.run f (Impl.mk (TreeParser.ParserState.mk' t)) with
  | EStateM.Result.ok k _ => Except.ok k
  | EStateM.Result.error err _ => Except.error err
