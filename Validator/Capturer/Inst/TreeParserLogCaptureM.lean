import Validator.Std.Debug

import Validator.Std.ParseTree
import Validator.Parser.TreeParser

import Validator.Capturer.CaptureM

namespace TreeParserLogCaptureM

structure State (α: Type) where
  parser: TreeParser.ParserState α
  logs : List String

abbrev Impl α β := EStateM String (State α) β

def Impl.mk (p: TreeParser.ParserState α): State α :=
  State.mk p []

instance : Debug (Impl α) where
  debug (line: String) := do
    let s <- EStateM.get
    set (State.mk s.parser (s.logs ++ [line]))
    return ()

instance: MonadStateOf (TreeParser.ParserState α) (Impl α) where
  get : Impl α (TreeParser.ParserState α) := do
    let s <- EStateM.get
    return s.parser
  set : TreeParser.ParserState α → Impl α PUnit :=
    fun parser => do
      let s <- EStateM.get
      EStateM.set (State.mk parser s.logs)
  modifyGet {β: Type}: (TreeParser.ParserState α → Prod β (TreeParser.ParserState α)) → Impl α β :=
    fun f => do
      let s <- EStateM.get
      let (res, parser) := f s.parser
      EStateM.set (State.mk parser s.logs)
      return res

instance
  [Monad (Impl α)] -- EStateM is monad
  [Debug (Impl α)] -- Debug instance is declared above
  [MonadExcept String (Impl α)] -- EStateM String is MonadExcept String
  [MonadStateOf (TreeParser.ParserState α) (Impl α)] -- MonadStateOf ParseTree.TreeParser is declared above
  : Parser (Impl α) α where -- This should just follow, but apparently we need to spell it out
  next := Parser.next
  skip := Parser.skip
  token := Parser.token

instance : CaptureM (Impl α) α where
  -- all instances have been created, so no implementations are required here

def run (f: Impl α β) (forest: ParseForest α): EStateM.Result String (State α) β :=
  EStateM.run f (Impl.mk (TreeParser.ParserState.mks forest))

def run' (f: Impl α β) (forest: ParseForest α): (List String × (Except String β)) :=
  match EStateM.run f (Impl.mk (TreeParser.ParserState.mks forest)) with
  | EStateM.Result.ok res s => (s.logs, Except.ok res)
  | EStateM.Result.error err s => (s.logs, Except.error err)
