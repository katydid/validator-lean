import Validator.Std.Debug

import Validator.Parser.ParseTree
import Validator.Parser.TreeParser

import Validator.Capturer.CaptureM

namespace TreeParserLogCaptureM

structure State where
  parser: TreeParser.TreeParser
  logs : List String

abbrev Impl α := EStateM String State α

def Impl.mk (p: TreeParser.TreeParser): State :=
  State.mk p []

instance : Debug Impl where
  debug (line: String) := do
    let s <- EStateM.get
    set (State.mk s.parser (s.logs ++ [line]))
    return ()

instance: MonadStateOf TreeParser.TreeParser Impl where
  get : Impl TreeParser.TreeParser := do
    let s <- EStateM.get
    return s.parser
  set : TreeParser.TreeParser → Impl PUnit :=
    fun parser => do
      let s <- EStateM.get
      EStateM.set (State.mk parser s.logs)
  modifyGet {α: Type}: (TreeParser.TreeParser → Prod α TreeParser.TreeParser) → Impl α :=
    fun f => do
      let s <- EStateM.get
      let (res, parser) := f s.parser
      EStateM.set (State.mk parser s.logs)
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

instance : CaptureM Impl where
  -- all instances have been created, so no implementations are required here

def run (f: Impl α) (forest: List ParseTree): EStateM.Result String State α :=
  EStateM.run f (Impl.mk (TreeParser.TreeParser.mks forest))

def run' (f: Impl α) (forest: List ParseTree): (List String × (Except String α)) :=
  match EStateM.run f (Impl.mk (TreeParser.TreeParser.mks forest)) with
  | EStateM.Result.ok res s => (s.logs, Except.ok res)
  | EStateM.Result.error err s => (s.logs, Except.error err)
