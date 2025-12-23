import Validator.Hedge.Grammar
import Validator.Parser.TreeParser

import Validator.Validator.ValidateM

namespace TreeParserM

abbrev Impl α β := EStateM String (TreeParser.ParserState α) β

instance : Debug (Impl α) where
  debug (_line: String) := return ()

instance
  [Monad (Impl α)] -- EStateM is monad
  [Debug (Impl α)] -- Debug instance is declared above
  [MonadExcept String (Impl α)] -- EStateM String is MonadExcept String
  [MonadStateOf (TreeParser.ParserState α) (Impl α)] -- EStateM ε Hedge.Node.TreeParser is a MonadStateOf Hedge.Node.TreeParser
  : Parser (Impl α) α where -- This should just follow, but apparently we need to spell it out
  next := Parser.next
  skip := Parser.skip
  token := Parser.token

instance : Regex.Enter.DeriveEnter (Impl α) (Symbol n φ) where
  deriveEnter xs := return Regex.Enter.enters xs

instance : Regex.Leave.DeriveLeaveM (Impl α) (Symbol n φ) where
  deriveLeaveM xs ns := Regex.LeaveSmart.deriveLeaveM xs ns

instance [DecidableEq φ] [DecidableEq α]: ValidateM (Impl α) (Symbol n φ) α where
  -- all instances have been created, so no implementations are required here

def run' (x: Impl α β) (t: Hedge.Node α): Except String β :=
  match EStateM.run x (TreeParser.ParserState.mk' t) with
  | EStateM.Result.ok k _ => Except.ok k
  | EStateM.Result.error err _ => Except.error err
