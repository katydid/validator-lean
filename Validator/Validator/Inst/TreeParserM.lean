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

instance : Enter.DeriveEnter (Impl α) n α where
  deriveEnter xs := return Enter.deriveEnter xs

instance : Leave.DeriveLeaveM (Impl α) n α where
  deriveLeaveM xs ns := Leave.deriveLeaveM xs ns

instance [DecidableEq α]: ValidateM (Impl α) n α where
  -- all instances have been created, so no implementations are required here

def run' (x: Impl α β) (t: Hedge.Node α): Except String β :=
  match EStateM.run x (TreeParser.ParserState.mk' t) with
  | EStateM.Result.ok k _ => Except.ok k
  | EStateM.Result.error err _ => Except.error err
