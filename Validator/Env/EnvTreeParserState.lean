import Validator.Parser.TreeParser

import Validator.Env.EnvM

namespace EnvTreeParserState

abbrev TreeParserState α := EStateM String TreeParser.TreeParser α

instance : Debug TreeParserState where
  debug (_line: String) := return ()

instance
  [Monad TreeParserState] -- EStateM is monad
  [Debug TreeParserState] -- Debug instance is declared above
  [MonadExcept String TreeParserState] -- EStateM String is MonadExcept String
  [MonadStateOf TreeParser.TreeParser TreeParserState] -- EStateM ε ParseTree.TreeParser is a MonadStateOf ParseTree.TreeParser
  : Parser TreeParserState where -- This should just follow, but apparently we need to spell it out
  next := Parser.next
  skip := Parser.skip
  token := Parser.token

instance : Enter.DeriveEnter TreeParserState where
  deriveEnter xs := return Enter.deriveEnter xs

instance : Leave.DeriveLeave TreeParserState where
  deriveLeave xs ns := Leave.deriveLeave xs ns

instance : EnvM TreeParserState where
  -- all instances have been created, so no implementations are required here

def run (x: TreeParserState α) (t: ParseTree): Except String α :=
  match EStateM.run x (TreeParser.TreeParser.mk t) with
  | EStateM.Result.ok k _ => Except.ok k
  | EStateM.Result.error err _ => Except.error err
