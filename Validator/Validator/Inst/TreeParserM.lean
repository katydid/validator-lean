import Validator.Parser.TreeParser

import Validator.Validator.ValidateM

namespace TreeParserM

abbrev TreeParserM α := EStateM String TreeParser.TreeParser α

instance : Debug TreeParserM where
  debug (_line: String) := return ()

instance
  [Monad TreeParserM] -- EStateM is monad
  [Debug TreeParserM] -- Debug instance is declared above
  [MonadExcept String TreeParserM] -- EStateM String is MonadExcept String
  [MonadStateOf TreeParser.TreeParser TreeParserM] -- EStateM ε ParseTree.TreeParser is a MonadStateOf ParseTree.TreeParser
  : Parser TreeParserM where -- This should just follow, but apparently we need to spell it out
  next := Parser.next
  skip := Parser.skip
  token := Parser.token

instance : Enter.DeriveEnter TreeParserM where
  deriveEnter xs := return Enter.deriveEnter xs

instance : Leave.DeriveLeave TreeParserM where
  deriveLeave xs ns := Leave.deriveLeave xs ns

instance : ValidateM TreeParserM where
  -- all instances have been created, so no implementations are required here

def run (x: TreeParserM α) (t: ParseTree): Except String α :=
  match EStateM.run x (TreeParser.TreeParser.mk t) with
  | EStateM.Result.ok k _ => Except.ok k
  | EStateM.Result.error err _ => Except.error err
