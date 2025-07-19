import Validator.Parser.TreeParser

import Validator.Validator.ValidateM

namespace TreeParserM

abbrev Impl α := EStateM String TreeParser.TreeParser α

instance : Debug Impl where
  debug (_line: String) := return ()

instance
  [Monad Impl] -- EStateM is monad
  [Debug Impl] -- Debug instance is declared above
  [MonadExcept String Impl] -- EStateM String is MonadExcept String
  [MonadStateOf TreeParser.TreeParser Impl] -- EStateM ε ParseTree.TreeParser is a MonadStateOf ParseTree.TreeParser
  : Parser Impl where -- This should just follow, but apparently we need to spell it out
  next := Parser.next
  skip := Parser.skip
  token := Parser.token

instance : Enter.DeriveEnter Impl where
  deriveEnter xs := return Enter.deriveEnter xs

instance : Leave.DeriveLeave Impl where
  deriveLeave xs ns := Leave.deriveLeave xs ns

instance : ValidateM Impl where
  -- all instances have been created, so no implementations are required here

def run' (x: Impl α) (t: ParseTree): Except String α :=
  match EStateM.run x (TreeParser.TreeParser.mk t) with
  | EStateM.Result.ok k _ => Except.ok k
  | EStateM.Result.error err _ => Except.error err
