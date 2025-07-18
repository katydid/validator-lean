import Validator.Deriv.Env

namespace EnvTreeParserState

abbrev TreeParserState α := EStateM String ParseTree.TreeParser α

instance : Debug TreeParserState where
  debug (_line: String) := return ()

instance
  [Monad TreeParserState] -- EStateM is monad
  [Debug TreeParserState] -- Debug instance is declared above
  [MonadExcept String TreeParserState] -- EStateM String is MonadExcept String
  [MonadStateOf ParseTree.TreeParser TreeParserState] -- EStateM ε ParseTree.TreeParser is a MonadStateOf ParseTree.TreeParser
  : Parser TreeParserState where -- This should just follow, but apparently we need to spell it out
  next := Parser.next
  skip := Parser.skip
  token := Parser.token

instance : Enter.DeriveEnters TreeParserState where
  deriveEnters xs := return Enter.enters xs

instance : Leave.DeriveLeaves TreeParserState where
  deriveLeaves xs ns := Leave.leaves xs ns

instance : Env TreeParserState where
  -- all instances have been created, so no implementations are required here

def run (x: TreeParserState α) (t: ParseTree): Except String α :=
  match EStateM.run x (ParseTree.TreeParser.mk t) with
  | EStateM.Result.ok k _ => Except.ok k
  | EStateM.Result.error err _ => Except.error err
