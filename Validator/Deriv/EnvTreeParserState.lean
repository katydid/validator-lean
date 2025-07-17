import Validator.Deriv.Env

namespace EnvTreeParserState

abbrev TreeParserState α := EStateM String ParseTree.TreeParser α

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
