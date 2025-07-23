import Validator.Std.Debug

import Validator.Parser.Hint
import Validator.Parser.Token

-- TODO: explain error is in except monad and state is also in m, but could also use IO
class Parser (m: Type -> Type u) (α: outParam Type) where
  next: m Hint
  skip: m Unit
  token: m α

namespace Parser

-- example: StateParser is the default Parser, where the State type (S) still needs to be specified.
example (S: Type) (α: Type) := Parser (StateT S (Except String)) α
-- example: Various Parsers implementations (other than StateT) are possible, just an example, here we have a parser with IO.
example α := IO α

inductive Action where
  | next
  | skip
  | token

def walk [ToString α] [Parser m α] [Monad m] [Debug m] (actions: List Action) (logs: List String := []): m (List String) := do
  match actions with
  | [] => return List.reverse logs
  | (Action.next::rest) => do
    match <- Parser.next with
    | Hint.eof => return List.reverse (toString Hint.eof :: logs)
    | h' => walk rest (toString h' :: logs)
  | (Action.skip::rest) => do
    _ <- Parser.skip
    walk rest logs
  | (Action.token::rest) => do
    let tok: α <- Parser.token
    walk rest ((toString tok) :: logs)
