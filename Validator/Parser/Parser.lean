import Validator.Parser.Hint
import Validator.Parser.Token

-- * `Next : () -> (Hint | error | EOF)`
-- * `Skip : () -> (error | EOF)?`
-- * `Token: () -> (Token | error)`

class Parser (m: Type -> Type u) [Monad m] where
  next: m Hint
  skip: m Unit
  token: m Token

namespace Parser

-- StateParser is the default Parser, where the State type (S) still needs to be specified.
private def StateParser (S: Type) := Parser (StateM S)
-- Various Parsers implementations (other than StateM) are possible, just an example, here we have a parser with IO.
private def IOParser := Parser IO

inductive Error where
  | unknown (desc: String)
  deriving DecidableEq

inductive Action where
  | next
  | skip
  | token

def walk [Monad m] [Parser m] (actions: List Action) (logs: List String := []): m (List String) := do
  match actions with
  | [] => return List.reverse logs
  | (Action.next::rest) => do
    match <- Parser.next with
    | Hint.eof =>
        return List.reverse (toString Hint.eof :: logs)
    | h' =>
        walk rest (toString h' :: logs)
  | (Action.skip::rest) => do
    _ <- Parser.skip
    walk rest logs
  | (Action.token::rest) => do
    walk rest (toString (<- Parser.token) :: logs)
