import Validator.Parser.Hint
import Validator.Parser.Token

inductive ParseError where
  | unknown (desc: String)
  deriving DecidableEq

-- * `Next : () -> (Hint | error | EOF)`
-- * `Skip : () -> (error | EOF)?`
-- * `Token: () -> (Token | error)`

class Parser (m: Type -> Type u) [Monad m] where
  next: m Hint
  skip: m Unit
  token: m Token

-- StateParser is the default Parser, where the State type (S) still needs to be specified.
def StateParser (S: Type) := Parser (StateM S)
-- Various Parsers implementations (other than StateM) are possible, just an example, here we have a parser with IO.
def IOParser := Parser IO

inductive Action where
  | next
  | skip
  | token

def walkActions [Monad m] [Parser m] (actions: List Action) (logs: List String := []): m (List String) := do
  match actions with
  | [] => return List.reverse logs
  | (Action.next::rest) => do
    match <- Parser.next with
    | Hint.eof =>
        return List.reverse (toString Hint.eof :: logs)
    | h' =>
        walkActions rest (toString h' :: logs)
  | (Action.skip::rest) => do
    _ <- Parser.skip
    walkActions rest logs
  | (Action.token::rest) => do
    walkActions rest (toString (<- Parser.token) :: logs)
