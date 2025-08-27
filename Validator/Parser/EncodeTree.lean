import Validator.Std.Except

import Validator.Parser.Hint
import Validator.Std.ParseTree
import Validator.Parser.TokenTree
import Validator.Parser.Parser
import Validator.Parser.Token
import Validator.Parser.TreeParser

namespace EncodeTree

partial def encode [Monad m] [MonadExcept String m] [Parser m α]: m (ParseForest α) := do
  match <- Parser.next with
  | Hint.enter =>
    let children <- encode
    let siblings <- encode
    return children ++ siblings
  | Hint.field =>
    let name <- Parser.token
    let children <-
      match <- Parser.next with
      -- use pure instead of return, because return would short circuit
      | Hint.value => pure [ParseTree.mk (<- Parser.token) []]
      | Hint.enter => encode
      | hint => throw s!"unexpected {hint}"
    let siblings <- encode
    return (ParseTree.mk name children) :: siblings
  | Hint.value =>
    let value <- Parser.token
    let siblings <- encode
    return (ParseTree.mk value []) :: siblings
  | Hint.leave => return []
  | Hint.eof => return []

def run (x: StateT (TreeParser.ParserState α) (Except String) β) (t: ParseTree α): Except String β :=
  StateT.run' x (TreeParser.ParserState.mk' t)

-- Tests

open TokenTree (node)

#guard run
  encode
  (node "a" []) =
  Except.ok [(node "a" [])]

#guard run
  encode
  (node "a" [node "b" []]) =
  Except.ok [(node "a" [node "b" []])]

#guard run
  encode
  (node "a" [node "b" [], node "c" [node "d" []]]) =
  Except.ok [node "a" [node "b" [], node "c" [node "d" []]]]
