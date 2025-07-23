import Validator.Std.Debug
import Validator.Std.Except

import Validator.Parser.Token
import Validator.Parser.TokenTree
import Validator.Parser.Stack
import Validator.Parser.ParseTree
import Validator.Parser.Parser

namespace TreeParser

inductive ParserState (α: Type) where
  | unknown (children: ParseForest α)
  | opened (nexts: ParseForest α)
  | value (v: α) (nexts: ParseForest α)
  | pair (f v: α) (nexts: ParseForest α)
  | field (f: α) (children: ParseForest α)
  | eof

abbrev TreeParser α := Stack (ParserState α)

def TreeParser.pop [Monad m] [MonadStateOf (TreeParser α) m]: m Bool :=
  Stack.pop (α := ParserState α)

def TreeParser.mk (tree: ParseTree α): TreeParser α :=
  Stack.mk (ParserState.unknown [tree]) []

def TreeParser.mks (forest: ParseForest α): TreeParser α :=
  Stack.mk (ParserState.unknown forest) []

def nextNode
  [Monad m] [Debug m] [MonadExcept String m] [MonadStateOf (TreeParser α) m]
  (current: ParseTree α) (nexts: ParseForest α): m Hint := do
  match current with
  | ParseTree.mk v [] =>
    Stack.setCurrent (ParserState.value v nexts)
    return Hint.value
  | ParseTree.mk f [ParseTree.mk v []] =>
    Stack.setCurrent (ParserState.pair f v nexts)
    return Hint.field
  | ParseTree.mk f children =>
    Stack.setCurrent (ParserState.opened nexts)
    Stack.push (ParserState.field f children)
    return Hint.field

def next
  [Monad m] [Debug m] [MonadExcept String m] [MonadStateOf (TreeParser α) m]
  : m Hint := do
  Debug.debug "next"
  let curr <- Stack.getCurrent
  match curr with
  | ParserState.unknown f =>
    Stack.setCurrent (ParserState.opened f)
    return Hint.enter
  | ParserState.opened [] =>
    let popped <- (TreeParser.pop (α := α))
    if not popped then Stack.setCurrent (@ParserState.eof α)
    return Hint.leave
  | ParserState.opened (t::ts) =>
    nextNode t ts
  | ParserState.value _ [] =>
    let popped <- (TreeParser.pop (α := α))
    if not popped then Stack.setCurrent (@ParserState.eof α)
    return Hint.leave
  | ParserState.value _ (t::ts) =>
    nextNode t ts
  | ParserState.pair _ v nexts =>
    Stack.setCurrent (ParserState.value v nexts)
    return Hint.value
  | ParserState.field _ children =>
    Stack.setCurrent (ParserState.opened children)
    return Hint.enter
  | ParserState.eof =>
    return Hint.eof

def skip
  [Monad m] [Debug m] [MonadExcept String m] [MonadStateOf (TreeParser α) m]
  : m Unit := do
  Debug.debug "skip"
  let curr <- Stack.getCurrent
  match curr with
  | ParserState.unknown _ =>
    Stack.setCurrent (@ParserState.eof α)
    return ()
  | ParserState.opened _ =>
    let popped <- (TreeParser.pop (α := α))
    if not popped then Stack.setCurrent (@ParserState.eof α)
    return ()
  | ParserState.value _ _ =>
    let popped: Bool <- (TreeParser.pop (α := α))
    if not popped then Stack.setCurrent (@ParserState.eof α)
    return ()
  | ParserState.pair _ _ nexts =>
    Stack.setCurrent (ParserState.opened nexts)
    return ()
  | ParserState.field _ _ =>
    let popped: Bool <- (TreeParser.pop (α := α))
    if not popped then Stack.setCurrent (@ParserState.eof α)
    return ()
  | ParserState.eof =>
    return ()

def token
  [Monad m] [Debug m] [MonadExcept String m] [MonadStateOf (TreeParser α) m]
  : m α := do
  Debug.debug "token"
  let curr <- Stack.getCurrent
  match curr with
  | ParserState.unknown _ =>
    throw "unknown"
  | ParserState.opened _ =>
    throw "unknown"
  | ParserState.value v _ =>
    return v
  | ParserState.pair f _ _ =>
    return f
  | ParserState.field f _ =>
    return f
  | ParserState.eof =>
    throw "unknown"

instance [Monad m] [Debug m] [MonadExcept String m] [MonadStateOf (TreeParser α) m] : Parser m α where
  next := next (α := α)
  skip := skip (α := α)
  token := token

def run (x: StateT (TreeParser α) (Except String) β) (t: ParseTree α): Except String β :=
  StateT.run' x (TreeParser.mk t)

instance : Debug (StateT (TreeParser α) (Except String)) where
  debug (_: String) := return ()

open Parser (walk Action)
open TokenTree (node)

#guard run
  (walk [Action.next, Action.next, Action.next])
  (node "a" []) =
  Except.ok ["{", "V", "}"]

#guard run
  (walk [Action.next, Action.next, Action.next, Action.next, Action.next, Action.next, Action.next, Action.next])
  (node "a" [node "b" [], node "c" [node "d" []]]) =
  Except.ok ["{", "F", "{", "V", "F", "V", "}", "}"]

-- walk next just two
#guard run
  (walk [Action.next, Action.next])
  (node "a" [node "b" [], node "c" [node "d" []]])
  = Except.ok ["{", "F"]

-- walk next to end
#guard run
  (walk [Action.next, Action.next, Action.next, Action.next, Action.next, Action.next, Action.next, Action.next, Action.next])
  (node "a" [node "b" [], node "c" [node "d" []]])
  = Except.ok ["{", "F", "{", "V", "F", "V", "}", "}", "$"]

-- walk next to end and tokenize all
#guard run
  (walk [Action.next, Action.next, Action.token, Action.next, Action.next, Action.token, Action.next, Action.token, Action.next, Action.token, Action.next, Action.next, Action.next])
  (node "a" [node "b" [], node "c" [node "d" []]])
  = Except.ok ["{", "F", "a", "{", "V", "b", "F", "c", "V", "d", "}", "}", "$"]

-- walk next to end and tokenize all
#guard run
  (walk [Action.next, Action.next, Action.token, Action.next, Action.next, Action.token, Action.next, Action.token, Action.next, Action.token, Action.next, Action.next, Action.next])
  (node "a" [node "b" [], node "c" [node "d" []]])
  = Except.ok ["{", "F", "a", "{", "V", "b", "F", "c", "V", "d", "}", "}", "$"]

-- walk skip
#guard run
  (walk [Action.skip, Action.next])
  (node "a" [node "b" [], node "c" [node "d" []]]) =
  Except.ok ["$"]

-- walk next skip
#guard run
  (walk [Action.next, Action.skip, Action.next])
  (node "a" [node "b" [], node "c" [node "d" []]]) =
  Except.ok ["{", "$"]

-- walk next next skip
#guard run
  (walk [Action.next, Action.next, Action.skip, Action.next, Action.next])
  (node "a" [node "b" [], node "c" [node "d" []]]) =
  Except.ok ["{", "F", "}", "$"]

-- walk next next token skip
#guard run
  (walk [Action.next, Action.next, Action.token, Action.skip, Action.next, Action.next])
  (node "a" [node "b" [], node "c" [node "d" []]]) =
  Except.ok ["{", "F", "a", "}", "$"]

-- walk next next token next skip
#guard run
  (walk [Action.next, Action.next, Action.token, Action.next, Action.skip, Action.next, Action.next])
  (node "a" [node "b" [], node "c" [node "d" []]]) =
  Except.ok ["{", "F", "a", "{", "}", "$"]

-- walk next next token next next token skip
#guard run
  (walk [Action.next, Action.next, Action.token, Action.next, Action.next, Action.token, Action.skip, Action.next, Action.next])
  (node "a" [node "b" [], node "c" [node "d" []]]) =
  Except.ok ["{", "F", "a", "{", "V", "b", "}", "$"]

-- walk next next token next next token next token skip
#guard run
  (walk [Action.next, Action.next, Action.token, Action.next, Action.next, Action.token, Action.next, Action.token, Action.skip, Action.next, Action.next, Action.next])
  (node "a" [node "b" [], node "c" [node "d" []]]) =
  Except.ok ["{", "F", "a", "{", "V", "b", "F", "c", "}", "}", "$"]
