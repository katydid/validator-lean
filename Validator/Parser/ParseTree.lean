import Validator.Std.Except

import Validator.Parser.Token
import Validator.Parser.Stack
import Validator.Parser.Parser

-- ParseTree is a Labelled Tree.
inductive ParseTree where
  | node (label: Token) (children: List ParseTree)

namespace ParseTree

def field (s: String) (children: List ParseTree): ParseTree :=
  ParseTree.node (Token.string s) children

def str (s: String): ParseTree :=
  ParseTree.node (Token.string s) []

def getLabel (t: ParseTree): Token :=
  match t with
  | ParseTree.node l _ => l

def getChildren (t: ParseTree): List ParseTree :=
  match t with
  | ParseTree.node _ c => c

inductive ParserState where
  | unknown (children: List ParseTree)
  | opened (nexts: List ParseTree)
  | value (v: Token) (nexts: List ParseTree)
  | pair (f v: Token) (nexts: List ParseTree)
  | field (f: Token) (children: List ParseTree)
  | eof

abbrev TreeParser := Stack ParserState

def TreeParser.pop [Monad m] [MonadStateOf (Stack ParserState) m]: m Bool :=
  Stack.pop (α := ParserState)

def TreeParser.mk' (t: ParseTree): TreeParser :=
  Stack.mk (ParserState.unknown [t]) []

def nextNode
  [Monad m] [MonadExcept String m] [MonadStateOf TreeParser m]
  (current: ParseTree) (nexts: List ParseTree): m Hint := do
  match current with
  | ParseTree.node v [] =>
    Stack.setCurrent (ParserState.value v nexts)
    return Hint.value
  | ParseTree.node f [ParseTree.node v []] =>
    Stack.setCurrent (ParserState.pair f v nexts)
    return Hint.field
  | ParseTree.node f children =>
    Stack.setCurrent (ParserState.opened nexts)
    Stack.push (ParserState.field f children)
    return Hint.field

def next
  [Monad m] [MonadExcept String m] [MonadStateOf TreeParser m]
  : m Hint := do
  let curr <- Stack.getCurrent
  match curr with
  | ParserState.unknown f =>
    Stack.setCurrent (ParserState.opened f)
    return Hint.enter
  | ParserState.opened [] =>
    let popped <- TreeParser.pop
    if not popped then Stack.setCurrent ParserState.eof
    return Hint.leave
  | ParserState.opened (t::ts) =>
    nextNode t ts
  | ParserState.value _ [] =>
    let popped <- TreeParser.pop
    if not popped then Stack.setCurrent ParserState.eof
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
  [Monad m] [MonadExcept String m] [MonadStateOf TreeParser m]
  : m Unit := do
  let curr <- Stack.getCurrent
  match curr with
  | ParserState.unknown _ =>
    Stack.setCurrent ParserState.eof
    return ()
  | ParserState.opened _ =>
    let popped <- TreeParser.pop
    if not popped then Stack.setCurrent ParserState.eof
    return ()
  | ParserState.value _ _ =>
    let popped: Bool <- TreeParser.pop
    if not popped then Stack.setCurrent ParserState.eof
    return ()
  | ParserState.pair _ _ nexts =>
    Stack.setCurrent (ParserState.opened nexts)
    return ()
  | ParserState.field _ _ =>
    let popped: Bool <- TreeParser.pop
    if not popped then Stack.setCurrent ParserState.eof
    return ()
  | ParserState.eof =>
    return ()

def token
  [Monad m] [MonadExcept String m] [MonadStateOf TreeParser m]
  : m Token := do
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

instance [Monad m] [MonadExcept String m] [MonadStateOf TreeParser m] : Parser m where
  next := next
  skip := skip
  token := token

def TreeParser.run (x: StateT TreeParser (Except String) α) (t: ParseTree): Except String α :=
  StateT.run' x (TreeParser.mk' t)

open Parser

#guard TreeParser.run
  (walk [Action.next, Action.next, Action.next])
  (field "a" []) =
  Except.ok ["{", "V", "}"]

#guard TreeParser.run
  (walk [Action.next, Action.next, Action.next, Action.next, Action.next, Action.next, Action.next, Action.next])
  (field "a" [field "b" [], field "c" [field "d" []]]) =
  Except.ok ["{", "F", "{", "V", "F", "V", "}", "}"]

-- walk next just two
#guard TreeParser.run
  (walk [Action.next, Action.next])
  (field "a" [field "b" [], field "c" [field "d" []]])
  = Except.ok ["{", "F"]

-- walk next to end
#guard TreeParser.run
  (walk [Action.next, Action.next, Action.next, Action.next, Action.next, Action.next, Action.next, Action.next, Action.next])
  (field "a" [field "b" [], field "c" [field "d" []]])
  = Except.ok ["{", "F", "{", "V", "F", "V", "}", "}", "$"]

-- walk next to end and tokenize all
#guard TreeParser.run
  (walk [Action.next, Action.next, Action.token, Action.next, Action.next, Action.token, Action.next, Action.token, Action.next, Action.token, Action.next, Action.next, Action.next])
  (field "a" [field "b" [], field "c" [field "d" []]])
  = Except.ok ["{", "F", "a", "{", "V", "b", "F", "c", "V", "d", "}", "}", "$"]

-- walk next to end and tokenize all
#guard TreeParser.run
  (walk [Action.next, Action.next, Action.token, Action.next, Action.next, Action.token, Action.next, Action.token, Action.next, Action.token, Action.next, Action.next, Action.next])
  (field "a" [field "b" [], field "c" [field "d" []]])
  = Except.ok ["{", "F", "a", "{", "V", "b", "F", "c", "V", "d", "}", "}", "$"]

-- walk skip
#guard TreeParser.run
  (walk [Action.skip, Action.next])
  (field "a" [field "b" [], field "c" [field "d" []]]) =
  Except.ok ["$"]

-- walk next skip
#guard TreeParser.run
  (walk [Action.next, Action.skip, Action.next])
  (field "a" [field "b" [], field "c" [field "d" []]]) =
  Except.ok ["{", "$"]

-- walk next next skip
#guard TreeParser.run
  (walk [Action.next, Action.next, Action.skip, Action.next, Action.next])
  (field "a" [field "b" [], field "c" [field "d" []]]) =
  Except.ok ["{", "F", "}", "$"]

-- walk next next token skip
#guard TreeParser.run
  (walk [Action.next, Action.next, Action.token, Action.skip, Action.next, Action.next])
  (field "a" [field "b" [], field "c" [field "d" []]]) =
  Except.ok ["{", "F", "a", "}", "$"]

-- walk next next token next skip
#guard TreeParser.run
  (walk [Action.next, Action.next, Action.token, Action.next, Action.skip, Action.next, Action.next])
  (field "a" [field "b" [], field "c" [field "d" []]]) =
  Except.ok ["{", "F", "a", "{", "}", "$"]

-- walk next next token next next token skip
#guard TreeParser.run
  (walk [Action.next, Action.next, Action.token, Action.next, Action.next, Action.token, Action.skip, Action.next, Action.next])
  (field "a" [field "b" [], field "c" [field "d" []]]) =
  Except.ok ["{", "F", "a", "{", "V", "b", "}", "$"]

-- walk next next token next next token next token skip
#guard TreeParser.run
  (walk [Action.next, Action.next, Action.token, Action.next, Action.next, Action.token, Action.next, Action.token, Action.skip, Action.next, Action.next, Action.next])
  (field "a" [field "b" [], field "c" [field "d" []]]) =
  Except.ok ["{", "F", "a", "{", "V", "b", "F", "c", "}", "}", "$"]
