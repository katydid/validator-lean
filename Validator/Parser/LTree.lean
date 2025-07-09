import Validator.Std.Except

import Validator.Parser.Stack
import Validator.Parser.Parser

-- LTree is a Labelled Tree.
inductive LTree where
  | node (label: String) (children: List LTree)

def label (t: LTree): String :=
  match t with
  | LTree.node l _ => l

def children (t: LTree): List LTree :=
  match t with
  | LTree.node _ c => c

inductive ParserState where
  | unknown (children: List LTree)
  | opened (nexts: List LTree)
  | value (v: Token) (nexts: List LTree)
  | pair (f v: Token) (nexts: List LTree)
  | field (f: Token) (children: List LTree)
  | eof

def LTreeParser := Stack ParserState

def LTreeParser.mk' (t: LTree): LTreeParser :=
  Stack.mk (ParserState.unknown [t]) []

def nextNode (current: LTree) (nexts: List LTree): StateT LTreeParser (Except ParseError) Hint := do
  match current with
  | LTree.node v [] =>
    setCurrent (ParserState.value (Token.string v) nexts)
    return Hint.value
  | LTree.node f [LTree.node v []] =>
    setCurrent (ParserState.pair (Token.string f) (Token.string v) nexts)
    return Hint.field
  | LTree.node f children =>
    setCurrent (ParserState.opened nexts)
    push (ParserState.field (Token.string f) children)
    return Hint.field

def next: StateT LTreeParser (Except ParseError) Hint := do
  let curr <- getCurrent
  match curr with
  | ParserState.unknown f =>
    setCurrent (ParserState.opened f)
    return Hint.enter
  | ParserState.opened [] =>
    let popped <- pop
    if not popped then setCurrent ParserState.eof
    return Hint.leave
  | ParserState.opened (t::ts) =>
    nextNode t ts
  | ParserState.value _ [] =>
    let popped <- pop
    if not popped then setCurrent ParserState.eof
    return Hint.leave
  | ParserState.value _ (t::ts) =>
    nextNode t ts
  | ParserState.pair _ v nexts =>
    setCurrent (ParserState.value v nexts)
    return Hint.value
  | ParserState.field _ children =>
    setCurrent (ParserState.opened children)
    return Hint.enter
  | ParserState.eof =>
    return Hint.eof

def skip: StateT LTreeParser (Except ParseError) Unit := do
  let curr <- getCurrent
  match curr with
  | ParserState.unknown _ =>
    setCurrent ParserState.eof
    return ()
  | ParserState.opened _ =>
    let popped <- pop
    if not popped then setCurrent ParserState.eof
    return ()
  | ParserState.value _ _ =>
    let popped <- pop
    if not popped then setCurrent ParserState.eof
    return ()
  | ParserState.pair _ _ nexts =>
    setCurrent (ParserState.opened nexts)
    return ()
  | ParserState.field _ _ =>
    let popped <- pop
    if not popped then setCurrent ParserState.eof
    return ()
  | ParserState.eof =>
    return ()

def token: StateT LTreeParser (Except ParseError) Token := do
  let curr <- getCurrent
  match curr with
  | ParserState.unknown _ =>
    throw (ParseError.unknown "unknown")
  | ParserState.opened _ =>
    throw (ParseError.unknown "unknown")
  | ParserState.value v _ =>
    return v
  | ParserState.pair f _ _ =>
    return f
  | ParserState.field f _ =>
    return f
  | ParserState.eof =>
    throw (ParseError.unknown "unknown")

instance : Parser (StateT LTreeParser (Except ParseError)) where
  next := next
  skip := skip
  token := token

def LTreeParser.run (x: StateT LTreeParser (Except ParseError) α) (t: LTree): Except ParseError α :=
  StateT.run' x (LTreeParser.mk' t)

#guard LTreeParser.run
  (walkActions [Action.next, Action.next, Action.next])
  (LTree.node "a" []) =
  Except.ok ["{", "V", "}"]

#guard LTreeParser.run
  (walkActions [Action.next, Action.next, Action.next, Action.next, Action.next, Action.next, Action.next, Action.next])
  (LTree.node "a" [LTree.node "b" [], LTree.node "c" [LTree.node "d" []]]) =
  Except.ok ["{", "F", "{", "V", "F", "V", "}", "}"]

-- walkActions next just two
#guard LTreeParser.run
  (walkActions [Action.next, Action.next])
  (LTree.node "a" [LTree.node "b" [], LTree.node "c" [LTree.node "d" []]])
  = Except.ok ["{", "F"]

-- walkActions next to end
#guard LTreeParser.run
  (walkActions [Action.next, Action.next, Action.next, Action.next, Action.next, Action.next, Action.next, Action.next, Action.next])
  (LTree.node "a" [LTree.node "b" [], LTree.node "c" [LTree.node "d" []]])
  = Except.ok ["{", "F", "{", "V", "F", "V", "}", "}", "$"]

-- walkActions next to end and tokenize all
#guard LTreeParser.run
  (walkActions [Action.next, Action.next, Action.token, Action.next, Action.next, Action.token, Action.next, Action.token, Action.next, Action.token, Action.next, Action.next, Action.next])
  (LTree.node "a" [LTree.node "b" [], LTree.node "c" [LTree.node "d" []]])
  = Except.ok ["{", "F", "a", "{", "V", "b", "F", "c", "V", "d", "}", "}", "$"]

-- walkActions next to end and tokenize all
#guard LTreeParser.run
  (walkActions [Action.next, Action.next, Action.token, Action.next, Action.next, Action.token, Action.next, Action.token, Action.next, Action.token, Action.next, Action.next, Action.next])
  (LTree.node "a" [LTree.node "b" [], LTree.node "c" [LTree.node "d" []]])
  = Except.ok ["{", "F", "a", "{", "V", "b", "F", "c", "V", "d", "}", "}", "$"]

-- walkActions skip
#guard LTreeParser.run
  (walkActions [Action.skip, Action.next])
  (LTree.node "a" [LTree.node "b" [], LTree.node "c" [LTree.node "d" []]]) =
  Except.ok ["$"]

-- walkActions next skip
#guard LTreeParser.run
  (walkActions [Action.next, Action.skip, Action.next])
  (LTree.node "a" [LTree.node "b" [], LTree.node "c" [LTree.node "d" []]]) =
  Except.ok ["{", "$"]

-- walkActions next next skip
#guard LTreeParser.run
  (walkActions [Action.next, Action.next, Action.skip, Action.next, Action.next])
  (LTree.node "a" [LTree.node "b" [], LTree.node "c" [LTree.node "d" []]]) =
  Except.ok ["{", "F", "}", "$"]

-- walkActions next next token skip
#guard LTreeParser.run
  (walkActions [Action.next, Action.next, Action.token, Action.skip, Action.next, Action.next])
  (LTree.node "a" [LTree.node "b" [], LTree.node "c" [LTree.node "d" []]]) =
  Except.ok ["{", "F", "a", "}", "$"]

-- walkActions next next token next skip
#guard LTreeParser.run
  (walkActions [Action.next, Action.next, Action.token, Action.next, Action.skip, Action.next, Action.next])
  (LTree.node "a" [LTree.node "b" [], LTree.node "c" [LTree.node "d" []]]) =
  Except.ok ["{", "F", "a", "{", "}", "$"]

-- walkActions next next token next next token skip
#guard LTreeParser.run
  (walkActions [Action.next, Action.next, Action.token, Action.next, Action.next, Action.token, Action.skip, Action.next, Action.next])
  (LTree.node "a" [LTree.node "b" [], LTree.node "c" [LTree.node "d" []]]) =
  Except.ok ["{", "F", "a", "{", "V", "b", "}", "$"]

-- walkActions next next token next next token next token skip
#guard LTreeParser.run
  (walkActions [Action.next, Action.next, Action.token, Action.next, Action.next, Action.token, Action.next, Action.token, Action.skip, Action.next, Action.next, Action.next])
  (LTree.node "a" [LTree.node "b" [], LTree.node "c" [LTree.node "d" []]]) =
  Except.ok ["{", "F", "a", "{", "V", "b", "F", "c", "}", "}", "$"]
