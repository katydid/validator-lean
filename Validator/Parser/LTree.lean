import Validator.Std.Except

import Validator.Parser.Stack
import Validator.Parser.Parser

-- LTree is a Labelled Tree.
inductive LTree where
  | node (label: String) (children: List LTree)

namespace LTree

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

def nextNode (current: LTree) (nexts: List LTree): StateT LTreeParser (Except Parser.Error) Hint := do
  match current with
  | LTree.node v [] =>
    Stack.setCurrent (ParserState.value (Token.string v) nexts)
    return Hint.value
  | LTree.node f [LTree.node v []] =>
    Stack.setCurrent (ParserState.pair (Token.string f) (Token.string v) nexts)
    return Hint.field
  | LTree.node f children =>
    Stack.setCurrent (ParserState.opened nexts)
    Stack.push (ParserState.field (Token.string f) children)
    return Hint.field

def next: StateT LTreeParser (Except Parser.Error) Hint := do
  let curr <- Stack.getCurrent
  match curr with
  | ParserState.unknown f =>
    Stack.setCurrent (ParserState.opened f)
    return Hint.enter
  | ParserState.opened [] =>
    let popped <- Stack.pop
    if not popped then Stack.setCurrent ParserState.eof
    return Hint.leave
  | ParserState.opened (t::ts) =>
    nextNode t ts
  | ParserState.value _ [] =>
    let popped <- Stack.pop
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

def skip: StateT LTreeParser (Except Parser.Error) Unit := do
  let curr <- Stack.getCurrent
  match curr with
  | ParserState.unknown _ =>
    Stack.setCurrent ParserState.eof
    return ()
  | ParserState.opened _ =>
    let popped <- Stack.pop
    if not popped then Stack.setCurrent ParserState.eof
    return ()
  | ParserState.value _ _ =>
    let popped <- Stack.pop
    if not popped then Stack.setCurrent ParserState.eof
    return ()
  | ParserState.pair _ _ nexts =>
    Stack.setCurrent (ParserState.opened nexts)
    return ()
  | ParserState.field _ _ =>
    let popped <- Stack.pop
    if not popped then Stack.setCurrent ParserState.eof
    return ()
  | ParserState.eof =>
    return ()

def token: StateT LTreeParser (Except Parser.Error) Token := do
  let curr <- Stack.getCurrent
  match curr with
  | ParserState.unknown _ =>
    throw (Parser.Error.unknown "unknown")
  | ParserState.opened _ =>
    throw (Parser.Error.unknown "unknown")
  | ParserState.value v _ =>
    return v
  | ParserState.pair f _ _ =>
    return f
  | ParserState.field f _ =>
    return f
  | ParserState.eof =>
    throw (Parser.Error.unknown "unknown")

instance : Parser (StateT LTreeParser (Except Parser.Error)) where
  next := next
  skip := skip
  token := token

def LTreeParser.run (x: StateT LTreeParser (Except Parser.Error) α) (t: LTree): Except Parser.Error α :=
  StateT.run' x (LTreeParser.mk' t)

open Parser

#guard LTreeParser.run
  (walk [Action.next, Action.next, Action.next])
  (LTree.node "a" []) =
  Except.ok ["{", "V", "}"]

#guard LTreeParser.run
  (walk [Action.next, Action.next, Action.next, Action.next, Action.next, Action.next, Action.next, Action.next])
  (LTree.node "a" [LTree.node "b" [], LTree.node "c" [LTree.node "d" []]]) =
  Except.ok ["{", "F", "{", "V", "F", "V", "}", "}"]

-- walk next just two
#guard LTreeParser.run
  (walk [Action.next, Action.next])
  (LTree.node "a" [LTree.node "b" [], LTree.node "c" [LTree.node "d" []]])
  = Except.ok ["{", "F"]

-- walk next to end
#guard LTreeParser.run
  (walk [Action.next, Action.next, Action.next, Action.next, Action.next, Action.next, Action.next, Action.next, Action.next])
  (LTree.node "a" [LTree.node "b" [], LTree.node "c" [LTree.node "d" []]])
  = Except.ok ["{", "F", "{", "V", "F", "V", "}", "}", "$"]

-- walk next to end and tokenize all
#guard LTreeParser.run
  (walk [Action.next, Action.next, Action.token, Action.next, Action.next, Action.token, Action.next, Action.token, Action.next, Action.token, Action.next, Action.next, Action.next])
  (LTree.node "a" [LTree.node "b" [], LTree.node "c" [LTree.node "d" []]])
  = Except.ok ["{", "F", "a", "{", "V", "b", "F", "c", "V", "d", "}", "}", "$"]

-- walk next to end and tokenize all
#guard LTreeParser.run
  (walk [Action.next, Action.next, Action.token, Action.next, Action.next, Action.token, Action.next, Action.token, Action.next, Action.token, Action.next, Action.next, Action.next])
  (LTree.node "a" [LTree.node "b" [], LTree.node "c" [LTree.node "d" []]])
  = Except.ok ["{", "F", "a", "{", "V", "b", "F", "c", "V", "d", "}", "}", "$"]

-- walk skip
#guard LTreeParser.run
  (walk [Action.skip, Action.next])
  (LTree.node "a" [LTree.node "b" [], LTree.node "c" [LTree.node "d" []]]) =
  Except.ok ["$"]

-- walk next skip
#guard LTreeParser.run
  (walk [Action.next, Action.skip, Action.next])
  (LTree.node "a" [LTree.node "b" [], LTree.node "c" [LTree.node "d" []]]) =
  Except.ok ["{", "$"]

-- walk next next skip
#guard LTreeParser.run
  (walk [Action.next, Action.next, Action.skip, Action.next, Action.next])
  (LTree.node "a" [LTree.node "b" [], LTree.node "c" [LTree.node "d" []]]) =
  Except.ok ["{", "F", "}", "$"]

-- walk next next token skip
#guard LTreeParser.run
  (walk [Action.next, Action.next, Action.token, Action.skip, Action.next, Action.next])
  (LTree.node "a" [LTree.node "b" [], LTree.node "c" [LTree.node "d" []]]) =
  Except.ok ["{", "F", "a", "}", "$"]

-- walk next next token next skip
#guard LTreeParser.run
  (walk [Action.next, Action.next, Action.token, Action.next, Action.skip, Action.next, Action.next])
  (LTree.node "a" [LTree.node "b" [], LTree.node "c" [LTree.node "d" []]]) =
  Except.ok ["{", "F", "a", "{", "}", "$"]

-- walk next next token next next token skip
#guard LTreeParser.run
  (walk [Action.next, Action.next, Action.token, Action.next, Action.next, Action.token, Action.skip, Action.next, Action.next])
  (LTree.node "a" [LTree.node "b" [], LTree.node "c" [LTree.node "d" []]]) =
  Except.ok ["{", "F", "a", "{", "V", "b", "}", "$"]

-- walk next next token next next token next token skip
#guard LTreeParser.run
  (walk [Action.next, Action.next, Action.token, Action.next, Action.next, Action.token, Action.next, Action.token, Action.skip, Action.next, Action.next, Action.next])
  (LTree.node "a" [LTree.node "b" [], LTree.node "c" [LTree.node "d" []]]) =
  Except.ok ["{", "F", "a", "{", "V", "b", "F", "c", "}", "}", "$"]
