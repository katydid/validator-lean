import Init.Control.State

import Validator.Std.Except

namespace Expr

open List

def Predicate := String -> Bool
def Bytes := Array UInt8
  deriving Repr

-- LTree is a Labelled Tree.
inductive LTree where
  | node (label: String) (children: List LTree)

def label (t: LTree): String :=
  match t with
  | LTree.node l _ => l

def children (t: LTree): List LTree :=
  match t with
  | LTree.node _ c => c

inductive Expr where
  | emptyset
  | epsilon
  | tree (labelPred: Predicate) (childrenExpr: Expr)
  | or (y z: Expr)
  | concat (y z: Expr)
  | star (y: Expr)

def nullable (x: Expr): Bool :=
  match x with
  | Expr.emptyset => False
  | Expr.epsilon => True
  | Expr.tree _ _ => False
  | Expr.or y z => nullable y || nullable z
  | Expr.concat y z => nullable y && nullable z
  | Expr.star _ => True

partial def derive (x: Expr) (t: LTree): Expr :=
  match x with
  | Expr.emptyset => Expr.emptyset
  | Expr.epsilon => Expr.emptyset
  | Expr.tree labelPred childrenExpr =>
    let childResExpr := List.foldl derive childrenExpr (children t)
    if labelPred (label t)
    then
      if nullable childResExpr
      then Expr.epsilon
      else Expr.emptyset
    else Expr.emptyset
  | Expr.or y z => Expr.or (derive y t) (derive z t)
  | Expr.concat y z =>
    if nullable y
    then Expr.or (Expr.concat (derive y t) z) (derive z t)
    else Expr.concat (derive y t) z
  | Expr.star y => Expr.concat (derive y t) (Expr.star y)

partial def validate (x: Expr) (forest: List LTree): Bool :=
  nullable (List.foldl derive x forest)

inductive ParseError where
  | unknown (desc: String)
  deriving DecidableEq

inductive Hint where
  | enter
  | leave
  | field
  | value
  | eof
  deriving Repr

instance : ToString Hint :=
  ⟨ fun h =>
    match h with
    | Hint.enter => "{"
    | Hint.leave => "}"
    | Hint.field => "F"
    | Hint.value => "V"
    | Hint.eof => "$"
  ⟩

inductive Token where
  | void
  | elem
  | bool (value: Bool)
  | bytes (value: Bytes)
  | string (value: String)
  | int64 (value: Int64)
  | float64 (value: Float)
  | decimal (value: String)
  | nanoseconds (value: Int64)
  | datetime (value: String)
  | tag (value: String)
  deriving Repr

instance : ToString Token :=
  ⟨ fun t =>
    match t with
    | Token.void => "_"
    | Token.elem => "i"
    | Token.bool false => "f"
    | Token.bool true => "t"
    | Token.bytes v => "x:" ++ reprStr v
    | Token.string v => v
    | Token.int64 v => "-:" ++ reprStr v
    | Token.float64 v => ".:" ++ reprStr v
    | Token.decimal v => "/:" ++ v
    | Token.nanoseconds v => "9:" ++ reprStr v
    | Token.datetime v => "z:" ++ v
    | Token.tag v => "#:" ++ v
  ⟩

-- * `Next : () -> (Hint | error | EOF)`
-- * `Skip : () -> (error | EOF)?`
-- * `Token: () -> (Token | error)`

class Parser (m: Type -> Type u) [Monad m] where
  next: m Hint
  skip: m Unit
  token: m Token

inductive Action where
  | next
  | skip
  | token

def walkActions [Monad m] [Parser m] (actions: List Action) (logs: List String := []): m (List String) := do
  match actions with
  | [] => return reverse logs
  | (Action.next::rest) => do
    match <- Parser.next with
    | Hint.eof =>
        return reverse (toString Hint.eof :: logs)
    | h' =>
        walkActions rest (toString h' :: logs)
  | (Action.skip::rest) => do
    _ <- Parser.skip
    walkActions rest logs
  | (Action.token::rest) => do
    walkActions rest (toString (<- Parser.token) :: logs)

-- StateParser is the default Parser, where the State type (S) still needs to be specified.
def StateParser (S: Type) := Parser (StateM S)
-- Various Parsers implementations (other than StateM) are possible, just an example, here we have a parser with IO.
def IOParser := Parser IO

inductive StackedState (S: Type) where
  | mk (current: S) (stack: List S)

def getCurrent [Monad m]: StateT (StackedState S) m S := do
  let s <- get
  match s with
  | StackedState.mk curr _ => return curr

def setCurrent [Monad m] (t: S): StateT (StackedState S) m Unit := do
  let s <- get
  match s with
  | StackedState.mk _ stack =>
    set (StackedState.mk t stack)
    return ()

def push [Monad m] (top: S): StateT (StackedState S) m Unit := do
  let s <- get
  match s with
  | StackedState.mk oldtop stack =>
    set (StackedState.mk top (oldtop::stack))
    return ()

def pop [Monad m]: StateT (StackedState S) m Bool := do
  let s <- get
  match s with
  | StackedState.mk _ [] =>
    return false
  | StackedState.mk _ (newtop::stack) =>
    set (StackedState.mk newtop stack)
    return true

inductive ParserState where
  | unknown (children: List LTree)
  | opened (nexts: List LTree)
  | value (v: Token) (nexts: List LTree)
  | pair (f v: Token) (nexts: List LTree)
  | field (f: Token) (children: List LTree)
  | eof

def LTreeParser := StackedState ParserState

def LTreeParser.mk' (t: LTree): LTreeParser :=
  StackedState.mk (ParserState.unknown [t]) []

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
