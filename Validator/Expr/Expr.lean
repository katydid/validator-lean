import Init.Control.State
import Init.Control.Except
import Init.Control.EState

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
  next: m (Except ParseError Hint)
  skip: m (Except ParseError Unit)
  token: m (Except ParseError Token)

inductive Action where
  | next
  | skip
  | token

def walkActions [Monad m] [Parser m] (actions: List Action) (logs: List String := []): m (List String) := do
  match actions with
  | [] => return reverse logs
  | (action::rest) =>
    match action with
    | Action.next => do
      match <- Parser.next with
      | Except.error (ParseError.unknown errstring) => return reverse (errstring::logs)
      | Except.ok Hint.eof => return reverse (toString Hint.eof :: logs)
      | Except.ok h' =>
        walkActions rest (toString h' :: logs)
    | Action.skip => do
      match <- Parser.skip with
      | Except.error (ParseError.unknown errstring) => return reverse (errstring::logs)
      | Except.ok () =>
        walkActions rest logs
    | Action.token => do
      match <- Parser.token with
      | Except.error (ParseError.unknown errstring) => return reverse (errstring::logs)
      | Except.ok t' =>
        walkActions rest (toString t' :: logs)

-- StateParser is the default Parser, where the State type (S) still needs to be specified.
def StateParser (S: Type) := Parser (StateM S)
-- Various Parsers implementations (other than StateM) are possible, just an example, here we have a parser with IO.
def IOParser := Parser IO

inductive StackedState (S: Type) where
  | mk (current: S) (stack: List S)

def getCurrent: StateM (StackedState S) S := do
  let s <- get
  match s with
  | StackedState.mk curr _ => return curr

def setCurrent (t: S): StateM (StackedState S) PUnit := do
  let s <- get
  match s with
  | StackedState.mk _ stack =>
    set (StackedState.mk t stack)
    return ()

def push (top: S): StateM (StackedState S) PUnit := do
  let s <- get
  match s with
  | StackedState.mk oldtop stack =>
    set (StackedState.mk top (oldtop::stack))
    return ()

def pop: StateM (StackedState S) Bool := do
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

def nextNode (current: LTree) (nexts: List LTree): StateM LTreeParser (Except ParseError Hint) := do
  match current with
  | LTree.node v [] =>
    setCurrent (ParserState.value (Token.string v) nexts)
    return Except.ok Hint.value
  | LTree.node f [LTree.node v []] =>
    setCurrent (ParserState.pair (Token.string f) (Token.string v) nexts)
    return Except.ok Hint.field
  | LTree.node f children =>
    setCurrent (ParserState.opened nexts)
    push (ParserState.field (Token.string f) children)
    return Except.ok Hint.field

def next: StateM LTreeParser (Except ParseError Hint) := do
  let curr <- getCurrent
  match curr with
  | ParserState.unknown f =>
    setCurrent (ParserState.opened f)
    return Except.ok Hint.enter
  | ParserState.opened [] =>
    let popped <- pop
    if not popped then setCurrent ParserState.eof
    return Except.ok Hint.leave
  | ParserState.opened (t::ts) =>
    nextNode t ts
  | ParserState.value _ [] =>
    let popped <- pop
    if not popped then setCurrent ParserState.eof
    return Except.ok Hint.leave
  | ParserState.value _ (t::ts) =>
    nextNode t ts
  | ParserState.pair _ v nexts =>
    setCurrent (ParserState.value v nexts)
    return Except.ok Hint.value
  | ParserState.field _ children =>
    setCurrent (ParserState.opened children)
    return Except.ok Hint.enter
  | ParserState.eof =>
    return Except.ok Hint.eof

def skip: StateM LTreeParser (Except ParseError Unit) := do
  let curr <- getCurrent
  match curr with
  | ParserState.unknown _ =>
    setCurrent ParserState.eof
    return Except.ok ()
  | ParserState.opened _ =>
    let popped <- pop
    if not popped then setCurrent ParserState.eof
    return Except.ok ()
  | ParserState.value _ _ =>
    let popped <- pop
    if not popped then setCurrent ParserState.eof
    return Except.ok ()
  | ParserState.pair _ _ nexts =>
    setCurrent (ParserState.opened nexts)
    return Except.ok ()
  | ParserState.field _ _ =>
    let popped <- pop
    if not popped then setCurrent ParserState.eof
    return Except.ok ()
  | ParserState.eof =>
    return Except.ok ()

def token: StateM LTreeParser (Except ParseError Token) := do
  let curr <- getCurrent
  match curr with
  | ParserState.unknown _ =>
    return Except.error (ParseError.unknown "unknown")
  | ParserState.opened _ =>
    return Except.error (ParseError.unknown "unknown")
  | ParserState.value v _ =>
    return Except.ok v
  | ParserState.pair f _ _ =>
    return Except.ok f
  | ParserState.field f _ =>
    return Except.ok f
  | ParserState.eof =>
    return Except.error (ParseError.unknown "unknown")

instance : Parser (StateM LTreeParser) where
  next := next
  skip := skip
  token := token

-- Unfortunately with StateT.run' we need the type hint (m := Id), so we define StateM.run':
def StateM.run' {σ : Type u} {α : Type u} (x : StateT σ Id α) (s : σ) : α :=
  StateT.run' x s

example : StateM.run'
  (walkActions [Action.next, Action.next, Action.next])
  (LTreeParser.mk' (LTree.node "a" [])) =
  ["{", "V", "}"] := by
  native_decide

def LTreeParser.run (x: StateM LTreeParser α) (t: LTree): α :=
  StateM.run' x (LTreeParser.mk' t)

example : LTreeParser.run
  (walkActions [Action.next, Action.next, Action.next])
  (LTree.node "a" []) =
  ["{", "V", "}"] := by
  native_decide

example : LTreeParser.run
  (walkActions [Action.next, Action.next, Action.next, Action.next, Action.next, Action.next, Action.next, Action.next])
  (LTree.node "a" [LTree.node "b" [], LTree.node "c" [LTree.node "d" []]]) =
  ["{", "F", "{", "V", "F", "V", "}", "}"] := by
  native_decide

-- walkActions next just two
example : LTreeParser.run
  (walkActions [Action.next, Action.next])
  (LTree.node "a" [LTree.node "b" [], LTree.node "c" [LTree.node "d" []]])
  = ["{", "F"] := by
  native_decide

-- walkActions next to end
example : LTreeParser.run
  (walkActions [Action.next, Action.next, Action.next, Action.next, Action.next, Action.next, Action.next, Action.next, Action.next])
  (LTree.node "a" [LTree.node "b" [], LTree.node "c" [LTree.node "d" []]])
  = ["{", "F", "{", "V", "F", "V", "}", "}", "$"] := by
  native_decide

-- walkActions next to end and tokenize all
example : LTreeParser.run
  (walkActions [Action.next, Action.next, Action.token, Action.next, Action.next, Action.token, Action.next, Action.token, Action.next, Action.token, Action.next, Action.next, Action.next])
  (LTree.node "a" [LTree.node "b" [], LTree.node "c" [LTree.node "d" []]])
  = ["{", "F", "a", "{", "V", "b", "F", "c", "V", "d", "}", "}", "$"] := by
  native_decide

-- walkActions next to end and tokenize all
example : LTreeParser.run
  (walkActions [Action.next, Action.next, Action.token, Action.next, Action.next, Action.token, Action.next, Action.token, Action.next, Action.token, Action.next, Action.next, Action.next])
  (LTree.node "a" [LTree.node "b" [], LTree.node "c" [LTree.node "d" []]])
  = ["{", "F", "a", "{", "V", "b", "F", "c", "V", "d", "}", "}", "$"] := by
  native_decide

-- walkActions skip
example : LTreeParser.run
  (walkActions [Action.skip, Action.next])
  (LTree.node "a" [LTree.node "b" [], LTree.node "c" [LTree.node "d" []]]) =
  ["$"] := by
  native_decide

-- walkActions next skip
example : LTreeParser.run
  (walkActions [Action.next, Action.skip, Action.next])
  (LTree.node "a" [LTree.node "b" [], LTree.node "c" [LTree.node "d" []]]) =
  ["{", "$"] := by
  native_decide

-- walkActions next next skip
example : LTreeParser.run
  (walkActions [Action.next, Action.next, Action.skip, Action.next, Action.next])
  (LTree.node "a" [LTree.node "b" [], LTree.node "c" [LTree.node "d" []]]) =
  ["{", "F", "}", "$"] := by
  native_decide

-- walkActions next next token skip
example : LTreeParser.run
  (walkActions [Action.next, Action.next, Action.token, Action.skip, Action.next, Action.next])
  (LTree.node "a" [LTree.node "b" [], LTree.node "c" [LTree.node "d" []]]) =
  ["{", "F", "a", "}", "$"] := by
  native_decide

-- walkActions next next token next skip
example : LTreeParser.run
  (walkActions [Action.next, Action.next, Action.token, Action.next, Action.skip, Action.next, Action.next])
  (LTree.node "a" [LTree.node "b" [], LTree.node "c" [LTree.node "d" []]]) =
  ["{", "F", "a", "{", "}", "$"] := by
  native_decide

-- walkActions next next token next next token skip
example : LTreeParser.run
  (walkActions [Action.next, Action.next, Action.token, Action.next, Action.next, Action.token, Action.skip, Action.next, Action.next])
  (LTree.node "a" [LTree.node "b" [], LTree.node "c" [LTree.node "d" []]]) =
  ["{", "F", "a", "{", "V", "b", "}", "$"] := by
  native_decide

-- walkActions next next token next next token next token skip
example : LTreeParser.run
  (walkActions [Action.next, Action.next, Action.token, Action.next, Action.next, Action.token, Action.next, Action.token, Action.skip, Action.next, Action.next, Action.next])
  (LTree.node "a" [LTree.node "b" [], LTree.node "c" [LTree.node "d" []]]) =
  ["{", "F", "a", "{", "V", "b", "F", "c", "}", "}", "$"] := by
  native_decide
