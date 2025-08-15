import Validator.Std.Ltac
import Validator.Std.Debug
import Validator.Std.Except

import Validator.Parser.Token
import Validator.Parser.TokenTree
import Validator.Parser.Stack
import Validator.Parser.ParseTree
import Validator.Parser.Parser

local elab "simp_monads" : tactic => do
  run `(tactic| simp [
    getThe,
    Bind.bind,
    Except.bind,
    Except.map,
    Except.pure,
    Functor.map,
    MonadState.get,
    MonadStateOf.get,
    MonadStateOf.set,
    Pure.pure,
    StateT.bind,
    StateT.get,
    StateT.map,
    StateT.pure,
    StateT.run,
    StateT.set] )

namespace TreeParser

open Nat

abbrev ParseStack α := Stack (ParseForest α)

inductive CurrentState (α: Type) where
  | unknown (children: ParseForest α)
  | opened (nexts: ParseForest α)
  | value (v: α) (nexts: ParseForest α)
  | pair (f v: α) (nexts: ParseForest α)
  | field (f: α) (children: ParseForest α)
  | eof

structure ParserState α where
  current: CurrentState α
  stack: ParseStack α

def ParserState.mk' (tree: ParseTree α): ParserState α :=
  ParserState.mk (CurrentState.unknown [tree]) []

def ParserState.mks (forest: ParseForest α): ParserState α :=
  ParserState.mk (CurrentState.unknown forest) []

mutual
@[simp]
noncomputable def ParseTree.size (x: ParseTree α): Nat :=
  match x with
  | ParseTree.mk _ children =>
    1 + ParseForest.size children
@[simp]
noncomputable def ParseForest.size (xs: ParseForest α): Nat :=
  match xs with
  | [] => 1
  | (x::xs') => 1 + ParseTree.size x + ParseForest.size xs'
end

@[simp]
noncomputable def ParseStack.size (s: ParseStack α): Nat :=
  match s with
  | [] => 0
  | (x::xs) => ParseForest.size x + ParseStack.size xs

@[simp]
noncomputable def CurrentState.size (s: CurrentState α): Nat :=
  match s with
  -- unknown needs to be the larger than opened, since it is the next state.
  | CurrentState.unknown forest => 4 + ParseForest.size forest
  -- field needs to be larger than opened, since opened follows from field.
  | CurrentState.field _ forest => 3 + ParseForest.size forest
  -- pair can only be one smaller than opened
  | CurrentState.pair _ _ forest => 3 + ParseForest.size forest
  -- opened is always the second state, but also follows from field, so it needs to be smaller than unknown and field.
  | CurrentState.opened forest => 2 + ParseForest.size forest
  -- value needs to smaller than pair and smaller or equal to opened
  | CurrentState.value _ forest => 2 + ParseForest.size forest
  -- eof
  | CurrentState.eof => 0

-- When calling next, none of the states grow the stack, except for:
-- ParserState.opened (t::nexts) and ParserState.value _ (t::nexts)
--   where t = ParseTree.mk f children
--         children ≠ []
--         children ≠ [ParseTree.mk v []]
-- These result in two states:
--   Stack.setCurrentM (ParserState.opened nexts)
--   Stack.pushM (ParserState.field f children)
-- We need to make sure that these two states together are smaller than the previous state.
-- This implies that we need show that the stack gets smaller as it grows in these two cases:
--   theorem sizeOf_opened_gt_push: ParserState.opened (t::nexts)  > ParserState.opened nexts + ParserState.field f children
--   theorem sizeOf_value_gt_push: ParserState.value _ (t::nexts) > ParserState.opened nexts + ParserState.field f children
-- While also making sure that as the stack shrinks for these two cases that it also gets smaller:
--   theorem sizeOf_value_gt_popped_value: x + ParserState.value _ [] > x
--   theorem sizeOf_opened_gt_popped_opened: x + ParserState.opened [] > x
-- Otherwise we also need to make sure the following equations hold:
--   theorem sizeOf_unknown_gt_opened: ParserState.unknown forest > ParserState.opened forest
--   theorem sizeOf_value_value_gt_value:  ParserState.value _ ((ParseTree.mk v [])::nexts) > ParserState.value v nexts
--   theorem sizeOf_opened_value_gt_value: ParserState.opened ((ParseTree.mk v [])::nexts) > ParserState.value v nexts
--   theorem sizeOf_value_pair_gt_pair:  ParserState.value _ ((ParseTree.mk f [ParseTree.mk v []])::nexts) > ParserState.pair f v nexts
--   theorem sizeOf_opened_pair_gt_pair: ParserState.opened ((ParseTree.mk f [ParseTree.mk v []])::nexts) > ParserState.pair f v nexts
--   theorem sizeOf_pair_gt_value: ParserState.pair _ v nexts > ParserState.value v nexts
--   theorem sizeOf_field_gt_opened: ParserState.field _ children > ParserState.opened children
@[simp]
noncomputable def ParserState.size (s: ParserState α): Nat :=
  s.current.size + s.stack.size

@[simp]
noncomputable instance: SizeOf (ParserState α) where
  sizeOf := ParserState.size

def pop
  [Monad m] [Debug m] [MonadExcept String m] [MonadStateOf (CurrentState α) m] [MonadStateOf (ParseStack α) m]:
  m Unit := do
  let top : Option (ParseForest α) <- Stack.popM?
  match top with
  | Option.some top' =>
    set (CurrentState.opened top')
    return ()
  | Option.none =>
    set (σ := CurrentState α) CurrentState.eof
    return ()

def nextNode
  [Monad m] [Debug m] [MonadExcept String m] [MonadStateOf (CurrentState α) m] [MonadStateOf (ParseStack α) m]
  (current: ParseTree α) (nexts: ParseForest α): m Hint := do
  match current with
  | ParseTree.mk v [] =>
    set (CurrentState.value v nexts)
    return Hint.value
  | ParseTree.mk f [ParseTree.mk v []] =>
    set (CurrentState.pair f v nexts)
    return Hint.field
  | ParseTree.mk f children =>
    Stack.pushM nexts
    set (CurrentState.field f children)
    return Hint.field

def next
  [Monad m] [Debug m] [MonadExcept String m] [MonadState (CurrentState α) m] [MonadStateOf (CurrentState α) m] [MonadStateOf (ParseStack α) m]
  : m Hint := do
  Debug.debug "next"
  let curr <- get
  match curr with
  | CurrentState.unknown f =>
    _ <- set (CurrentState.opened f)
    return Hint.enter
  | CurrentState.opened [] =>
    pop (α := α)
    return Hint.leave
  | CurrentState.opened (t::ts) =>
    nextNode t ts
  | CurrentState.value _ [] =>
    pop (α := α)
    return Hint.leave
  | CurrentState.value _ (t::ts) =>
    nextNode t ts
  | CurrentState.pair _ v nexts =>
    _ <- set (CurrentState.value v nexts)
    return Hint.value
  | CurrentState.field _ children =>
    _ <- set (CurrentState.opened children)
    return Hint.enter
  | CurrentState.eof =>
    return Hint.eof

def skip
  [Monad m] [Debug m] [MonadExcept String m] [MonadState (CurrentState α) m] [MonadStateOf (CurrentState α) m] [MonadStateOf (ParseStack α) m]
  : m Unit := do
  Debug.debug "skip"
  let curr <- get
  match curr with
  | CurrentState.unknown _ => pop (α := α)
  | CurrentState.opened _ => pop (α := α)
  | CurrentState.value _ _ => pop (α := α)
  | CurrentState.pair _ _ nexts => set (CurrentState.opened nexts)
  | CurrentState.field _ _ => pop (α := α)
  | CurrentState.eof => return ()
  return ()

def token
  [Monad m] [Debug m] [MonadExcept String m] [MonadStateOf (CurrentState α) m]
  : m α := do
  Debug.debug "token"
  let curr <- get
  match curr with
  | CurrentState.unknown _ => throw "unknown"
  | CurrentState.opened _ => throw "unknown"
  | CurrentState.value v _ => return v
  | CurrentState.pair f _ _ => return f
  | CurrentState.field f _ => return f
  | CurrentState.eof => throw "unknown"

instance [Monad m] [Debug m] [MonadExcept String m] [MonadState (CurrentState α) m] [MonadStateOf (CurrentState α) m] [MonadStateOf (ParseStack α) m] : Parser m α where
  next := next (α := α)
  skip := skip (α := α)
  token := token

instance : Debug (StateT (ParserState α) (Except String)) where
  debug (_: String) := return ()

abbrev TreeParser α β := StateT (ParserState α) (Except String) β

def getStack [Monad m] [MonadStateOf (ParserState α) m] : m (ParseStack α) := do
  let t: ParserState α <- MonadStateOf.get
  return t.stack

def setStack [Monad m] [MonadStateOf (ParserState α) m] (stack: ParseStack α) : m PUnit := do
  let t: ParserState α <- MonadStateOf.get
  MonadStateOf.set (ParserState.mk t.current stack)
  return ()

@[simp]
instance instMonadStateOfParserStateMonadStateOfParseStack[Monad m] [MonadStateOf (ParserState α) m]: MonadStateOf (ParseStack α) m where
  get : m (ParseStack α) := getStack
  set (stack: ParseStack α) : m PUnit := setStack stack
  modifyGet {β: Type} (f: ParseStack α → Prod β (ParseStack α)): m β := do
    let t: ParserState α <- MonadStateOf.get
    let (res, newstack) := f t.stack
    MonadStateOf.set (ParserState.mk t.current newstack)
    return res

def getCurrent [Monad m] [MonadStateOf (ParserState α) m]: m (CurrentState α) := do
  let t <- MonadState.get
  return t.current

def setCurrent [Monad m] [MonadStateOf (ParserState α) m] (current: CurrentState α) : m PUnit := do
    let t <- MonadState.get
    MonadStateOf.set (ParserState.mk current t.stack)
    return ()

def modifyGetCurrent [Monad m] [MonadStateOf (ParserState α) m] {β: Type} (f: CurrentState α → Prod β (CurrentState α)): m β := do
    let t <- MonadState.get
    let (res, newcurrent) := f t.current
    MonadStateOf.set (ParserState.mk newcurrent t.stack)
    return res

@[simp]
instance instMonadStateOfParserStateMonadStateOfCurrentState [Monad m] [MonadStateOf (ParserState α) m]: MonadStateOf (CurrentState α) m where
  get : m (CurrentState α) := getCurrent
  set (current: CurrentState α) : m PUnit := setCurrent current
  modifyGet {β: Type} (f: CurrentState α → Prod β (CurrentState α)): m β := modifyGetCurrent f

instance {α}: Parser (TreeParser α) α where
  next := next
  skip := skip
  token := token

def run' (x: TreeParser α β) (s: ParserState α): Except String β :=
  StateT.run' x s

def run (x: TreeParser α β) (s: ParserState α): Except String (β × (ParserState α)) :=
  StateT.run x s

def runTree (x: TreeParser α β) (t: ParseTree α): Except String β :=
  StateT.run' x (ParserState.mk' t)

theorem next_unknown_gt_opened:
  run next (ParserState.mk (CurrentState.unknown children) stack) =
  Except.ok (Hint.enter, ParserState.mk (CurrentState.opened children) stack) := by
  simp [run, next, Debug.debug, getCurrent, setCurrent]
  simp_monads

theorem sizeOf_unknown_gt_opened:
  sizeOf (ParserState.mk (CurrentState.unknown children) stack) >
  sizeOf (ParserState.mk (CurrentState.opened children) stack) := by
  simp

theorem next_value_value_gt_value:
  run next (ParserState.mk (CurrentState.value v' ((ParseTree.mk v [])::siblings)) stack) =
  Except.ok (Hint.value, ParserState.mk (CurrentState.value v siblings) stack) := by
  simp [run, next, nextNode, Debug.debug, getCurrent, setCurrent]
  simp_monads

theorem sizeOf_value_value_gt_value:
  sizeOf (ParserState.mk (CurrentState.value v' ((ParseTree.mk v [])::siblings)) stack) >
  sizeOf (ParserState.mk (CurrentState.value v siblings) stack) := by
  simp

theorem next_opened_value_gt_value:
  run next (ParserState.mk (CurrentState.opened ((ParseTree.mk v [])::siblings)) stack) =
  Except.ok (Hint.value, ParserState.mk (CurrentState.value v siblings) stack) := by
  simp [run, next, nextNode, Debug.debug, getCurrent, setCurrent]
  simp_monads

theorem sizeOf_opened_value_gt_value:
  sizeOf (ParserState.mk (CurrentState.opened ((ParseTree.mk v [])::siblings)) stack) >
  sizeOf (ParserState.mk (CurrentState.value v siblings) stack) := by
  simp

theorem next_value_pair_gt_pair:
  run next (ParserState.mk (CurrentState.value v' ((ParseTree.mk f [ParseTree.mk v []])::siblings)) stack) =
  Except.ok (Hint.field, ParserState.mk (CurrentState.pair f v siblings) stack) := by
  simp [run, next, nextNode, Debug.debug, getCurrent, setCurrent]
  simp_monads

theorem sizeOf_value_pair_gt_pair:
  sizeOf (ParserState.mk (CurrentState.value v' ((ParseTree.mk f [ParseTree.mk v []])::siblings)) stack) >
  sizeOf (ParserState.mk (CurrentState.pair f v siblings) stack) := by
  simp +arith

theorem next_opened_pair_gt_pair:
  run next (ParserState.mk (CurrentState.opened ((ParseTree.mk f [ParseTree.mk v []])::siblings)) stack) =
  Except.ok (Hint.field, ParserState.mk (CurrentState.pair f v siblings) stack) := by
  simp [run, next, nextNode, Debug.debug, getCurrent, setCurrent]
  simp_monads

theorem sizeOf_opened_pair_gt_pair:
  sizeOf (ParserState.mk (CurrentState.opened ((ParseTree.mk f [ParseTree.mk v []])::siblings)) stack) >
  sizeOf (ParserState.mk (CurrentState.pair f v siblings) stack) := by
  simp +arith

theorem next_pair_gt_value:
  run next (ParserState.mk (CurrentState.pair _k v siblings) stack) =
  Except.ok (Hint.value, ParserState.mk (CurrentState.value v siblings) stack) := by
  simp [run, next, nextNode, Debug.debug, getCurrent, setCurrent]
  simp_monads

theorem sizeOf_pair_gt_value:
  sizeOf (ParserState.mk (CurrentState.pair _k v siblings) stack) >
  sizeOf (ParserState.mk (CurrentState.value v siblings) stack) := by
  simp

theorem next_field_gt_opened:
  run next (ParserState.mk (CurrentState.field f' children) stack) =
  Except.ok (Hint.enter, ParserState.mk (CurrentState.opened children) stack) := by
  simp [run, next, nextNode, Debug.debug, getCurrent, setCurrent]
  simp_monads

theorem sizeOf_field_gt_opened:
  sizeOf (ParserState.mk (CurrentState.field f' children) stack) >
  sizeOf (ParserState.mk (CurrentState.opened children) stack) := by
  simp

theorem next_opened_gt_push
  {fchildren: ParseForest α}
  -- if not a value and not a pair
  (hc: (∃ v vchild vchildren, fchildren = [ParseTree.mk v (vchild::vchildren)])
    \/ (∃ fchild1 fchild2 fchilds, fchildren = fchild1::fchild2::fchilds)):
  run next (ParserState.mk ((CurrentState.opened ((ParseTree.mk f fchildren)::siblings))) stack) =
  Except.ok (Hint.field, ParserState.mk (CurrentState.field f fchildren) (siblings::stack)) := by
  cases hc with
  | inl hc =>
    obtain ⟨ v, vchild, vchildren, hc ⟩ := hc
    rw [hc]
    simp [run, next, nextNode, Debug.debug, getCurrent, setCurrent]
    simp_monads
    simp [Stack.pushM, getStack, setStack]
    simp_monads
  | inr hc =>
    obtain ⟨ fchild1, fchild2, fchilds, hc ⟩ := hc
    rw [hc]
    simp [run, next, nextNode, Debug.debug, getCurrent, setCurrent]
    simp_monads
    simp [Stack.pushM, getStack, setStack]
    simp_monads

theorem sizeOf_opened_gt_push:
  sizeOf (ParserState.mk ((CurrentState.opened ((ParseTree.mk f children)::siblings))) stack) >
  sizeOf (ParserState.mk (CurrentState.field f children) (siblings::stack)) := by
  simp +arith

-- run next (ParserState.mk (CurrentState.value v' ((ParseTree.mk f [ParseTree.mk v []])::siblings)) stack) =
-- run next (ParserState.mk (CurrentState.value v' ((ParseTree.mk v [])::siblings)) stack) =
theorem next_value_gt_push
  {fchildren: ParseForest α}
  -- if not a value and not a pair
  (hc: (∃ v vchild vchildren, fchildren = [ParseTree.mk v (vchild::vchildren)])
    \/ (∃ fchild1 fchild2 fchilds, fchildren = fchild1::fchild2::fchilds)):
  run next (ParserState.mk (CurrentState.value v ((ParseTree.mk f fchildren)::fsiblings)) stack) =
  Except.ok (Hint.field, ParserState.mk (CurrentState.field f fchildren) (fsiblings::stack)) := by
  cases hc with
  | inl hc =>
    obtain ⟨ v, vchild, vchildren, hc ⟩ := hc
    rw [hc]
    simp [run, next, nextNode, Debug.debug, getCurrent, setCurrent]
    simp_monads
    simp [Stack.pushM, getStack, setStack]
    simp_monads
  | inr hc =>
    obtain ⟨ fchild1, fchild2, fchilds, hc ⟩ := hc
    rw [hc]
    simp [run, next, nextNode, Debug.debug, getCurrent, setCurrent]
    simp_monads
    simp [Stack.pushM, getStack, setStack]
    simp_monads

theorem sizeOf_value_gt_push:
  sizeOf (ParserState.mk ((CurrentState.value v ((ParseTree.mk f children)::siblings))) stack) >
  sizeOf (ParserState.mk (CurrentState.field f children) (siblings::stack)) := by
  simp +arith

theorem next_value_gt_popped_value_eof {α: Type} (v: α):
  run next (ParserState.mk (α := α) (CurrentState.value v []) []) =
  Except.ok (Hint.leave, ParserState.mk (α := α) CurrentState.eof []) := by
  simp [run, next, nextNode, Debug.debug, getCurrent, setCurrent]
  simp_monads
  simp [pop, Stack.popM?, getStack]
  simp_monads

theorem sizeOf_value_gt_popped_value_eof {α: Type}:
  sizeOf (ParserState.mk (CurrentState.value _v []) []) >
  sizeOf (ParserState.mk (α := α) CurrentState.eof []) := by
  simp

theorem next_value_gt_popped_value_more:
  run next (ParserState.mk (CurrentState.value _v []) (elem::stack)) =
  Except.ok (Hint.leave, ParserState.mk (CurrentState.opened elem) stack) := by
  simp [run, next, nextNode, Debug.debug, getCurrent, setCurrent]
  simp_monads
  simp [pop, Stack.popM?, getStack, setStack]
  simp_monads

theorem sizeOf_value_gt_popped_value_more:
  sizeOf (ParserState.mk (CurrentState.value _v []) (elem::stack)) >
  sizeOf (ParserState.mk (CurrentState.opened elem) stack) := by
  simp +arith

theorem next_opened_gt_popped_opened_eof {α: Type}:
  run next (ParserState.mk (α := α) (CurrentState.opened []) []) =
  Except.ok (Hint.leave, ParserState.mk (α := α) CurrentState.eof []) := by
  simp [run, next, nextNode, Debug.debug, getCurrent, setCurrent]
  simp_monads
  simp [pop, Stack.popM?, getStack, setStack]
  simp_monads

theorem sizeOf_opened_gt_popped_opened_eof {α: Type}:
  sizeOf (ParserState.mk (α := α) (CurrentState.opened []) []) >
  sizeOf (ParserState.mk (α := α) CurrentState.eof []) := by
  simp

theorem next_opened_gt_popped_opened_more:
  run next (ParserState.mk (CurrentState.opened []) (elem::stack)) =
  Except.ok (Hint.leave, ParserState.mk (CurrentState.opened elem) stack) := by
  simp [run, next, nextNode, Debug.debug, getCurrent, setCurrent]
  simp_monads
  simp [pop, Stack.popM?, getStack, setStack]
  simp_monads

theorem sizeOf_opened_gt_popped_opened_more:
  sizeOf (ParserState.mk (CurrentState.opened []) (elem::stack)) >
  sizeOf (ParserState.mk (CurrentState.opened elem) stack) := by
  simp +arith

theorem next_eof_gt_eof:
  run next (ParserState.mk CurrentState.eof stack) =
  Except.ok (Hint.eof, ParserState.mk CurrentState.eof stack) := by
  simp [run, next, Debug.debug, getCurrent]
  simp_monads

open Parser (walk Action)
open TokenTree (node)

#guard run'
  next
  (ParserState.mk (CurrentState.unknown [ParseTree.mk 0 []]) [])
  = Except.ok Hint.enter

#guard runTree
  (walk [Action.next, Action.next, Action.next])
  (node "a" []) =
  Except.ok ["{", "V", "}"]

#guard runTree
  (walk [Action.next, Action.next, Action.next, Action.next, Action.next, Action.next, Action.next, Action.next])
  (node "a" [node "b" [], node "c" [node "d" []]]) =
  Except.ok ["{", "F", "{", "V", "F", "V", "}", "}"]

-- walk next just two
#guard runTree
  (walk [Action.next, Action.next])
  (node "a" [node "b" [], node "c" [node "d" []]])
  = Except.ok ["{", "F"]

-- walk next to end
#guard runTree
  (walk [Action.next, Action.next, Action.next, Action.next, Action.next, Action.next, Action.next, Action.next, Action.next])
  (node "a" [node "b" [], node "c" [node "d" []]])
  = Except.ok ["{", "F", "{", "V", "F", "V", "}", "}", "$"]

-- walk next to end and tokenize all
#guard runTree
  (walk [Action.next, Action.next, Action.token, Action.next, Action.next, Action.token, Action.next, Action.token, Action.next, Action.token, Action.next, Action.next, Action.next])
  (node "a" [node "b" [], node "c" [node "d" []]])
  = Except.ok ["{", "F", "a", "{", "V", "b", "F", "c", "V", "d", "}", "}", "$"]

-- walk next to end and tokenize all
#guard runTree
  (walk [Action.next, Action.next, Action.token, Action.next, Action.next, Action.token, Action.next, Action.token, Action.next, Action.token, Action.next, Action.next, Action.next])
  (node "a" [node "b" [], node "c" [node "d" []]])
  = Except.ok ["{", "F", "a", "{", "V", "b", "F", "c", "V", "d", "}", "}", "$"]

-- walk skip
#guard runTree
  (walk [Action.skip, Action.next])
  (node "a" [node "b" [], node "c" [node "d" []]]) =
  Except.ok ["$"]

-- walk next skip
#guard runTree
  (walk [Action.next, Action.skip, Action.next])
  (node "a" [node "b" [], node "c" [node "d" []]]) =
  Except.ok ["{", "$"]

-- walk next next skip
#guard runTree
  (walk [Action.next, Action.next, Action.skip, Action.next, Action.next])
  (node "a" [node "b" [], node "c" [node "d" []]]) =
  Except.ok ["{", "F", "}", "$"]

-- walk next next token skip
#guard runTree
  (walk [Action.next, Action.next, Action.token, Action.skip, Action.next, Action.next])
  (node "a" [node "b" [], node "c" [node "d" []]]) =
  Except.ok ["{", "F", "a", "}", "$"]

-- walk next next token next skip
#guard runTree
  (walk [Action.next, Action.next, Action.token, Action.next, Action.skip, Action.next, Action.next])
  (node "a" [node "b" [], node "c" [node "d" []]]) =
  Except.ok ["{", "F", "a", "{", "}", "$"]

-- walk next next token next next token skip
#guard runTree
  (walk [Action.next, Action.next, Action.token, Action.next, Action.next, Action.token, Action.skip, Action.next, Action.next])
  (node "a" [node "b" [], node "c" [node "d" []]]) =
  Except.ok ["{", "F", "a", "{", "V", "b", "}", "$"]

-- walk next next token next next token next token skip
#guard runTree
  (walk [Action.next, Action.next, Action.token, Action.next, Action.next, Action.token, Action.next, Action.token, Action.skip, Action.next, Action.next, Action.next])
  (node "a" [node "b" [], node "c" [node "d" []]]) =
  Except.ok ["{", "F", "a", "{", "V", "b", "F", "c", "}", "}", "$"]

theorem next_decreases_stack_size
  {hint: Hint}
  {thisParserState nextParserState: ParserState α}
  (hneof: hint ≠ Hint.eof)
  (h: Except.ok (hint, nextParserState) = run next thisParserState):
  sizeOf nextParserState < sizeOf thisParserState := by
  have h' := Eq.symm h
  clear h
  have h := congrArg (Except.map (fun x => x.snd)) h'
  simp [Except.map] at h
  cases thisParserState with
  | mk thisCurrent thisStack =>
  cases thisCurrent with
  | unknown xs =>
    rw [next_unknown_gt_opened] at h
    simp at h
    rw [<- h]
    exact sizeOf_unknown_gt_opened
  | opened xs =>
    cases xs with
    | nil =>
      cases thisStack with
      | nil =>
        rw [next_opened_gt_popped_opened_eof] at h
        simp at h
        rw [<- h]
        exact sizeOf_opened_gt_popped_opened_eof
      | cons s' ss' =>
        rw [next_opened_gt_popped_opened_more] at h
        simp at h
        rw [<- h]
        exact sizeOf_opened_gt_popped_opened_more
    | cons tree fsiblings =>
      cases tree with
      | mk f v =>
        cases v with
        | nil =>
          -- is value
          rw [next_opened_value_gt_value] at h
          simp at h
          rw [<- h]
          exact sizeOf_opened_value_gt_value
        | cons v vsiblings =>
          -- is pair or field
          cases v with
          | mk v vchildren =>
            cases vchildren with
            | nil =>
              cases vsiblings with
              | nil =>
                -- is pair
                rw [next_opened_pair_gt_pair] at h
                simp at h
                rw [<- h]
                exact sizeOf_opened_pair_gt_pair
              | cons vsibling vsiblings =>
                -- is field
                rw [next_opened_gt_push] at h
                simp at h
                rw [<- h]
                apply sizeOf_opened_gt_push
                right
                exists ParseTree.mk v []
                exists vsibling
                exists vsiblings
            | cons vchild vchildren =>
              -- if field
              rw [next_opened_gt_push] at h
              simp at h
              rw [<- h]
              apply sizeOf_opened_gt_push
              cases vsiblings with
              | nil =>
                left
                exists v
                exists vchild
                exists vchildren
              | cons vsibling vsiblings =>
                right
                exists ParseTree.mk v (vchild :: vchildren)
                exists vsibling
                exists vsiblings
  | value x xs =>
    cases xs with
    | nil =>
      cases thisStack with
      | nil =>
        rw [next_value_gt_popped_value_eof] at h
        simp at h
        rw [<- h]
        exact sizeOf_value_gt_popped_value_eof
      | cons s' ss' =>
        rw [next_value_gt_popped_value_more] at h
        simp at h
        rw [<- h]
        exact sizeOf_value_gt_popped_value_more
    | cons tree fsiblings =>
      cases tree with
      | mk f v =>
        cases v with
        | nil =>
          -- is value
          rw [next_value_value_gt_value] at h
          simp at h
          rw [<- h]
          exact sizeOf_opened_value_gt_value
        | cons v vsiblings =>
          -- is pair or field
          cases v with
          | mk v vchildren =>
            cases vchildren with
            | nil =>
              cases vsiblings with
              | nil =>
                -- is pair
                rw [next_value_pair_gt_pair] at h
                simp at h
                rw [<- h]
                exact sizeOf_opened_pair_gt_pair
              | cons vsibling vsiblings =>
                -- is field
                rw [next_value_gt_push] at h
                simp at h
                rw [<- h]
                apply sizeOf_opened_gt_push
                right
                exists ParseTree.mk v []
                exists vsibling
                exists vsiblings
            | cons vchild vchildren =>
              -- if field
              rw [next_value_gt_push] at h
              simp at h
              rw [<- h]
              apply sizeOf_opened_gt_push
              cases vsiblings with
              | nil =>
                left
                exists v
                exists vchild
                exists vchildren
              | cons vsibling vsiblings =>
                right
                exists ParseTree.mk v (vchild :: vchildren)
                exists vsibling
                exists vsiblings
  | pair f v xs =>
    rw [next_pair_gt_value] at h
    simp at h
    rw [<- h]
    exact sizeOf_pair_gt_value
  | field f xs =>
    rw [next_field_gt_opened] at h
    simp at h
    rw [<- h]
    exact sizeOf_field_gt_opened
  | eof =>
    rw [next_eof_gt_eof] at h'
    simp at h'
    obtain ⟨heof, _⟩ := h'
    rw [<- heof] at hneof
    contradiction
