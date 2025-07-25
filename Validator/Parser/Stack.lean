inductive Stack (α: Type u) where
  | mk (current: α) (stack: List α)

namespace Stack

def getCurrent {α: outParam Type} [Monad m] [MonadState (Stack α) m]: m α := do
  let s <- get
  match s with
  | Stack.mk curr _ => return curr

def setCurrent [Monad m] [MonadStateOf (Stack α) m] (t: α): m Unit := do
  let s <- get
  match s with
  | Stack.mk _ stack =>
    set (Stack.mk t stack)
    return ()

def push [Monad m] [MonadStateOf (Stack α) m] (top: α): m Unit := do
  let s <- get
  match s with
  | Stack.mk oldtop stack =>
    set (Stack.mk top (oldtop::stack))
    return ()

def pop [Monad m] [MonadStateOf (Stack α) m]: m Bool := do
  let s <- get
  match s with
  | Stack.mk _ [] =>
    return false
  | Stack.mk _ (newtop::stack) =>
    set (Stack.mk newtop stack)
    return true
