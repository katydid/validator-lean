inductive Stack (S: Type) where
  | mk (current: S) (stack: List S)

namespace Stack

def getCurrent [Monad m]: StateT (Stack S) m S := do
  let s <- get
  match s with
  | Stack.mk curr _ => return curr

def setCurrent [Monad m] (t: S): StateT (Stack S) m Unit := do
  let s <- get
  match s with
  | Stack.mk _ stack =>
    set (Stack.mk t stack)
    return ()

def push [Monad m] (top: S): StateT (Stack S) m Unit := do
  let s <- get
  match s with
  | Stack.mk oldtop stack =>
    set (Stack.mk top (oldtop::stack))
    return ()

def pop [Monad m]: StateT (Stack S) m Bool := do
  let s <- get
  match s with
  | Stack.mk _ [] =>
    return false
  | Stack.mk _ (newtop::stack) =>
    set (Stack.mk newtop stack)
    return true
