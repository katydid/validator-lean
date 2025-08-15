abbrev Stack α := List α

namespace Stack

def getCurrent? {α: outParam Type} (stack: Stack α) : Option α :=
  match stack with
  | [] => Option.none
  | curr::_ => curr

def isEmpty (stack: Stack α): Bool :=
  match stack with
  | [] => true
  | _ => false

def getCurrentM? {α: outParam Type} [Monad m] [MonadState (Stack α) m]: m (Option α) := do
  let stack <- get
  return stack.getCurrent?

def setCurrentM [Monad m] [MonadExcept String m] [MonadStateOf (Stack α) m] (current: α): m Unit := do
  let stack <- get
  match stack with
  | [] =>
    throw "cannot setCurrent, stack is empty"
  | _::rest =>
    set (current::rest)
    return ()

def pushM [Monad m] [MonadStateOf (Stack α) m] (top: α): m Unit := do
  let stack <- get
  set (top::stack)
  return ()

def popM? [Monad m] [MonadStateOf (Stack α) m]: m (Option α) := do
  let stack <- get
  match stack with
  | [] =>
    return Option.none
  | top::rest =>
    set rest
    return Option.some top
