import Validator.Deriv.Env

namespace EnvTreeParserStateWithMem

structure TreeParserAndMem where
  parser: ParseTree.TreeParser
  enter: Mem.MemEnter
  leave: Mem.MemLeave

abbrev TreeParserStateWithMem α := EStateM String TreeParserAndMem α

def TreeParserStateWithMem.mk (p: ParseTree.TreeParser): TreeParserAndMem :=
  TreeParserAndMem.mk p Std.ExtHashMap.emptyWithCapacity Std.ExtHashMap.emptyWithCapacity

-- TODO: find better way to write exactly the same code for each method.
-- There has to be shorter way to lift accross these monads.
instance : Parser TreeParserStateWithMem where
  next := do
    let s <- get
    match StateT.run ParseTree.next s.parser with
    | Except.ok (res, parser') =>
      set (TreeParserAndMem.mk parser' s.enter s.leave)
      return res
    | Except.error err =>
      throw err
  skip := do
    let s <- get
    match StateT.run ParseTree.skip s.parser with
    | Except.ok (res, parser') =>
      set (TreeParserAndMem.mk parser' s.enter s.leave)
      return res
    | Except.error err =>
      throw err
  token := do
    let s <- get
    match StateT.run ParseTree.token s.parser with
    | Except.ok (res, parser') =>
      set (TreeParserAndMem.mk parser' s.enter s.leave)
      return res
    | Except.error err =>
      throw err

instance : Enter.DeriveEnters TreeParserStateWithMem where
  deriveEnters xs := do
    let s <- get
    match StateT.run (m := Id) (Mem.enters xs) s.enter with
    | (res, enter') =>
      set (TreeParserAndMem.mk s.parser enter' s.leave)
      return res

instance : Leave.DeriveLeaves TreeParserStateWithMem where
  deriveLeaves xs ns := do
    let s <- get
    match StateT.run (Mem.leaves xs ns) s.leave with
    | Except.ok (res, leave') =>
      set (TreeParserAndMem.mk s.parser s.enter leave')
      return res
    | Except.error err =>
      throw err

instance : Env TreeParserStateWithMem where
  -- all instances have been created, so no implementations are required here

def run (f: TreeParserStateWithMem α) (t: ParseTree): Except String α :=
  match EStateM.run f (TreeParserStateWithMem.mk (ParseTree.TreeParser.mk t)) with
  | EStateM.Result.ok k _ => Except.ok k
  | EStateM.Result.error err _ => Except.error err
