import Validator.Deriv.Env

namespace EnvTreeParserIO

structure TreeParserAndMem where
  parser: ParseTree.TreeParser
  enter: Mem.MemEnter
  leave: Mem.MemLeave

abbrev TreeParserIO α := StateT TreeParserAndMem (EIO String) α

def TreeParserIO.mk (p: ParseTree.TreeParser): TreeParserAndMem :=
  TreeParserAndMem.mk p Std.ExtHashMap.emptyWithCapacity Std.ExtHashMap.emptyWithCapacity

def print (s: String): StateT TreeParserAndMem (EIO String) Unit := do
  StateT.lift (IO.toEIO (fun x => "ERROR: " ++ x.toString) (IO.println s))

-- TODO: find better way to write exactly the same code for each method.
-- There has to be shorter way to lift accross these monads.
instance : Parser TreeParserIO where
  next := do
    print "next"
    let s <- get
    match StateT.run ParseTree.next s.parser with
    | Except.ok (res, parser') =>
      set (TreeParserAndMem.mk parser' s.enter s.leave)
      return res
    | Except.error err =>
      throw err
  skip := do
    print "skip"
    let s <- get
    match StateT.run ParseTree.skip s.parser with
    | Except.ok (res, parser') =>
      set (TreeParserAndMem.mk parser' s.enter s.leave)
      return res
    | Except.error err =>
      throw err
  token := do
    print "token"
    let s <- get
    match StateT.run ParseTree.token s.parser with
    | Except.ok (res, parser') =>
      set (TreeParserAndMem.mk parser' s.enter s.leave)
      return res
    | Except.error err =>
      throw err

instance : Enter.DeriveEnters TreeParserIO where
  deriveEnters xs := do
    print "deriveEnters"
    let s <- get
    match StateT.run (m := Id) (Mem.enters xs) s.enter with
    | (res, enter') =>
      set (TreeParserAndMem.mk s.parser enter' s.leave)
      return res

instance : Leave.DeriveLeaves TreeParserIO where
  deriveLeaves xs ns := do
    print "deriveLeaves"
    let s <- get
    match StateT.run (Mem.leaves xs ns) s.leave with
    | Except.ok (res, leave') =>
      set (TreeParserAndMem.mk s.parser s.enter leave')
      return res
    | Except.error err =>
      throw err

instance : Env TreeParserIO where
  -- all instances have been created, so no implementations are required here

def run (f: TreeParserIO α) (t: ParseTree): EIO String α :=
  StateT.run' f (TreeParserIO.mk (ParseTree.TreeParser.mk t))
