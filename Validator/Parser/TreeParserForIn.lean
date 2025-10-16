import Validator.Parser.Hint
import Validator.Std.Hedge
import Validator.Parser.TreeParser

namespace TreeParserForIn

def forIn {α: Type} {β: Type v} {m: Type v -> Type v'} [Monad m]
  (initParser: TreeParser.ParserState α) (initLoop: β) (f: Hint -> β -> m (ForInStep β)): m β :=
  let rec loop (loopState: β) (parserState: TreeParser.ParserState α): m β :=
    match _hnext: TreeParser.run TreeParser.next parserState with
    | Except.error _err =>
      pure loopState
      -- TODO do not just terminate, but `throw _err`
    | Except.ok ⟨ hint, parserState' ⟩ =>
      if hint = Hint.eof
      then pure loopState
      else do
        match (<- f hint loopState) with
        | ForInStep.done loopState' => pure loopState'
        | ForInStep.yield loopState' => loop loopState' parserState'
    termination_by parserState
    decreasing_by
      apply @TreeParser.next_decreases_size_of_parserstate _ hint parserState parserState'
      · assumption
      · exact (Eq.symm _hnext)
  loop initLoop initParser

-- class ForIn (m : Type u₁ → Type u₂) (ρ : Type u) (α : outParam (Type v)) where
instance [Monad m]: ForIn m (TreeParser.ParserState α) Hint where
  -- forIn {β} [Monad m] (state : ρ) (b : β) (f : α → β → m (ForInStep β)) : m β
  forIn {β} [Monad m] (state: TreeParser.ParserState α) (init : β) (f : Hint → β → m (ForInStep β)): m β := forIn state init f

open Parser (walk Action)
open TokenTree (node)

def exampleLoop: IO Unit := do
  let tree := TreeParser.ParserState.mk' (node "a" [node "b" [], node "c" [node "d" []]])
  for hint in tree do
    IO.println hint

/--
info: {
F
{
V
F
V
}
}
-/
#guard_msgs in
#eval exampleLoop
