inductive Hint where
  | enter
  | leave
  | field
  | value
  | eof
  deriving Repr, DecidableEq

instance : ToString Hint :=
  ⟨ fun h =>
    match h with
    | Hint.enter => "{"
    | Hint.leave => "}"
    | Hint.field => "F"
    | Hint.value => "V"
    | Hint.eof => "$"
  ⟩

namespace Hint
