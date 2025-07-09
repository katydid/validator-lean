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
