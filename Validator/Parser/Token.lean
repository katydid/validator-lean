def Bytes := Array UInt8
  deriving Repr

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

namespace Token
