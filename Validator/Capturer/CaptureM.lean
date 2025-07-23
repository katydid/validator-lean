import Validator.Std.Debug

import Validator.Parser.Parser

class CaptureM (m: Type -> Type u) (α: Type) extends
  Monad m,
  Debug m,
  MonadExcept String m,
  Parser m α
