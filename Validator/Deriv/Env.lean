import Validator.Std.Debug

import Validator.Parser.Parser
import Validator.Parser.ParseTree

import Validator.Deriv.Enter
import Validator.Deriv.Leave
import Validator.Deriv.Mem

-- Env is the derivative validator environment.
-- Executing the derivative algorithm requires:
--   a pull based Parser
--   a deriveEnter and deriveLeave function that could optionally be memoized.
--   the possibility of returning an error.
-- Tagless final class inspired by https://jproyo.github.io/posts/2019-03-17-tagless-final-haskell/
class Env (m: Type -> Type u) extends
  Monad m,
  Debug m,
  MonadExcept String m,
  Parser m,
  Enter.DeriveEnters m,
  Leave.DeriveLeaves m

namespace Env
