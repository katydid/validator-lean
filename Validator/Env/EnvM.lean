import Validator.Std.Debug

import Validator.Parser.Parser
import Validator.Parser.ParseTree

import Validator.Derive.Enter
import Validator.Derive.Leave

-- EnvM is the derivative validator environment monad.
-- Executing the derivative algorithm requires:
--   a pull based Parser
--   a deriveEnter and deriveLeave function that could optionally be memoized.
--   the possibility of returning an error.
--   a debug line printer (implementations should print nothing when not debugging).
-- Tagless final class inspired by https://jproyo.github.io/posts/2019-03-17-tagless-final-haskell/
class EnvM (m: Type -> Type u) extends
  Monad m,
  Debug m,
  MonadExcept String m,
  Parser m,
  Enter.DeriveEnter m,
  Leave.DeriveLeave m

namespace EnvM
