import Validator.Std.Debug

import Validator.Parser.Parser

import Validator.Derive.Enter
import Validator.Derive.Leave

-- ValidateM is the collection of monads required for the validator.
-- Executing the derivative validator algorithm requires:
--   a pull based Parser
--   a deriveEnter and deriveLeave function that could optionally be memoized.
--   the possibility of returning an error.
--   a debug line printer (implementations should print nothing when not debugging).
-- Tagless final class inspired by https://jproyo.github.io/posts/2019-03-17-tagless-final-haskell/
class ValidateM (m: Type -> Type u) (μ: Nat) (α: Type) extends
  Monad m,
  Debug m,
  MonadExcept String m,
  Parser m α,
  Enter.DeriveEnter m μ α,
  Leave.DeriveLeaveM m μ α

namespace ValidateM
