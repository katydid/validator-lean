class Debug (m: Type -> Type u) where
  debug (line: String): m Unit

namespace Debug

instance : Debug IO where
  debug (line: String) := IO.println line
