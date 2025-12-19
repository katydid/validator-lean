import Validator.Regex.Regex

namespace Regex.Closure

-- derive embeds the input alphabet symbol α inside of the predicate closure,
-- so there is no need to pass it along as a parameter as well.
def derive {σ: Type} (Φ: σ -> Bool) (r: Regex σ): Regex σ :=
  match r with
  | emptyset => emptyset
  | emptystr => emptyset
  | symbol s => onlyif (Φ s) emptystr
  | or r1 r2 =>
    or (derive Φ r1) (derive Φ r2)
  | concat r1 r2 =>
    or
      (concat (derive Φ r1) r2)
      (onlyif (nullable r1) (derive Φ r2))
  | star r1 =>
    concat (derive Φ r1) (star r1)
