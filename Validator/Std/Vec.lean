import Mathlib.Data.Vector.Basic
import Mathlib.Data.Vector.Snoc

namespace Vec

def fromList (xs: List α): List.Vector α (xs.length) :=
  Subtype.mk xs rfl
