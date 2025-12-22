import Validator.Regex.Enter
import Validator.Regex.Drawer
import Validator.Regex.Leave
import Validator.Regex.Num
import Validator.Regex.Regex

-- room, since we enter and leave
-- Also this a power in One Piece, which seems appropriate: https://onepiece.fandom.com/wiki/Ope_Ope_no_Mi
namespace Room

def derive {σ: Type}
  (Φ: σ -> Bool) (r: Regex σ): Regex σ :=
  let symbols: Vec σ (Symbol.num r) := Enter.enter r
  let pred_results: Vec Bool (Symbol.num r) := Vec.map symbols Φ
  Leave.leave r pred_results

def derive_unapplied {σ: Type} {α: Type} (Φ: σ -> α -> Bool) (r: Regex σ) (a: α): Regex σ :=
  let symbols: Vec σ (Symbol.num r) := Enter.enter r
  let pred_results: Vec Bool (Symbol.num r) := Vec.map symbols (flip Φ a)
  Leave.leave r pred_results
