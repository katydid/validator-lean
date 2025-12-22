import Validator.Regex.Enter
import Validator.Regex.Leave
import Validator.Regex.Num
import Validator.Regex.Regex

-- room, since we enter and leave
-- Also this a power in One Piece, which seems appropriate: https://onepiece.fandom.com/wiki/Ope_Ope_no_Mi
namespace Room

def derive_partial {σ: Type}
  (Φ: σ -> Bool) (r: Regex σ): Regex σ :=
  let symbols: Vec σ (Symbol.num r) := Enter.enter r
  let pred_results: Vec Bool (Symbol.num r) := Vec.map symbols Φ
  Leave.leave r pred_results

def derive_partial_unfolded {σ: Type}
  (Φ: σ -> Bool) (r: Regex σ): Regex σ :=
  Regex.Point.derive
    (Symbol.replaceFrom
      (Symbol.extractFrom r).1
      (Vec.zip
        (Symbol.extractFrom r).2
        (Vec.map
          (Symbol.extractFrom r).2
          Φ
        )
      )
    )

def derive {σ: Type} {α: Type} (Φ: σ -> α -> Bool) (r: Regex σ) (a: α): Regex σ :=
  let symbols: Vec σ (Symbol.num r) := Enter.enter r
  let pred_results: Vec Bool (Symbol.num r) := Vec.map symbols (flip Φ a)
  Leave.leave r pred_results

def derive_unfolded {σ: Type} {α: Type} (Φ: σ -> α -> Bool) (r: Regex σ) (a: α): Regex σ :=
  let (r', symbols): (Symbol.RegexID (Symbol.num r) × Vec σ (Symbol.num r)) := Symbol.extractFrom r
  let pred_results: Vec Bool (Symbol.num r) := Vec.map symbols (fun s => Φ s a)
  let replaces: Vec (σ × Bool) (Symbol.num r) := Vec.zip symbols pred_results
  let replaced: Regex (σ × Bool) := Symbol.replaceFrom r' replaces
  Regex.Point.derive replaced

theorem derive_partial_is_derive_partial_unfolded (Φ: σ -> Bool) (r: Regex σ):
  derive_partial Φ r = derive_partial_unfolded Φ r := by
  simp only [derive_partial, derive_partial_unfolded, Enter.enter, Leave.leave]

theorem derive_is_derive_unfolded (Φ: σ -> α -> Bool) (r: Regex σ):
  derive Φ r = derive_unfolded Φ r := by
  unfold derive
  unfold derive_unfolded
  unfold flip
  simp only [Enter.enter, Leave.leave]
