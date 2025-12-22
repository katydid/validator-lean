import Validator.Regex.Enter
import Validator.Regex.Functor
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

def derive_unfolded {σ: Type}
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

def derive_unapplied {σ: Type} {α: Type} (Φ: σ -> α -> Bool) (r: Regex σ) (a: α): Regex σ :=
  let symbols: Vec σ (Symbol.num r) := Enter.enter r
  let pred_results: Vec Bool (Symbol.num r) := Vec.map symbols (flip Φ a)
  Leave.leave r pred_results

def derive_unapplied_unfolded {σ: Type} {α: Type} (Φ: σ -> α -> Bool) (r: Regex σ) (a: α): Regex σ :=
  let (r', symbols): (Symbol.RegexID (Symbol.num r) × Vec σ (Symbol.num r)) := Symbol.extractFrom r
  let pred_results: Vec Bool (Symbol.num r) := Vec.map symbols (fun s => Φ s a)
  let replaces: Vec (σ × Bool) (Symbol.num r) := Vec.zip symbols pred_results
  let replaced: Regex (σ × Bool) := Symbol.replaceFrom r' replaces
  Regex.Point.derive replaced

theorem derive_is_derive_unfolded (Φ: σ -> Bool) (r: Regex σ):
  derive Φ r = derive_unfolded Φ r := by
  simp only [derive, derive_unfolded, Enter.enter, Leave.leave]

theorem derive_unapplied_is_derive_unapplied_unfolded (Φ: σ -> α -> Bool) (r: Regex σ):
  derive_unapplied Φ r = derive_unapplied_unfolded Φ r := by
  unfold derive_unapplied
  unfold derive_unapplied_unfolded
  unfold flip
  simp only [Enter.enter, Leave.leave]

theorem Room_derive_unapplied_unfolded_is_Regex_derive
  {σ: Type} {α: Type} (Φ: σ -> α -> Bool) (r: Regex σ) (a: α):
  Room.derive_unapplied_unfolded Φ r a = Regex.derive Φ r a := by
  unfold Room.derive_unapplied_unfolded
  simp only
  rw [<- Vec.zip_map]
  rw [<- Symbol.extractFrom_replaceFrom_is_fmap]
  rw [Regex.Point.derive_is_point_derive]

theorem Room_derive_unfolded_is_derive_unapplied_unfolded
  (p: σ -> Bool) (r: Regex σ) (a: α):
  Room.derive_unfolded p r = Room.derive_unapplied_unfolded (fun s _ => p s) r a := by
  rfl

theorem Room_derive_unapplied_unfolded_is_derive_unfolded
  (p: σ -> α -> Bool) (r: Regex σ) (a: α):
  Room.derive_unapplied_unfolded p r a = Room.derive_unfolded (fun s => p s a) r := by
  rfl
