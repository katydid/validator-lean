import Validator.Std.Vec

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

def derives {σ: Type}
  (Φ: σ -> Bool) (rs: Vec (Regex σ) l): Vec (Regex σ) l :=
  let symbols: Vec σ (Symbol.nums rs) := Enter.enters rs
  let pred_results: Vec Bool (Symbol.nums rs) := Vec.map symbols Φ
  Leave.leaves rs pred_results

def derives_unapplied {σ: Type} {α: Type}
  (Φ: σ -> α -> Bool) (rs: Vec (Regex σ) l) (a: α): Vec (Regex σ) l :=
  let symbols: Vec σ (Symbol.nums rs) := Enter.enters rs
  let pred_results: Vec Bool (Symbol.nums rs) := Vec.map symbols (flip Φ a)
  let res: Vec (Regex σ) l := Leave.leaves rs pred_results
  res

def derives_distrib {σ: Type}
  (ps: {n: Nat} -> Vec σ n -> Vec Bool n) (rs: Vec (Regex σ) l): Vec (Regex σ) l :=
  let symbols: Vec σ (Symbol.nums rs) := Enter.enters rs
  let pred_results: Vec Bool (Symbol.nums rs) := ps symbols
  Leave.leaves rs pred_results

def derives_unapplied_distrib {σ: Type} {α: Type}
  (ps: {n: Nat} -> Vec σ n -> α -> Vec Bool n) (rs: Vec (Regex σ) l) (a: α): Vec (Regex σ) l :=
  let symbols: Vec σ (Symbol.nums rs) := Enter.enters rs
  let pred_results: Vec Bool (Symbol.nums rs) := ps symbols a
  Leave.leaves rs pred_results

theorem derives_is_derives_unapplied
  {σ: Type} {α: Type} (p: σ -> Bool) (rs: Vec (Regex σ) l) (a: α):
  Room.derives p rs = Room.derives_unapplied (fun s _ => p s) rs a := by
  rfl

theorem derives_unapplied_is_derives
  {σ: Type} {α: Type} (p: σ -> α -> Bool) (rs: Vec (Regex σ) l) (a: α):
  Room.derives_unapplied p rs a = Room.derives (fun s => p s a) rs := by
  rfl

theorem derives_unapplied_is_fmap
  {σ: Type} {α: Type} (Φ: σ -> α -> Bool) (rs: Vec (Regex σ) l) (a: α):
  Room.derives_unapplied Φ rs a = Vec.map rs (fun r => Room.derive_unapplied Φ r a) := by
  unfold Room.derives_unapplied
  unfold Enter.enters
  unfold Leave.leaves
  simp only
  unfold Regex.Point.derives
  unfold Room.derive_unapplied
  unfold Enter.enter
  unfold Leave.leave
  unfold flip
  nth_rewrite 2 [<- Vec.map_map]
  nth_rewrite 1 [<- Vec.map_map]
  apply (congrArg (fun xs => Vec.map xs Regex.Point.derive))
  rw [Vec.map_id]
  rw [<- Vec.zip_map]
  rw [<- Symbol.extractsFrom_replacesFrom_is_fmap]
  unfold Regex.maps
  simp only [<- Vec.zip_map]
  simp only [<- Symbol.extractFrom_replaceFrom_is_fmap]

theorem derives_unapplied_is_Regex_map_derive
  {σ: Type} {α: Type} (Φ: σ -> α -> Bool)
  (r: Vec (Regex σ) l) (a: α):
  Room.derives_unapplied Φ r a = Regex.map_derive Φ r a := by
  rw [derives_unapplied_is_fmap]
  unfold Room.derive_unapplied
  unfold flip
  unfold Enter.enter
  unfold Leave.leave
  unfold Regex.map_derive
  congr
  funext r
  simp only [<- Vec.zip_map]
  rw [<- Symbol.extractFrom_replaceFrom_is_fmap]
  rw [Regex.Point.derive_is_point_derive]

theorem derives_is_derives_unapplied_distrib
  {σ: Type} {α: Type} (ps: {n: Nat} -> Vec σ n -> α -> Vec Bool n) (rs: Vec (Regex σ) l) (a: α)
  (h: ∀ {n': Nat} (xs: Vec σ n') (a: α), ps xs a = Vec.map xs (fun x => (ps (#vec[x]) a).head)):
  Room.derives_unapplied (fun s a => (ps #vec[s] a).head) rs a = Room.derives_unapplied_distrib ps rs a := by
  unfold Room.derives_unapplied
  simp only
  unfold Leave.leaves
  unfold Enter.enters
  unfold flip
  simp only
  rw [<- h]
  unfold Room.derives_unapplied_distrib
  unfold Leave.leaves
  unfold Enter.enters
  simp only

theorem derives_unapplied_distrib_isderives_distrib
  {σ: Type} {α: Type} (ps: {n: Nat} -> Vec σ n -> α -> Vec Bool n) (rs: Vec (Regex σ) l) (a: α):
  Room.derives_unapplied_distrib ps rs a = Room.derives_distrib (fun ss => ps ss a) rs := by
  rfl

theorem derives_distrib_is_derives_unapplied_distrib
  {σ: Type} {α: Type} (ps: {n: Nat} -> Vec σ n -> Vec Bool n) (rs: Vec (Regex σ) l) (a: α):
  Room.derives_distrib ps rs = Room.derives_unapplied_distrib (fun ss _ => ps ss) rs a := by
  rfl

theorem derives_distrib_nil:
  Room.derives_distrib ps Vec.nil = Vec.nil := by
  rfl
