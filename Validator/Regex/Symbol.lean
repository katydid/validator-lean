import Validator.Std.Vec

import Validator.Regex.Enter
import Validator.Regex.Extract
import Validator.Regex.Functor
import Validator.Regex.Leave
import Validator.Regex.Map
import Validator.Regex.Num
import Validator.Regex.Point
import Validator.Regex.Regex
import Validator.Regex.RegexID
import Validator.Regex.Replace
import Validator.Regex.Room

-- I want to define a map function over a regular expression:

-- inductive Regex (σ: Type) where
--   | emptyset
--   | emptystr
--   | symbol (s: σ)
--   | or (p q: Regex σ)
--   | concat (p q: Regex σ)
--   | star (p: Regex σ)
--   deriving DecidableEq, Ord, Repr, Hashable

-- def Regex.map (r: Regex σ) (f: σ -> σ'): Regex σ' :=
--   match r with
--   | emptyset => emptyset
--   | emptystr => emptystr
--   | symbol s => symbol (f s)
--   | or r1 r2 => or (r1.map f) (r2.map f)
--   | concat r1 r2 => concat (r1.map f) (r2.map f)
--   | star r1 => star (r1.map f)

-- But I want to split the function application of the functor up into three steps:
-- 1. extract
-- 2. modify
-- 3. replace

-- We want to prove the theorem that if the function is id then replace (id (extract r)) = r

namespace Symbol

def derives {σ: Type} {α: Type} (Φ: σ -> α -> Bool) (rs: Vec (Regex σ) l) (a: α): Vec (Regex σ) l :=
  let (rs', symbols): (Vec (RegexID (Symbol.nums rs)) l × Vec σ (Symbol.nums rs)) := Symbol.extractsFrom rs
  let pred_results: Vec Bool (Symbol.nums rs) := Vec.map symbols (fun s => Φ s a)
  let replaces: Vec (σ × Bool) (Symbol.nums rs) := Vec.zip symbols pred_results
  let replaced: Vec (Regex (σ × Bool)) l := replacesFrom rs' replaces
  Regex.Point.derives replaced

-- derives_preds unlike derives takes a predicate that works out the full vector of predicates.
-- This gives the predicate control over the evaluation order of α, for example α is a tree, we can first evaluate the same label, before traversing down.
def derives_preds {σ: Type} {α: Type}
  (ps: {n: Nat} -> Vec σ n -> α -> Vec Bool n) (rs: Vec (Regex σ) l) (a: α): Vec (Regex σ) l :=
  let symbols: Vec σ (Symbol.nums rs) := Enter.enters rs
  let pred_results: Vec Bool (Symbol.nums rs) := ps symbols a
  Leave.leaves rs pred_results

def derives_closures {σ: Type}
  (ps: {n: Nat} -> Vec σ n -> Vec Bool n) (rs: Vec (Regex σ) l): Vec (Regex σ) l :=
  let symbols: Vec σ (Symbol.nums rs) := Enter.enters rs
  let pred_results: Vec Bool (Symbol.nums rs) := ps symbols
  Leave.leaves rs pred_results

def derives_closures' {σ: Type}
  (ps: {n: Nat} -> Vec σ n -> Vec Bool n) (rs: Vec (Regex σ) l): Vec (Regex σ) l :=
  Leave.leaves rs (ps (Enter.enters rs))

def derives_closure {σ: Type}
  (p: σ -> Bool) (rs: Vec (Regex σ) l): Vec (Regex σ) l :=
  let symbols: Vec σ (Symbol.nums rs) := Enter.enters rs
  let pred_results: Vec Bool (Symbol.nums rs) := Vec.map symbols p
  Leave.leaves rs pred_results

theorem Room_derive_unfolded_is_Regex_derive
  {σ: Type} {α: Type} (Φ: σ -> α -> Bool) (r: Regex σ) (a: α):
  Room.derive_unfolded Φ r a = Regex.derive Φ r a := by
  unfold Room.derive_unfolded
  simp only
  rw [<- Vec.zip_map]
  rw [<- extractFrom_replaceFrom_is_fmap]
  rw [Regex.Point.derive_is_point_derive]

theorem Symbol_derives_is_fmap
  {σ: Type} {α: Type} (Φ: σ -> α -> Bool) (rs: Vec (Regex σ) l) (a: α):
  Symbol.derives Φ rs a = Vec.map rs (fun r => Room.derive_unfolded Φ r a) := by
  unfold Symbol.derives
  simp only
  unfold Regex.Point.derives
  unfold Room.derive_unfolded
  nth_rewrite 2 [<- Vec.map_map]
  nth_rewrite 1 [<- Vec.map_map]
  apply (congrArg (fun xs => Vec.map xs Regex.Point.derive))
  rw [Vec.map_id]
  rw [<- Vec.zip_map]
  rw [<- extractsFrom_replacesFrom_is_fmap]
  unfold Regex.maps
  simp only [<- Vec.zip_map]
  simp only [<- extractFrom_replaceFrom_is_fmap]

theorem Symbol_derives_is_Regex_derives
  {σ: Type} {α: Type} (Φ: σ -> α -> Bool)
  (r: Vec (Regex σ) l) (a: α):
  Symbol.derives Φ r a = Regex.map_derive Φ r a := by
  rw [Symbol_derives_is_fmap]
  unfold Room.derive_unfolded
  unfold Regex.map_derive
  congr
  funext r
  simp only
  simp only [<- Vec.zip_map]
  rw [<- extractFrom_replaceFrom_is_fmap]
  rw [Regex.Point.derive_is_point_derive]

theorem Symbol_derives_is_derives_preds
  {σ: Type} {α: Type} (ps: {n: Nat} -> Vec σ n -> α -> Vec Bool n) (rs: Vec (Regex σ) l) (a: α)
  (h: ∀ {n': Nat} (xs: Vec σ n') (a: α), ps xs a = Vec.map xs (fun x => (ps (#vec[x]) a).head)):
  Symbol.derives (fun s a => (ps #vec[s] a).head) rs a = Symbol.derives_preds ps rs a := by
  unfold derives
  simp only
  rw [<- h]
  unfold derives_preds
  unfold Leave.leaves
  unfold Enter.enters
  simp only

theorem Symbol_derives_preds_is_derives_closures
  {σ: Type} {α: Type} (ps: {n: Nat} -> Vec σ n -> α -> Vec Bool n) (rs: Vec (Regex σ) l) (a: α):
  Symbol.derives_preds ps rs a = Symbol.derives_closures (fun ss => ps ss a) rs := by
  rfl

theorem Symbol_derives_closures_is_derives_preds
  {σ: Type} {α: Type} (ps: {n: Nat} -> Vec σ n -> Vec Bool n) (rs: Vec (Regex σ) l) (a: α):
  Symbol.derives_closures ps rs = Symbol.derives_preds (fun ss _ => ps ss) rs a := by
  rfl

theorem Symbol_derives_closures_nil:
  Symbol.derives_closures ps Vec.nil = Vec.nil := by
  rfl

theorem Symbol_derives_closure_is_derives
  {σ: Type} {α: Type} (p: σ -> Bool) (rs: Vec (Regex σ) l) (a: α):
  Symbol.derives_closure p rs = Symbol.derives (fun s _ => p s) rs a := by
  rfl

theorem Symbol_derives_is_derives_closure
  {σ: Type} {α: Type} (p: σ -> α -> Bool) (rs: Vec (Regex σ) l) (a: α):
  Symbol.derives p rs a = Symbol.derives_closure (fun s => p s a) rs := by
  rfl

theorem Room_derive_partial_unfolded_is_derive'
  (p: σ -> Bool) (r: Regex σ) (a: α):
  Room.derive_partial_unfolded p r = Room.derive_unfolded (fun s _ => p s) r a := by
  rfl

theorem Symbol_derive'_is_Room_derive_partial_unfolded
  (p: σ -> α -> Bool) (r: Regex σ) (a: α):
  Room.derive_unfolded p r a = Room.derive_partial_unfolded (fun s => p s a) r := by
  rfl
