import Validator.Regex.Regex
import Validator.Regex.Point

namespace Regex.Partial

-- derive partially applies the predicate with the input alphabet symbol α,
-- so there is no need to pass it along as a parameter as well.
def derive {σ: Type} (Φ: σ -> Bool) (r: Regex σ): Regex σ :=
  match r with
  | emptyset => emptyset
  | emptystr => emptyset
  | symbol s => onlyif (Φ s) emptystr
  | or r1 r2 => or (derive Φ r1) (derive Φ r2)
  | concat r1 r2 =>
    or
      (concat (derive Φ r1) r2)
      (onlyif (null r1) (derive Φ r2))
  | star r1 => concat (derive Φ r1) (star r1)

-- example to show how to partially apply the input inside the predicate
#guard
  Regex.derive (· == ·) (Regex.or (Regex.symbol 1) (Regex.symbol 2)) 1
  = Regex.Partial.derive (· == 1) (Regex.or (Regex.symbol 1) (Regex.symbol 2))

def map_derive (Φ: σ-> Bool) (rs: Vec (Regex σ) l): Vec (Regex σ) l :=
  Vec.map rs (fun r => derive Φ r)

theorem derive_is_partial_derive (Φ: σ -> α -> Bool) (r: Regex σ) (a: α):
  Regex.derive Φ r a = Regex.Partial.derive (fun s => Φ s a) r := by
  induction r with
  | emptyset =>
    simp only [Regex.derive, Regex.Partial.derive]
  | emptystr =>
    simp only [Regex.derive, Regex.Partial.derive]
  | symbol s =>
    simp only [Regex.derive, Regex.Partial.derive]
  | or r1 r2 ih1 ih2 =>
    simp only [Regex.derive, Regex.Partial.derive]
    rw [ih1]
    rw [ih2]
  | concat r1 r2 ih1 ih2 =>
    simp only [Regex.derive, Regex.Partial.derive]
    rw [ih1]
    rw [ih2]
  | star r1 ih1 =>
    simp only [Regex.derive, Regex.Partial.derive]
    rw [ih1]

theorem derive_commutesb {σ: Type} {α: Type} (Φ: σ -> α -> Bool) (r: Regex σ) (a: α):
  denote (fun s a => Φ s a) (Regex.Partial.derive (fun s => Φ s a) r) = Language.derive (denote (fun s a => Φ s a) r) a := by
  rw [<- derive_is_partial_derive]
  rw [<- Regex.derive_commutesb]

theorem derive_is_point_derive (Φ: σ -> Bool) (r: Regex σ):
  derive Φ r = Regex.Point.derive (map r (fun s => (s, Φ s))) := by
  induction r with
  | emptyset =>
    simp only [Regex.Point.derive, Regex.map, derive]
  | emptystr =>
    simp only [Regex.Point.derive, Regex.map, derive]
  | symbol _ =>
    simp only [Regex.Point.derive, Regex.map, derive]
  | or r1 r2 ih1 ih2 =>
    simp only [Regex.Point.derive, Regex.map, derive]
    rw [<- ih1]
    rw [<- ih2]
  | concat r1 r2 ih1 ih2 =>
    simp only [Regex.Point.derive, Regex.map, derive]
    rw [<- ih1]
    rw [<- ih2]
    have h : Regex.Point.first (r2.map fun s => (s, Φ s)) = r2 := by
      apply Regex.Point.map_first
    have h' : (r1.map fun s => (s, Φ s)).null = r1.null := by
      apply Regex.map_null
    rw [h]
    rw [h']
  | star r1 ih1 =>
    simp only [Regex.Point.derive, Regex.map, derive]
    rw [<- ih1]
    have h : Regex.Point.first (r1.map fun s => (s, Φ s)) = r1 := by
      apply Regex.Point.map_first
    rw [h]
