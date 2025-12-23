import Validator.Regex.Regex

import Validator.Std.Vec

namespace Regex

def map (r: Regex α) (f: α -> β): Regex β :=
  match r with
  | emptyset => emptyset
  | emptystr => emptystr
  | symbol s => symbol (f s)
  | or r1 r2 => or (map r1 f) (map r2 f)
  | concat r1 r2 => concat (map r1 f) (map r2 f)
  | star r1 => star (map r1 f)

theorem map_id (r: Regex α):
  map r (fun s => s) = r := by
  induction r with
  | emptyset =>
    simp only [map]
  | emptystr =>
    simp only [map]
  | symbol =>
    simp only [map]
  | or r1 r2 ih1 ih2 =>
    simp only [map]
    rw [ih1]
    rw [ih2]
  | concat r1 r2 ih1 ih2 =>
    simp only [map]
    rw [ih1]
    rw [ih2]
  | star r1 ih1 =>
    simp only [map]
    rw [ih1]

theorem map_map (r: Regex α) (f: α -> β) (g: β -> σ):
  map (map r f) g = map r (fun r' => g (f r')) := by
  induction r with
  | emptyset =>
    simp only [map]
  | emptystr =>
    simp only [map]
  | symbol =>
    simp only [map]
  | or r1 r2 ih1 ih2 =>
    simp only [map]
    rw [ih1]
    rw [ih2]
  | concat r1 r2 ih1 ih2 =>
    simp only [map]
    rw [ih1]
    rw [ih2]
  | star r1 ih1 =>
    simp only [map]
    rw [ih1]

theorem map_null {σ} (Φ: σ -> Bool) (r: Regex σ):
  (map r (fun s => (s, Φ s))).null = r.null := by
  induction r with
  | emptyset =>
    simp only [map, Regex.null]
  | emptystr =>
    simp only [map, Regex.null]
  | symbol _ =>
    simp only [map, Regex.null]
  | or r1 r2 ih1 ih2 =>
    simp only [map, Regex.null]
    rw [ih1]
    rw [ih2]
  | concat r1 r2 ih1 ih2 =>
    simp only [map, Regex.null]
    rw [ih1]
    rw [ih2]
  | star r1 ih1 =>
    simp only [map, Regex.null]

def maps (rs: Vec (Regex α) l) (f: α -> β): Vec (Regex β) l :=
  Vec.map rs (fun r => Regex.map r f)
