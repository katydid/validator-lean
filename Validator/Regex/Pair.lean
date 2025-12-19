import Validator.Regex.Regex
import Validator.Regex.Map

namespace Regex.Pair

def first (r: Regex (α × β)): Regex α :=
  map r (fun (s, _) => s)

-- Regex.Pair.derive is the same as Regex.derive, except the answer to the predicate is already included in a tuple with the original symbol.
def derive {σ: Type} (r: Regex (σ × Bool)): Regex σ :=
  match r with
  | emptyset => emptyset
  | emptystr => emptyset
  | symbol (_, b) => onlyif b emptystr
  | or r1 r2 =>
    or (derive r1) (derive r2)
  | concat r1 r2 =>
    or
      (concat (derive r1) (first r2))
      (onlyif (null r1) (derive r2))
  | star r1 =>
      concat (derive r1) (star (first r1))

theorem map_first (Φ: σ -> α -> Bool) (r: Regex σ) (a: α):
  first (Regex.map r (fun s => (s, Φ s a))) = r := by
  induction r with
  | emptyset =>
    simp only [Regex.map, first]
  | emptystr =>
    simp only [Regex.map, first]
  | symbol _ =>
    simp only [Regex.map, first]
  | or r1 r2 ih1 ih2 =>
    simp only [Regex.map, first]
    simp only [or.injEq]
    apply And.intro
    · exact ih1
    · exact ih2
  | concat r1 r2 ih1 ih2 =>
    simp only [Regex.map, first]
    simp only [concat.injEq]
    apply And.intro
    · exact ih1
    · exact ih2
  | star r1 ih1 =>
    simp only [Regex.map, first]
    simp only [star.injEq]
    exact ih1

theorem derive_is_pair_derive (Φ: σ -> α -> Bool) (r: Regex σ) (a: α):
  Regex.derive Φ r a = Regex.Pair.derive (map r (fun s => (s, Φ s a))) := by
  induction r with
  | emptyset =>
    simp only [Regex.derive, Regex.map, derive]
  | emptystr =>
    simp only [Regex.derive, Regex.map, derive]
  | symbol _ =>
    simp only [Regex.derive, Regex.map, derive]
  | or r1 r2 ih1 ih2 =>
    simp only [Regex.derive, Regex.map, derive]
    rw [<- ih1]
    rw [<- ih2]
  | concat r1 r2 ih1 ih2 =>
    simp only [Regex.derive, Regex.map, derive]
    rw [<- ih1]
    rw [<- ih2]
    have h : first (r2.map fun s => (s, Φ s a)) = r2 := by
      apply map_first
    have h' : (r1.map fun s => (s, Φ s a)).null = r1.null := by
      apply map_null
    rw [h]
    rw [h']
  | star r1 ih1 =>
    simp only [Regex.derive, Regex.map, derive]
    rw [<- ih1]
    have h : first (r1.map fun s => (s, Φ s a)) = r1 := by
      apply map_first
    rw [h]

def derives (rs: Vec (Regex (σ × Bool)) l): Vec (Regex σ) l :=
  Vec.map rs derive
