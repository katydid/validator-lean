import Validator.Regex.Regex

namespace Regex.Closure

-- derive embeds the input alphabet symbol α inside of the predicate closure,
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

theorem derive_is_closure_derive (Φ: σ -> α -> Bool) (r: Regex σ) (a: α):
  Regex.derive Φ r a = Regex.Closure.derive (fun s => Φ s a) r := by
  induction r with
  | emptyset =>
    simp only [Regex.derive, Regex.Closure.derive]
  | emptystr =>
    simp only [Regex.derive, Regex.Closure.derive]
  | symbol s =>
    simp only [Regex.derive, Regex.Closure.derive]
  | or r1 r2 ih1 ih2 =>
    simp only [Regex.derive, Regex.Closure.derive]
    rw [ih1]
    rw [ih2]
  | concat r1 r2 ih1 ih2 =>
    simp only [Regex.derive, Regex.Closure.derive]
    rw [ih1]
    rw [ih2]
  | star r1 ih1 =>
    simp only [Regex.derive, Regex.Closure.derive]
    rw [ih1]

theorem derive_commutesb {σ: Type} {α: Type} (Φ: σ -> α -> Bool) (r: Regex σ) (a: α):
  denote (fun s a => Φ s a) (Regex.Closure.derive (fun s => Φ s a) r) = Language.derive (denote (fun s a => Φ s a) r) a := by
  rw [<- derive_is_closure_derive]
  rw [<- Regex.derive_commutesb]

theorem derive_commutesb' {σ: Type} {α: Type} (Φ: σ -> α -> Bool) (r: Regex σ) (a: α):
  denote (fun s a => Φ s a) (Regex.Closure.derive (fun s => Φ s a) r) = Language.derive (denote (fun s a => Φ s a) r) a := by
  rw [<- derive_is_closure_derive]
  rw [<- Regex.derive_commutesb]
