import Validator.Regex.Num
import Validator.Regex.Regex
import Validator.Regex.RegexID

namespace Regex.Symbol

def replace (r: RegexID n) (xs: Vec σ l) (h: n <= l): Regex σ :=
  match r with
  | Regex.emptyset => Regex.emptyset
  | Regex.emptystr => Regex.emptystr
  | Regex.symbol s => Regex.symbol (Vec.get xs (Fin.mk s.val (by
      cases s
      simp only
      omega
    )))
  | Regex.or r1 r2 =>
    Regex.or (replace r1 xs h) (replace r2 xs h)
  | Regex.concat r1 r2 =>
    Regex.concat (replace r1 xs h) (replace r2 xs h)
  | Regex.star r1 =>
    Regex.star (replace r1 xs h)

def replaceFrom (r: RegexID n) (xs: Vec σ n): Regex σ :=
  replace r xs (le_refl n)

def replacesFrom (rs: Vec (RegexID n) l) (xs: Vec σ n): Vec (Regex σ) l :=
  Vec.map rs (fun r => replaceFrom r xs)

theorem replace_cast_both (r: RegexID n) (xs: Vec σ n) (h: n = l):
  replace r xs (by omega) = replace (RegexID.cast r h) (Vec.cast xs h) (by omega) := by
  subst h
  simp only [Vec.cast_rfl]
  rfl

theorem replaceFrom_cast_both (r: RegexID n) (xs: Vec σ n) (h: n = l):
  replaceFrom r xs = replaceFrom (RegexID.cast r h) (Vec.cast xs h) := by
  unfold replaceFrom
  rw [replace_cast_both]

theorem replace_cast_symbols (r: RegexID n) (xs: Vec σ n) (h: n = l):
  replace r xs (by omega) = replace r (Vec.cast xs h) (by omega) := by
  subst h
  simp only [Vec.cast_rfl]

theorem replace_nil_is_map_id (r: Regex (Fin 0)):
  replace r Vec.nil (by simp) = Regex.map r id := by
  induction r with
  | emptyset =>
    simp only [replace, Regex.map]
  | emptystr =>
    simp only [replace, Regex.map]
  | symbol s =>
    nomatch s
  | or r1 r2 ih1 ih2 =>
    simp only [replace, Regex.map, Regex.or.injEq]
    rw [ih1]
    rw [ih2]
    apply And.intro rfl rfl
  | concat r1 r2 ih1 ih2 =>
    simp only [replace, Regex.map, Regex.concat.injEq]
    rw [ih1]
    rw [ih2]
    apply And.intro rfl rfl
  | star r1 ih1 =>
    simp only [replace, Regex.map]
    rw [ih1]

theorem replace_take (r: RegexID n) (xs: Vec σ (n + l)):
  replace r (Vec.take n xs) (by omega) = replace r xs (by omega):= by
  induction r with
  | emptyset =>
    simp only [replace]
  | emptystr =>
    simp only [replace]
  | symbol s =>
    generalize_proofs h1 h2 at *
    simp only [replace]
    obtain ⟨s, hs⟩ := s
    simp only [Regex.symbol.injEq]
    generalize_proofs h3 h4
    rw [Vec.take_get]
    omega
  | or r1 r2 ih1 ih2 =>
    simp only [replace, Regex.or.injEq]
    generalize_proofs h1 h2 at *
    rw [<- ih1]
    rw [<- ih2]
    apply And.intro rfl rfl
  | concat r1 r2 ih1 ih2 =>
    simp only [replace, Regex.concat.injEq]
    generalize_proofs h1 h2 at *
    rw [<- ih1]
    rw [<- ih2]
    apply And.intro rfl rfl
  | star r1 ih1 =>
    simp only [replace]
    generalize_proofs h1 at *
    rw [<- ih1]

theorem replace_regexid_add (r: RegexID n) (xs: Vec σ (n + l)):
  replace r xs (by omega) = replace (RegexID.add l r) xs (by omega):= by
  generalize_proofs h1 h2
  induction r with
  | emptyset =>
    simp only [replace, RegexID.add, Regex.map]
  | emptystr =>
    simp only [replace, RegexID.add, Regex.map]
  | symbol s =>
    generalize_proofs h1 h2 at *
    simp only [replace, RegexID.add, Regex.map, Fin.coe_castLE]
  | or r1 r2 ih1 ih2 =>
    simp only [replace, RegexID.add, Regex.map, Regex.or.injEq]
    generalize_proofs h1 h2 at *
    rw [ih1]
    rw [ih2]
    apply And.intro rfl rfl
  | concat r1 r2 ih1 ih2 =>
    simp only [replace, RegexID.add, Regex.map, Regex.concat.injEq]
    generalize_proofs h1 h2 at *
    rw [ih1]
    rw [ih2]
    apply And.intro rfl rfl
  | star r1 ih1 =>
    simp only [replace, RegexID.add, Regex.map, Regex.star.injEq]
    generalize_proofs h1 h2 at *
    rw [ih1]
    rfl

theorem replacesFrom_cast_both (rs: Vec (RegexID n) l) (ss: Vec σ n) (h: n = m):
  replacesFrom rs ss =
  replacesFrom (RegexID.casts rs h) (Vec.cast ss h) := by
  subst h
  simp only [Vec.cast_rfl]
  simp only [RegexID.casts_rfl]

theorem replacesFrom_cons (rs: Vec (RegexID n) l) (xs: Vec σ n):
  replacesFrom (Vec.cons r rs) xs
  = Vec.cons (replaceFrom r xs) (replacesFrom rs xs)
  := by
  simp only [replacesFrom]
  simp only [Vec.map]

theorem replaceFrom_append (e: RegexID n) {xs: Vec α n} {ys: Vec α m}:
  replaceFrom (RegexID.add m e) (Vec.append xs ys)
  = replaceFrom e xs := by
  unfold replaceFrom
  rw [← replace_regexid_add e (xs.append ys)]
  rw [← replace_take e (xs.append ys)]
  rw [Vec.take_append xs ys]
  rw [replace_cast_symbols]
