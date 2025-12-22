import Validator.Regex.Regex
import Validator.Regex.Num

namespace Symbol

abbrev RegexID n := Regex (Fin n)

def RegexID.add {n: Nat} (m: Nat) (r: RegexID n): RegexID (n + m) :=
  Regex.map r (fun s => (Fin.castLE (by omega) s))

def RegexID.cast (r: RegexID n) (h: n = m): RegexID m :=
  match h with
  | Eq.refl _ => r

def RegexID.castLE {n: Nat} (r: RegexID n) (h : n ≤ m): RegexID m :=
  Regex.map r (fun s => (Fin.castLE h s))

def RegexID.cast_map (r: RegexID n) (h: n = m): RegexID m :=
  Regex.map r (fun s => Fin.castLE (by omega) s)

def RegexID.casts (rs: Vec (RegexID n) l) (h: n = m): Vec (RegexID m) l :=
  Vec.map rs (fun r => RegexID.cast r h)

def RegexID.casts_rw (rs: Vec (RegexID n) l) (h: n = m): Vec (RegexID m) l := by
  subst h
  exact rs

def RegexID.castsLE (rs: Vec (RegexID n) l) (h: n ≤ m): Vec (RegexID m) l :=
  Vec.map rs (fun r => RegexID.castLE r h)

abbrev RegexID.add_assoc (r: RegexID (n + Symbol.num r1 + Symbol.num r2)): RegexID (n + (Symbol.num r1 + Symbol.num r2)) :=
  have h : (n + Symbol.num r1 + Symbol.num r2) = n + (Symbol.num r1 + Symbol.num r2) := by
    rw [<- Nat.add_assoc]
  RegexID.cast r h

def RegexID.add_or (r: RegexID (n + Symbol.num r1 + Symbol.num r2)): RegexID (n + Symbol.num (Regex.or r1 r2)) :=
  RegexID.add_assoc r

def RegexID.add_concat (r: RegexID (n + Symbol.num r1 + Symbol.num r2)): RegexID (n + Symbol.num (Regex.concat r1 r2)) :=
  RegexID.add_assoc r

theorem RegexID.cast_rfl (r: RegexID n): RegexID.cast r rfl = r := by
  rfl

theorem RegexID.cast_rfl' (r: RegexID n) (h: n = n): RegexID.cast r h = r := by
  rfl

theorem RegexID.cast_map_rfl (r: RegexID n): RegexID.cast_map r rfl = r := by
  unfold RegexID.cast_map
  simp only [Fin.castLE_refl]
  rw [Regex.map_id]

theorem RegexID.cast_is_cast_map (r: RegexID n) (h: n = m):
  RegexID.cast r h = RegexID.cast_map r h := by
  subst h
  rw [RegexID.cast_rfl]
  rw [RegexID.cast_map_rfl]

theorem RegexID.cons_cast:
  Vec (RegexID (nacc + Symbol.nums (Vec.cons x xs))) n
  = Vec (RegexID (nacc + Symbol.num x + Symbol.nums xs)) n := by
  simp only [Symbol.nums]
  simp only [Vec.map]
  simp only [Vec.foldl]
  nth_rewrite 2 [Nat.add_comm]
  rw [Vec.foldl_assoc]
  ac_rfl

theorem RegexID.casts_rfl {n} {xs : Vec (RegexID n) l} {h : n = n} : RegexID.casts xs h = xs := by
  induction xs with
  | nil =>
    unfold RegexID.casts
    rfl
  | @cons l x xs ih =>
    simp only [casts] at *
    simp only [Vec.map]
    rw [ih]
    rfl

theorem RegexID.casts_symm:
  RegexID.casts rs1 h = rs2
  <->
  RegexID.casts rs2 (Eq.symm h) = rs1 := by
  apply Iff.intro
  case mp =>
    intro h
    rw [<- h]
    unfold RegexID.casts
    rw [Vec.map_map]
    simp only [RegexID.cast_is_cast_map]
    unfold RegexID.cast_map
    simp only [Regex.map_map]
    rename_i h_1
    subst h h_1
    simp_all only [Fin.castLE_refl]
    simp only [Regex.map_id]
    simp only [Vec.map_id]
  case mpr =>
    intro h
    rw [<- h]
    unfold RegexID.casts
    rw [Vec.map_map]
    simp only [RegexID.cast_is_cast_map]
    unfold RegexID.cast_map
    simp only [Regex.map_map]
    rename_i h_1
    subst h h_1
    simp_all only [Fin.castLE_refl]
    simp only [Regex.map_id]
    simp only [Vec.map_id]

theorem RegexID.cast_lift_cons {x: RegexID n} {h: n = m} {xs: Vec (RegexID n) l}:
  Vec.cons (RegexID.cast x h) (RegexID.casts xs h)
  = RegexID.casts (Vec.cons x xs) h := by
  simp only [RegexID.casts]
  simp only [Vec.map]

theorem RegexID.castLE_lift_cons {x: RegexID n} {h: n ≤ m} {xs: Vec (RegexID n) l}:
  Vec.cons (RegexID.castLE x h) (RegexID.castsLE xs h)
  = RegexID.castsLE (Vec.cons x xs) h := by
  simp only [RegexID.castsLE]
  simp only [Vec.map]

theorem RegexID.castLE_id {h: n ≤ n}:
  (RegexID.castLE r h) = r := by
  simp only [RegexID.castLE]
  simp_all only [Fin.castLE_refl]
  simp_all only [le_refl]
  rw [Regex.map_id]

theorem RegexID.castLE_casts_lift_cons {x: RegexID n1} {h1: n1 ≤ k} {h2: n2 = k} {xs: Vec (RegexID n2) l}:
  Vec.cons (RegexID.castLE x h1) (RegexID.casts xs h2)
  = RegexID.castsLE (Vec.cons (RegexID.castLE x (by omega)) xs) (by omega) := by
  simp only [RegexID.casts]
  simp only [RegexID.cast_is_cast_map]
  simp only [RegexID.cast_map]
  simp only [RegexID.castsLE]
  subst h2
  simp_all only [Fin.castLE_refl]
  simp only [Vec.map]
  simp only [Regex.map_id]
  generalize_proofs h2
  simp only [Vec.map_id]
  rw [RegexID.castLE_id]
  congr
  · induction xs with
    | nil =>
      simp only [Vec.map_nil]
    | @cons l x xs ih =>
      simp only [Vec.map]
      rw [<- ih]
      rw [RegexID.castLE_id]

theorem RegexID.add_zero:
  (RegexID.add 0 r) = r := by
  simp only [Nat.add_zero, RegexID.add]
  simp_all only [Fin.castLE_refl]
  simp only [Regex.map_id]

theorem RegexID.casts_casts (xs: Vec (RegexID n1) l) (h12: n1 = n2) (h23: n2 = n3):
  RegexID.casts (RegexID.casts xs h12) h23 = RegexID.casts xs (by omega) := by
  subst h12 h23
  simp only [RegexID.casts_rfl]

theorem RegexID.add_cast_is_castLE (r: RegexID n) (h: n = m):
  (RegexID.add k (RegexID.cast r h)) = RegexID.castLE r (by omega) := by
  simp only [RegexID.add, RegexID.cast]
  subst h
  simp_all only
  rfl

theorem RegexID.add_is_castLE (r: RegexID n):
  (RegexID.add k r) = RegexID.castLE r (by omega) := by
  simp only [RegexID.add, RegexID.castLE]

theorem RegexID.casts_is_casts_rw:
  RegexID.casts xs h =
  RegexID.casts_rw xs h := by
  subst h
  simp only [RegexID.casts]
  simp only [RegexID.cast]
  simp only [RegexID.casts_rw]
  rw [Vec.map_id]
