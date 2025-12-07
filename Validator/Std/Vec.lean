import Mathlib.Data.Vector.Basic
import Mathlib.Data.Vector.Snoc
import Mathlib.Data.Vector.MapLemmas

inductive Vec (α: Type): Nat -> Type where
  | nil : Vec α 0
  | cons {n: Nat} (x: α) (xs: Vec α n): Vec α (n + 1)

namespace Vec

def cast {n1 n2 : Nat} (xs: Vec α n1) (h : n1 = n2): Vec α n2 :=
  h ▸ xs

def append (xs: Vec α nxs) (ys: Vec α nys): (Vec α (nxs + nys)) :=
  match xs with
  | Vec.nil => Vec.cast ys (Eq.symm (Nat.zero_add nys))
  | Vec.cons x xs => Vec.cast (Vec.cons x (append xs ys)) (by ac_rfl)

def singleton (x: α): Vec α 1 :=
  Vec.cons x Vec.nil

def fromList (xs: List α): Vec α (xs.length) :=
  match xs with
  | [] => Vec.nil
  | (x::xs) => Vec.cons x (fromList xs)

def toList (xs: Vec α n): List α :=
  match xs with
  | Vec.nil => []
  | Vec.cons x xs => List.cons x (toList xs)

def map (xs: Vec α n) (f: α -> β): Vec β n :=
  match xs with
  | Vec.nil => Vec.nil
  | Vec.cons x xs => Vec.cons (f x) (map xs f)

def zip (xs: Vec α n) (ys: Vec β n): Vec (α × β) n :=
  match xs with
  | Vec.nil => Vec.nil
  | Vec.cons x xs =>
    match ys with
    | Vec.cons y ys =>
      Vec.cons (x, y) (Vec.zip xs ys)

def take (i : Nat) (xs : Vec α n): Vec α (min i n) :=
  match i with
  | 0 => Vec.cast Vec.nil (Eq.symm (Nat.zero_min n))
  | i + 1 =>
    match xs with
    | Vec.nil => Vec.nil
    | Vec.cons x xs =>
      Vec.cast
        (Vec.cons x (Vec.take i xs))
        (by simp only [Nat.add_min_add_right])

def drop (i: Nat) (xs: Vec α l): Vec α (l - i) :=
  match i with
  | 0 => xs
  | i + 1 =>
    match xs with
    | Vec.nil => Vec.cast Vec.nil (by simp only [Nat.le_add_left, Nat.sub_eq_zero_of_le])
    | Vec.cons x xs => Vec.cast (Vec.drop i xs) (by simp only [Nat.reduceSubDiff])

def get (xs: Vec α l) (i: Fin l): α :=
  match xs, i with
  | Vec.nil, i =>
    match i with
    | Fin.mk _ h =>
      nomatch h
  | Vec.cons x xs, i =>
    match i with
    | Fin.mk 0 h => x
    | Fin.mk (i + 1) h =>
      Vec.get xs (Fin.mk i (by omega))

def snoc (xs: Vec α l) (y: α): Vec α (l + 1) :=
  match xs with
  | Vec.nil => Vec.cons y Vec.nil
  | Vec.cons x xs =>
    Vec.cons x (snoc xs y)

def set (xs: Vec α l) (i: Fin l) (y: α): Vec α l :=
  match xs with
  | Vec.nil =>
    match i with
    | Fin.mk _ h =>
      nomatch h
  | Vec.cons x xs =>
    match i with
    | Fin.mk 0 h => Vec.cons y xs
    | Fin.mk (i + 1) h =>
      Vec.cons x (Vec.set xs (Fin.mk i (by omega)) y)

def head (xs: Vec α (Nat.succ l)): α :=
  match xs with
  | Vec.cons x _ => x

theorem eq (xs ys: Vec α n) (h: Vec.toList xs = Vec.toList ys): xs = ys := by
  induction xs with
  | nil =>
    cases ys with
    | nil => rfl
  | cons x xs ih =>
    cases ys with
    | cons y ys =>
      simp only [toList] at h
      congr
      · -- aesop?
        simp_all only [List.cons.injEq]
      · have ih := ih ys
        apply ih
        -- aesop?
        simp_all only [List.cons.injEq, forall_const]

theorem cast_rfl {α: Type} (xs: Vec α n) (h: n = n):
  cast xs h = xs := by
  rfl

theorem cast_toList_nil {α: Type} (h: 0 = n):
  (cast (@Vec.nil α) h).toList = [] := by
  cases n with
  | zero =>
    rw [cast_rfl]
    simp only [toList]
  | succ n =>
    contradiction

theorem cast_toList {n: Nat} (xs: Vec α n) (h: n = n2):
  (cast xs h).toList = xs.toList := by
  subst h
  rw [cast_rfl]

theorem fromList_toList_is_id (xs: List α):
  (fromList xs).toList = xs := by
  induction xs with
  | nil =>
    simp only [List.length_nil, fromList, toList]
  | cons x xs ih =>
    simp only [fromList, toList]
    rw [ih]

theorem take_zero (xs : Vec α n):
  Vec.take 0 xs = Vec.cast Vec.nil (Eq.symm (Nat.zero_min n)) := by
  simp only [take]

theorem drop_zero (xs : Vec α n):
  Vec.drop 0 xs = Vec.cast xs (by omega) := by
  simp only [drop]
  simp only [cast_rfl]

theorem take_nil (i: Nat):
  Vec.take i Vec.nil = Vec.cast (@Vec.nil α) (Eq.symm (Nat.min_zero i)) := by
  cases i with
  | zero =>
    rw [take_zero]
  | succ i =>
    simp only [take]
    congr

theorem drop_nil (i: Nat):
  Vec.drop i Vec.nil = Vec.cast (@Vec.nil α) (by omega) := by
  cases i with
  | zero =>
    rw [drop_zero]
  | succ i =>
    simp only [drop]

theorem toList_take {xs: Vec α n}:
  List.take i xs.toList = (Vec.take i xs).toList := by
  fun_induction Vec.take with
  | case1 xs =>
    rename_i n
    rw [cast_toList]
    simp only [toList, List.take]
  | case2 i =>
    simp only [toList]
    simp only [Nat.succ_eq_add_one, List.take_nil]
  | case3 i n x xs ih =>
    rw [cast_toList]
    simp only [List.take, toList]
    rw [ih]

theorem toList_cons {xs: Vec α n}:
  List.cons x xs.toList = (Vec.cons x xs).toList := by
  simp only [toList]

theorem map_nil:
  Vec.map Vec.nil f = Vec.nil := by
  simp only [Vec.map]

theorem map_cons:
  Vec.map (Vec.cons x xs) f = Vec.cons (f x) (Vec.map xs f) := by
  simp only [Vec.map]

theorem toList_map (xs: Vec α n) (f: α -> β):
  (Vec.map xs f).toList = (List.map f xs.toList) := by
  induction xs with
  | nil =>
    simp only [map_nil]
    rfl
  | cons x xs ih =>
    simp only [map_cons]
    simp only [toList]
    rw [ih]
    rfl

theorem cons_cast {α: Type} {l n: Nat} (x: α) (xs: Vec α l) (h: l = n):
  (Vec.cons x (Vec.cast xs h)) = Vec.cast (Vec.cons x xs) (by omega) := by
  subst h
  rfl

theorem cast_cast (xs: Vec α n) (h1: n = k) (h2: k = l):
  (Vec.cast (Vec.cast xs h1) h2) = Vec.cast xs (by subst h1 h2; simp only):= by
  simp only [cast]
  subst h2 h1
  simp_all only

theorem cons_append (xs: Vec α n1) (ys: Vec α n2):
  Vec.cons x (Vec.append xs ys) = Vec.cast (Vec.append (Vec.cons x xs) ys) (by omega) := by
  simp only [Vec.append]
  rw [cast_cast]
  rw [cast_rfl]

theorem nil_append (xs: Vec α n):
  Vec.append Vec.nil xs = Vec.cast xs (Eq.symm (Nat.zero_add n)) := by
  cases xs with
  | nil => simp only [Nat.add_zero, append]
  | cons x xs => simp only [append]

theorem append_nil (xs: Vec α n):
  Vec.append xs Vec.nil = Vec.cast xs (Eq.symm (Nat.add_zero n)) := by
  induction xs with
  | nil => simp only [Nat.add_zero, append]
  | cons x xs ih =>
    simp only [append]
    rw [ih]
    rw [cons_cast]
    rw [cast_cast]

theorem cast_append (xs: Vec α n1) (ys: Vec α n2):
  Vec.append (Vec.cast xs h1) ys = Vec.cast (Vec.append xs ys) h2 := by
  subst h1
  rw [cast_rfl]
  rw [cast_rfl]

theorem append_cons (xs: Vec α n1) (ys: Vec α n2):
  Vec.append (Vec.cons x xs) ys = Vec.cast (Vec.cons x (Vec.append xs ys)) (by omega) := by
  simp only [Vec.append]

theorem append_cast (xs: Vec α n1) (ys: Vec α n2):
  Vec.append xs (Vec.cast ys h1) = Vec.cast (Vec.append xs ys) h2 := by
  subst h1
  rw [cast_rfl]
  rw [cast_rfl]

theorem take_append_drop (i : Nat) (xs : Vec α l): (Vec.append (xs.take i) (xs.drop i)) = (Vec.cast xs (by omega)) := by
  induction i generalizing xs l with
  | zero =>
    simp only [take, drop]
    rw [cast_append]
    rw [nil_append]
    rw [cast_cast]
    simp only [Nat.sub_zero, zero_add, Nat.zero_le, inf_of_le_left]
  | succ i ih =>
    cases xs with
    | nil =>
      simp only [take_nil, drop_nil]
      rw [append_cast]
      rw [cast_append]
      simp only [nil_append]
      rw [cast_cast]
      rw [cast_cast]
      simp only [add_zero, Nat.le_add_left, inf_of_le_right]
      simp only [Nat.le_add_left, inf_of_le_right, add_zero, Nat.sub_eq_zero_of_le]
    | cons x xs =>
      simp only [Vec.take]
      simp only [Vec.drop]
      rw [append_cast]
      rw [cast_append]
      rw [cast_cast]
      rw [append_cons]
      rw [ih]
      repeat rw [cast_cast]
      rw [cons_cast]
      rw [cast_cast]
      simp only [Nat.add_min_add_right]
      simp only [Nat.add_min_add_right, Nat.reduceSubDiff]

theorem take_append_drop_cast (i : Nat) (xs : Vec α l): Vec.cast (Vec.append (xs.take i) (xs.drop i)) (by omega) = xs := by
  rw [take_append_drop]
  rw [cast_cast]
  rw [cast_rfl]

theorem get_cast (xs: Vec α n) (h: n = m):
  Vec.get (Vec.cast xs h) i = Vec.get xs ⟨i.val, by omega⟩ := by
  subst h
  simp_all only [Fin.eta]
  rfl

theorem append_get (xs: Vec α n) (ys: Vec α m) (h: i < n):
  Vec.get (Vec.append xs ys) ⟨i, by omega⟩ = Vec.get xs ⟨i, h⟩ := by
  induction xs generalizing i with
  | nil =>
    omega
  | cons x xs ih =>
    rename_i n
    simp only [append]
    rw [get_cast]
    simp only [get]
    generalize_proofs h1 h2 h3
    -- aesop?
    split
    next i_1 h_1
      heq =>
      simp_all only [Nat.add_lt_add_iff_right, implies_true, Fin.zero_eta, Fin.mk_eq_zero]
      subst heq
      simp_all only [Nat.zero_lt_succ]
      rfl
    next i_1 i_2 h_1 heq =>
      simp_all only [Nat.succ_eq_add_one, Fin.mk.injEq]
      subst heq
      simp_all only

theorem take_get (xs: Vec α (n + m)) (h1: i < n):
  Vec.get (Vec.take n xs) ⟨i, (by omega)⟩ = Vec.get xs ⟨i, h⟩ := by
  have h := take_append_drop_cast (xs := xs) (i := n)
  nth_rewrite 2 [<- h]
  rw [Vec.get_cast]
  simp only
  rw [append_get]

theorem cons_snoc:
  ((cons x xs).snoc y) = cons x (xs.snoc y) := by
  simp only [snoc]

theorem snoc_append (xs: Vec α l):
  (xs.snoc y) = (xs.append (Vec.cons y Vec.nil)) := by
  induction xs with
  | nil =>
    simp only [snoc, append]
    rfl
  | @cons l x xs ih =>
    simp only [snoc]
    rw [ih]
    rfl

theorem snoc_get {n: Nat} {α: Type} (xs: Vec α n) (y: α):
  Vec.get (Vec.snoc xs y) (Fin.mk n (by omega)) = y := by
  induction xs with
  | nil =>
    simp only [Vec.snoc]
    simp only [Vec.get]
  | @cons n x xs ih =>
    simp only [cons_snoc]
    simp only [Vec.get]
    rw [ih]

theorem snoc_map (xs: Vec α l) (f: α -> β):
  (Vec.map (Vec.snoc xs x) f)
  = (Vec.snoc (Vec.map xs f) (f x)) := by
  induction xs with
  | nil =>
    simp only [snoc, map]
  | @cons l x xs ih =>
    simp only [snoc, map]
    rw [ih]

theorem get_map {β : Type} (xs : Vec α n) (f : α → β) (i : Fin n) :
  (Vec.map xs f).get i = f (xs.get i) := by
  induction xs with
  | nil =>
    nomatch i
  | @cons l x xs ih =>
    simp only [Vec.map]
    cases i with
    | mk i hi =>
      cases i with
      | zero =>
        simp only [Vec.get]
      | succ i =>
        simp only [Vec.get]
        rw [ih]

theorem toList_append {n m : ℕ} (xs : Vec α n) (ys : Vec α m) :
  Vec.toList (Vec.append xs ys) = Vec.toList xs ++ Vec.toList ys := by
  induction xs with
  | nil =>
    simp only [Vec.append]
    rw [Vec.cast_toList]
    rw [Vec.toList]
    simp only [List.nil_append]
  | @cons l x xs ih =>
    simp only [Vec.append]
    rw [Vec.cast_toList]
    simp only [Vec.toList]
    rw [ih]
    rfl

theorem toList_cast (xs: Vec σ l) (h: l = n):
  Vec.toList (Vec.cast xs h) = Vec.toList xs := by
  subst h
  rfl

theorem map_map (xs: Vec α l) (g : β → σ) (f : α → β) :
  Vec.map (Vec.map xs f) g = Vec.map xs (fun x => g (f x)) := by
  induction xs with
  | nil =>
    simp only [Vec.map]
  | @cons l x xs ih =>
    simp only [Vec.map]
    rw [ih]

theorem map_id {n : ℕ} (xs : Vec α n):
  Vec.map xs (fun x => x) = xs :=
  Vec.eq _ _ (by simp_all only [Vec.toList_map, List.map_id_fun', id_eq])

theorem toList_length (xs : Vec α l):
  xs.toList.length = l := by
  induction xs with
  | nil =>
    simp only [toList, List.length_nil]
  | @cons l x xs ih =>
    simp only [toList, List.length]
    rw [ih]

theorem map_toList:
  (Vec.map xs f).toList = List.map f (xs.toList) := by
  simp_all only [Vec.toList_map]

theorem map_cast (xs : Vec α l) (f: α -> β) (h: l = n):
  (Vec.map (Vec.cast xs h) f) = Vec.cast (Vec.map xs f) h := by
  apply eq
  rw [map_toList]
  repeat rw [cast_toList]
  rw [map_toList]
