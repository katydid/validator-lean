import Validator.Regex.Map
import Validator.Regex.Regex

namespace Symbol

@[reducible, simp]
def num (r: Regex σ): Nat :=
  match r with
  | Regex.emptyset => 0
  | Regex.emptystr => 0
  | Regex.symbol _ => 1
  | Regex.or r1 r2 => num r1 + num r2
  | Regex.concat r1 r2 => num r1 + num r2
  | Regex.star r1 => num r1

def nums (xs: Vec (Regex σ) l): Nat :=
  Vec.foldl (· + ·) 0 (Vec.map xs num)

theorem nums_add:
  num x + nums xs = nums (Vec.cons x xs) := by
  simp only [nums]
  simp only [Vec.map]
  simp only [Vec.foldl]
  nth_rewrite 2 [Nat.add_comm]
  rw [Vec.foldl_nat_add]

def nums_list (xs: List (Regex σ)): Nat :=
  List.foldl (· + ·) 0 (List.map num xs)

theorem nums_nil {σ: Type}:
  nums (@Vec.nil (Regex σ)) = 0 := by
  unfold nums
  rfl

theorem nums_zero {σ: Type} (xs: Vec (Regex σ) 0):
  nums xs = 0 := by
  unfold nums
  cases xs with
  | nil =>
  simp only [Vec.map_nil]
  simp only [Vec.foldl_nil]

theorem nums_is_nums_list (xs: Vec (Regex σ) l):
  nums xs = nums_list xs.toList := by
  simp only [nums]
  simp only [nums_list]
  induction xs with
  | nil =>
    simp only [Vec.toList, Vec.map_nil, Vec.foldl_nil, List.map_nil, List.foldl_nil]
  | cons x xs ih =>
    simp only [Vec.toList, Vec.foldl, Vec.map, List.map, List.foldl]
    nth_rewrite 1 [Nat.add_comm]
    rw [Vec.foldl_assoc]
    rw [ih]
    nth_rewrite 2 [Nat.add_comm]
    rw [List.foldl_assoc]

theorem num_map (r: Regex α) (f: α -> β):
  num (Regex.map r f) = num r := by
  fun_induction num with
  | case1 =>
    simp only [Regex.map, num]
  | case2 =>
    simp only [Regex.map, num]
  | case3 =>
    simp only [Regex.map, num]
  | case4 r1 r2 hr1 hr2 =>
    simp only [Regex.map, num, hr1, hr2]
  | case5 r1 r2 hr1 hr2 =>
    simp only [Regex.map, num, hr1, hr2]
  | case6 r1 hr1 =>
    simp only [Regex.map, hr1]

theorem nums_map (rs: Vec (Regex α) l) (f: α -> β):
  nums (Regex.maps rs f) = nums rs := by
  simp only [Regex.maps]
  simp only [nums]
  induction rs with
  | nil =>
    simp only [Vec.map_nil]
  | @cons l r rs ih =>
    simp only [Vec.map]
    simp only [Vec.foldl]
    rw [num_map]
    nth_rewrite 1 [Nat.add_comm]
    rw [Vec.foldl_assoc]
    rw [ih]
    nth_rewrite 2 [Nat.add_comm]
    rw [Vec.foldl_assoc]

theorem nums_map_map:
  nums rs = nums (rs.map fun r => r.map f) := by
  simp only [nums]
  induction rs with
  | nil =>
    simp only [Vec.map_nil]
  | @cons l r rs ih =>
    simp only [Vec.map]
    simp only [Vec.foldl]
    nth_rewrite 1 [Nat.add_comm]
    nth_rewrite 2 [Nat.add_comm]
    rw [Vec.foldl_assoc]
    rw [Vec.foldl_assoc]
    rw [ih]
    rw [num_map]

theorem nums_cons_is_add:
  nums (Vec.cons x xs) = num x + nums xs
  := by
  simp only [nums]
  simp only [Vec.map]
  simp only [Vec.foldl]
  nth_rewrite 1 [Nat.add_comm]
  rw [Vec.foldl_assoc]

def Vec.cast_or (xs: Vec σ (n + num r1 + num r2)): Vec σ (n + num (Regex.or r1 r2)) :=
  have h : (n + num r1 + num r2) = (n + num (Regex.or r1 r2)) := by
    rw [<- Nat.add_assoc]
  Vec.cast xs h

def Vec.cast_concat (xs: Vec σ (n + num r1 + num r2)): Vec σ (n + num (Regex.concat r1 r2)) :=
  have h : (n + num r1 + num r2) = (n + num (Regex.concat r1 r2)) := by
    rw [<- Nat.add_assoc]
  Vec.cast xs h
