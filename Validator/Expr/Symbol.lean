import Validator.Std.Vec

import Validator.Expr.Regex

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

@[reducible, simp]
def num (r: Regex σ): Nat :=
  match r with
  | Regex.emptyset => 0
  | Regex.emptystr => 0
  | Regex.symbol _ => 1
  | Regex.or r1 r2 => num r1 + num r2
  | Regex.concat r1 r2 => num r1 + num r2
  | Regex.star r1 => num r1

def nums (xs: List.Vector (Regex σ) l): Nat :=
  match xs with
  | ⟨[], _⟩ => 0
  | ⟨x::xs, h⟩ => nums ⟨xs, congrArg Nat.pred h⟩ + num x

theorem nums_nil {σ: Type}:
  nums (@List.Vector.nil (Regex σ)) = 0 := by
  unfold nums
  rfl

def nums_list (xs: List (Regex σ)): Nat :=
  match xs with
  | [] => 0
  | x::xs => nums_list xs + num x

theorem nums_is_nums_list (xs: List.Vector (Regex σ) l):
  nums xs = nums_list xs.toList := by
  cases xs with
  | mk xs hxs =>
  simp only [List.Vector.toList]
  induction xs generalizing l with
  | nil =>
    simp [nums, nums_list]
  | cons x xs ih =>
    simp only [List.length] at hxs
    have hxs' : xs.length = l - 1 := by
      omega
    have ih := @ih (l - 1) hxs'
    simp only [nums, nums_list]
    rw [ih]

abbrev RegexID n := Regex (Fin n)
abbrev Symbols σ n := List.Vector σ n

def RegexID.add {n: Nat} (m: Nat) (r: RegexID n): RegexID (n + m) :=
  Regex.map r (fun s => (Fin.mk s.val (by omega)))

def RegexID.cast (r: RegexID n) (h: n = m): RegexID m :=
  match h with
  | Eq.refl _ => r

theorem RegexID.cast_rfl (r: RegexID n): RegexID.cast r rfl = r := by
  rfl

def RegexID.cast_map (r: RegexID n) (h: n = m): RegexID m :=
  Regex.map r (fun s => Fin.cast h s)

theorem RegexID.cast_map_rfl (r: RegexID n): RegexID.cast_map r rfl = r := by
  unfold RegexID.cast_map
  simp [Fin.cast]
  rw [Regex.map_id]

theorem RegexID.cast_is_cast_map (r: RegexID n) (h: n = m):
  RegexID.cast r h = RegexID.cast_map r h := by
  subst h
  rw [RegexID.cast_rfl]
  rw [RegexID.cast_map_rfl]

def RegexID.casts (rs: List.Vector (RegexID n) l) (h: n = m): List.Vector (RegexID m) l :=
  List.Vector.map (fun r => RegexID.cast r h) rs

abbrev RegexID.add_assoc (r: RegexID (n + num r1 + num r2)): RegexID (n + (num r1 + num r2)) :=
  have h : (n + num r1 + num r2) = n + (num r1 + num r2) := by
    rw [<- Nat.add_assoc]
  RegexID.cast r h

def RegexID.add_or (r: RegexID (n + num r1 + num r2)): RegexID (n + num (Regex.or r1 r2)) :=
  RegexID.add_assoc r

def RegexID.add_concat (r: RegexID (n + num r1 + num r2)): RegexID (n + num (Regex.concat r1 r2)) :=
  RegexID.add_assoc r

def Symbols.cast (xs: Symbols σ n) (h: n = m): Symbols σ m :=
  List.Vector.congr h xs

theorem List.Vector.toList_cast_is_toList (xs: List.Vector σ n):
  List.Vector.toList xs = List.Vector.toList (Symbols.cast xs h) := by
  rcases xs with ⟨xs, hxs⟩
  simp [Symbols.cast, List.Vector.toList]
  subst h hxs
  simp only [List.Vector.congr]

abbrev Symbols.take {α: Type} (i: Nat) (xs: List.Vector α l) := List.Vector.take i xs
abbrev Symbols.get {α: Type} (xs: List.Vector α l) (i: Fin l) := List.Vector.get xs i
abbrev Symbols.nil {α: Type} := @List.Vector.nil α
abbrev Symbols.snoc {α: Type} (xs: List.Vector α l) (x: α) := List.Vector.snoc xs x
abbrev Symbols.cons {α: Type} (x: α) (xs: List.Vector α l) := List.Vector.cons x xs
abbrev Symbols.set {α: Type} (v : List.Vector α l) (i : Fin l) (a : α) := List.Vector.set v i a
abbrev Symbols.toList {α: Type} (v : List.Vector α l) := List.Vector.toList v

def Symbols.add_or (xs: Symbols σ (n + num r1 + num r2)): Symbols σ (n + num (Regex.or r1 r2)) :=
  have h : (n + num r1 + num r2) = (n + num (Regex.or r1 r2)) := by
    rw [<- Nat.add_assoc]
  Symbols.cast xs h

def Symbols.add_concat (xs: Symbols σ (n + num r1 + num r2)): Symbols σ (n + num (Regex.concat r1 r2)) :=
  have h : (n + num r1 + num r2) = (n + num (Regex.concat r1 r2)) := by
    rw [<- Nat.add_assoc]
  Symbols.cast xs h

theorem Symbols.cast_rfl {α n} {xs : Symbols α n} : Symbols.cast xs rfl = xs := by
  rcases xs with ⟨xs, rfl⟩
  rfl

theorem Symbols.cast_eq {α n} {xs : Symbols α n} (h: n = n): Symbols.cast xs h = xs := by
  rcases xs with ⟨xs, rfl⟩
  rfl

theorem Symbols.take_get (xs: Symbols σ (n + m)):
  Symbols.get (Symbols.take n xs) ⟨s, h3⟩ = Symbols.get xs ⟨s, h4⟩ := by
  obtain ⟨xs, hxs⟩ := xs
  simp only [List.Vector.get, List.Vector.take]
  simp only [Fin.cast_mk, List.get_eq_getElem, List.getElem_take]

theorem Symbols.cast_nil:
  ⟨[], h1⟩ = Symbols.cast ⟨[], h3⟩ h2 := by
  subst h3 h1
  simp only [List.length_nil]
  rfl

theorem Symbols.cons_is_list_cons (x: σ) (xs: List.Vector σ n) (hxs: (x :: xs.val).length = n.succ):
  ⟨List.cons x xs.val, hxs⟩ = List.Vector.cons x xs := by
  simp only [Nat.succ_eq_add_one]
  rfl

theorem Symbols.cast_list {n m: Nat} {σ: Type} (xs: List σ) (h1: xs.length = n) (h2: m = n) (h3: xs.length = m):
  ⟨xs, h1⟩ = Symbols.cast ⟨xs, h3⟩ h2 := by
  apply List.Vector.eq
  simp
  aesop

theorem Symbols.take_succ (xs: Symbols α n):
  (
    Symbols.take (i + 1) (Symbols.cons x xs)
    : Symbols α (min (i + 1) (n + 1))
  )
  =
  (Symbols.cast
    (n := ((min i n) + 1))
    (m := (min (i + 1) (n + 1)))
    (
      (
        Symbols.cons x (
          Symbols.take i xs
        )
      )
      : Symbols α ((min i n) + 1)
    )
    (by
      rw [Nat.min_def]
      split_ifs
      omega
      omega
    )
  )
  := by
  unfold Symbols at *
  apply List.Vector.eq
  rw [<- List.Vector.toList_cast_is_toList]
  rw [<- Vec.toList_take]
  rw [<- Vec.toList_cons]
  simp only [List.Vector.cons_val, List.take_succ_cons, List.cons.injEq, true_and]
  rw [Vec.toList_take]
  simp [List.Vector.toList]

theorem Symbols.cast_take (xs: Symbols σ n):
  Symbols.take n xs = Symbols.cast (n := n) (m := min n n) xs (by omega) := by
  unfold Symbols.take
  apply List.Vector.eq
  generalize_proofs h
  rw [<- List.Vector.toList_cast_is_toList]
  rw [<- Vec.toList_take]
  rcases xs with ⟨xs, hxs⟩
  simp only [List.Vector.toList_mk, List.take_eq_self_iff]
  omega

theorem Symbols.cast_append_take (xs: Symbols σ n) (ys: Symbols σ m):
  (xs ++ ys).take n = Symbols.cast (n := n) (m := min n (n + m)) xs ((by
    omega
  ): n = min n (n + m)) := by
  unfold Symbols at *
  apply List.Vector.eq
  rw [<- List.Vector.toList_cast_is_toList]
  rcases xs with ⟨xs, hxs⟩
  simp only [_root_.List.Vector.toList_take, List.Vector.toList_append, List.Vector.toList_mk]
  subst hxs
  simp_all only [List.take_left']

theorem Symbols.push_get {n: Nat} {α: Type} (xs: Symbols α n) (x: α):
  Symbols.get (Symbols.snoc xs x) (Fin.mk n (by omega)) = x := by
  unfold Symbols at *
  unfold Symbols.get
  unfold Symbols.snoc
  rcases xs with ⟨xs, hxs⟩
  subst hxs
  generalize_proofs h1 h2
  rw [List.Vector.get_eq_get_toList]
  generalize_proofs h3
  simp only [List.Vector.toList, List.Vector.snoc, List.Vector.cons, List.Vector.append_def]
  simp only [Fin.cast_mk, List.get_eq_getElem, le_refl, List.getElem_append_right, tsub_self,
    List.getElem_cons_zero]

def replace (r: RegexID n) (xs: Symbols σ l) (h: n <= l): Regex σ :=
  match r with
  | Regex.emptyset => Regex.emptyset
  | Regex.emptystr => Regex.emptystr
  | Regex.symbol s => Regex.symbol (Symbols.get xs (Fin.mk s.val (by
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

theorem replace_cast_both (r: RegexID n) (xs: Symbols σ n) (h: n = l):
  replace r xs (by omega) = replace (RegexID.cast r h) (Symbols.cast xs h) (by omega) := by
  subst h
  simp only [Symbols.cast_rfl]
  rfl

theorem replace_cast_symbols (r: RegexID n) (xs: Symbols σ n) (h: n = l):
  replace r xs (by omega) = replace r (Symbols.cast xs h) (by omega) := by
  subst h
  simp only [Symbols.cast_rfl]

theorem replace_nil_is_map_id (r: Regex (Fin 0)):
  replace r List.Vector.nil (by simp) = Regex.map r id := by
  induction r with
  | emptyset =>
    simp [replace, Regex.map]
  | emptystr =>
    simp [replace, Regex.map]
  | symbol s =>
    nomatch s
  | or r1 r2 ih1 ih2 =>
    simp [replace, Regex.map]
    rw [ih1]
    rw [ih2]
    apply And.intro rfl rfl
  | concat r1 r2 ih1 ih2 =>
    simp [replace, Regex.map]
    rw [ih1]
    rw [ih2]
    apply And.intro rfl rfl
  | star r1 ih1 =>
    simp [replace, Regex.map]
    rw [ih1]

theorem replace_take (r: RegexID n) (xs: Symbols σ (n + l)):
  replace r (Symbols.take n xs) (by omega) = replace r xs (by omega):= by
  induction r with
  | emptyset =>
    simp [replace]
  | emptystr =>
    simp [replace]
  | symbol s =>
    generalize_proofs h1 h2 at *
    simp only [replace]
    obtain ⟨s, hs⟩ := s
    simp only [Regex.symbol.injEq]
    generalize_proofs h3 h4
    rw [Symbols.take_get]
  | or r1 r2 ih1 ih2 =>
    simp [replace]
    generalize_proofs h1 h2 at *
    rw [<- ih1]
    rw [<- ih2]
    apply And.intro rfl rfl
  | concat r1 r2 ih1 ih2 =>
    simp [replace]
    generalize_proofs h1 h2 at *
    rw [<- ih1]
    rw [<- ih2]
    apply And.intro rfl rfl
  | star r1 ih1 =>
    simp only [replace]
    generalize_proofs h1 at *
    rw [<- ih1]

theorem replace_regexid_add (r: RegexID n) (xs: List.Vector σ (n + l)):
  replace r xs (by omega) = replace (RegexID.add l r) xs (by omega):= by
  generalize_proofs h1 h2
  rcases xs with ⟨xs, hxs⟩
  induction r with
  | emptyset =>
    simp [replace, RegexID.add, Regex.map]
  | emptystr =>
    simp [replace, RegexID.add, Regex.map]
  | symbol s =>
    generalize_proofs h1 h2 at *
    simp [replace, RegexID.add, Regex.map]
  | or r1 r2 ih1 ih2 =>
    simp [replace, RegexID.add, Regex.map]
    generalize_proofs h1 h2 at *
    rw [ih1]
    rw [ih2]
    apply And.intro rfl rfl
  | concat r1 r2 ih1 ih2 =>
    simp [replace, RegexID.add, Regex.map]
    generalize_proofs h1 h2 at *
    rw [ih1]
    rw [ih2]
    apply And.intro rfl rfl
  | star r1 ih1 =>
    simp [replace, RegexID.add, Regex.map]
    generalize_proofs h1 h2 at *
    rw [ih1]
    rfl

def extract (r: Regex σ) (acc: Symbols σ n): RegexID (n + num r) × Symbols σ (n + num r) :=
  match r with
  | Regex.emptyset => (Regex.emptyset, acc)
  | Regex.emptystr => (Regex.emptystr, acc)
  | Regex.symbol s => (Regex.symbol (Fin.mk n (by
      simp only [num]
      omega
    )), Symbols.snoc acc s)
  | Regex.or r1 r2 =>
    let (er1, acc1) := extract r1 acc
    let (er2, acc2) := extract r2 acc1
    (Regex.or (RegexID.add_or (RegexID.add (num r2) er1)) (RegexID.add_or er2), Symbols.add_or acc2)
  | Regex.concat r1 r2 =>
    let (er1, acc1) := extract r1 acc
    let (er2, acc2) := extract r2 acc1
    (Regex.concat (RegexID.add_concat (RegexID.add (num r2) er1)) (RegexID.add_concat er2), Symbols.add_concat acc2)
  | Regex.star r1 =>
    let (er1, acc1) := extract r1 acc
    (Regex.star er1, acc1)

theorem extract_append_toList (acc: Symbols σ n) (r: Regex σ):
  List.Vector.toList (extract r acc).2 = List.Vector.toList (acc ++ (extract r Symbols.nil).2) := by
  induction r generalizing acc n  with
  | emptyset =>
    simp only [num, Nat.add_zero, extract, List.Vector.append_nil]
  | emptystr =>
    simp only [num, Nat.add_zero, extract, List.Vector.append_nil]
  | symbol s =>
    simp only [extract]
    rfl
  | or r1 r2 ih1 ih2 =>
    simp only [extract]
    rw [Symbols.add_or]
    generalize_proofs h1 h2 h3
    rw [Symbols.add_or]
    generalize_proofs h4
    rw [List.Vector.toList_append]
    rw [<- List.Vector.toList_cast_is_toList]
    rw [<- List.Vector.toList_cast_is_toList]
    rw [ih2]
    rw [List.Vector.toList_append]
    rw [ih1]
    rw [List.Vector.toList_append]
    nth_rewrite 2 [ih2]
    rw [List.Vector.toList_append]
    ac_rfl
  | concat r1 r2 ih1 ih2 =>
    simp only [extract]
    rw [Symbols.add_concat]
    generalize_proofs h1 h2 h3
    rw [Symbols.add_concat]
    generalize_proofs h4
    rw [List.Vector.toList_append]
    rw [<- List.Vector.toList_cast_is_toList]
    rw [<- List.Vector.toList_cast_is_toList]
    rw [ih2]
    rw [List.Vector.toList_append]
    rw [ih1]
    rw [List.Vector.toList_append]
    nth_rewrite 2 [ih2]
    rw [List.Vector.toList_append]
    ac_rfl
  | star r1 ih1 =>
    simp only [extract]
    rw [ih1]

theorem extract_append (acc: Symbols σ l) (r: Regex σ):
  (extract r acc).2 = Symbols.cast (acc ++ (extract r Symbols.nil).2) (by omega) := by
  apply List.Vector.eq
  rw [extract_append_toList]
  rw [<- List.Vector.toList_cast_is_toList]

theorem extract_take_toList (acc: Symbols σ l):
  (List.Vector.toList
    (List.Vector.take
      (l + num r1)
      (extract r2
      (extract r1 acc).2).2
    )
  )
  =
  (List.Vector.toList (extract r1 acc).2) := by
  rw [<- Vec.toList_take]
  rw [<- List.Vector.toList]
  rw [extract_append_toList]
  rw [List.Vector.toList_append]
  rw [List.Vector.toList]
  generalize he: (extract r1 acc).2 = her
  obtain ⟨her, hher⟩ := her
  simp only
  simp_all only [List.take_left']

theorem extract_take (acc: Symbols σ l):
  (List.Vector.take
    (l + num r1)
    (extract r2
      (extract r1 acc).2).2
  )
  =
    Symbols.cast
    (extract r1 acc).2
    (by omega) := by
  apply List.Vector.eq
  rw [extract_take_toList]
  rw [<- List.Vector.toList_cast_is_toList]

theorem toList_fmap:
  (List.Vector.map f xs).toList = List.map f (xs.toList) := by
  simp_all only [List.Vector.toList_map]

theorem extract_take_toList_fmap (acc: Symbols σ l):
  (List.Vector.toList
    (List.Vector.take
      (l + num r1)
      (List.Vector.map
        f
        (extract r2
        (extract r1 acc).2).2
      )
    )
  )
  =
  (List.Vector.toList
    (List.Vector.map
      f
      (extract r1 acc).2
    )
  ) := by
  rw [<- Vec.toList_take]
  rw [<- List.Vector.toList]
  rw [toList_fmap]
  rw [extract_append_toList]
  rw [List.Vector.toList_append]
  rw [List.Vector.toList]
  generalize he: (extract r1 acc).2 = her
  obtain ⟨her, hher⟩ := her
  simp only
  simp_all only [List.map_append, List.length_map, List.take_left', List.Vector.toList_map,
    List.Vector.toList_mk]

theorem extract_take_fmap (acc: Symbols α l) (f: α -> β):
  (List.Vector.take
    (l + num r1)
    (List.Vector.map
      f
      (extract r2
        (extract r1 acc).2).2
    )
  )
  =
    Symbols.cast
    (List.Vector.map
      f
      (extract r1 acc).2
    )
    (by omega) := by
  apply List.Vector.eq
  rw [extract_take_toList_fmap]
  rw [<- List.Vector.toList_cast_is_toList]

def replaceFrom (r: RegexID n) (xs: Symbols σ n): Regex σ :=
  replace r xs (le_refl n)

theorem extract_replaceFrom_is_id (r: Regex σ) (acc: Symbols σ l):
  r = replaceFrom (extract r acc).1 (extract r acc).2 := by
  simp only [replaceFrom]
  generalize_proofs hr
  revert acc l
  induction r with
  | emptyset =>
    intro n acc hr
    simp only [replace, extract]
  | emptystr =>
    intro n acc hr
    simp only [replace, extract]
  | symbol s =>
    intro n acc hr
    simp only [replace, extract]
    rw [Symbols.push_get]
  | or r1 r2 ih1 ih2 =>
    intro n acc hr
    simp only [extract]
    simp only [replace]
    have hh1 :
      r1 =
        (replace
          (RegexID.add_or (RegexID.add (num r2) (extract r1 acc).1))
          (Symbols.add_or (extract r2 (extract r1 acc).2).2)
          hr
        ) := by
      clear ih2
      rw [RegexID.add_or]
      rw [Symbols.add_or]
      rw [<- replace_cast_both]
      rw [<- replace_regexid_add]
      rw [<- replace_take]
      generalize_proofs h1
      unfold Symbols.take
      rw [extract_take]
      generalize_proofs h1 h2
      nth_rewrite 1 [ih1 acc]
      rw [replace_cast_symbols]
    rw [<- hh1]
    clear hh1
    clear ih1
    congr
    rw [RegexID.add_or]
    rw [Symbols.add_or]
    rw [<- replace_cast_both]
    rw [<- ih2 ((extract r1 acc).2)]
  | concat r1 r2 ih1 ih2 =>
    intro n acc hr
    simp only [extract]
    simp only [replace]
    have hh1 :
      r1 =
        (replace
          (RegexID.add_concat (RegexID.add (num r2) (extract r1 acc).1))
          (Symbols.add_concat (extract r2 (extract r1 acc).2).2)
          hr
        ) := by
      clear ih2
      rw [RegexID.add_concat]
      rw [Symbols.add_concat]
      rw [<- replace_cast_both]
      rw [<- replace_regexid_add]
      rw [<- replace_take]
      generalize_proofs h1
      unfold Symbols.take
      rw [extract_take]
      generalize_proofs h1 h2
      nth_rewrite 1 [ih1 acc]
      rw [replace_cast_symbols]
    rw [<- hh1]
    clear hh1
    clear ih1
    congr
    rw [RegexID.add_concat]
    rw [Symbols.add_concat]
    rw [<- replace_cast_both]
    rw [<- ih2 ((extract r1 acc).2)]
  | star r1 ih1 =>
    simp only [extract]
    simp only [replace]
    intro n acc hr
    rw [<- ih1 acc]

theorem extract_replace_is_id (r: Regex σ) (acc: Symbols σ l):
  r = replace (extract r acc).1 (extract r acc).2 (by omega):= by
  rw [<- replaceFrom]
  rw [<- extract_replaceFrom_is_id]

def extractFrom (r: Regex σ): RegexID (num r) × Symbols σ (num r) :=
  match extract r List.Vector.nil with
  | (r', xs) => (RegexID.cast r' (by omega), Symbols.cast xs (by omega))

theorem extractFrom_replaceFrom_is_id (r: Regex σ):
  r = replaceFrom (extractFrom r).1 (extractFrom r).2 := by
  simp only [extractFrom]
  simp only [replaceFrom]
  rw [<- replace_cast_both]
  rw [<- extract_replace_is_id r List.Vector.nil]

theorem nums_cons_is_add:
  nums (⟨x::xs, h⟩)
  = num x + nums ⟨xs, congrArg Nat.pred h⟩
  := by
  simp [nums]
  ac_rfl

theorem RegexID.cons_cast:
  List.Vector (RegexID (nacc + nums (⟨x::xs, h⟩))) n
  = List.Vector (RegexID (nacc + num x + nums ⟨xs, congrArg Nat.pred h⟩)) n := by
  simp [nums]
  ac_rfl

def extracts (xs: List.Vector (Regex σ) nregex) (acc: Symbols σ nacc):
  (List.Vector (RegexID (nacc + nums xs)) nregex) × (Symbols σ (nacc + nums xs)) :=
  match xs with
  | ⟨[], h⟩ =>
    (
      ⟨[], by assumption ⟩,
      ⟨acc.val, by simp only [List.Vector.length_val, nums, add_zero]⟩
    )
  | ⟨x::xs, h⟩ =>
    let xs': List.Vector (Regex σ) nregex.pred := ⟨xs, congrArg Nat.pred h⟩
    let (regex, symbols) := Symbol.extract x acc
    let regex' := RegexID.add (nums ⟨xs, congrArg Nat.pred h⟩) regex
    let regex'': RegexID (nacc + nums (⟨x::xs, h⟩)) :=
      RegexID.cast
      regex'
      (by
        simp
        rw [nums_cons_is_add]
        ac_rfl
      )
    let (regexes, symbols') := extracts xs' symbols
    let regexes': List.Vector (RegexID (nacc + nums (⟨x::xs, h⟩))) nregex.pred
      := by
        rw [RegexID.cons_cast]
        exact regexes
    let regexes'' : List.Vector (RegexID (nacc + nums (⟨x::xs, h⟩))) nregex :=
      (Symbols.cast
        ((List.Vector.cons
          regex''
          regexes'
        ): List.Vector (RegexID (nacc + nums (⟨x::xs, h⟩))) nregex.pred.succ)
        (by
          rw [<- h]
          simp only [List.length_cons, Nat.pred_eq_sub_one, add_tsub_cancel_right, Nat.succ_eq_add_one]
        )
      )
    let symbols': Symbols σ (nacc + nums (⟨x::xs, h⟩)) :=
      Symbols.cast
      symbols'
      (by
        simp [nums]
        ac_rfl
      )
    (
      regexes'',
      symbols'
    )

theorem extracts_nil (acc: Symbols σ nacc):
  extracts (@List.Vector.nil (Regex σ)) acc = (RegexID.casts List.Vector.nil (by
    simp only [nums_nil]
    rfl
  ), List.Vector.congr (by
    simp only [nums_nil]
    simp only [add_zero]
  ) acc) := by
  unfold extracts
  congr

theorem snoc_fmap:
  (List.Vector.map f (Symbols.snoc acc s))
  = (Symbols.snoc (List.Vector.map f acc) (f s)) := by
  simp_all only [List.Vector.map_snoc]

theorem map_cast (xs: List.Vector α l1) (f: α -> β) (h: l1 = l2):
  List.Vector.map f (Symbols.cast xs h) = Symbols.cast (List.Vector.map f xs) h := by
  subst h
  rfl

theorem extract_replaceFrom_is_fmap (r: Regex α) (acc: Symbols α l) (f: α -> β):
  Regex.map r f = replaceFrom (extract r acc).1 (List.Vector.map f (extract r acc).2) := by
  simp only [replaceFrom]
  generalize_proofs hr
  revert acc l
  induction r with
  | emptyset =>
    intro n acc hr
    simp only [replace, extract, Regex.map]
  | emptystr =>
    intro n acc hr
    simp only [replace, extract, Regex.map]
  | symbol s =>
    intro n acc hr
    simp only [replace, extract, Regex.map]
    simp only [snoc_fmap]
    rw [Symbols.push_get]
  | or r1 r2 ih1 ih2 =>
    intro n acc hr
    simp only [extract]
    simp only [replace]
    simp only [Regex.map]
    have hh1 :
      Regex.map r1 f =
        (replace
          (RegexID.add_or (RegexID.add (num r2) (extract r1 acc).1))
          (List.Vector.map f (Symbols.add_or (extract r2 (extract r1 acc).2).2))
          hr
        ) := by
      clear ih2
      rw [RegexID.add_or]
      rw [Symbols.add_or]
      rw [map_cast]
      rw [<- replace_cast_both]
      rw [<- replace_regexid_add]
      rw [<- replace_take]
      generalize_proofs h1
      unfold Symbols.take
      rw [extract_take_fmap]
      generalize_proofs h1 h2
      have ih1' := ih1 acc
      nth_rewrite 1 [ih1']
      rw [replace_cast_symbols]
    rw [<- hh1]
    clear hh1
    clear ih1
    congr
    rw [RegexID.add_or]
    rw [Symbols.add_or]
    rw [map_cast]
    rw [<- replace_cast_both]
    rw [<- ih2 ((extract r1 acc).2)]
  | concat r1 r2 ih1 ih2 =>
    intro n acc hr
    simp only [extract]
    simp only [replace]
    simp only [Regex.map]
    have hh1 :
      Regex.map r1 f =
        (replace
          (RegexID.add_concat (RegexID.add (num r2) (extract r1 acc).1))
          (List.Vector.map f (Symbols.add_concat (extract r2 (extract r1 acc).2).2))
          hr
        ) := by
      clear ih2
      rw [RegexID.add_concat]
      rw [Symbols.add_concat]
      rw [map_cast]
      rw [<- replace_cast_both]
      rw [<- replace_regexid_add]
      rw [<- replace_take]
      generalize_proofs h1
      unfold Symbols.take
      rw [extract_take_fmap]
      generalize_proofs h1 h2
      have ih1' := ih1 acc
      nth_rewrite 1 [ih1']
      rw [replace_cast_symbols]
    rw [<- hh1]
    clear hh1
    clear ih1
    congr
    rw [RegexID.add_concat]
    rw [Symbols.add_concat]
    rw [map_cast]
    rw [<- replace_cast_both]
    rw [<- ih2 ((extract r1 acc).2)]
  | star r1 ih1 =>
    simp only [extract]
    simp only [replace]
    intro n acc hr
    rw [<- ih1 acc]
    simp only [Regex.map]

theorem extract_replace_is_fmap (r: Regex α) (acc: Symbols α l) (f: α -> β):
  Regex.map r f = replace (extract r acc).1 (List.Vector.map f (extract r acc).2) (by omega) := by
  rw [<- replaceFrom]
  rw [<- extract_replaceFrom_is_fmap]

theorem extractFrom_replaceFrom_is_fmap (r: Regex α) (f: α -> β):
  Regex.map r f = replaceFrom (extractFrom r).1 (List.Vector.map f (extractFrom r).2) := by
  simp only [extractFrom]
  simp only [replaceFrom]
  rw [map_cast]
  rw [<- replace_cast_both]
  rw [<- extract_replace_is_fmap r List.Vector.nil]

def derive {σ: Type} {α: Type} (p: σ -> α -> Bool) (r: Regex σ) (a: α): Regex σ :=
  Regex.derive2 (replaceFrom (extractFrom r).1 (List.Vector.map (fun s => (s, p s a)) (extractFrom r).2))

def derive' {σ: Type} {α: Type} (p: σ -> α -> Bool) (r: Regex σ) (a: α): Regex σ :=
  let (r', symbols): (RegexID (num r) × Symbols σ (num r)) := extractFrom r
  let pred_results: List.Vector Bool (num r) := List.Vector.map (fun s => p s a) symbols
  let replaces: List.Vector (σ × Bool) (num r) := Vec.zip symbols pred_results
  let replaced: Regex (σ × Bool) := replaceFrom r' replaces
  Regex.derive2 replaced

theorem zip_map {α: Type} {β: Type} (f: α -> β) (xs: List.Vector α l):
  (List.Vector.map (fun x => (x, f x)) xs) =
  (Vec.zip xs (List.Vector.map f xs)) := by
  simp only [Vec.zip, List.Vector.map]
  cases xs with
  | mk xs h =>
  simp only
  congr
  rw [← List.zip_eq_zipWith]
  rw [← List.map_prod_left_eq_zip]

theorem Symbol_derive_is_derive'
  {σ: Type} {α: Type} (p: σ -> α -> Bool) (r: Regex σ) (a: α):
  Symbol.derive p r a = Symbol.derive' p r a := by
  unfold Symbol.derive
  unfold Symbol.derive'
  simp only
  rw [zip_map]

theorem Symbol_derive_is_Regex_derive
  {σ: Type} {α: Type} (p: σ -> α -> Bool) (r: Regex σ) (a: α):
  Symbol.derive p r a = Regex.derive p r a := by
  unfold Symbol.derive
  rw [<- extractFrom_replaceFrom_is_fmap]
  rw [Regex.derive_is_derive2]

def extractsFrom (xs: List.Vector (Regex σ) nregex):
  (List.Vector (RegexID (nums xs)) nregex) × (Symbols σ (nums xs)) :=
  let (xs0, symbols0) := extracts xs List.Vector.nil
  let symbols': Symbols σ (nums xs) := Symbols.cast symbols0 (by ac_rfl)
  let xs': List.Vector (RegexID (nums xs)) nregex := RegexID.casts xs0 (by ac_rfl)
  (xs', symbols')

def replacesFrom (rs: List.Vector (RegexID n) l) (xs: List.Vector σ n): List.Vector (Regex σ) l :=
  List.Vector.map (fun r => replaceFrom r xs) rs

def derives {σ: Type} {α: Type} (p: σ -> α -> Bool) (rs: List.Vector (Regex σ) l) (a: α): List.Vector (Regex σ) l :=
  let (rs', symbols): (List.Vector (RegexID (nums rs)) l × Symbols σ (nums rs)) := Symbol.extractsFrom rs
  let pred_results: List.Vector Bool (nums rs) := List.Vector.map (fun s => p s a) symbols
  let replaces: List.Vector (σ × Bool) (nums rs) := Vec.zip symbols pred_results
  let replaced: List.Vector (Regex (σ × Bool)) l := replacesFrom rs' replaces
  Regex.derives2 replaced

theorem RegexID.casts_rfl {n} {xs : List.Vector (RegexID n) l} {h : n = n} : RegexID.casts xs h = xs := by
  rcases xs with ⟨xs, rfl⟩
  generalize_proofs h1 h2
  unfold RegexID.casts
  -- aesop?
  ext m : 1
  simp only [List.Vector.get_map]
  rfl

theorem replacesFrom_cast_both (rs: List.Vector (RegexID n) l) (ss: Symbols σ n) (h: n = m):
  replacesFrom rs ss =
  replacesFrom (RegexID.casts rs h) (Symbols.cast ss h) := by
  subst h
  simp only [Symbols.cast_rfl]
  simp only [RegexID.casts_rfl]

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

theorem nums_map (rs: List.Vector (Regex α) l) (f: α -> β):
  nums (Regexes.map rs f) = nums rs := by
  simp only [Regexes.map]
  simp only [List.Vector.map]
  cases rs with
  | mk rs hrs =>
  simp only
  rw [nums_is_nums_list]
  rw [nums_is_nums_list]
  simp only [List.Vector.toList]
  induction rs generalizing l with
  | nil =>
    simp only [List.map]
    rfl
  | cons r rs ih =>
    simp only [List.map]
    simp only [List.length] at hrs
    have hrs' : rs.length = l - 1 := by
      omega
    have ih := ih hrs'
    simp only [nums_list]
    rw [ih]
    rw [num_map]

theorem toList_cast (xs: Symbols σ l) (h: l = n):
  List.Vector.toList (Symbols.cast xs h) = List.Vector.toList xs := by
  cases xs with
  | mk xs hxs =>
  subst hxs h
  simp only [List.Vector.toList_mk]
  rfl

theorem extract_lift_cast (r: Regex α) (acc: List.Vector α n) (h1: n + num r = l + num r) (h2: n = l):
  (Symbols.cast (extract r acc).2 h1) = (extract r (Symbols.cast acc h2)).2 := by
  subst h2
  rfl

theorem extract_lift_cast_1 (r: Regex α) (acc: List.Vector α n) (h1: n + num r = l + num r) (h2: n = l):
  RegexID.cast (extract r acc).1 h1 = (extract r (Symbols.cast acc h2)).1 := by
  subst h2
  rfl

theorem extract_is_fmap_2 (r: Regex α) (acc: List.Vector α n) (f: α -> β):
  (extract (Regex.map r f) (List.Vector.map f acc)).2 = Symbols.cast (List.Vector.map f (extract r acc).2) (by rw [num_map]) := by
  generalize_proofs hr
  fun_induction extract with
  | case1 =>
    apply List.Vector.eq
    repeat rw [toList_cast]
    simp only [extract, Regex.map]
  | case2 =>
    apply List.Vector.eq
    repeat rw [toList_cast]
    simp only [extract, Regex.map]
  | case3 =>
    apply List.Vector.eq
    repeat rw [toList_cast]
    simp only [extract, Regex.map, num]
    -- aesop?
    simp_all only [num, Nat.add_left_cancel_iff, List.Vector.map_snoc]
  | case4 acc r1 r2 er1 acc1 he1 er2 acc2 he2 ih1 ih2 => -- or
    rename_i n
    simp [Regex.map] at *
    have hacc1 : acc1 = (extract r1 acc).2 := by
      rw [he1]
    have hacc2 : acc2 = (extract r2 (extract r1 acc).2).2 := by
      rw [<- hacc1]
      rw [he2]
    rw [hacc2]
    rw [hacc1] at ih2
    have ih1' := ih1 (by rw [num_map])
    clear ih1
    have ih2' := ih2 (by rw [num_map])
    clear ih2
    simp only [extract]
    simp [Symbols.add_or]
    rw [ih1']
    have hh: n + num r1 + num (r2.map f) = n + num (r1.map f) + num (r2.map f) := by
      repeat rw [num_map]
    rw [<- extract_lift_cast (h1 := hh)]
    rw [ih2']
    apply List.Vector.eq
    repeat rw [toList_cast]
    rw [map_cast]
    repeat rw [toList_cast]
  | case5 acc r1 r2 er1 acc1 he1 er2 acc2 he2 ih1 ih2 => -- concat
    rename_i n
    simp [Regex.map] at *
    have hacc1 : acc1 = (extract r1 acc).2 := by
      rw [he1]
    have hacc2 : acc2 = (extract r2 (extract r1 acc).2).2 := by
      rw [<- hacc1]
      rw [he2]
    rw [hacc2]
    rw [hacc1] at ih2
    have ih1' := ih1 (by rw [num_map])
    clear ih1
    have ih2' := ih2 (by rw [num_map])
    clear ih2
    simp only [extract]
    simp [Symbols.add_concat]
    rw [ih1']
    have hh: n + num r1 + num (r2.map f) = n + num (r1.map f) + num (r2.map f) := by
      repeat rw [num_map]
    rw [<- extract_lift_cast (h1 := hh)]
    rw [ih2']
    apply List.Vector.eq
    repeat rw [toList_cast]
    rw [map_cast]
    repeat rw [toList_cast]
  | case6 acc r1 er1 acc1 he ih1 => -- star
    simp [Regex.map] at *
    have hacc1 : acc1 = (extract r1 acc).2 := by
      rw [he]
    rw [hacc1]
    rw [<- ih1]
    rfl
    rw [num_map]

theorem extract_is_fmap_1 (r: Regex α) (acc: List.Vector α n) (f: α -> β):
  (extract (Regex.map r f) (List.Vector.map f acc)).1 = RegexID.cast (extract r acc).1 (by simp only [num_map]) := by
  generalize_proofs hr
  fun_induction extract with
  | case1 =>
    simp only [Regex.map, extract, RegexID.cast]
  | case2 =>
    simp only [Regex.map, extract, RegexID.cast]
  | case3 =>
    simp only [Regex.map, extract, RegexID.cast]
  | case4 acc r1 r2 er1 acc1 he1 er2 acc2 he2 ih1 ih2 =>
    rename_i n

    have hacc1 : acc1 = (extract r1 acc).2 := by
      rw [he1]
    have hacc2 : acc2 = (extract r2 (extract r1 acc).2).2 := by
      rw [<- hacc1]
      rw [he2]
    have her1 : er1 = (extract r1 acc).1 := by
      rw [he1]
    have her2 : er2 = (extract r2 (extract r1 acc).2).1 := by
      rw [<- hacc1]
      rw [he2]
    rw [hacc1] at ih2
    clear he1
    clear he2

    subst_vars

    have hr1: n + num r1 = n + num (r1.map f) := by
      rw [num_map]
    have ih1' := ih1 hr1
    clear ih1
    have hr2: n + num r1 + num r2 = n + num r1 + num (r2.map f) := by
      rw [num_map]
    have ih2' := ih2 hr2
    clear ih2

    simp only [Regex.map]
    simp only [extract]

    rw [ih1']
    rw [extract_is_fmap_2]
    generalize_proofs
    have hhlift : n + num r1 + num (r2.map f) = n + num (r1.map f) + num (r2.map f) := by
      repeat rw [num_map]
    have hlift := extract_lift_cast_1 (r := r2.map f) (acc := List.Vector.map f (extract r1 acc).2) (h2 := hr1) (h1 := hhlift)
    rw [<- hlift]
    clear hlift
    rw [ih2']
    clear ih1'
    clear ih2'

    simp only [RegexID.add]
    simp only [RegexID.add_or]
    simp only [RegexID.add_assoc]
    repeat rw [RegexID.cast_is_cast_map]
    unfold RegexID.cast_map
    simp [Regex.map_map]
    congr 1
    · simp [Regex.map_map]
    · simp [Regex.map_map]
  | case5 acc r1 r2 er1 acc1 he1 er2 acc2 he2 ih1 ih2 =>
    rename_i n

    have hacc1 : acc1 = (extract r1 acc).2 := by
      rw [he1]
    have hacc2 : acc2 = (extract r2 (extract r1 acc).2).2 := by
      rw [<- hacc1]
      rw [he2]
    have her1 : er1 = (extract r1 acc).1 := by
      rw [he1]
    have her2 : er2 = (extract r2 (extract r1 acc).2).1 := by
      rw [<- hacc1]
      rw [he2]
    rw [hacc1] at ih2
    clear he1
    clear he2

    subst_vars

    have hr1: n + num r1 = n + num (r1.map f) := by
      rw [num_map]
    have ih1' := ih1 hr1
    clear ih1
    have hr2: n + num r1 + num r2 = n + num r1 + num (r2.map f) := by
      rw [num_map]
    have ih2' := ih2 hr2
    clear ih2

    simp only [Regex.map]
    simp only [extract]

    rw [ih1']
    rw [extract_is_fmap_2]
    generalize_proofs
    have hhlift : n + num r1 + num (r2.map f) = n + num (r1.map f) + num (r2.map f) := by
      repeat rw [num_map]
    have hlift := extract_lift_cast_1 (r := r2.map f) (acc := List.Vector.map f (extract r1 acc).2) (h2 := hr1) (h1 := hhlift)
    rw [<- hlift]
    rw [ih2']

    simp only [RegexID.add]
    simp only [RegexID.add_concat]
    simp only [RegexID.add_assoc]
    repeat rw [RegexID.cast_is_cast_map]
    unfold RegexID.cast_map
    simp [Regex.map_map]
    congr 1
    · simp [Regex.map_map]
    · simp [Regex.map_map]
  | case6 acc r1 er1 acc1 he1 ih1 =>
    rename_i n

    have hacc1 : acc1 = (extract r1 acc).2 := by
      rw [he1]
    have her1 : er1 = (extract r1 acc).1 := by
      rw [he1]
    clear he1

    subst_vars

    have hr1: n + num r1 = n + num (r1.map f) := by
      rw [num_map]
    have ih1' := ih1 hr1
    clear ih1

    simp only [Regex.map]
    simp only [extract]

    rw [ih1']
    generalize (extract r1 acc).1 = rid

    repeat rw [RegexID.cast_is_cast_map]
    unfold RegexID.cast_map
    simp [Regex.map]

theorem extracts_lift_cast (rs: List.Vector (Regex α) m) (acc: List.Vector α n) (h1: n + nums rs = l + nums rs) (h2: n = l):
  (Symbols.cast (extracts rs acc).2 h1) = (extracts rs (Symbols.cast acc h2)).2 := by
  subst h2
  rfl

theorem extracts_fmap2 (rs: List.Vector (Regex α) l) (acc: Symbols α n) (f: α -> β):
  (List.Vector.map f (extracts rs acc).2)
  = (Symbols.cast (extracts (Regexes.map rs f) (List.Vector.map f acc)).2 (by
    rw [Nat.add_right_inj]
    apply nums_map
  )) := by
  generalize_proofs h
  generalize_proofs hrs0 hmap0
  apply List.Vector.eq
  simp only [List.Vector.toList_map]
  repeat rw [toList_cast]
  simp only [Regexes.map]
  cases rs with
  | mk rs hrs =>
  induction rs generalizing n l acc with
  | nil =>
    simp only [extracts, List.Vector.map, List.map, List.Vector.toList]
    rfl
  | cons r rs ih =>
    simp only [extracts]
    repeat rw [toList_cast]
    simp only [List.length] at hrs
    have hrs': rs.length = l - 1 := by omega
    have hrs'': rs.length = l.pred := by
      simp [Nat.pred]
      rw [hrs']
      cases l
      · simp
      · simp
    have hh: n + num r + nums (Regexes.map ⟨rs, hrs'⟩ f) = n + num r + nums ⟨rs, hrs'⟩ := by
      rw [nums_map]
    have ih' := ih ((extract r acc).2) hrs'' hh
    rw [ih']

    have h1 : (List.Vector.map (fun r => r.map f) ⟨rs, hrs''⟩).length = l.pred := by
      simp only [Nat.pred_eq_sub_one]
    have h2: n + num (r.map f) + nums (List.Vector.map (fun r => r.map f) ⟨rs, hrs'⟩) =
      n + nums (List.Vector.map (fun r => r.map f) ⟨r :: rs, hrs⟩) := by
      repeat rw [nums_is_nums_list]
      simp only [List.Vector.toList_map, List.Vector.toList_mk, List.map_cons]
      simp only [nums_list]
      ac_rfl

    have hh :
      (extracts
        (List.Vector.map (fun r => r.map f) ⟨r :: rs, hrs⟩)
        (List.Vector.map f acc)
      ).2
      = (Symbols.cast (extracts
          (List.Vector.map (fun r => r.map f) ⟨rs, hrs''⟩)
          (extract (r.map f) (List.Vector.map f acc)).2
        ).2 h2) := by
      simp only [List.Vector.map, List.map, extracts]
    rw [hh]
    rw [toList_cast]

    have hextract := extract_is_fmap_2 (f := f) (r := r) (n := n)
    rw [hextract]

    have hhh :
      n + num r + nums (List.Vector.map (fun r => r.map f) ⟨rs, hrs''⟩) =
      n + num (r.map f) + nums (List.Vector.map (fun r => r.map f) ⟨rs, hrs''⟩) := by
      rw [num_map]

    rw [<- (extracts_lift_cast (h1 := hhh))]
    rw [toList_cast]

theorem Vec.map_cons (f : α → β) (x : α) (xs: List.Vector α n):
  List.Vector.map f (List.Vector.cons x xs) = (List.Vector.cons (f x) (List.Vector.map f xs)) := by
  simp only [List.Vector.map]
  -- aesop?
  simp_all only [Nat.succ_eq_add_one]
  rfl

theorem map_cons (f : α → β) (x : α) (xs: List α) (h: (x :: xs).length = n):
  List.Vector.map f ⟨List.cons x xs, h⟩ = List.Vector.congr (by
    simp only [List.length] at h
    subst h
    simp_all only [add_tsub_cancel_right, Nat.succ_eq_add_one]
  ) (List.Vector.cons (f x) ((List.Vector.map f ⟨xs, by
    simp only [List.length] at h
    rw [<- h]
    simp only [add_tsub_cancel_right]
  ⟩) : List.Vector β (n - 1)): List.Vector β ((n - 1).succ)) := by
  simp only [List.Vector.map, List.map]
  -- aesop?
  subst h
  simp_all only [Nat.succ_eq_add_one]
  rfl

theorem Vec.map_id {n : ℕ} (xs : List.Vector α n) : List.Vector.map (fun x => x) xs = xs :=
  List.Vector.eq _ _ (by simp_all only [List.Vector.toList_map, List.map_id_fun', id_eq])

theorem RegexID.casts_symm:
  RegexID.casts rs1 h = rs2
  <->
  RegexID.casts rs2 (Eq.symm h) = rs1 := by
  apply Iff.intro
  case mp =>
    intro h
    rw [<- h]
    unfold RegexID.casts
    rw [List.Vector.map_map]
    simp only [RegexID.cast_is_cast_map]
    unfold RegexID.cast_map
    simp only [Regex.map_map]
    simp only [Fin.cast_trans, Fin.cast_eq_self]
    simp only [Regex.map_id]
    simp only [Vec.map_id]
  case mpr =>
    intro h
    rw [<- h]
    unfold RegexID.casts
    rw [List.Vector.map_map]
    simp only [RegexID.cast_is_cast_map]
    unfold RegexID.cast_map
    simp only [Regex.map_map]
    simp only [Fin.cast_trans, Fin.cast_eq_self]
    simp only [Regex.map_id]
    simp only [Vec.map_id]

theorem extracts_fmap1 (rs: List.Vector (Regex α) l) (acc: Symbols α n) (f: α -> β):
  (extracts rs acc).1
  = (RegexID.casts (extracts (Regexes.map rs f) (List.Vector.map f acc)).1
      (by simp only [nums_map])
    ) := by
  repeat rw [toList_cast]
  simp only [Regexes.map]

  induction rs generalizing n acc with
  | nil =>
    simp only [List.Vector.map_nil]
    repeat rw [extracts_nil]
    simp only
    unfold RegexID.casts
    simp only [RegexID.cast_is_cast_map]
    simp only [Nat.add_zero, List.Vector.map_nil]
  | cons ih =>
    rename_i l r rs
    rw [RegexID.casts_symm.mpr]


    -- generalize_proofs h1 h2 at *
    -- (extract (r.map f) (List.Vector.map f acc)).1
    have hfmap1 := extract_is_fmap_1 (f := f) (r := r) (n := n)
    -- generalize_proofs hhfamp1 at hfmap1
    -- rw [hfmap1]

    -- (List.Vector.map (fun r => r.map f) ⟨r :: rs, hrs⟩)
    have hmapcons := Vec.map_cons (f := fun r => r.map f) (x := r) (xs := rs)
    -- simp only [hmapcons]
    -- generalize_proofs hmapcons1 hmapcons2 at hmapcons
    -- rw [hmapcons]

    -- have hhcastsrfl : (n + nums ⟨r :: rs, hrs⟩) = (n + nums ⟨r :: rs, hrs⟩) := by rfl
    -- have hcastsrfl := RegexID.casts_rfl (xs := (extracts ⟨r :: rs, hrs⟩ acc).1) (h := rfl)
    -- rw [<- hcastsrfl]

    -- congr 1
    -- · simp [nums_map]
    --   sorry
    -- · sorry
    -- · rw [show Regexes.map ⟨r :: rs, hrs⟩ f = List.Vector.map (fun r => r.map f) ⟨r :: rs, hrs⟩ from
    --       rfl] at h


    -- have hpred: rs.length = l.pred := by
    --   simp only [List.length] at hrs
    --   simp only [Nat.pred]
    --   rw [<- hrs]

    -- have ih' := ih (l := l.pred) ((extract r acc).2) hpred
    clear ih

    simp only [extracts]
    rw [ih']
    clear ih'

    unfold Symbols.cast











    apply List.Vector.eq
    rw [toList_cast]


    -- rw [hmapcons]
    -- rw [hfmap1]


    simp only [List.Vector.map, List.map, extracts]

    sorry









theorem extracts_replacesFrom_is_id (rs: List.Vector (Regex α) l) (acc: Symbols α n):
  rs = replacesFrom (extracts rs acc).1 (extracts rs acc).2 := by
  cases rs with
  | mk rs hrs =>
  induction rs generalizing n l acc with
  | nil =>
    apply List.Vector.eq
    simp [extracts, replacesFrom]
  | cons r rs ih =>
    simp only [extracts]
    simp only [replacesFrom] at *
    simp only [map_cast]
    generalize_proofs h1 h2 h3 h4

    sorry


theorem extracts_replacesFrom_is_fmap (rs: List.Vector (Regex α) l) (f: α -> β):
  Regexes.map rs f = replacesFrom (extracts rs acc).1 (List.Vector.map f (extracts rs acc).2) := by
  rw [extracts_fmap2]
  have hh := extracts_replacesFrom_is_id (rs := Regexes.map rs f) (acc := List.Vector.map f acc)
  simp_all only
  nth_rewrite 2 [extracts_fmap1]
  rw [<- replacesFrom_cast_both]

theorem extractsFrom_replacesFrom_is_fmap (rs: List.Vector (Regex α) l) (f: α -> β):
  Regexes.map rs f = replacesFrom (extractsFrom rs).1 (List.Vector.map f (extractsFrom rs).2) := by
  simp only [extractsFrom]
  generalize_proofs h
  rw [extracts_replacesFrom_is_fmap (acc := List.Vector.nil) (f := f)]
  rw [replacesFrom_cast_both (h := h)]
  simp only [map_cast]

theorem Symbol_derives_is_fmap
  {σ: Type} {α: Type} (p: σ -> α -> Bool) (rs: List.Vector (Regex σ) l) (a: α):
  Symbol.derives p rs a = List.Vector.map (fun r => Symbol.derive p r a) rs := by
  unfold Symbol.derives
  simp only
  unfold Regex.derives2
  unfold Symbol.derive
  nth_rewrite 2 [<- List.Vector.map_map]
  nth_rewrite 1 [<- List.Vector.map_map]
  apply (congrArg (List.Vector.map Regex.derive2))
  rw [<- zip_map]
  -- rewrites under the closure
  simp only [<- extractFrom_replaceFrom_is_fmap]
  rw [<- extractsFrom_replacesFrom_is_fmap]
  unfold Regexes.map
  simp only [List.Vector.map_map]

theorem Symbol_derives_is_Regex_derives
  {σ: Type} {α: Type} (p: σ -> α -> Bool) (r: List.Vector (Regex σ) l) (a: α):
  Symbol.derives p r a = Regex.derives p r a := by
  rw [Symbol_derives_is_fmap]
  unfold Symbol.derive
  unfold Regex.derives
  congr
  funext r
  rw [<- extractFrom_replaceFrom_is_fmap]
  rw [Regex.derive_is_derive2]

def leave
  (rs: List.Vector (Regex σ) l)
  (ns: List.Vector Bool (Symbol.nums rs))
  : (List.Vector (Regex σ) l) :=
  let replaces: List.Vector (σ × Bool) (nums rs) := Vec.zip (Symbol.extractsFrom rs).2 ns
  let replaced: List.Vector (Regex (σ × Bool)) l := replacesFrom (Symbol.extractsFrom rs).1 replaces
  Regex.derives2 replaced

def enter (rs: List.Vector (Regex σ) l): Symbols σ (nums rs) :=
  let (_, symbols): (List.Vector (RegexID (nums rs)) l × Symbols σ (nums rs)) := Symbol.extractsFrom rs
  symbols

-- derives_preds unlike derives takes a predicate that works out the full vector of predicates.
-- This gives the predicate control over the evaluation order of α, for example α is a tree, we can first evaluate the same label, before traversing down.
def derives_preds {σ: Type} {α: Type}
  (ps: {n: Nat} -> List.Vector σ n -> α -> List.Vector Bool n) (rs: List.Vector (Regex σ) l) (a: α): List.Vector (Regex σ) l :=
  let symbols: Symbols σ (nums rs) := enter rs
  let pred_results: List.Vector Bool (nums rs) := ps symbols a
  leave rs pred_results

theorem Symbol_derive_is_derive_preds
  {σ: Type} {α: Type} (ps: {n: Nat} -> List.Vector σ n -> α -> List.Vector Bool n) (rs: List.Vector (Regex σ) l) (a: α)
  (h: ∀ {n': Nat} (xs: List.Vector σ n') (a: α), ps xs a = List.Vector.map (fun x => (ps (Vec.singleton x) a).head) xs):
  Symbol.derives (fun s a => (ps (Vec.singleton s) a).head) rs a = Symbol.derives_preds ps rs a := by
  unfold derives
  simp only
  rw [<- h]
  unfold derives_preds
  unfold leave
  unfold enter
  simp only
