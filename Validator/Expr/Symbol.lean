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

def nums_list (xs: List (Regex σ)): Nat :=
  nums (Vec.fromList xs)

abbrev RegexID n := Regex (Fin n)
abbrev Symbols σ l := List.Vector σ l

def RegexID.add {n: Nat} (m: Nat) (r: RegexID n): RegexID (n + m) :=
  Regex.map r (fun s => (Fin.mk s.val (by omega)))

def RegexID.cast (r: RegexID n) (h: n = m): RegexID m := by
  rw [<- h]
  exact r

def RegexID.add_or (r: RegexID (n + num r1 + num r2)): RegexID (n + num (Regex.or r1 r2)) :=
  have h : (n + num r1 + num r2) = (n + num (Regex.or r1 r2)) := by
    rw [<- Nat.add_assoc]
  RegexID.cast r h

def RegexID.add_concat (r: RegexID (n + num r1 + num r2)): RegexID (n + num (Regex.concat r1 r2)) :=
  have h : (n + num r1 + num r2) = (n + num (Regex.concat r1 r2)) := by
    rw [<- Nat.add_assoc]
  RegexID.cast r h

def Symbols.cast (xs: Symbols σ n) (h: n = m): Symbols σ m := by
  rw [<- h]
  exact xs

theorem List.Vector.toList_cast_is_toList (xs: List.Vector σ n):
  List.Vector.toList xs = List.Vector.toList (Symbols.cast xs h) := by
  rcases xs with ⟨xs, hxs⟩
  simp [Symbols.cast, _root_.cast, List.Vector.toList]
  subst h hxs
  simp only

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

def Symbols.add_concat (xs: Symbols σ (n + num r1 + num r2)): Symbols σ (n + num (Regex.or r1 r2)) :=
  have h : (n + num r1 + num r2) = (n + num (Regex.concat r1 r2)) := by
    rw [<- Nat.add_assoc]
  Symbols.cast xs h

theorem Symbols.cast_rfl {xs : Symbols α n} : Symbols.cast xs rfl = xs := by
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

def extractsSymbols (xs: List.Vector (Regex σ) l1) (acc: Symbols σ l2):
  Symbols σ (l2 + Symbol.nums xs) :=
  match xs with
  | ⟨[], h⟩ => ⟨acc.val, by simp only [List.Vector.length_val, Symbol.nums, add_zero]⟩
  | ⟨x::xs, h⟩ =>
      (Symbol.Symbols.cast
        (extractsSymbols ⟨xs, congrArg Nat.pred h⟩ (Symbol.extract x acc).2)
        (by simp only [Symbol.nums]; ac_rfl)
      )

def extracts_list (xs: List (Regex σ)) (acc: List σ):
  (List (RegexID (acc.length + nums_list xs))) × (List σ) :=
  let (r1, r2) := extracts (Vec.fromList xs) (Vec.fromList acc)
  let r2List: List σ := List.Vector.toList r2
  (r1.toList, r2List)

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

theorem Symbol_derive_is_Regex_derive
  {σ: Type} {α: Type} (p: σ -> α -> Bool) (r: Regex σ) (a: α):
  Symbol.derive p r a = Regex.derive p r a := by
  unfold Symbol.derive
  rw [<- extractFrom_replaceFrom_is_fmap]
  rw [Regex.derive_is_derive2]
