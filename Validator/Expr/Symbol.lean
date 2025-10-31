import Mathlib.Data.Vector.Basic
import Mathlib.Data.Vector.Snoc
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

def nums (xs: List.Vector (Regex σ) μ): Nat :=
  match xs with
  | ⟨[], _⟩ => 0
  | ⟨x::xs, h⟩ => nums ⟨xs, congrArg Nat.pred h⟩ + num x

abbrev RegexID n := Regex (Fin n)
abbrev Symbols σ n := List.Vector σ n

def RegexID.add {n: Nat} (m: Nat) (r: RegexID n): RegexID (n + m) :=
  Regex.map r (fun s => (Fin.mk s.val (by omega)))

def RegexID.cast (r: RegexID n) (h: n = m): RegexID m := by
  rw [<- h]
  exact r

def RegexID.add_or (r: RegexID (μ + num r1 + num r2)): RegexID (μ + num (Regex.or r1 r2)) :=
  have h : (μ + num r1 + num r2) = (μ + num (Regex.or r1 r2)) := by
    rw [<- Nat.add_assoc]
  RegexID.cast r h

def RegexID.add_concat (r: RegexID (μ + num r1 + num r2)): RegexID (μ + num (Regex.concat r1 r2)) :=
  have h : (μ + num r1 + num r2) = (μ + num (Regex.concat r1 r2)) := by
    rw [<- Nat.add_assoc]
  RegexID.cast r h

theorem List.Vector.toList_take:
  List.take n xs.val = (List.Vector.take n xs).toList := by
  simp only [_root_.List.Vector.toList_take]
  rfl

theorem List.Vector.toList_cons:
  List.cons x xs.val = (List.Vector.cons x xs).toList := by
  simp only [Nat.succ_eq_add_one, _root_.List.Vector.toList_cons, List.cons.injEq, true_and]
  rfl

def Symbols.cast (xs: Symbols σ n) (h: n = m): Symbols σ m := by
  rw [<- h]
  exact xs

theorem List.Vector.toList_cast_is_toList (xs: List.Vector σ n):
  List.Vector.toList xs = List.Vector.toList (Symbols.cast xs h) := by
  rcases xs with ⟨xs, hxs⟩
  simp [Symbols.cast, _root_.cast, List.Vector.toList]
  subst h hxs
  simp only

abbrev Symbols.take {α: Type} (i: Nat) (xs: List.Vector α n) := List.Vector.take i xs
abbrev Symbols.get {α: Type} (xs: List.Vector α n) (i: Fin n) := List.Vector.get xs i
abbrev Symbols.nil {α: Type} := @List.Vector.nil α
abbrev Symbols.snoc {α: Type} (xs: List.Vector α n) (x: α) := List.Vector.snoc xs x
abbrev Symbols.cons {α: Type} (x: α) (xs: List.Vector α n) := List.Vector.cons x xs
abbrev Symbols.set {α: Type} (v : List.Vector α n) (i : Fin n) (a : α) := List.Vector.set v i a
abbrev Symbols.toList {α: Type} (v : List.Vector α n) := List.Vector.toList v

def Symbols.add_or (xs: Symbols σ (μ + num r1 + num r2)): Symbols σ (μ + num (Regex.or r1 r2)) :=
  have h : (μ + num r1 + num r2) = (μ + num (Regex.or r1 r2)) := by
    rw [<- Nat.add_assoc]
  Symbols.cast xs h

def Symbols.add_concat (xs: Symbols σ (μ + num r1 + num r2)): Symbols σ (μ + num (Regex.or r1 r2)) :=
  have h : (μ + num r1 + num r2) = (μ + num (Regex.concat r1 r2)) := by
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
  rw [<- List.Vector.toList_take]
  rw [<- List.Vector.toList_cons]
  simp only [List.Vector.cons_val, List.take_succ_cons, List.cons.injEq, true_and]
  rw [List.Vector.toList_take]
  simp [List.Vector.toList]

theorem Symbols.cast_take (xs: Symbols σ n):
  Symbols.take n xs = Symbols.cast (n := n) (m := min n n) xs (by omega) := by
  unfold Symbols.take
  apply List.Vector.eq
  generalize_proofs h
  rw [<- List.Vector.toList_cast_is_toList]
  rw [<- List.Vector.toList_take]
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

theorem Symbols.push_get {μ: Nat} {α: Type} (xs: Symbols α μ) (x: α):
  Symbols.get (Symbols.snoc xs x) (Fin.mk μ (by omega)) = x := by
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

def replace (r: RegexID μ) (xs: Symbols σ ν) (h: μ <= ν): Regex σ :=
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

theorem replace_cast_both (r: RegexID μ) (xs: Symbols σ μ) (h: μ = ν):
  replace r xs (by omega) = replace (RegexID.cast r h) (Symbols.cast xs h) (by omega) := by
  subst h
  simp only [Symbols.cast_rfl]
  rfl

theorem replace_cast_symbols (r: RegexID μ) (xs: Symbols σ μ) (h: μ = ν):
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

theorem replace_take (r: RegexID μ) (xs: Symbols σ (μ + n)):
  replace r (Symbols.take μ xs) (by omega) = replace r xs (by omega):= by
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

theorem replace_regexid_add (r: RegexID μ) (xs: List.Vector σ (μ + n)):
  replace r xs (by omega) = replace (RegexID.add n r) xs (by omega):= by
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

def extract (r: Regex σ) (res: Symbols σ μ): RegexID (μ + num r) × Symbols σ (μ + num r) :=
  match r with
  | Regex.emptyset => (Regex.emptyset, res)
  | Regex.emptystr => (Regex.emptystr, res)
  | Regex.symbol s => (Regex.symbol (Fin.mk μ (by
      simp only [num]
      omega
    )), Symbols.snoc res s)
  | Regex.or r1 r2 =>
    let (er1, res1) := extract r1 res
    let (er2, res2) := extract r2 res1
    (Regex.or (RegexID.add_or (RegexID.add (num r2) er1)) (RegexID.add_or er2), Symbols.add_or res2)
  | Regex.concat r1 r2 =>
    let (er1, res1) := extract r1 res
    let (er2, res2) := extract r2 res1
    (Regex.concat (RegexID.add_concat (RegexID.add (num r2) er1)) (RegexID.add_concat er2), Symbols.add_concat res2)
  | Regex.star r1 =>
    let (er1, res1) := extract r1 res
    (Regex.star er1, res1)

theorem extract_append_toList (res: Symbols σ μ) (r: Regex σ):
  List.Vector.toList (extract r res).2 = List.Vector.toList (res ++ (extract r Symbols.nil).2) := by
  induction r generalizing res μ  with
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

theorem extract_append (res: Symbols σ μ) (r: Regex σ):
  (extract r res).2 = Symbols.cast (res ++ (extract r Symbols.nil).2) (by omega) := by
  apply List.Vector.eq
  rw [extract_append_toList]
  rw [<- List.Vector.toList_cast_is_toList]

theorem extract_take_toList (res: Symbols σ μ):
  (List.Vector.toList
    (List.Vector.take
      (μ + num r1)
      (extract r2
      (extract r1 res).2).2
    )
  )
  =
  (List.Vector.toList (extract r1 res).2) := by
  rw [<- List.Vector.toList_take]
  rw [<- List.Vector.toList]
  rw [extract_append_toList]
  rw [List.Vector.toList_append]
  rw [List.Vector.toList]
  generalize he: (extract r1 res).2 = her
  obtain ⟨her, hher⟩ := her
  simp only
  simp_all only [List.take_left']

theorem extract_take (res: Symbols σ μ):
  (List.Vector.take
    (μ + num r1)
    (extract r2
      (extract r1 res).2).2
  )
  =
    Symbols.cast
    (extract r1 res).2
    (by omega) := by
  apply List.Vector.eq
  rw [extract_take_toList]
  rw [<- List.Vector.toList_cast_is_toList]

def replaceFrom (r: RegexID μ) (xs: Symbols σ μ): Regex σ :=
  replace r xs (le_refl μ)

theorem extract_replaceFrom_is_id (r: Regex σ) (res: Symbols σ μ):
  r = replaceFrom (extract r res).1 (extract r res).2 := by
  simp only [replaceFrom]
  generalize_proofs hr
  revert res μ
  induction r with
  | emptyset =>
    intro μ res hr
    simp only [replace, extract]
  | emptystr =>
    intro μ res hr
    simp only [replace, extract]
  | symbol s =>
    intro μ res hr
    simp only [replace, extract]
    rw [Symbols.push_get]
  | or r1 r2 ih1 ih2 =>
    intro μ res hr
    simp only [extract]
    simp only [replace]
    have hh1 :
      r1 =
        (replace
          (RegexID.add_or (RegexID.add (num r2) (extract r1 res).1))
          (Symbols.add_or (extract r2 (extract r1 res).2).2)
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
      nth_rewrite 1 [ih1 res]
      rw [replace_cast_symbols]
    rw [<- hh1]
    clear hh1
    clear ih1
    congr
    rw [RegexID.add_or]
    rw [Symbols.add_or]
    rw [<- replace_cast_both]
    rw [<- ih2 ((extract r1 res).2)]
  | concat r1 r2 ih1 ih2 =>
    intro μ res hr
    simp only [extract]
    simp only [replace]
    have hh1 :
      r1 =
        (replace
          (RegexID.add_concat (RegexID.add (num r2) (extract r1 res).1))
          (Symbols.add_concat (extract r2 (extract r1 res).2).2)
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
      nth_rewrite 1 [ih1 res]
      rw [replace_cast_symbols]
    rw [<- hh1]
    clear hh1
    clear ih1
    congr
    rw [RegexID.add_concat]
    rw [Symbols.add_concat]
    rw [<- replace_cast_both]
    rw [<- ih2 ((extract r1 res).2)]
  | star r1 ih1 =>
    simp only [extract]
    simp only [replace]
    intro μ res hr
    rw [<- ih1 res]

theorem extract_replace_is_id (r: Regex σ) (res: Symbols σ μ):
  r = replace (extract r res).1 (extract r res).2 (by omega):= by
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
  List.Vector (RegexID (nres + nums (⟨x::xs, h⟩))) n
  = List.Vector (RegexID (nres + num x + nums ⟨xs, congrArg Nat.pred h⟩)) n := by
  simp [nums]
  ac_rfl

def extracts (xs: List.Vector (Regex σ) nregex) (res: Symbols σ nres):
  (List.Vector (RegexID (nres + nums xs)) nregex) × (Symbols σ (nres + nums xs)) :=
  match xs with
  | ⟨[], h⟩ =>
    (
      ⟨[], by assumption ⟩,
      ⟨res.val, by simp only [List.Vector.length_val, nums, add_zero]⟩
    )
  | ⟨x::xs, h⟩ =>
    let xs': List.Vector (Regex σ) nregex.pred := ⟨xs, congrArg Nat.pred h⟩
    let (regex, symbols) := Symbol.extract x res
    let regex' := RegexID.add (nums ⟨xs, congrArg Nat.pred h⟩) regex
    let regex'': RegexID (nres + nums (⟨x::xs, h⟩)) :=
      RegexID.cast
      regex'
      (by
        simp
        rw [nums_cons_is_add]
        ac_rfl
      )
    let (regexes, symbols') := extracts xs' symbols
    let regexes': List.Vector (RegexID (nres + nums (⟨x::xs, h⟩))) nregex.pred
      := by
        rw [RegexID.cons_cast]
        exact regexes
    let regexes'' : List.Vector (RegexID (nres + nums (⟨x::xs, h⟩))) nregex :=
      (Symbols.cast
        ((List.Vector.cons
          regex''
          regexes'
        ): List.Vector (RegexID (nres + nums (⟨x::xs, h⟩))) nregex.pred.succ)
        (by
          rw [<- h]
          simp only [List.length_cons, Nat.pred_eq_sub_one, add_tsub_cancel_right, Nat.succ_eq_add_one]
        )
      )
    let symbols': Symbols σ (nres + nums (⟨x::xs, h⟩)) :=
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

def extractsSymbols (xs: List.Vector (Regex σ) μ) (res: Symbols σ μ1):
  Symbols σ (μ1 + Symbol.nums xs) :=
  match xs with
  | ⟨[], h⟩ => ⟨res.val, by simp only [List.Vector.length_val, Symbol.nums, add_zero]⟩
  | ⟨x::xs, h⟩ =>
      (Symbol.Symbols.cast
        (extractsSymbols ⟨xs, congrArg Nat.pred h⟩ (Symbol.extract x res).2)
        (by simp only [Symbol.nums]; ac_rfl)
      )
