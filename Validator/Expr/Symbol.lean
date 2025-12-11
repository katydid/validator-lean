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

abbrev RegexID n := Regex (Fin n)

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
  match xs with
  | Vec.nil => 0
  | Vec.cons x xs => nums xs + num x

def nums_list (xs: List (Regex σ)): Nat :=
  match xs with
  | [] => 0
  | x::xs => nums_list xs + num x

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

abbrev RegexID.add_assoc (r: RegexID (n + num r1 + num r2)): RegexID (n + (num r1 + num r2)) :=
  have h : (n + num r1 + num r2) = n + (num r1 + num r2) := by
    rw [<- Nat.add_assoc]
  RegexID.cast r h

def RegexID.add_or (r: RegexID (n + num r1 + num r2)): RegexID (n + num (Regex.or r1 r2)) :=
  RegexID.add_assoc r

def RegexID.add_concat (r: RegexID (n + num r1 + num r2)): RegexID (n + num (Regex.concat r1 r2)) :=
  RegexID.add_assoc r

def Vec.cast_or (xs: Vec σ (n + num r1 + num r2)): Vec σ (n + num (Regex.or r1 r2)) :=
  have h : (n + num r1 + num r2) = (n + num (Regex.or r1 r2)) := by
    rw [<- Nat.add_assoc]
  Vec.cast xs h

def Vec.cast_concat (xs: Vec σ (n + num r1 + num r2)): Vec σ (n + num (Regex.concat r1 r2)) :=
  have h : (n + num r1 + num r2) = (n + num (Regex.concat r1 r2)) := by
    rw [<- Nat.add_assoc]
  Vec.cast xs h

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

def extract (r: Regex σ) (acc: Vec σ n): RegexID (n + num r) × Vec σ (n + num r) :=
  match r with
  | Regex.emptyset => (Regex.emptyset, acc)
  | Regex.emptystr => (Regex.emptystr, acc)
  | Regex.symbol s => (Regex.symbol (Fin.mk n (by
      simp only [num]
      omega
    )), Vec.snoc acc s)
  | Regex.or r1 r2 =>
    let (er1, acc1) := extract r1 acc
    let (er2, acc2) := extract r2 acc1
    (Regex.or (RegexID.add_or (RegexID.add (num r2) er1)) (RegexID.add_or er2), Vec.cast_or acc2)
  | Regex.concat r1 r2 =>
    let (er1, acc1) := extract r1 acc
    let (er2, acc2) := extract r2 acc1
    (Regex.concat (RegexID.add_concat (RegexID.add (num r2) er1)) (RegexID.add_concat er2), Vec.cast_concat acc2)
  | Regex.star r1 =>
    let (er1, acc1) := extract r1 acc
    (Regex.star er1, acc1)

def extractFrom (r: Regex σ): RegexID (num r) × Vec σ (num r) :=
  match extract r Vec.nil with
  | (r', xs) => (RegexID.cast r' (by omega), Vec.cast xs (by omega))

def derive {σ: Type} {α: Type} (p: σ -> α -> Bool) (r: Regex σ) (a: α): Regex σ :=
  Regex.derive2
    (replaceFrom
      (extractFrom r).1
      (Vec.map
        (extractFrom r).2
        (fun s => (s, p s a))
      )
    )

def derive' {σ: Type} {α: Type} (p: σ -> α -> Bool) (r: Regex σ) (a: α): Regex σ :=
  let (r', symbols): (RegexID (num r) × Vec σ (num r)) := extractFrom r
  let pred_results: Vec Bool (num r) := Vec.map symbols (fun s => p s a)
  let replaces: Vec (σ × Bool) (num r) := Vec.zip symbols pred_results
  let replaced: Regex (σ × Bool) := replaceFrom r' replaces
  Regex.derive2 replaced

def extracts (xs: Vec (Regex σ) nregex) (acc: Vec σ nacc):
  (Vec (RegexID (nacc + nums xs)) nregex) × (Vec σ (nacc + nums xs)) :=
  match xs with
  | Vec.nil =>
    ( Vec.nil, acc )
  | @Vec.cons _ nregex x xs =>
    let (regexid, acc1) := Symbol.extract x acc
    let (regexids, accs) := extracts xs acc1
    let regexid': RegexID (nacc + nums (Vec.cons x xs)) :=
      RegexID.cast (RegexID.add (nums xs) regexid) (by simp only [nums]; ac_rfl)
    let regexesids' : Vec (RegexID (nacc + nums (Vec.cons x xs))) nregex :=
      RegexID.casts regexids (by simp only [nums]; ac_rfl)
    let regexidcons: Vec (RegexID (nacc + nums (Vec.cons x xs))) (nregex + 1) :=
      Vec.cast (Vec.cons regexid' regexesids') (by simp only)
    let accs' : (Vec σ (nacc + nums (Vec.cons x xs))) :=
      Vec.cast accs (by simp only [nums]; ac_rfl)
    (regexidcons, accs')

def extractsFrom (xs: Vec (Regex σ) nregex):
  (Vec (RegexID (nums xs)) nregex) × (Vec σ (nums xs)) :=
  let (xs0, symbols0) := extracts xs Vec.nil
  let symbols': Vec σ (nums xs) := Vec.cast symbols0 (by ac_rfl)
  let xs': Vec (RegexID (nums xs)) nregex := RegexID.casts xs0 (by ac_rfl)
  (xs', symbols')

def replacesFrom (rs: Vec (RegexID n) l) (xs: Vec σ n): Vec (Regex σ) l :=
  Vec.map rs (fun r => replaceFrom r xs)

def derives {σ: Type} {α: Type} (p: σ -> α -> Bool) (rs: Vec (Regex σ) l) (a: α): Vec (Regex σ) l :=
  let (rs', symbols): (Vec (RegexID (nums rs)) l × Vec σ (nums rs)) := Symbol.extractsFrom rs
  let pred_results: Vec Bool (nums rs) := Vec.map symbols (fun s => p s a)
  let replaces: Vec (σ × Bool) (nums rs) := Vec.zip symbols pred_results
  let replaced: Vec (Regex (σ × Bool)) l := replacesFrom rs' replaces
  Regex.derives2 replaced

def leave
  (rs: Vec (Regex σ) l)
  (ps: Vec Bool (Symbol.nums rs))
  : (Vec (Regex σ) l) :=
  let replaces: Vec (σ × Bool) (nums rs) := Vec.zip (Symbol.extractsFrom rs).2 ps
  let replaced: Vec (Regex (σ × Bool)) l := replacesFrom (Symbol.extractsFrom rs).1 replaces
  Regex.derives2 replaced

def enter (rs: Vec (Regex σ) l): Vec σ (nums rs) :=
  let (_, symbols): (Vec (RegexID (nums rs)) l × Vec σ (nums rs)) := Symbol.extractsFrom rs
  symbols

-- derives_preds unlike derives takes a predicate that works out the full vector of predicates.
-- This gives the predicate control over the evaluation order of α, for example α is a tree, we can first evaluate the same label, before traversing down.
def derives_preds {σ: Type} {α: Type}
  (ps: {n: Nat} -> Vec σ n -> α -> Vec Bool n) (rs: Vec (Regex σ) l) (a: α): Vec (Regex σ) l :=
  let symbols: Vec σ (nums rs) := enter rs
  let pred_results: Vec Bool (nums rs) := ps symbols a
  leave rs pred_results

theorem nums_nil {σ: Type}:
  nums (@Vec.nil (Regex σ)) = 0 := by
  unfold nums
  rfl

theorem nums_is_nums_list (xs: Vec (Regex σ) l):
  nums xs = nums_list xs.toList := by
  induction xs with
  | nil =>
    simp only [nums, Vec.toList, nums_list]
  | cons x xs ih =>
    simp only [nums, Vec.toList, nums_list]
    rw [ih]

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

theorem extract_append_toList (acc: Vec σ n) (r: Regex σ):
  Vec.toList (extract r acc).2 = Vec.toList (Vec.append acc (extract r Vec.nil).2) := by
  induction r generalizing acc n  with
  | emptyset =>
    simp only [num, Nat.add_zero, extract, Vec.append_nil, Vec.cast_toList]
  | emptystr =>
    simp only [num, Nat.add_zero, extract, Vec.append_nil, Vec.cast_toList]
  | symbol s =>
    simp only [extract, Vec.snoc]
    rw [Vec.snoc_append]
  | or r1 r2 ih1 ih2 =>
    simp only [extract]
    rw [Vec.cast_or]
    generalize_proofs h1 h2 h3
    rw [Vec.cast_or]
    generalize_proofs h4
    rw [Vec.toList_append]
    rw [Vec.cast_toList]
    rw [Vec.cast_toList]
    rw [ih2]
    rw [Vec.toList_append]
    rw [ih1]
    rw [Vec.toList_append]
    nth_rewrite 2 [ih2]
    rw [Vec.toList_append]
    ac_rfl
  | concat r1 r2 ih1 ih2 =>
    simp only [extract]
    rw [Vec.cast_concat]
    generalize_proofs h1 h2 h3
    rw [Vec.cast_concat]
    generalize_proofs h4
    rw [Vec.toList_append]
    rw [Vec.cast_toList]
    rw [Vec.cast_toList]
    rw [ih2]
    rw [Vec.toList_append]
    rw [ih1]
    rw [Vec.toList_append]
    nth_rewrite 2 [ih2]
    rw [Vec.toList_append]
    ac_rfl
  | star r1 ih1 =>
    simp only [extract]
    rw [ih1]

theorem extract_append (acc: Vec σ l) (r: Regex σ):
  (extract r acc).2 = Vec.cast (Vec.append acc (extract r Vec.nil).2) (by omega) := by
  apply Vec.eq
  rw [extract_append_toList]
  rw [<- Vec.cast_toList]

theorem extract_take_toList (acc: Vec σ l):
  (Vec.toList
    (Vec.take
      (l + num r1)
      (extract r2
      (extract r1 acc).2).2
    )
  )
  =
  (Vec.toList (extract r1 acc).2) := by
  rw [<- Vec.toList_take]
  rw [extract_append_toList]
  rw [Vec.toList_append]
  rw [List.take_left']
  rw [Vec.toList_length]

theorem extract_take (acc: Vec σ l):
  (Vec.take
    (l + num r1)
    (extract r2
      (extract r1 acc).2).2
  )
  =
    Vec.cast
    (extract r1 acc).2
    (by omega) := by
  apply Vec.eq
  rw [extract_take_toList]
  rw [<- Vec.cast_toList]

theorem extract_take_toList_fmap (acc: Vec σ l):
  (Vec.toList
    (Vec.take
      (l + num r1)
      (Vec.map
        (extract r2
        (extract r1 acc).2).2
        f
      )
    )
  )
  =
  (Vec.toList
    (Vec.map
      (extract r1 acc).2
      f
    )
  ) := by
  rw [<- Vec.toList_take]
  rw [Vec.map_toList]
  rw [extract_append_toList]
  rw [Vec.toList_append]
  simp_all only [List.map_append, Vec.toList_map]
  rw [List.take_left']
  rw [<- Vec.map_toList]
  rw [Vec.toList_length]

theorem extract_take_fmap (acc: Vec α l) (f: α -> β):
  (Vec.take
    (l + num r1)
    (Vec.map
      (extract r2
        (extract r1 acc).2).2
      f
    )
  )
  =
    Vec.cast
    (Vec.map
      (extract r1 acc).2
      f
    )
    (by omega) := by
  apply Vec.eq
  rw [extract_take_toList_fmap]
  rw [<- Vec.cast_toList]

theorem extract_replaceFrom_is_id (r: Regex σ) (acc: Vec σ l):
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
    rw [Vec.snoc_get]
  | or r1 r2 ih1 ih2 =>
    intro n acc hr
    simp only [extract]
    simp only [replace]
    have hh1 :
      r1 =
        (replace
          (RegexID.add_or (RegexID.add (num r2) (extract r1 acc).1))
          (Vec.cast_or (extract r2 (extract r1 acc).2).2)
          hr
        ) := by
      clear ih2
      rw [RegexID.add_or]
      rw [Vec.cast_or]
      rw [<- replace_cast_both]
      rw [<- replace_regexid_add]
      rw [<- replace_take]
      generalize_proofs h1
      rw [extract_take]
      generalize_proofs h1 h2
      nth_rewrite 1 [ih1 acc]
      rw [replace_cast_symbols]
    rw [<- hh1]
    clear hh1
    clear ih1
    congr
    rw [RegexID.add_or]
    rw [Vec.cast_or]
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
          (Vec.cast_concat (extract r2 (extract r1 acc).2).2)
          hr
        ) := by
      clear ih2
      rw [RegexID.add_concat]
      rw [Vec.cast_concat]
      rw [<- replace_cast_both]
      rw [<- replace_regexid_add]
      rw [<- replace_take]
      generalize_proofs h1
      rw [extract_take]
      generalize_proofs h1 h2
      nth_rewrite 1 [ih1 acc]
      rw [replace_cast_symbols]
    rw [<- hh1]
    clear hh1
    clear ih1
    congr
    rw [RegexID.add_concat]
    rw [Vec.cast_concat]
    rw [<- replace_cast_both]
    rw [<- ih2 ((extract r1 acc).2)]
  | star r1 ih1 =>
    simp only [extract]
    simp only [replace]
    intro n acc hr
    rw [<- ih1 acc]

theorem extract_replace_is_id (r: Regex σ) (acc: Vec σ l):
  r = replace (extract r acc).1 (extract r acc).2 (by omega):= by
  rw [<- replaceFrom]
  rw [<- extract_replaceFrom_is_id]

theorem extractFrom_replaceFrom_is_id (r: Regex σ):
  r = replaceFrom (extractFrom r).1 (extractFrom r).2 := by
  simp only [extractFrom]
  simp only [replaceFrom]
  rw [<- replace_cast_both]
  rw [<- extract_replace_is_id r Vec.nil]

theorem nums_cons_is_add:
  nums (Vec.cons x xs) = num x + nums xs
  := by
  simp only [nums]
  ac_rfl

theorem RegexID.cons_cast:
  Vec (RegexID (nacc + nums (Vec.cons x xs))) n
  = Vec (RegexID (nacc + num x + nums xs)) n := by
  simp only [nums]
  ac_rfl

theorem extracts_nil (acc: Vec σ nacc):
  extracts (@Vec.nil (Regex σ)) acc = (RegexID.casts Vec.nil (by
    simp only [nums_nil]
    rfl
  ), Vec.cast acc (by
    simp only [nums_nil]
    simp only [add_zero]
  )) := by
  simp only [extracts]
  rfl

theorem map_cast (xs: Vec α l1) (f: α -> β) (h: l1 = l2):
  Vec.map (Vec.cast xs h) f = Vec.cast (Vec.map xs f) h := by
  subst h
  rfl

theorem extract_replaceFrom_is_fmap (r: Regex α) (acc: Vec α l) (f: α -> β):
  Regex.map r f = replaceFrom (extract r acc).1 (Vec.map (extract r acc).2 f) := by
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
    simp only [Vec.snoc_map]
    rw [Vec.snoc_get]
  | or r1 r2 ih1 ih2 =>
    intro n acc hr
    simp only [extract]
    simp only [replace]
    simp only [Regex.map]
    have hh1 :
      Regex.map r1 f =
        (replace
          (RegexID.add_or (RegexID.add (num r2) (extract r1 acc).1))
          (Vec.map (Vec.cast_or (extract r2 (extract r1 acc).2).2) f)
          hr
        ) := by
      clear ih2
      rw [RegexID.add_or]
      rw [Vec.cast_or]
      rw [map_cast]
      rw [<- replace_cast_both]
      rw [<- replace_regexid_add]
      rw [<- replace_take]
      generalize_proofs h1
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
    rw [Vec.cast_or]
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
          (Vec.map (Vec.cast_concat (extract r2 (extract r1 acc).2).2) f)
          hr
        ) := by
      clear ih2
      rw [RegexID.add_concat]
      rw [Vec.cast_concat]
      rw [map_cast]
      rw [<- replace_cast_both]
      rw [<- replace_regexid_add]
      rw [<- replace_take]
      generalize_proofs h1
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
    rw [Vec.cast_concat]
    rw [map_cast]
    rw [<- replace_cast_both]
    rw [<- ih2 ((extract r1 acc).2)]
  | star r1 ih1 =>
    simp only [extract]
    simp only [replace]
    intro n acc hr
    rw [<- ih1 acc]
    simp only [Regex.map]

theorem extract_replace_is_fmap (r: Regex α) (acc: Vec α l) (f: α -> β):
  Regex.map r f = replace (extract r acc).1 (Vec.map (extract r acc).2 f) (by omega) := by
  rw [<- replaceFrom]
  rw [<- extract_replaceFrom_is_fmap]

theorem extractFrom_replaceFrom_is_fmap (r: Regex α) (f: α -> β):
  Regex.map r f = replaceFrom (extractFrom r).1 (Vec.map (extractFrom r).2 f) := by
  simp only [extractFrom]
  simp only [replaceFrom]
  rw [map_cast]
  rw [<- replace_cast_both]
  rw [<- extract_replace_is_fmap r Vec.nil]

theorem Symbol_derive_is_derive'
  {σ: Type} {α: Type} (p: σ -> α -> Bool) (r: Regex σ) (a: α):
  Symbol.derive p r a = Symbol.derive' p r a := by
  unfold Symbol.derive
  unfold Symbol.derive'
  simp only
  rw [Vec.zip_map]

theorem Symbol_derive_is_Regex_derive
  {σ: Type} {α: Type} (p: σ -> α -> Bool) (r: Regex σ) (a: α):
  Symbol.derive p r a = Regex.derive p r a := by
  unfold Symbol.derive
  rw [<- extractFrom_replaceFrom_is_fmap]
  rw [Regex.derive_is_derive2]

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

theorem replacesFrom_cast_both (rs: Vec (RegexID n) l) (ss: Vec σ n) (h: n = m):
  replacesFrom rs ss =
  replacesFrom (RegexID.casts rs h) (Vec.cast ss h) := by
  subst h
  simp only [Vec.cast_rfl]
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

theorem nums_map (rs: Vec (Regex α) l) (f: α -> β):
  nums (Regexes.map rs f) = nums rs := by
  simp only [Regexes.map]
  induction rs with
  | nil =>
    simp only [Vec.map]
    rfl
  | @cons l r rs ih =>
    simp only [Vec.map]
    simp only [nums]
    rw [ih]
    rw [num_map]

theorem extract_lift_cast (r: Regex α) (acc: Vec α n) (h1: n + num r = l + num r) (h2: n = l):
  (Vec.cast (extract r acc).2 h1) = (extract r (Vec.cast acc h2)).2 := by
  subst h2
  rfl

theorem extract_lift_cast_1 (r: Regex α) (acc: Vec α n) (h1: n + num r = l + num r) (h2: n = l):
  RegexID.cast (extract r acc).1 h1 = (extract r (Vec.cast acc h2)).1 := by
  subst h2
  rfl

theorem extract_is_fmap_2 (r: Regex α) (acc: Vec α n) (f: α -> β):
  (extract (Regex.map r f) (Vec.map acc f)).2 = Vec.cast (Vec.map (extract r acc).2 f) (by rw [num_map]) := by
  generalize_proofs hr
  fun_induction extract with
  | case1 =>
    apply Vec.eq
    simp only [extract, Regex.map]
    rfl
  | case2 =>
    apply Vec.eq
    simp only [extract, Regex.map]
    rfl
  | case3 =>
    apply Vec.eq
    simp only [extract, Regex.map, num]
    rw [Vec.cast_toList]
    rw [Vec.snoc_map]
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
    simp only [Vec.cast_or]
    rw [ih1']
    have hh: n + num r1 + num (r2.map f) = n + num (r1.map f) + num (r2.map f) := by
      repeat rw [num_map]
    rw [<- extract_lift_cast (h1 := hh)]
    rw [ih2']
    apply Vec.eq
    rw [map_cast]
    repeat rw [Vec.cast_cast]
  | case5 acc r1 r2 er1 acc1 he1 er2 acc2 he2 ih1 ih2 => -- concat
    rename_i n
    simp only [Regex.map] at *
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
    simp only [Vec.cast_concat]
    rw [ih1']
    have hh: n + num r1 + num (r2.map f) = n + num (r1.map f) + num (r2.map f) := by
      repeat rw [num_map]
    rw [<- extract_lift_cast (h1 := hh)]
    rw [ih2']
    apply Vec.eq
    rw [map_cast]
    congr 1
    simp only [Vec.cast_cast]
  | case6 acc r1 er1 acc1 he ih1 => -- star
    simp only [Nat.add_left_cancel_iff, Regex.map, num] at *
    have hacc1 : acc1 = (extract r1 acc).2 := by
      rw [he]
    rw [hacc1]
    rw [<- ih1]
    rfl
    rw [num_map]

theorem extract_is_fmap_1 (r: Regex α) (acc: Vec α n) (f: α -> β):
  (extract (Regex.map r f) (Vec.map acc f)).1 = RegexID.cast (extract r acc).1 (by simp only [num_map]) := by
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
    have hlift := extract_lift_cast_1 (r := r2.map f) (acc := Vec.map (extract r1 acc).2 f) (h2 := hr1) (h1 := hhlift)
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
    simp only [Regex.map_map]
    congr 1
    · simp only [num, Fin.castLE_castLE, Regex.map_map]
    · simp only [num, Fin.castLE_castLE, Regex.map_map]
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
    have hlift := extract_lift_cast_1 (r := r2.map f) (acc := Vec.map (extract r1 acc).2 f) (h2 := hr1) (h1 := hhlift)
    rw [<- hlift]
    rw [ih2']

    simp only [RegexID.add]
    simp only [RegexID.add_concat]
    simp only [RegexID.add_assoc]
    repeat rw [RegexID.cast_is_cast_map]
    unfold RegexID.cast_map
    simp only [Regex.map_map]
    congr 1
    · simp only [num, Fin.castLE_castLE, Regex.map_map]
    · simp only [num, Fin.castLE_castLE, Regex.map_map]
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
    simp only [Regex.map]

theorem extracts_lift_cast (rs: Vec (Regex α) m) (acc: Vec α n) (h1: n + nums rs = l + nums rs) (h2: n = l):
  (Vec.cast (extracts rs acc).2 h1) = (extracts rs (Vec.cast acc h2)).2 := by
  subst h2
  rfl

theorem extracts_fmap2 (rs: Vec (Regex α) l) (acc: Vec α n) (f: α -> β):
  (Vec.map (extracts rs acc).2 f)
  = (Vec.cast (extracts (Regexes.map rs f) (Vec.map acc f)).2 (by
    rw [Nat.add_right_inj]
    apply nums_map
  )) := by
  generalize_proofs h
  induction rs generalizing n acc with
  | nil =>
    apply Vec.eq
    simp only [Vec.toList_map]
    simp only [Regexes.map]
    simp only [extracts, Vec.map]
    rw [Vec.cast_toList]
    rw [Vec.map_toList]
  | @cons l r rs ih =>
    simp only [extracts]
    have h' : n + num r + nums (Regexes.map rs f) = n + num r + nums rs := by
      simp only [nums_map]
    have ih' := ih ((extract r acc).2) h'
    apply Vec.eq
    repeat rw [Vec.toList_cast]
    rw [Vec.map_cast]
    rw [ih']
    repeat rw [Vec.toList_cast]
    simp only [Regexes.map]
    simp only [Vec.map]
    simp only [extracts]
    repeat rw [Vec.toList_cast]
    have hextract := extract_is_fmap_2 (f := f) (r := r) (n := n)
    rw [hextract]
    rw [<- extracts_lift_cast]
    repeat rw [Vec.toList_cast]
    congr 1
    simp only [num_map]

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

theorem extracts_append (acc: Vec α n) (xs: Vec (Regex α) l):
  (extracts xs acc).2 = Vec.cast (Vec.append acc (extracts xs Vec.nil).2) (by omega) := by
  induction xs generalizing acc n with
  | nil =>
    simp only [extracts, Vec.append_nil, Vec.cast_cast]
    rfl
  | @cons l x xs ih =>
    simp only [extracts]
    rw [ih]
    rw [extract_append]
    nth_rewrite 2 [ih]
    rw [Vec.append_cast_r]
    rw [Vec.cast_cast]
    rw [Vec.cast_cast]
    rw [Vec.append_cast_l]
    rw [Vec.cast_cast]
    rw [Vec.append_cast_r]
    rw [Vec.cast_cast]
    rw [Vec.append_assoc_l]
    rw [Vec.cast_cast]

theorem extracts_take (r: Regex α) (acc: Vec α n) (rs: Vec (Regex α) l):
  (Vec.take (n + num r) (extracts rs (extract r acc).2).2)
    = Vec.cast (extract r acc).2 (by omega) := by
  rw [extracts_append]
  rw [Vec.take_lift_cast]
  rw [Vec.take_append]
  rw [Vec.cast_cast]

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

theorem replacesFrom_cons (rs: Vec (RegexID n) l) (xs: Vec σ n):
  replacesFrom (Vec.cons r rs) xs
  = Vec.cons (replaceFrom r xs) (replacesFrom rs xs)
  := by
  simp only [replacesFrom]
  simp only [Vec.map]

theorem RegexID.add_zero:
  (RegexID.add 0 r) = r := by
  simp only [Nat.add_zero, RegexID.add]
  simp_all only [Fin.castLE_refl]
  simp only [Regex.map_id]

theorem replaceFrom_append {r: Regex α} {xs: Vec α (n + num r)} {acc: Vec α n} {ys: Vec α m}:
  replaceFrom (RegexID.add m (extract r acc).1) (Vec.append xs ys)
  = replaceFrom (extract r acc).1 xs := by
  unfold replaceFrom
  rw [← replace_regexid_add (extract r acc).1 (xs.append ys)]
  rw [← replace_take (extract r acc).1 (xs.append ys)]
  rw [Vec.take_append xs ys]
  rw [replace_cast_symbols]

theorem replaceFrom_extracts_cons:
  replaceFrom (RegexID.add (nums rs) (extract r acc).1) (((extract r acc).2.append ((extracts rs Vec.nil).2.cast h)))
  = replaceFrom (extract r acc).1 (extract r acc).2
  := by
  rw [replaceFrom_append]

theorem extracts_replacesFrom_is_id (rs: Vec (Regex α) l) (acc: Vec α n):
  rs = replacesFrom (extracts rs acc).1 (extracts rs acc).2 := by
  induction rs generalizing n acc with
  | nil =>
    apply Vec.eq
    simp only [extracts, replacesFrom]
    simp only [Vec.map_nil]
  | @cons l r rs ih =>
    simp only [extracts]
    rw [Vec.cast_rfl]
    simp only [RegexID.cast_lift_cons]
    rw [<- replacesFrom_cast_both]
    rw [replacesFrom_cons]
    nth_rewrite 1 [extracts_append]
    congr 1
    · rw [<- Vec.append_cast_r (xs := (extract r acc).2) (ys := (extracts rs Vec.nil).2) (h := (by simp only [zero_add]))]
      rw [replaceFrom_extracts_cons]
      rw [<- extract_replaceFrom_is_id]
    · generalize (extract r acc).2 = acc'
      rw [<- ih]

theorem RegexID.casts_casts (xs: Vec (RegexID n1) l) (h12: n1 = n2) (h23: n2 = n3):
  RegexID.casts (RegexID.casts xs h12) h23 = RegexID.casts xs (by omega) := by
  subst h12 h23
  simp only [RegexID.casts_rfl]

theorem nums_map_map:
  nums rs = nums (rs.map fun r => r.map f) := by
  induction rs with
  | nil =>
    simp only [Vec.map]
    rfl
  | @cons l r rs ih =>
    simp only [Vec.map]
    simp only [nums]
    rw [ih]
    rw [num_map]

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

theorem extracts_fmap1 (rs: Vec (Regex α) l) (acc: Vec α n) (f: α -> β):
  (extracts rs acc).1
  = (RegexID.casts (extracts (Regexes.map rs f) (Vec.map acc f)).1 (by simp only [nums_map])) := by
  simp only [Regexes.map]
  generalize_proofs h
  rw [RegexID.casts_symm.mpr]
  induction rs generalizing n acc f with
  | nil =>
    rw [extracts_nil]
    simp only [RegexID.casts]
    simp only [Vec.map_nil]
    simp only [Vec.map]
    rw [extracts_nil]
    simp only [RegexID.casts]
    simp only [Vec.map]
  | @cons l r rs ih =>
    simp only [Vec.map]
    simp only [extracts]
    generalize_proofs h1 h2 h3 h4
    simp only [RegexID.cast_lift_cons]
    rw [Vec.cast_rfl]
    rw [RegexID.casts_casts]
    generalize_proofs h5
    clear h1 h3

    rw [extract_is_fmap_2]
    generalize_proofs h7

    rw [extract_is_fmap_1]
    generalize_proofs h8
    clear h
    simp only [Vec.cast_rfl]
    clear h2

    simp only [<- Vec.map_cast]

    have ih' : n + num (r.map f) + nums (rs.map fun r => r.map f) = n + num (r.map f) + nums rs := by
      simp only [Nat.add_left_cancel_iff]
      rw [<- nums_map_map]
    rw [<- ih (h := ih')]
    clear ih
    generalize_proofs h9
    clear ih'

    rw [RegexID.add_cast_is_castLE]
    generalize_proofs h10
    simp only [RegexID.add_is_castLE]
    generalize_proofs h11

    congr 1
    · simp_all only [Nat.add_left_cancel_iff, add_le_add_iff_left] -- aesop
    · congr 1
      · simp_all only [Nat.add_left_cancel_iff, add_le_add_iff_left] -- aesop
      · congr 1
        · simp_all only [Nat.add_left_cancel_iff, add_le_add_iff_left] -- aesop
        · simp_all only [Nat.add_left_cancel_iff, add_le_add_iff_left, heq_eq_eq] -- aesop
      · simp only [RegexID.casts_is_casts_rw]
        simp only [RegexID.casts_rw]
        simp only [Vec.cast]
        simp_all only [add_le_add_iff_left, heq_eqRec_iff_heq]
        simp_all only
        congr 1
        · simp_all only [Nat.add_left_cancel_iff] -- aesop
        · simp_all only [Nat.add_left_cancel_iff] -- aesop
        · congr 1
          · simp_all only [heq_eqRec_iff_heq, heq_eq_eq] -- aesop
    · simp_all only [Nat.add_left_cancel_iff, add_le_add_iff_left, heq_eq_eq] -- aesop

theorem extracts_replacesFrom_is_fmap (rs: Vec (Regex α) l) (f: α -> β):
  Regexes.map rs f = replacesFrom (extracts rs acc).1 (Vec.map (extracts rs acc).2 f) := by
  rw [extracts_fmap2]
  have hh := extracts_replacesFrom_is_id (rs := Regexes.map rs f) (acc := Vec.map acc f)
  simp_all only
  nth_rewrite 2 [extracts_fmap1]
  rw [<- replacesFrom_cast_both]

theorem extractsFrom_replacesFrom_is_fmap (rs: Vec (Regex α) l) (f: α -> β):
  Regexes.map rs f = replacesFrom (extractsFrom rs).1 (Vec.map (extractsFrom rs).2 f) := by
  simp only [extractsFrom]
  generalize_proofs h
  rw [extracts_replacesFrom_is_fmap (acc := Vec.nil) (f := f)]
  rw [replacesFrom_cast_both (h := h)]
  simp only [map_cast]

theorem Symbol_derives_is_fmap
  {σ: Type} {α: Type} (p: σ -> α -> Bool) (rs: Vec (Regex σ) l) (a: α):
  Symbol.derives p rs a = Vec.map rs (fun r => Symbol.derive p r a) := by
  unfold Symbol.derives
  simp only
  unfold Regex.derives2
  unfold Symbol.derive
  nth_rewrite 2 [<- Vec.map_map]
  nth_rewrite 1 [<- Vec.map_map]
  apply (congrArg (fun xs => Vec.map xs Regex.derive2))
  rw [<- Vec.zip_map]
  -- rewrites under the closure
  simp only [<- extractFrom_replaceFrom_is_fmap]
  rw [<- extractsFrom_replacesFrom_is_fmap]
  unfold Regexes.map
  simp only [Vec.map_map]

theorem Symbol_derives_is_Regex_derives
  {σ: Type} {α: Type} (p: σ -> α -> Bool) (r: Vec (Regex σ) l) (a: α):
  Symbol.derives p r a = Regex.derives p r a := by
  rw [Symbol_derives_is_fmap]
  unfold Symbol.derive
  unfold Regex.derives
  congr
  funext r
  rw [<- extractFrom_replaceFrom_is_fmap]
  rw [Regex.derive_is_derive2]

theorem Symbol_derive_is_derive_preds
  {σ: Type} {α: Type} (ps: {n: Nat} -> Vec σ n -> α -> Vec Bool n) (rs: Vec (Regex σ) l) (a: α)
  (h: ∀ {n': Nat} (xs: Vec σ n') (a: α), ps xs a = Vec.map xs (fun x => (ps (Vec.singleton x) a).head)):
  Symbol.derives (fun s a => (ps (Vec.singleton s) a).head) rs a = Symbol.derives_preds ps rs a := by
  unfold derives
  simp only
  rw [<- h]
  unfold derives_preds
  unfold leave
  unfold enter
  simp only
