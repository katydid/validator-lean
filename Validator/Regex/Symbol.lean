import Validator.Std.Vec

import Validator.Regex.Extract
import Validator.Regex.Map
import Validator.Regex.Num
import Validator.Regex.Pair
import Validator.Regex.Regex
import Validator.Regex.RegexID
import Validator.Regex.Replace

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

def derive {σ: Type} {α: Type} (Φ: σ -> α -> Bool) (r: Regex σ) (a: α): Regex σ :=
  Regex.Pair.derive
    (replaceFrom
      (extractFrom r).1
      (Vec.map
        (extractFrom r).2
        (fun s => (s, Φ s a))
      )
    )

def derive' {σ: Type} {α: Type} (Φ: σ -> α -> Bool) (r: Regex σ) (a: α): Regex σ :=
  let (r', symbols): (RegexID (Symbol.num r) × Vec σ (Symbol.num r)) := extractFrom r
  let pred_results: Vec Bool (Symbol.num r) := Vec.map symbols (fun s => Φ s a)
  let replaces: Vec (σ × Bool) (Symbol.num r) := Vec.zip symbols pred_results
  let replaced: Regex (σ × Bool) := replaceFrom r' replaces
  Regex.Pair.derive replaced

def derives {σ: Type} {α: Type} (Φ: σ -> α -> Bool) (rs: Vec (Regex σ) l) (a: α): Vec (Regex σ) l :=
  let (rs', symbols): (Vec (RegexID (Symbol.nums rs)) l × Vec σ (Symbol.nums rs)) := Symbol.extractsFrom rs
  let pred_results: Vec Bool (Symbol.nums rs) := Vec.map symbols (fun s => Φ s a)
  let replaces: Vec (σ × Bool) (Symbol.nums rs) := Vec.zip symbols pred_results
  let replaced: Vec (Regex (σ × Bool)) l := replacesFrom rs' replaces
  Regex.Pair.derives replaced

def leave
  (rs: Vec (Regex σ) l)
  (ps: Vec Bool (Symbol.nums rs))
  : (Vec (Regex σ) l) :=
  let replaces: Vec (σ × Bool) (Symbol.nums rs) := Vec.zip (Symbol.extractsFrom rs).2 ps
  let replaced: Vec (Regex (σ × Bool)) l := replacesFrom (Symbol.extractsFrom rs).1 replaces
  Regex.Pair.derives replaced

def enter (rs: Vec (Regex σ) l): Vec σ (Symbol.nums rs) :=
  let (_, symbols): (Vec (RegexID (Symbol.nums rs)) l × Vec σ (Symbol.nums rs)) := Symbol.extractsFrom rs
  symbols

-- derives_preds unlike derives takes a predicate that works out the full vector of predicates.
-- This gives the predicate control over the evaluation order of α, for example α is a tree, we can first evaluate the same label, before traversing down.
def derives_preds {σ: Type} {α: Type}
  (ps: {n: Nat} -> Vec σ n -> α -> Vec Bool n) (rs: Vec (Regex σ) l) (a: α): Vec (Regex σ) l :=
  let symbols: Vec σ (Symbol.nums rs) := enter rs
  let pred_results: Vec Bool (Symbol.nums rs) := ps symbols a
  leave rs pred_results

def derives_closures {σ: Type}
  (ps: {n: Nat} -> Vec σ n -> Vec Bool n) (rs: Vec (Regex σ) l): Vec (Regex σ) l :=
  let symbols: Vec σ (Symbol.nums rs) := enter rs
  let pred_results: Vec Bool (Symbol.nums rs) := ps symbols
  leave rs pred_results

def derives_closures' {σ: Type}
  (ps: {n: Nat} -> Vec σ n -> Vec Bool n) (rs: Vec (Regex σ) l): Vec (Regex σ) l :=
  leave rs (ps (enter rs))

def derives_closure {σ: Type}
  (p: σ -> Bool) (rs: Vec (Regex σ) l): Vec (Regex σ) l :=
  let symbols: Vec σ (Symbol.nums rs) := enter rs
  let pred_results: Vec Bool (Symbol.nums rs) := Vec.map symbols p
  leave rs pred_results

def derive_closure {σ: Type}
  (p: σ -> Bool) (r: Regex σ): Regex σ :=
  let symbols: Vec σ (Symbol.nums #vec[r]) := enter #vec[r]
  let pred_results: Vec Bool (Symbol.nums #vec[r]) := Vec.map symbols p
  let res := (leave #vec[r] pred_results)
  match res with
  | Vec.cons res' Vec.nil => res'

def derive_closure' {σ: Type}
  (p: σ -> Bool) (r: Regex σ): Regex σ :=
  Regex.Pair.derive
    (replaceFrom
      (extractFrom r).1
      (Vec.map
        (extractFrom r).2
        (fun s => (s, p s))
      )
    )

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
          (RegexID.add_or (RegexID.add (Symbol.num r2) (extract r1 acc).1))
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
      omega
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
          (RegexID.add_concat (RegexID.add (Symbol.num r2) (extract r1 acc).1))
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
      omega
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
          (RegexID.add_or (RegexID.add (Symbol.num r2) (extract r1 acc).1))
          (Vec.map (Vec.cast_or (extract r2 (extract r1 acc).2).2) f)
          hr
        ) := by
      clear ih2
      rw [RegexID.add_or]
      rw [Vec.cast_or]
      rw [Vec.map_cast]
      rw [<- replace_cast_both]
      rw [<- replace_regexid_add]
      rw [<- replace_take]
      generalize_proofs h1
      rw [extract_take_fmap]
      generalize_proofs h1 h2
      have ih1' := ih1 acc
      nth_rewrite 1 [ih1']
      rw [replace_cast_symbols]
      omega
    rw [<- hh1]
    clear hh1
    clear ih1
    congr
    rw [RegexID.add_or]
    rw [Vec.cast_or]
    rw [Vec.map_cast]
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
          (RegexID.add_concat (RegexID.add (Symbol.num r2) (extract r1 acc).1))
          (Vec.map (Vec.cast_concat (extract r2 (extract r1 acc).2).2) f)
          hr
        ) := by
      clear ih2
      rw [RegexID.add_concat]
      rw [Vec.cast_concat]
      rw [Vec.map_cast]
      rw [<- replace_cast_both]
      rw [<- replace_regexid_add]
      rw [<- replace_take]
      generalize_proofs h1
      rw [extract_take_fmap]
      generalize_proofs h1 h2
      have ih1' := ih1 acc
      nth_rewrite 1 [ih1']
      rw [replace_cast_symbols]
      omega
    rw [<- hh1]
    clear hh1
    clear ih1
    congr
    rw [RegexID.add_concat]
    rw [Vec.cast_concat]
    rw [Vec.map_cast]
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
  rw [Vec.map_cast]
  rw [<- replace_cast_both]
  rw [<- extract_replace_is_fmap r Vec.nil]

theorem Symbol_derive_is_derive'
  {σ: Type} {α: Type} (Φ: σ -> α -> Bool) (r: Regex σ) (a: α):
  Symbol.derive Φ r a = Symbol.derive' Φ r a := by
  unfold Symbol.derive
  unfold Symbol.derive'
  simp only
  rw [Vec.zip_map]

theorem Symbol_derive_is_Regex_derive
  {σ: Type} {α: Type} (Φ: σ -> α -> Bool) (r: Regex σ) (a: α):
  Symbol.derive Φ r a = Regex.derive Φ r a := by
  unfold Symbol.derive
  rw [<- extractFrom_replaceFrom_is_fmap]
  rw [Regex.Pair.derive_is_pair_derive]

theorem replaceFrom_append {r: Regex α} {xs: Vec α (n + Symbol.num r)} {acc: Vec α n} {ys: Vec α m}:
  replaceFrom (RegexID.add m (extract r acc).1) (Vec.append xs ys)
  = replaceFrom (extract r acc).1 xs := by
  unfold replaceFrom
  rw [← replace_regexid_add (extract r acc).1 (xs.append ys)]
  rw [← replace_take (extract r acc).1 (xs.append ys)]
  rw [Vec.take_append xs ys]
  rw [replace_cast_symbols]

theorem replaceFrom_extracts_cons:
  replaceFrom (RegexID.add (Symbol.nums rs) (extract r acc).1) (((extract r acc).2.append ((extracts rs Vec.nil).2.cast h)))
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

theorem extracts_replacesFrom_is_fmap (rs: Vec (Regex α) l) (f: α -> β):
  Regex.maps rs f = replacesFrom (extracts rs acc).1 (Vec.map (extracts rs acc).2 f) := by
  rw [extracts_fmap2]
  have hh := extracts_replacesFrom_is_id (rs := Regex.maps rs f) (acc := Vec.map acc f)
  simp_all only
  nth_rewrite 2 [extracts_fmap1]
  rw [<- replacesFrom_cast_both]

theorem extractsFrom_replacesFrom_is_fmap (rs: Vec (Regex α) l) (f: α -> β):
  Regex.maps rs f = replacesFrom (extractsFrom rs).1 (Vec.map (extractsFrom rs).2 f) := by
  simp only [extractsFrom]
  generalize_proofs h
  rw [extracts_replacesFrom_is_fmap (acc := Vec.nil) (f := f)]
  rw [replacesFrom_cast_both (h := h)]
  simp only [Vec.map_cast]

theorem Symbol_derives_is_fmap
  {σ: Type} {α: Type} (Φ: σ -> α -> Bool) (rs: Vec (Regex σ) l) (a: α):
  Symbol.derives Φ rs a = Vec.map rs (fun r => Symbol.derive Φ r a) := by
  unfold Symbol.derives
  simp only
  unfold Regex.Pair.derives
  unfold Symbol.derive
  nth_rewrite 2 [<- Vec.map_map]
  nth_rewrite 1 [<- Vec.map_map]
  apply (congrArg (fun xs => Vec.map xs Regex.Pair.derive))
  rw [<- Vec.zip_map]
  -- rewrites under the closure
  simp only [<- extractFrom_replaceFrom_is_fmap]
  rw [<- extractsFrom_replacesFrom_is_fmap]
  unfold Regex.maps
  simp only [Vec.map_map]

theorem Symbol_derives_is_Regex_derives
  {σ: Type} {α: Type} (Φ: σ -> α -> Bool)
  (r: Vec (Regex σ) l) (a: α):
  Symbol.derives Φ r a = Regex.map_derive Φ r a := by
  rw [Symbol_derives_is_fmap]
  unfold Symbol.derive
  unfold Regex.map_derive
  congr
  funext r
  rw [<- extractFrom_replaceFrom_is_fmap]
  rw [Regex.Pair.derive_is_pair_derive]

theorem Symbol_derives_is_derives_preds
  {σ: Type} {α: Type} (ps: {n: Nat} -> Vec σ n -> α -> Vec Bool n) (rs: Vec (Regex σ) l) (a: α)
  (h: ∀ {n': Nat} (xs: Vec σ n') (a: α), ps xs a = Vec.map xs (fun x => (ps (#vec[x]) a).head)):
  Symbol.derives (fun s a => (ps #vec[s] a).head) rs a = Symbol.derives_preds ps rs a := by
  unfold derives
  simp only
  rw [<- h]
  unfold derives_preds
  unfold leave
  unfold enter
  simp only

theorem Symbol_derives_preds_is_derives_closures
  {σ: Type} {α: Type} (ps: {n: Nat} -> Vec σ n -> α -> Vec Bool n) (rs: Vec (Regex σ) l) (a: α):
  Symbol.derives_preds ps rs a = Symbol.derives_closures (fun ss => ps ss a) rs := by
  rfl

theorem Symbol_derives_closures_is_derives_preds
  {σ: Type} {α: Type} (ps: {n: Nat} -> Vec σ n -> Vec Bool n) (rs: Vec (Regex σ) l) (a: α):
  Symbol.derives_closures ps rs = Symbol.derives_preds (fun ss _ => ps ss) rs a := by
  rfl

theorem Symbol_derives_closures_nil:
  Symbol.derives_closures ps Vec.nil = Vec.nil := by
  rfl

theorem Symbol_derives_closure_is_derives
  {σ: Type} {α: Type} (p: σ -> Bool) (rs: Vec (Regex σ) l) (a: α):
  Symbol.derives_closure p rs = Symbol.derives (fun s _ => p s) rs a := by
  rfl

theorem Symbol_derives_is_derives_closure
  {σ: Type} {α: Type} (p: σ -> α -> Bool) (rs: Vec (Regex σ) l) (a: α):
  Symbol.derives p rs a = Symbol.derives_closure (fun s => p s a) rs := by
  rfl

theorem Symbol_derive_closure_is_derive
  (p: σ -> Bool) (r: Regex σ) (a: α):
  Symbol.derive_closure' p r = Symbol.derive (fun s _ => p s) r a := by
  rfl

theorem Symbol_derive_is_derive_closure
  (p: σ -> α -> Bool) (r: Regex σ) (a: α):
  Symbol.derive p r a = Symbol.derive_closure' (fun s => p s a) r := by
  rfl
