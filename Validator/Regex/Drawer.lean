import Validator.Regex.Extract
import Validator.Regex.Replace

-- In Map.lean we have defined a map function over a regular expression:

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

-- In this file we prove that if we split function application of the functor up into three steps:
-- 1. extract
-- 2. apply function
-- 3. replace
-- it is the same as Regex.map

-- Also if we have a Vector of regexes, then we can split up the maps function into three steps:
-- 1. extracts
-- 2. map function
-- 3. replaces

-- We have proved functor properties:
-- * r = replaceFrom (extractFrom r).1 (extractFrom r).2
-- * Regex.map r f = replaceFrom (extractFrom r).1 (Vec.map (extractFrom r).2 f)
-- * rs = replacesFrom (extracts rs acc).1 (extracts rs acc).2
-- * Regex.maps rs f = replacesFrom (extractsFrom rs).1 (Vec.map (extractsFrom rs).2 f)

namespace Symbol

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
  r = replace (extract r acc).1 (extract r acc).2 (by omega) := by
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
      rw [replaceFrom_append]
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
