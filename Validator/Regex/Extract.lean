import Validator.Regex.Num
import Validator.Regex.Regex
import Validator.Regex.RegexID

namespace Regex.Symbol

def extract (r: Regex σ) (acc: Vec σ n): RegexID (n + Symbol.num r) × Vec σ (n + Symbol.num r) :=
  match r with
  | Regex.emptyset => (Regex.emptyset, acc)
  | Regex.emptystr => (Regex.emptystr, acc)
  | Regex.symbol s => (Regex.symbol (Fin.mk n (by
      simp only [Symbol.num]
      omega
    )), Vec.snoc acc s)
  | Regex.or r1 r2 =>
    let (er1, acc1) := extract r1 acc
    let (er2, acc2) := extract r2 acc1
    (Regex.or (RegexID.add_or (RegexID.add (Symbol.num r2) er1)) (RegexID.add_or er2), Vec.cast_or acc2)
  | Regex.concat r1 r2 =>
    let (er1, acc1) := extract r1 acc
    let (er2, acc2) := extract r2 acc1
    (Regex.concat (RegexID.add_concat (RegexID.add (Symbol.num r2) er1)) (RegexID.add_concat er2), Vec.cast_concat acc2)
  | Regex.star r1 =>
    let (er1, acc1) := extract r1 acc
    (Regex.star er1, acc1)

def extractFrom (r: Regex σ): RegexID (Symbol.num r) × Vec σ (Symbol.num r) :=
  match extract r Vec.nil with
  | (r', xs) => (RegexID.cast r' (by omega), Vec.cast xs (by omega))

def extracts (xs: Vec (Regex σ) nregex) (acc: Vec σ nacc):
  (Vec (RegexID (nacc + Symbol.nums xs)) nregex) × (Vec σ (nacc + Symbol.nums xs)) :=
  match xs with
  | Vec.nil =>
    ( Vec.nil, acc )
  | @Vec.cons _ nregex x xs =>
    let (regexid, acc1) := extract x acc
    let (regexids, accs) := extracts xs acc1
    let regexid': RegexID (nacc + Symbol.nums (Vec.cons x xs)) :=
      RegexID.cast (RegexID.add (Symbol.nums xs) regexid) (by rw [<- Symbol.nums_add]; ac_rfl)
    let regexesids' : Vec (RegexID (nacc + Symbol.nums (Vec.cons x xs))) nregex :=
      RegexID.casts regexids (by rw [<- Symbol.nums_add]; ac_rfl)
    let regexidcons: Vec (RegexID (nacc + Symbol.nums (Vec.cons x xs))) (nregex + 1) :=
      Vec.cast (Vec.cons regexid' regexesids') (by simp only)
    let accs' : (Vec σ (nacc + Symbol.nums (Vec.cons x xs))) :=
      Vec.cast accs (by rw [<- Symbol.nums_add]; ac_rfl)
    (regexidcons, accs')

def extractsFrom (xs: Vec (Regex σ) nregex):
  (Vec (RegexID (Symbol.nums xs)) nregex) × (Vec σ (Symbol.nums xs)) :=
  let (xs0, symbols0) := extracts xs Vec.nil
  let symbols': Vec σ (Symbol.nums xs) := Vec.cast symbols0 (by ac_rfl)
  let xs': Vec (RegexID (Symbol.nums xs)) nregex := RegexID.casts xs0 (by ac_rfl)
  (xs', symbols')

theorem extract_append_toList (acc: Vec σ n) (r: Regex σ):
  Vec.toList (extract r acc).2 = Vec.toList (Vec.append acc (extract r Vec.nil).2) := by
  induction r generalizing acc n  with
  | emptyset =>
    simp only [Symbol.num, Nat.add_zero, extract, Vec.append_nil, Vec.cast_toList]
  | emptystr =>
    simp only [Symbol.num, Nat.add_zero, extract, Vec.append_nil, Vec.cast_toList]
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
      (l + Symbol.num r1)
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
    (l + Symbol.num r1)
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
      (l + Symbol.num r1)
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
    (l + Symbol.num r1)
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

theorem extracts_nil (acc: Vec σ nacc):
  extracts (@Vec.nil (Regex σ)) acc = (RegexID.casts Vec.nil (by
    simp only [Symbol.nums_nil]
    rfl
  ), Vec.cast acc (by
    simp only [Symbol.nums_nil]
    simp only [add_zero]
  )) := by
  simp only [extracts]
  rfl

theorem extracts_zero_nil (xs: Vec (Regex σ) 0):
  extracts xs Vec.nil = (Vec.nil (α := RegexID (0 + Symbol.nums xs)), Vec.cast (Vec.nil (α := σ)) (by simp only [Symbol.nums_zero])) := by
  cases xs
  simp only [extracts_nil]
  congr

theorem extract_lift_cast (r: Regex α) (acc: Vec α n) (h1: n + Symbol.num r = l + Symbol.num r) (h2: n = l):
  (Vec.cast (extract r acc).2 h1) = (extract r (Vec.cast acc h2)).2 := by
  subst h2
  rfl

theorem extract_lift_cast_1 (r: Regex α) (acc: Vec α n) (h1: n + Symbol.num r = l + Symbol.num r) (h2: n = l):
  RegexID.cast (extract r acc).1 h1 = (extract r (Vec.cast acc h2)).1 := by
  subst h2
  rfl

theorem extract_is_fmap_2 (r: Regex α) (acc: Vec α n) (f: α -> β):
  (extract (Regex.map r f) (Vec.map acc f)).2 = Vec.cast (Vec.map (extract r acc).2 f) (by rw [Symbol.num_map]) := by
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
    simp only [extract, Regex.map, Symbol.num]
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
    have ih1' := ih1 (by rw [Symbol.num_map])
    clear ih1
    have ih2' := ih2 (by rw [Symbol.num_map])
    clear ih2
    simp only [extract]
    simp only [Vec.cast_or]
    rw [ih1']
    have hh: n + Symbol.num r1 + Symbol.num (r2.map f) = n + Symbol.num (r1.map f) + Symbol.num (r2.map f) := by
      repeat rw [Symbol.num_map]
    rw [<- extract_lift_cast (h1 := hh)]
    rw [ih2']
    apply Vec.eq
    rw [Vec.map_cast]
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
    have ih1' := ih1 (by rw [Symbol.num_map])
    clear ih1
    have ih2' := ih2 (by rw [Symbol.num_map])
    clear ih2
    simp only [extract]
    simp only [Vec.cast_concat]
    rw [ih1']
    have hh: n + Symbol.num r1 + Symbol.num (r2.map f) = n + Symbol.num (r1.map f) + Symbol.num (r2.map f) := by
      repeat rw [Symbol.num_map]
    rw [<- extract_lift_cast (h1 := hh)]
    rw [ih2']
    apply Vec.eq
    rw [Vec.map_cast]
    congr 1
    simp only [Vec.cast_cast]
  | case6 acc r1 er1 acc1 he ih1 => -- star
    simp only [Nat.add_left_cancel_iff, Regex.map, Symbol.num] at *
    have hacc1 : acc1 = (extract r1 acc).2 := by
      rw [he]
    rw [hacc1]
    rw [<- ih1]
    rfl
    rw [Symbol.num_map]

theorem extract_is_fmap_1 (r: Regex α) (acc: Vec α n) (f: α -> β):
  (extract (Regex.map r f) (Vec.map acc f)).1 = RegexID.cast (extract r acc).1 (by simp only [Symbol.num_map]) := by
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

    have hr1: n + Symbol.num r1 = n + Symbol.num (r1.map f) := by
      rw [Symbol.num_map]
    have ih1' := ih1 hr1
    clear ih1
    have hr2: n + Symbol.num r1 + Symbol.num r2 = n + Symbol.num r1 + Symbol.num (r2.map f) := by
      rw [Symbol.num_map]
    have ih2' := ih2 hr2
    clear ih2

    simp only [Regex.map]
    simp only [extract]

    rw [ih1']
    rw [extract_is_fmap_2]
    generalize_proofs
    have hhlift : n + Symbol.num r1 + Symbol.num (r2.map f) = n + Symbol.num (r1.map f) + Symbol.num (r2.map f) := by
      repeat rw [Symbol.num_map]
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
    · simp only [Symbol.num, Fin.castLE_castLE, Regex.map_map]
    · simp only [Symbol.num, Fin.castLE_castLE, Regex.map_map]
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

    have hr1: n + Symbol.num r1 = n + Symbol.num (r1.map f) := by
      rw [Symbol.num_map]
    have ih1' := ih1 hr1
    clear ih1
    have hr2: n + Symbol.num r1 + Symbol.num r2 = n + Symbol.num r1 + Symbol.num (r2.map f) := by
      rw [Symbol.num_map]
    have ih2' := ih2 hr2
    clear ih2

    simp only [Regex.map]
    simp only [extract]

    rw [ih1']
    rw [extract_is_fmap_2]
    generalize_proofs
    have hhlift : n + Symbol.num r1 + Symbol.num (r2.map f) = n + Symbol.num (r1.map f) + Symbol.num (r2.map f) := by
      repeat rw [Symbol.num_map]
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
    · simp only [Symbol.num, Fin.castLE_castLE, Regex.map_map]
    · simp only [Symbol.num, Fin.castLE_castLE, Regex.map_map]
  | case6 acc r1 er1 acc1 he1 ih1 =>
    rename_i n

    have hacc1 : acc1 = (extract r1 acc).2 := by
      rw [he1]
    have her1 : er1 = (extract r1 acc).1 := by
      rw [he1]
    clear he1

    subst_vars

    have hr1: n + Symbol.num r1 = n + Symbol.num (r1.map f) := by
      rw [Symbol.num_map]
    have ih1' := ih1 hr1
    clear ih1

    simp only [Regex.map]
    simp only [extract]

    rw [ih1']
    generalize (extract r1 acc).1 = rid

    repeat rw [RegexID.cast_is_cast_map]
    unfold RegexID.cast_map
    simp only [Regex.map]

theorem extracts_lift_cast (rs: Vec (Regex α) m) (acc: Vec α n) (h1: n + Symbol.nums rs = l + Symbol.nums rs) (h2: n = l):
  (Vec.cast (extracts rs acc).2 h1) = (extracts rs (Vec.cast acc h2)).2 := by
  subst h2
  rfl

theorem extracts_fmap2 (rs: Vec (Regex α) l) (acc: Vec α n) (f: α -> β):
  (Vec.map (extracts rs acc).2 f)
  = (Vec.cast (extracts (Regex.maps rs f) (Vec.map acc f)).2 (by
    rw [Nat.add_right_inj]
    apply Symbol.nums_map
  )) := by
  generalize_proofs h
  induction rs generalizing n acc with
  | nil =>
    apply Vec.eq
    simp only [Vec.toList_map]
    simp only [Regex.maps]
    simp only [extracts, Vec.map]
    rw [Vec.cast_toList]
    rw [Vec.map_toList]
  | @cons l r rs ih =>
    simp only [extracts]
    have h' : n + Symbol.num r + Symbol.nums (Regex.maps rs f) = n + Symbol.num r + Symbol.nums rs := by
      simp only [Symbol.nums_map]
    have ih' := ih ((extract r acc).2) h'
    apply Vec.eq
    repeat rw [Vec.toList_cast]
    rw [Vec.map_cast]
    rw [ih']
    repeat rw [Vec.toList_cast]
    simp only [Regex.maps]
    simp only [Vec.map]
    simp only [extracts]
    repeat rw [Vec.toList_cast]
    have hextract := extract_is_fmap_2 (f := f) (r := r) (n := n)
    rw [hextract]
    rw [<- extracts_lift_cast]
    repeat rw [Vec.toList_cast]
    congr 1
    simp only [Symbol.num_map]

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
  (Vec.take (n + Symbol.num r) (extracts rs (extract r acc).2).2)
    = Vec.cast (extract r acc).2 (by omega) := by
  rw [extracts_append]
  rw [Vec.take_lift_cast]
  rw [Vec.take_append]
  rw [Vec.cast_cast]

theorem extracts_fmap1 (rs: Vec (Regex α) l) (acc: Vec α n) (f: α -> β):
  (extracts rs acc).1
  = (RegexID.casts (extracts (Regex.maps rs f) (Vec.map acc f)).1 (by simp only [Symbol.nums_map])) := by
  simp only [Regex.maps]
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

    have ih' : n + Symbol.num (r.map f) + Symbol.nums (rs.map fun r => r.map f) = n + Symbol.num (r.map f) + Symbol.nums rs := by
      simp only [Nat.add_left_cancel_iff]
      rw [<- Symbol.nums_map_map]
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
