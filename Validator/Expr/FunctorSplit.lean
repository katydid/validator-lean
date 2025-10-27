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

@[reducible]
def numSymbols (r: Regex σ): Nat :=
  match r with
  | Regex.emptyset => 0
  | Regex.emptystr => 0
  | Regex.symbol _ => 1
  | Regex.or r1 r2 => numSymbols r1 + numSymbols r2
  | Regex.concat r1 r2 => numSymbols r1 + numSymbols r2
  | Regex.star r1 => numSymbols r1

def Regex.add (y: Nat) (r: Regex (Fin x)): Regex (Fin (x + y)) :=
  Regex.map r (fun s =>
    (Fin.mk s.val (by
      obtain ⟨s, hs⟩ := s
      simp only
      omega
    ))
  )

def add_or_r (r: Regex (Fin (μ + numSymbols r1 + numSymbols r2))): Regex (Fin (μ + numSymbols (Regex.or r1 r2))) := by
  simp only [numSymbols]
  rw [<- Nat.add_assoc]
  exact r

def add_or_l (r: Regex (Fin (μ + numSymbols r1))): Regex (Fin (μ + numSymbols (Regex.or r1 r2))) := by
  simp only [numSymbols]
  apply add_or_r
  apply Regex.add
  exact r

def add_or_vec (v: Vector σ (μ + numSymbols r1 + numSymbols r2)): Vector σ (μ + numSymbols (Regex.or r1 r2)) := by
  simp only [numSymbols]
  rw [<- Nat.add_assoc]
  exact v

def add_concat_r (r: Regex (Fin (μ + numSymbols r1 + numSymbols r2))): Regex (Fin (μ + numSymbols (Regex.concat r1 r2))) := by
  simp only [numSymbols]
  rw [<- Nat.add_assoc]
  exact r

def add_concat_l (r: Regex (Fin (μ + numSymbols r1))): Regex (Fin (μ + numSymbols (Regex.concat r1 r2))) := by
  simp only [numSymbols]
  apply add_concat_r
  apply Regex.add
  exact r

def add_concat_vec (v: Vector σ (μ + numSymbols r1 + numSymbols r2)): Vector σ (μ + numSymbols (Regex.or r1 r2)) := by
  simp only [numSymbols]
  rw [<- Nat.add_assoc]
  exact v

def extractSymbols (r: Regex σ) (res: Vector σ μ): Regex (Fin (μ + numSymbols r)) × Vector σ (μ + numSymbols r) :=
  match r with
  | Regex.emptyset => (Regex.emptyset, res)
  | Regex.emptystr => (Regex.emptystr, res)
  | Regex.symbol s => (Regex.symbol (Fin.mk μ (by
      simp only [numSymbols]
      omega
    )), Vector.push res s)
  | Regex.or r1 r2 =>
    let (er1, res1) := extractSymbols r1 res
    let (er2, res2) := extractSymbols r2 res1
    (Regex.or (add_or_l er1) (add_or_r er2), add_or_vec res2)
  | Regex.concat r1 r2 =>
    let (er1, res1) := extractSymbols r1 res
    let (er2, res2) := extractSymbols r2 res1
    (Regex.concat (add_concat_l er1) (add_concat_r er2), add_concat_vec res2)
  | Regex.star r1 =>
    let (er1, res1) := extractSymbols r1 res
    (Regex.star er1, res1)

-- def extractSymbols {μ: Nat} {σ: Type}
--   (r: Regex σ) (res: Vector σ μ) (n: Nat) (h: n + numSymbols r < μ):
--   Regex (Fin (n + numSymbols r)) × Vector σ μ :=
--   match r with
--   | Regex.emptyset => (Regex.emptyset, res)
--   | Regex.emptystr => (Regex.emptystr, res)
--   | Regex.symbol s => (Regex.symbol
--         (Fin.mk n (by simp only [numSymbols]; omega))
--       , Vector.set res n s
--     )
--   | Regex.or r1 r2 =>
--     let (er1, res1) := extractSymbols r1 res n (by
--       simp only [numSymbols] at h
--       omega
--     )
--     let (er2, res2) := extractSymbols r2 res (n + numSymbols r1) (by
--       simp only [numSymbols] at h
--       omega
--     )
--     let hsize :
--       μ = (min (n + numSymbols r1) μ + (μ - (n + numSymbols r1))) := by
--         simp only [numSymbols] at h
--         omega
--     (Regex.or (add_or_l er1) (add_or_r er2), Vector.cast (Eq.symm hsize)
--       (Vector.append
--         (res1.take (n + numSymbols r1))
--         (res2.drop (n + numSymbols r1))))
--   | Regex.concat r1 r2 =>
--     sorry
--   | Regex.star r1 =>
--     let (er1, res1) := extractSymbols r1 res n (by
--       simp only [numSymbols] at h
--       omega
--     )
--     (Regex.star er1, res1)

def replaceSymbols (r: Regex (Fin μ)) (xs: Vector σ μ): Regex σ :=
  match r with
  | Regex.emptyset => Regex.emptyset
  | Regex.emptystr => Regex.emptystr
  | Regex.symbol s => Regex.symbol (xs.get s)
  | Regex.or r1 r2 =>
    Regex.or (replaceSymbols r1 xs) (replaceSymbols r2 xs)
  | Regex.concat r1 r2 =>
    Regex.concat (replaceSymbols r1 xs) (replaceSymbols r2 xs)
  | Regex.star r1 =>
    Regex.star (replaceSymbols r1 xs)

def replaceSymbols' (r: Regex (Fin μ)) (xs: Vector σ ν) (h: μ <= ν): Regex σ :=
  match r with
  | Regex.emptyset => Regex.emptyset
  | Regex.emptystr => Regex.emptystr
  | Regex.symbol s => Regex.symbol (xs.get (Fin.mk s.val (by
      cases s
      simp only
      omega
    )))
  | Regex.or r1 r2 =>
    Regex.or (replaceSymbols' r1 xs h) (replaceSymbols' r2 xs h)
  | Regex.concat r1 r2 =>
    Regex.concat (replaceSymbols' r1 xs h) (replaceSymbols' r2 xs h)
  | Regex.star r1 =>
    Regex.star (replaceSymbols' r1 xs h)

-- theorem replaceSymbols_append (r: Regex (Fin μ)) (xs: Vector σ μ) (ys: Vector σ ν):
--   replaceSymbols r xs = replaceSymbols r (Vector.append xs ys) := by
--   sorry

theorem Vector.push_get {μ: Nat} {α: Type} (xs: Vector α μ) (x: α):
  Vector.get (Vector.push (α := α) (n := μ) xs x) (Fin.mk μ (by omega)) = x := by
  obtain ⟨⟨xs⟩, hxs⟩ := xs
  simp only [Array.size] at hxs
  simp only [Vector.push, Array.push, Vector.get]
  simp only [List.concat_eq_append, Fin.cast_mk]
  simp only [List.getElem_toArray]
  -- aesop?
  simp only [<- hxs, le_refl, List.getElem_append_right, tsub_self, List.getElem_cons_zero]

theorem Vector.set_get {μ: Nat} {α: Type} (xs: Vector α μ) (n: Nat) (x: α) (h: n < μ):
  Vector.get (Vector.set (α := α) xs n x) (Fin.mk n (by assumption)) = x := by
  obtain ⟨⟨xs⟩, hxs⟩ := xs
  simp only [Array.size] at hxs
  simp only [Vector.get]
  -- aesop?
  rw [<- hxs] at h
  simp only [Vector.set_mk, List.set_toArray, Fin.cast_mk, List.getElem_toArray, List.getElem_set_self]

theorem extract_replace_is_id (r: Regex σ) (res: Vector σ μ) (n: Nat):
  r = replaceSymbols (extractSymbols r res).1 (extractSymbols r res).2 := by
  revert res
  induction r with
  | emptyset =>
    intro res
    simp only [replaceSymbols, extractSymbols]
  | emptystr =>
    intro res
    simp only [replaceSymbols, extractSymbols]
  | symbol s =>
    intro res
    simp only [replaceSymbols, extractSymbols]
    rw [Vector.push_get]
  | or r1 r2 ih1 ih2 =>
    intro res
    simp only [extractSymbols]
    simp only [replaceSymbols]
    have hh1 :
      r1 = (replaceSymbols (add_or_l (extractSymbols r1 res).1) (add_or_vec (extractSymbols r2 (extractSymbols r1 res).2).2)) := by
      rw [add_or_l]
      rw [add_or_r]
      rw [add_or_vec]
      rw [Regex.add]
      simp only [id_eq]
      generalize_proofs hhh1 hhh2 hhh3





      sorry
    rw [<- hh1]
    sorry


  | concat r1 r2 ih1 ih2 =>
    sorry
  | star r1 ih1 =>
    sorry

-- theorem extract_replace_is_id (r: Regex σ) (res: Vector σ μ) (n: Nat) (h: n + numSymbols r < μ):
--   r = replaceSymbols (extractSymbols r res n h).1 (extractSymbols r res n h).2 := by
--   fun_induction extractSymbols
--   case case1 => -- emptyset
--     simp only [replaceSymbols]
--   case case2 => -- emptystr
--     simp only [replaceSymbols]
--   case case3 => -- symbol
--     simp only [replaceSymbols]
--     rw [Vector.set_get]
--   case case4 res n r1 r2 hn er1 res1 h1 er2 res2 h2 hsize ih1 ih2 => -- or
--     simp only
--     simp only [numSymbols] at hn
--     generalize_proofs ihn1 ihn2 at ih1 ih2 h1 h2
--     nth_rewrite 1 [ih1]
--     clear ih1
--     nth_rewrite 1 [ih2]
--     clear ih2

--     have her1 : er1 = (extractSymbols r1 res n ihn1).1 := by rw [h1]
--     have hres1 : res1 = (extractSymbols r1 res n ihn1).2 := by rw [h1]
--     clear h1

--     have her2 : er2 = (extractSymbols r2 res (n + numSymbols r1) ihn2).1 := by rw [h2]
--     have hres2 : res2 = (extractSymbols r2 res (n + numSymbols r1) ihn2).2 := by rw [h2]
--     clear h2

--     simp only [replaceSymbols]

--     rw [her2]
--     clear her2
--     rw [hres2]
--     clear hres2
--     rw [her1]
--     clear her1
--     rw [hres1]
--     clear hres1

--     generalize_proofs ha

--     have hh :
--       (replaceSymbols
--         (extractSymbols r1 res n ihn1).1
--         (extractSymbols r1 res n ihn1).2
--       )
--       = (replaceSymbols (extractSymbols r1 res n ihn1).1
--           (Vector.cast ha
--             (((extractSymbols r1 res n ihn1).2.take (n + numSymbols r1)).append
--             ((extractSymbols r2 res (n + numSymbols r1) ihn2).2.drop (n + numSymbols r1))))) := by
--       aesop




--       sorry
--     rw [<- hh]

--   case case5 => -- concat
--     sorry
--   case case6 => -- star
--     sorry






















-- theorem or3
--   {r1 r2 : Regex σ}
--   {er1 : Regex (Fin (μ + numSymbols r1))}
--   {er2 : Regex (Fin (μ + numSymbols r1 + numSymbols r2))}
--   {res1 : Vector σ (μ + numSymbols r1)}
--   {res2 : Vector σ (μ + numSymbols r1 + numSymbols r2)}
--   (h1: extractSymbols r1 res = (er1, res1))
--   (h2: extractSymbols r2 res1 = (er2, res2))
--   (hp1: Regex (Fin (μ + numSymbols (r1.or r2))) = Regex (Fin (μ + numSymbols r1 + numSymbols r2)))
--   (hp2: Vector σ (μ + numSymbols (r1.or r2)) = Vector σ (μ + numSymbols r1 + numSymbols r2)):
--   replaceSymbols (hp1.mpr (Regex.add (numSymbols r2) er1)) (hp2.mpr res2) = replaceSymbols er1 res1 := by
--   sorry

-- theorem or4
--   {r1 r2 : Regex σ}
--   {er1 : Regex (Fin (μ + numSymbols r1))}
--   {er2 : Regex (Fin (μ + numSymbols r1 + numSymbols r2))}
--   {res1 : Vector σ (μ + numSymbols r1)}
--   {res2 : Vector σ (μ + numSymbols r1 + numSymbols r2)}
--   (h1: extractSymbols r1 res = (er1, res1))
--   (h2: extractSymbols r2 res1 = (er2, res2))
--   (hp1: Regex (Fin (μ + numSymbols (r1.or r2))) = Regex (Fin (μ + numSymbols r1 + numSymbols r2)))
--   (hp2: Vector σ (μ + numSymbols (r1.or r2)) = Vector σ (μ + numSymbols r1 + numSymbols r2)):
--   replaceSymbols (hp1.mpr er2) (hp2.mpr res2) = replaceSymbols er2 res2 := by
--   sorry

-- theorem extract_replace_is_id {r: Regex σ} {res: Vector σ μ}:
--   replaceSymbols (extractSymbols r res).1 (extractSymbols r res).2 = r := by
--   fun_induction extractSymbols
--   case case1 =>
--     -- emptyset
--     simp only [replaceSymbols]
--   case case2 =>
--     -- emptystr
--     simp only [replaceSymbols]
--   case case3 μ res s =>
--     -- symbol
--     simp only [replaceSymbols]
--     rw [Vector.push_get]
--   case case4 μ res r1 r2 er1 res1 h1 er2 res2 h2 ih1 ih2 =>
--     -- or
--     rw [h1] at ih1
--     simp only at ih1
--     rw [h2] at ih2
--     simp only at ih2

--     simp only [add_or_l]
--     simp only [add_or_r]
--     simp only [add_or_vec]
--     simp only [id_eq]
--     generalize_proofs hp1 hp2

--     simp only [replaceSymbols]
--     rw [or3 h1 h2 hp1 hp2]
--     rw [ih1]
--     rw [or4 h1 h2 hp1 hp2]
--     rw [ih2]
--   case case5 μ res r1 r2 er1 res1 h1 er2 res2 h2 ih1 ih2 =>
--     -- concat
--     sorry
--   case case6 μ res r1 er1 res1 h ih1 =>
--     -- star
--     simp only [replaceSymbols]
--     have h1 : (extractSymbols r1 res).1 = er1 := by rw [h]
--     have h2 : (extractSymbols r1 res).2 = res1 := by rw [h]
--     rw [<- h1]
--     rw [<- h2]
--     rw [ih1]
