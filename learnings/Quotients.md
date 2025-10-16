# Quotients

> Set-theoretically, Quotient `s` can seen as the set of equivalence classes of `α` modulo the Setoid instance's relation `s`.

We will explain Quotients with the example of slices.

## Slice

A Slice is a list with an offset and length.

```lean
structure Slice (α: Type) where
  data: List α
  off: Nat
  len: Nat
```

A LawfulSlice is a Slice where the offset plus the length does not go out of the bounds of the list.

```lean
def LawfulSlice (α: Type) := { s: Slice α // s.off + s.len <= s.data.length }
```

We can can create a LawfulSlice given all 4 parameters:

```lean
def LawfulSlice.mk (data: List α) (off: Nat) (len: Nat) (p: off + len <= data.length): LawfulSlice α :=
  Subtype.mk (Slice.mk data off len) p
```

We can also create a LawfulSlice from a whole list:

```lean
def LawfulSlice.fromList (xs: List α): LawfulSlice α :=
  Subtype.mk (Slice.mk xs 0 xs.length) (by
    simp only [zero_add, le_refl]
  )
```

Other helper methods include:

```lean
def LawfulSlice.isEmpty (s: LawfulSlice α): Bool :=
  s.val.len = 0

def LawfulSlice.toList (s: LawfulSlice α): List α :=
  List.take s.val.len (List.drop s.val.off s.val.data)

def LawfulSlice.data (s: LawfulSlice α): List α :=
  s.val.data

def LawfulSlice.length (s: LawfulSlice α): Nat :=
  s.val.len

def LawfulSlice.offset (s: LawfulSlice α): Nat :=
  s.val.off

def LawfulSlice.bounds {α} (s: LawfulSlice α): s.offset + s.length <= s.data.length :=
  s.property

def LawfulSlice.nonEmpty {α: Type} (s: LawfulSlice α): Option {s': LawfulSlice α // s'.length > 0} :=
  match h: s.val.len with
  | 0 => Option.none
  | l + 1 => Option.some (Subtype.mk s (by
    simp only [length, gt_iff_lt]
    omega
  ))
```

The `LawfulSlice.nonEmpty` helper method, either returns `none` or a `LawfulSlice` that has a length greater than 0.
This allows us to check wether the list is empty or not and have the property that the list is non empty, which is useful for termination proofs.

The `LawfulSlice` includes functions that allows us to slice the input the list:

```lean
def LawfulSlice.take (n: Nat) (s: LawfulSlice α): LawfulSlice α :=
  LawfulSlice.mk s.data s.offset (min n s.length) (by
    rw [show min n s.length = if n ≤ s.length then n else s.length from rfl]
    obtain ⟨⟨d, o, l⟩, hs⟩ := s
    simp only at hs
    simp only [offset, length, data]
    split_ifs
    case pos h =>
      omega
    case neg h =>
      exact hs
  )

def LawfulSlice.drop (n: Nat) (s: LawfulSlice α): LawfulSlice α :=
  LawfulSlice.mk s.data (min (s.offset + n) (s.offset + s.length)) (s.length - n) (by
    obtain ⟨⟨ data, offset, len⟩, prop⟩ := s
    simp only at prop
    simp only [LawfulSlice.offset, length, Nat.add_min_add_left, LawfulSlice.data]
    rw [Nat.min_def]
    split_ifs
    case pos h =>
      omega
    case neg h =>
      omega
  )
```

We prove that these functions work the same as `List.take` and `List.drop` respectively:

```lean
theorem LawfulSlice.take_is_List.take {xs: List α}:
  (LawfulSlice.take n (LawfulSlice.fromList xs)).toList = List.take n xs := by
  simp only [toList, LawfulSlice.take, mk, data, fromList, offset, length, List.drop_zero,
    List.take_eq_take_iff, inf_le_right, inf_of_le_left]

theorem LawfulSlice.drop_is_List.drop {xs: List α}:
  (LawfulSlice.drop n (LawfulSlice.fromList xs)).toList = List.drop n xs := by
  simp only [toList, LawfulSlice.drop, mk, data, fromList, offset, zero_add, length]
  rw [Nat.nat_min]
  split_ifs
  case pos h =>
    rw [List.take_eq_self_iff]
    rw [List.length_drop]
  case neg h =>
    simp only [List.drop_length, List.take_nil, List.nil_eq, List.drop_eq_nil_iff]
    omega
```

Now that we can create and manipulate a `LawfulSlice` we can create an equivalence class.

## Equivalence Class

An equivalence class is a set of items that are equivalent.

> Let α be any type, and let r be an equivalence relation on α. It is mathematically common to form the "quotient" α / r, that is, the type of elements of α "modulo" r. Set theoretically, one can view α / r as the set of equivalence classes of α modulo r. 

In our example α is (x: LawfulSlice α) and r is:

```lean
abbrev eqv {α: Type} (s1 s2 : LawfulSlice α) : Prop :=
  s1.toList = s2.toList

infix:50 " ~ " => eqv
```

, which means that α / r is `x.toList`, which is also expressed as ⟦x⟧ when we implement the Quotient type later.

Different slices can be equivalent, even though underlying the structures are not equal.
For example

```lean
example:
  LawfulSlice.fromList [1,2,3] ~ (LawfulSlice.fromList [1,2,3,4]).take 3 := by
  unfold eqv
  rw [LawfulSlice.take_is_List.take]
  simp only [LawfulSlice.toList, LawfulSlice.fromList, List.length_cons, List.length_nil, zero_add,
    Nat.reduceAdd, List.drop_zero, List.take_succ_cons, List.take_nil, List.take_zero]
```

We can implement Equivalence for our relation:

```lean
private lemma eqv.refl {α: Type} (s : LawfulSlice α) : s ~ s := rfl

private lemma eqv.symm {α: Type} : ∀ {s1 s2 : LawfulSlice α},
  s1 ~ s2 → s2 ~ s1 := by
  intro r1 r2 h
  unfold eqv at *
  rw [h]

private lemma eqv.trans {α: Type} : ∀ {s1 s2 s3 : LawfulSlice α}, s1 ~ s2 → s2 ~ s3 → s1 ~ s3 := by
  unfold eqv
  intro s1 s2 s3 s1s2 s2s3
  rw [s1s2, s2s3]

instance IsEquivalence_LawfulSlice {α: Type} : Equivalence (@eqv α) :=
  { refl := eqv.refl, symm := eqv.symm, trans := eqv.trans }
```

## Setoid

> Quotient types are built on setoids. A setoid is a type paired with a distinguished equivalence relation. Unlike a quotient type, the abstraction barrier is not enforced, and proof automation designed around equality cannot be used with the setoid's equivalence relation. Setoids are useful on their own, in addition to being a building block for quotient types.

We can implement a Setoid for our relation:

```lean
instance IsSetoid_LawfulSlice (α: Type): Setoid (LawfulSlice α) where
   r     := eqv
   iseqv := IsEquivalence_LawfulSlice
```

HasEquiv is the typeclass which supports the notation `x ≈ y`.
All Setoids are automatically also instances of HasEquiv:

```lean
instance {α : Sort u} [Setoid α] : HasEquiv α :=
   ⟨Setoid.r⟩
```

This means we can use the syntax `x ≈ y` for our relation:

```lean
theorem LawfulSlice.refl {α: Type} (a : LawfulSlice α) : a ≈ a :=
  IsEquivalence_LawfulSlice.refl a

theorem LawfulSlice.symm {α: Type} {a b : LawfulSlice α} (hab : a ≈ b) : b ≈ a :=
  IsEquivalence_LawfulSlice.symm hab

theorem LawfulSlice.trans {α: Type} {a b c : LawfulSlice α} (hab : a ≈ b) (hbc : b ≈ c) : a ≈ c :=
  IsEquivalence_LawfulSlice.trans hab hbc
```

## Quotient

We define a Quotient Type for our LawfulSlice:

```lean
def LawfulSliceQ (α: Type): Type :=
  Quotient (IsSetoid_LawfulSlice α)
```

## Quotient.mk

We can now define our quotient constructor using our Setoid implementation:

```lean
def LawfulSliceQ.fromLawfulSlice' {α: Type} (x: LawfulSlice α): LawfulSliceQ α  :=
  Quot.mk Setoid.r x
```

We can also use the specialized version of `Quot`, called `Quotient` to do define the equivalent function:

```lean
def LawfulSliceQ.fromLawfulSlice {α: Type} (x: LawfulSlice α): LawfulSliceQ α :=
  Quotient.mk' x
```

We can also create other constructors, like:

```lean
def LawfulSliceQ.fromList {α: Type} (data: List α): LawfulSliceQ α :=
  Quotient.mk' (LawfulSlice.fromList data)
```

Here the specific Setoid is infered.

This `Quotient.mk' x` also introduces notation `⟦x⟧`.

```lean
⟦x⟧ = Quotient.mk' x = Quot.mk Setoid.r x = LawfulSliceQ.fromLawfulSlice x
```

## Quotient.lift

> If f : α → β is any function that respects the equivalence relation in the sense that for every x y : α, r x y implies f x = f y, then f "lifts" to a function f' : α / r → β defined on each equivalence class ⟦x⟧ by f' ⟦x⟧ = f x. Lean's standard library extends the Calculus of Constructions with additional constants that perform exactly these constructions, and installs this last equation as a definitional reduction rule.

```lean
axiom Quot.lift :
    {α : Sort u} → {r : α → α → Prop} → {β : Sort u} → (f : α → β)
    → (∀ a b, r a b → f a = f b) → Quot r → β

protected abbrev lift
    {α : Sort u} {β : Sort v} {s : Setoid α} (f : α → β) :
    ((a b : α) → a ≈ b → f a = f b) → Quotient s → β :=
  Quot.lift f
```

If we substitute our LawfulSlice we get:

```lean
axiom Quot.lift :
    {α : Type} → {eqv : LawfulSlice α → LawfulSlice α → Prop} → {β : Sort u} → (f : LawfulSlice α → β)
    → (∀ a b: LawfulSlice α, r a b → f a = f b) → LawfulSliceQ α → β
```

We have to decide what a useful β will be, but we can't move out of our equivalence relation, otherwise `(∀ a b: LawfulSlice α, r a b → f a = f b)` would not be True.
For example β cannot be LawfulSlice α, since then we lose denote and that would be outside of the equivalence relation.

We can however make β, Bool and lift isEmpty.
In this example `f = (fun x => LawfulSlice.isEmpty x))`:

```lean
theorem LawfulSlice.isEmpty_respects_eqv {α: Type}:
  ∀ (x y: LawfulSlice α), x ~ y ->
    (LawfulSlice.isEmpty x) = (LawfulSlice.isEmpty y) := by
  intro x y
  intro h
  unfold LawfulSlice.isEmpty
  unfold eqv at h
  obtain ⟨⟨xd, xo, xl⟩, xp⟩ := x
  obtain ⟨⟨yd, yo, yl⟩, yp⟩ := y
  simp only [toList] at h
  simp only [decide_eq_decide]
  apply Iff.intro
  case mp =>
    intro hxl
    subst_vars
    simp only [add_zero] at xp
    simp only at yp
    simp only [List.take_zero, List.nil_eq, List.take_eq_nil_iff, List.drop_eq_nil_iff] at h
    cases h
    · omega
    · omega
  case mpr =>
    intro hyl
    subst_vars
    simp only at xp
    simp only [add_zero] at yp
    simp only [List.take_zero, List.take_eq_nil_iff, List.drop_eq_nil_iff] at h
    omega

def LawfulSliceQ.isEmpty {α: Type} (s: LawfulSliceQ α): Bool :=
  Quotient.lift LawfulSlice.isEmpty LawfulSlice.isEmpty_respects_eqv s
```

We can also choose β to be Nat, for length:

```lean
theorem List.eq_slice_eq_length
  {xo xl: Nat} {xd: List α} (hx : xo + xl ≤ xd.length)
  {yo yl: Nat} {yd: List α} (hy : yo + yl ≤ yd.length)
  (h : List.take xl (List.drop xo xd) = List.take yl (List.drop yo yd)):
  xl = yl := by
  rw [← List.Sublist.length_eq (by rw [h])] at h
  simp only [length_take, length_drop] at h
  rw [Nat.min_def] at h
  rw [Nat.min_def] at h
  rw [← Nat.le_sub_iff_add_le' (by omega)] at hx
  rw [← Nat.le_sub_iff_add_le' (by omega)] at hy
  split_ifs at h
  assumption

theorem LawfulSlice.length_respects_eqv {α: Type}:
  ∀ (x y: LawfulSlice α), x ~ y ->
    (LawfulSlice.length x) = (LawfulSlice.length y) := by
  intro x y
  intro h
  unfold LawfulSlice.length
  unfold eqv at h
  obtain ⟨⟨xd, xo, xl⟩, xp⟩ := x
  obtain ⟨⟨yd, yo, yl⟩, yp⟩ := y
  simp only [toList] at xp yp h
  simp only
  apply @List.eq_slice_eq_length α xo xl xd xp yo yl yd yp h

def LawfulSliceQ.length {α: Type} (s: LawfulSliceQ α): Nat :=
  Quotient.lift LawfulSlice.length LawfulSlice.length_respects_eqv s
```

We can also choose β to be `LawfulSliceQ α`, so we can define the main operations of a slice:
```lean
def LawfulSliceQ.take {α: Type} (n: Nat) (s: LawfulSliceQ α): LawfulSliceQ α
def LawfulSliceQ.drop {α: Type} (n: Nat) (s: LawfulSliceQ α): LawfulSliceQ α
```

The `take` and `drop` functions for LawfulSliceQ, is defined using the following helper proofs:

```lean
theorem List.take_min_eq_take_take:
  List.take (min a b) xs = List.take a (List.take b xs) := by
  rw [Nat.min_def]
  fun_induction List.take generalizing a
  case case1 =>
    simp only [nonpos_iff_eq_zero, take_nil, take_eq_nil_iff, ite_eq_right_iff, imp_self, true_or]
  case case2 =>
    simp only [Nat.succ_eq_add_one, take_nil]
  case case3 b x xs ih =>
    cases a with
    | zero =>
      simp only [Nat.succ_eq_add_one, le_add_iff_nonneg_left, zero_le, ↓reduceIte, take_zero]
    | succ a =>
      simp only [Nat.succ_eq_add_one, add_le_add_iff_right, take_succ_cons]
      rw [<- ih]
      rw [← ite_add (a ≤ b) a b 1]
      simp only [take_succ_cons]

theorem List.take_respects_eqv
  (h: List.take xl (List.drop xo data) = List.take yl (List.drop yo data)):
  List.take (min n xl) (List.drop xo data) = List.take (min n yl) (List.drop yo data) := by
  rw [List.take_min_eq_take_take]
  rw [List.take_min_eq_take_take]
  rw [h]

theorem LawfulSlice.take_respects_eqv {α: Type} (n: Nat):
  ∀ (x y: LawfulSlice α), x ~ y ->
    (LawfulSlice.take n x) ~ (LawfulSlice.take n y) := by
  unfold eqv
  intro x y
  obtain ⟨⟨xd, xo, xl⟩, xp⟩ := x
  obtain ⟨⟨yd, yo, yl⟩, yp⟩ := y
  simp only [LawfulSlice.take]
  simp only [toList, mk, data, offset, length]
  simp only at xp
  simp only at yp
  intro hxy
  have h' := @List.eq_slice_eq_length α xo xl xd xp yo yl yd yp hxy
  subst_vars
  rw [List.take_min_eq_take_take]
  rw [List.take_min_eq_take_take]
  rw [hxy]

theorem LawfulSliceQ.take_respects_eqv {α: Type} (n: Nat):
  ∀ (x y: LawfulSlice α), x ~ y ->
    (Quotient.mk' (LawfulSlice.take n x)) = (Quotient.mk' (LawfulSlice.take n y)) := by
  simp only [Quotient.eq']
  simp only [IsSetoid_LawfulSlice]
  apply LawfulSlice.take_respects_eqv

def LawfulSliceQ.take {α: Type} (n: Nat) (s: LawfulSliceQ α): LawfulSliceQ α :=
  Quotient.lift (fun xs => (Quotient.mk' (LawfulSlice.take n xs))) (LawfulSliceQ.take_respects_eqv n) s

theorem min_sub_is_pos (n m: Nat):
  (min n m + (m - n)) = m := by
  rw [Nat.min_def]
  split_ifs
  case pos =>
    omega
  case neg =>
    omega

theorem List.drop_respects_eqv
  (hx : xo + xl ≤ data.length)
  (hy : yo + yl ≤ data.length)
  (h: List.take xl (List.drop xo data) = List.take yl (List.drop yo data)):
  List.take (xl - n) (List.drop (min (xo + n) (xo + xl)) data) =
    List.take (yl - n) (List.drop (min (yo + n) (yo + yl)) data) := by
  rw [Nat.add_min_add_left]
  rw [Nat.add_min_add_left]
  rw [<- List.drop_drop]
  rw [<- List.drop_drop]
  rw [take_drop]
  rw [min_sub_is_pos]
  nth_rewrite 2 [take_drop]
  rw [min_sub_is_pos]
  rw [h]
  have hl := List.eq_slice_eq_length hx hy h
  rw [hl]

theorem LawfulSlice.drop_respects_eqv {α: Type} (n: Nat):
  ∀ (x y: LawfulSlice α), x ~ y ->
    (LawfulSlice.drop n x) ~ (LawfulSlice.drop n y) := by
  unfold eqv
  intro x y
  obtain ⟨⟨xd, xo, xl⟩, xp⟩ := x
  obtain ⟨⟨yd, yo, yl⟩, yp⟩ := y
  simp only [LawfulSlice.drop]
  simp only [toList, mk, data, offset, length, Nat.add_min_add_left]
  simp only at xp
  simp only at yp
  intro hxy
  have h' := @List.eq_slice_eq_length α xo xl xd xp yo yl yd yp hxy
  subst_vars
  rw [← List.drop_drop]
  rw [← List.drop_drop]
  rw [List.take_drop]
  nth_rewrite 2 [List.take_drop]
  nth_rw 2 [min_sub_is_pos n yl]
  nth_rw 1 [min_sub_is_pos n yl]
  rw [hxy]

theorem LawfulSliceQ.drop_respects_eqv {α: Type} (n: Nat):
  ∀ (x y: LawfulSlice α), x ~ y ->
    (Quotient.mk' (LawfulSlice.drop n x)) = (Quotient.mk' (LawfulSlice.drop n y)) := by
  simp only [Quotient.eq']
  simp only [IsSetoid_LawfulSlice]
  apply LawfulSlice.drop_respects_eqv

def LawfulSliceQ.drop {α: Type} (n: Nat) (s: LawfulSliceQ α): LawfulSliceQ α :=
  (Quotient.lift (fun xs => (Quotient.mk' (LawfulSlice.drop n xs)))) (LawfulSliceQ.drop_respects_eqv n) s

theorem LawfulSliceQ.take_fromList_eq_fromList_take {α: Type} {n: Nat} {xs: List α}:
  (LawfulSliceQ.take n (LawfulSliceQ.fromList xs))
  = (LawfulSliceQ.fromList (List.take n xs)) := by
  unfold LawfulSliceQ.take
  apply Quot.sound
  simp only [LawfulSlice, IsSetoid_LawfulSlice, LawfulSlice.take, LawfulSlice.mk, LawfulSlice.data,
    LawfulSlice.fromList, LawfulSlice.offset, LawfulSlice.length, List.length_take]
  unfold eqv
  simp only [LawfulSlice.toList, List.drop_zero]
  rw [List.take_take]
  rw [Nat.min_right_comm n xs.length n]
  rw [Nat.min_self n]
```

We can also choose β to be RegexQ α.
In this example `f = RegexQ.mkStar`:

```lean
theorem starq_respects_eqv:
  ∀ (x y: Regex α), x ~ y ->
    RegexQ.mkStar x = RegexQ.mkStar y := by
  intro x y
  intro H
  apply Quot.sound
  apply star_respects_eqv
  apply H

def RegexQ.star: (RegexQ α -> RegexQ α) :=
  Quotient.lift RegexQ.mkStar starq_respects_eqv
```

Finally we can try a tougher example of `nonEmpty`

```lean
def LawfulSliceQ.nonEmpty {α: Type} (s: LawfulSliceQ α):
  Option {ys: LawfulSliceQ α // ys.length > 0}
```

This is defined using the following helper functions and theorems:

```lean

theorem LawfulSliceQ.length_respects_eqv {α: Type}:
   ∀ (xs: LawfulSlice α),
    (LawfulSlice.length xs) = (LawfulSliceQ.length (LawfulSliceQ.fromLawfulSlice xs)) := by
  intro xs
  unfold LawfulSliceQ.fromLawfulSlice
  unfold Quotient.mk'
  unfold LawfulSliceQ.length
  simp only [LawfulSlice.length, LawfulSlice, Quotient.lift_mk]

def Quotient.fromOptionSubtype
  (s: Option {ys: LawfulSlice α // ys.length > 0}):
  Option {ys: LawfulSliceQ α // ys.length > 0} :=
  match s with
  | Option.none => Option.none
  | Option.some s => Option.some (
    match s with
    | Subtype.mk ys hys =>
      Subtype.mk (LawfulSliceQ.fromLawfulSlice ys) (by
        simp only at hys
        rw [LawfulSliceQ.length_respects_eqv] at hys
        exact hys
      )
    )

theorem LawfulSliceQ.nonEmpty_respects_eqv {α: Type}:
  ∀ (x y: LawfulSlice α), x ~ y ->
    (Quotient.fromOptionSubtype (LawfulSlice.nonEmpty x)) = (Quotient.fromOptionSubtype (LawfulSlice.nonEmpty y)) := by
  unfold eqv
  simp only [Quotient.fromOptionSubtype]
  intro x y
  intro hxy
  simp only [LawfulSlice.nonEmpty]
  simp only [LawfulSlice, LawfulSlice.length, Nat.succ_eq_add_one, fromLawfulSlice]
  obtain ⟨⟨xd, xo, xl⟩, xp⟩ := x
  obtain ⟨⟨yd, yo, yl⟩, yp⟩ := y
  simp only [LawfulSlice.toList] at hxy
  simp only at yp
  simp only at xp
  have hl := @List.eq_slice_eq_length α xo xl xd xp yo yl yd yp hxy
  subst_vars
  cases yl with
  | zero =>
    simp only
  | succ yl =>
    simp only [Option.some.injEq, Subtype.mk.injEq]
    apply Quot.sound
    simp only [IsSetoid_LawfulSlice, LawfulSlice]
    simp only [eqv, LawfulSlice.toList]
    exact hxy

def LawfulSliceQ.nonEmpty {α: Type} (s: LawfulSliceQ α):
  Option {ys: LawfulSliceQ α // ys.length > 0} :=
  (Quotient.lift (fun xs => (Quotient.fromOptionSubtype (LawfulSlice.nonEmpty xs)))) LawfulSliceQ.nonEmpty_respects_eqv s
```

## References

* [The Lean Language Reference - Quotients](https://lean-lang.org/doc/reference/latest/The-Type-System/Quotients/)
* [Theorem Proving in Lean4 - Axioms and Computation](https://lean-lang.org/theorem_proving_in_lean4/axioms_and_computation.html)
* [Beginner problem: 'Lift' a proposition to a Quotient type](https://leanprover.zulipchat.com/#narrow/channel/113489-new-members/topic/.E2.9C.94.20Beginner.20problem.3A.20'Lift'.20a.20proposition.20to.20a.20Quotient.20type/near/516853703)
* [How to lift a binary function to a quotient?](https://proofassistants.stackexchange.com/questions/2663/how-to-lift-a-binary-function-to-a-quotient)