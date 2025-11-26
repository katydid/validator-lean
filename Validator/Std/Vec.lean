import Mathlib.Data.Vector.Basic
import Mathlib.Data.Vector.Snoc
import Mathlib.Data.Vector.MapLemmas

namespace Vec

def fromList (xs: List α): List.Vector α (xs.length) :=
  Subtype.mk xs rfl

def singleton (x: α): List.Vector α 1 :=
  List.Vector.cons x List.Vector.nil

def nil: List.Vector α 0 :=
  List.Vector.nil

def zip : List.Vector α n → List.Vector β n → List.Vector (α × β) n
  | ⟨x, _⟩, ⟨y, _⟩ => ⟨List.zipWith (fun x' y' => (x', y')) x y, by simp [*]⟩

theorem toList_take:
  List.take n xs.val = (List.Vector.take n xs).toList := by
  simp only [_root_.List.Vector.toList_take]
  rfl

theorem toList_cons:
  List.cons x xs.val = (List.Vector.cons x xs).toList := by
  simp only [Nat.succ_eq_add_one, _root_.List.Vector.toList_cons, List.cons.injEq, true_and]
  rfl
