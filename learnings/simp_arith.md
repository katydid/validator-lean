# simp_arith

`simp +arith` is a tactic that does simplification and includes simplifying arithmetic.
This means you can replace `simp ; omega` with `simp +airth`.
This doesn't seem that useful, but it really shines when you add extra definitions for simp to include.

```lean
def add1 x := x + 1

example: (add1 x) + 1 = add1 1 + x := by
  simp [add1]
  omega

example: (add1 x) + 1 = add1 1 + x := by
  simp +airth [add1]
```

This also works if `add1` was included in the `simp` library:


```lean
@[simp]
def add1' x := x + 1

example: (add1' x) + 1 = add1' 1 + x := by
  simp +arith
```