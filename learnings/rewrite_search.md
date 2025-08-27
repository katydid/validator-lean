# rw??

`rw??` is a tactic that can be used to search for rewrite rules that are applicable to the goal or any subexpression in the goal.

When invoking the `rw??` tactic the Lean InfoView on the right asks that an subexpression is `Shift+click`ed.
It will then print out several possible theorems to apply, by showing what the new goals would be.
Then `click` on the preferred new goals and `rw??` will be replaced with the new `rw` rule.

For example

```lean
import Mathlib.Tactic.RewriteSearch

theorem elem_lt_list [SizeOf α] {xs: List α} (h: x ∈ xs): sizeOf x ≤ sizeOf xs := by
  rw??
```

If we then `Shift+click` on the `∈` in `h`, so that the whole hypothesis is highlighted,
we would get the following Rewrite Suggestions:

```
* List.Mem x xs
* ∃ n, xs.get n = x
...
```

If we then click on `List.Mem x xs` in the Lean InfoView, it:
* replaces `rw??` with `rw [show (x ∈ xs) = List.Mem x xs from rfl] at h` and
* our hypothesis `h: x ∈ xs` is updated to `h : List.Mem x xs`.

This doesn't always result in great suggestions, but it is usually worth a try.