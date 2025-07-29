# obtain

`obtain` is a tactic much like `have`, but when used for destruction it also clears the original hypothesis, which makes it possible to reuse names.

## destruct

We can use `obtain` as a substitute for Coq's `destruct` tactic.

For example to destruct a conjuction or `And`:

```lean
theorem destruct_and (h: a /\ b): b := by
  obtain ⟨ _, h ⟩ := h
  exact h
```

This can be done instead of using `cases`:

```lean
theorem destruct_and (h: a /\ b): b := by
  cases h with
  | intro a b =>
    exact b
```

`cases` works just like `obtain`, but it creates an indentation for something that only has one posibility for destruction.

Or `have`:

```lean
theorem destruct_and (h: a /\ b): b := by
  have ⟨ _, h' ⟩ := h
  clear h
  exact h'
```

`have` works just like `obtain`, but it doesn't clear the original hypothesis, so you need to clear it up if you don't want a noisy number of hypotheses.