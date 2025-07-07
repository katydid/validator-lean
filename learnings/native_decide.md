# native_decide

[native_decide](https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference/#native_decide) is a tactic that is useful to evaluate examples in such a way that the compiler can that nothing changed.
In this repo we native_decide to effectively create unit tests as examples.

```lean
example : (List.range 1000).length = 1000 := by native_decide
```

> native_decide is a synonym for decide +native. It will attempt to prove a goal of type p by synthesizing an instance of Decidable p and then evaluating it to isTrue ... Unlike decide, this uses #eval to evaluate the decidability instance. This should be used with care because it adds the entire lean compiler to the trusted part, and the axiom Lean.ofReduceBool will show up in #print axioms for theorems using this method or anything that transitively depends on them. Nevertheless, because it is compiled, this can be significantly more efficient than using decide, and for very large computations this is one way to run external programs and trust the result. - https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference/#native_decide

## Failed to Synthesize Decidable

This can work out of the box, but when it doesn't the problem is usually that `native_decide` for equality requires instances of `DecidableEq`, which it cannot infer.

If this is the case you the error is usually:
```
failed to synthesize
  Decidable
```

If the result type of your unit test is your a type your declared yourself, then you can add `deriving DecidableEq` to your type, for example:
```lean
inductive ParseError where
  | unknown (desc: String)
  deriving DecidableEq
```

If not, then you will need to create an instance for it.

Here is an example of `Except`, provided by [Brandon Rozek](https://fosstodon.org/@brozek).

```lean
-- Thank you Brandon Rozek - https://brandonrozek.com/blog/writing-unit-tests-lean-4/
instance [DecidableEq α] [DecidableEq β] : DecidableEq (Except α β) := by
  unfold DecidableEq
  intro a b
  cases a <;> cases b <;>
  -- Get rid of obvious cases where .ok != .err
  try { apply isFalse ; intro h ; injection h }
  case error.error c d =>
    match decEq c d with
      | isTrue h => apply isTrue (by rw [h])
      | isFalse _ => apply isFalse (by intro h; injection h; contradiction)
  case ok.ok c d =>
    match decEq c d with
      | isTrue h => apply isTrue (by rw [h])
      | isFalse _ => apply isFalse (by intro h; injection h; contradiction)
```
