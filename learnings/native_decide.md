# native_decide

[native_decide](https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference/#native_decide) is a tactic that is useful to evaluate examples in such a way that the compiler can that nothing changed.
In this repo we native_decide to effectively create unit tests as examples.

```lean
example : (List.range 1000).length = 1000 := by native_decide
```