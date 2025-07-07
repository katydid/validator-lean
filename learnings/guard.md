# guard

`#guard` is a command that can be used to write unit tests, instead of using `#eval` and checking results manually.
The eval command will print the result of its expression, which will create a noisy compile step and you will have to check it manually.

```lean
#eval "hello"
```

The guard command will automatically check that the result matches your expected output and a compiler error will be generated if it fails.

```lean
#guard "hello" = "hello"
```

See [Writing Unit Tests in Lean 4 by Brandon Rozek](https://brandonrozek.com/blog/writing-unit-tests-lean-4/)

## How to fix errors

You might get an error, for example:
```
has type
  Prop : Type
but is expected to have type
  Bool : Type
```

In this case, `#guard` is failing to infer the `Decidable` instance for equality.
See the "Failed to Synthesize Decidable" section in [native_decide](./native_decide.md) on how to create an instance of `Decidable` for your type or a type that is out of your control.