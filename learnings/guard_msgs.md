# guard_msgs

Testing out code sometimes requires using `#eval`,
but when we run `lake build` this can become noise in the build that we need to manually check.

In some cases we can use `#guard` to overcome this problem.
In others we can use `#guard_msgs`, for example:

```lean
/--
info: 2
-/
#guard_msgs in
#eval (1 + 1)
```

This could have been rewritten using `#guard`:

```lean
#guard
  (1 + 1)
  = 2
```

But we do not have decidable equality or we might be using `IO` and then using `guard_msgs` is another way to automatically check out tests and clean up our build log.

```lean
/--
info: a
-/
#guard_msgs in
#eval IO.println "a"
```
