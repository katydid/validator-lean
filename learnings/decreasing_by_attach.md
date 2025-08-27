# decreasing_by List.attach

We need to show that each total function terminates.
Usually Lean does this automatically, 
but when Lean fails we have to `termination_by` and `decreasing_by` to prove this manually.

```lean
def derive [DecidableEq α] (x: Expr α) (tree: ParseTree α): Expr α :=
  match x with
  | Expr.emptyset => Expr.emptyset
  | Expr.epsilon => Expr.emptyset
  | Expr.tree labelPred childrenExpr =>
    if Pred.eval labelPred (ParseTree.getLabel tree)
    && Expr.nullable (List.foldl derive childrenExpr (ParseTree.getChildren tree))
    then Expr.epsilon
    else Expr.emptyset
  | Expr.or y z => Expr.or (derive y tree) (derive z tree)
  | Expr.concat y z =>
    if Expr.nullable y
    then Expr.or (Expr.concat (derive y tree) z) (derive z tree)
    else Expr.concat (derive y tree) z
  | Expr.star y => Expr.concat (derive y tree) (Expr.star y)
termination_by (tree, x)
decreasing_by
  · ...
```

This first case we need to prove is:

```lean
⊢ Prod.Lex (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂) (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂) (tree, x) (tree✝, Expr.tree labelPred childrenExpr)
```

We can see this is the case for the tree expression, so we need to show that the size of the tree is decreasing and we do not need to show that the expression is decreasing. For this reason we can `apply Prod.Lex.left`.
This results in:

```lean
α : Type
tree✝ : ParseTree α
labelPred : Pred α
childrenExpr x : Expr α
tree : ParseTree α
⊢ sizeOf tree < sizeOf tree✝
```

The relation between `tree` and `tree✝` has been lost, even if we know that `tree` is a child of `tree✝`, Lean has forgotten this fact.

We can use `List.attach` to remind Lean.
The function maps the list to a list where each element includes a proof that it is an element of the original list.

```lean
def attach (l : List α) : List {x // x ∈ l}
```

We can modify one line of the `derive` function to use `attach`:

```lean
&& Expr.nullable (List.foldl (fun res ⟨y, hy⟩ => derive res y) childrenExpr (ParseTree.getChildren tree).attach)
```

The parameter `hy` is ignored during the execution of the function, but it is used in the termination proof:

```lean
α : Type
tree : ParseTree α
labelPred : Pred α
childrenExpr res : Expr α
y : ParseTree α
hy : y ∈ tree.getChildren
⊢ sizeOf y < sizeOf tree
```

Using the new hypothesis `hy` and the following theorem:

```lean
theorem elem_lt_list [SizeOf α] {xs: List α} (h: x ∈ xs): sizeOf x ≤ sizeOf xs
```

we can prove that `sizeOf y < sizeOf tree`.

## References

* [2024-01-11: Recursive definitions in Lean - Joachim Breitner](https://web.archive.org/web/20250618125453/https://lean-lang.org/blog/2024-1-11-recursive-definitions-in-lean/)
