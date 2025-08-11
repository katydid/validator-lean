# rw??

`rw??` is a tactic that can be used to search for rewrite rules that are applicable to the goal or any subexpression in the goal.

When invoking the `rw??` tactic the `Lean InfoView` on the right asks that an subexpression is `Shift+click`ed.
It will then print out several possible theorems to apply, by showing what the new goals would be.
Then `click` on the preferred new goals and `rw??` will be replaced with the new `rw` rule.

