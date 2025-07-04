# validator-lean


### Setup

  - Lean4 has exceptional [instructions for installing Lean4 in VS Code](https://github.com/leanprover/lean4/blob/master/doc/quickstart.md).
  - Remember to also add `lake` (the build system for lean) to your `PATH`.  You can do this on mac by adding `export PATH=~/.elan/bin/:${PATH}` to your  `~/.zshrc` file
  - Use mathlib's cache to speed up building time by running: `$ lake exe cache get`