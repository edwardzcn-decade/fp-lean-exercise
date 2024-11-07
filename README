# Functional Programming in Lean Exercise

[FP-in-Lean Book Repo](https://github.com/leanprover/fp-lean)

[FP-in-Lean Online Book](https://lean-lang.org/functional_programming_in_lean/)

[👉NEXT Theorem-Proving-in-Lean4](https://leanprover.github.io/theorem_proving_in_lean4/)

## About

This repo is basically all my personal programming exercise. It was written on the fly and might not be immediately relevant to you. Apart from the examples and exercises mentioned in FP-in-Lean book, I write many variants of the definitions (with `'` suffix) due to my experience with Coq and attempted to prove them.

## May Potentially Useful Information

- `by simp` **may not work as expected** if Lean 4 release >= `4.3.0`. You can not use `simp` to close the goal although it could be closed in the same way written in the textbook due to the change of simp default.[More explanation in Lean4 community](https://github.com/leanprover/lean4/pull/1888)
  - Close the goal with two other ways: `(by simp (config := {decide := true}))` and `by decide`. This change resets the simp default to match previous versions.