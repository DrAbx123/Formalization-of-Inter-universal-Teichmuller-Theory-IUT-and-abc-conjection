# LeanFormal

This project formalizes the following real-analysis problem in Lean 4:

- `f` is continuous at `0`.
- As `x -> 0` with `x != 0`,
  `(x * f x - exp (2 * sin x) + 1) / (log (1 + x) + log (1 - x)) -> -3`.
- Prove that `f` is differentiable at `0` and compute its derivative.

The machine-checked result is:

```lean
DifferentiableAt Real f 0 ∧ deriv f 0 = 5
```

The stronger theorem `LeanFormal.hasDerivAt_five_of_limit` proves
`HasDerivAt f 5 0` directly. The full proof is in `LeanFormal/Basic.lean`.

## Versions

- Lean: `v4.32.2`, official `leanprover/lean4` release
- Mathlib: `v4.32.2`, official `leanprover-community/mathlib4` release

## Verify

```text
lake build
```
