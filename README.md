# Unfinished 100% AI LeanFormal IUT audit project

This repository is a source-oriented, auditable Lean 4 project for the
bottom-up study of Mochizuki's IUT I--IV papers and the ABC bridge.  The
production entry point is `LeanFormal/IUT/Project.lean`; the root library
`LeanFormal.lean` imports that entry point only.

The ordinary arithmetic, theta-kernel, labelled-coordinate, and weighted-volume
foundations use Mathlib directly.  IUT-specific constructions are separated
from interfaces and marked obligations.  The Theorem 3.11 -> Corollary 3.12
Step XI contract is intentionally the remaining `sorry` boundary; no claim is
made that IUT or ABC has been proved.

The source corpus and citation/dependency map are under
`papers/motizuki_corpus/`.  The per-module status and exact verification
history are maintained in `AUDIT_LEDGER.md`.

The previous independent real-analysis exercise is retained, but quarantined
at `LeanFormal/Archive/AnalysisExercise/Basic.lean` and is not part of the IUT
production entry point.

## Versions

- Lean: `v4.32.2`
- Mathlib: `v4.32.2`

## Verify

```text
lake build LeanFormal
lake env lean verification/abc_without_sorry.lean
lake env lean verification/abc_with_sorry.lean
powershell -File tools/check_axiom_boundary_logged.ps1
powershell -File tools/check_no_custom_axioms.ps1
```

# If it've benefited your project, I'll more than excited.
# It's paused cause the ability of the AI is far more than enough to achieve the goal