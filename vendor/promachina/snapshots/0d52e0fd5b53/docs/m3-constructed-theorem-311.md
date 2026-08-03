# Legacy M3 Finite Model

> **Status correction (2026-07-20).** This is a toy model of selected
> combinatorics. It is not a construction or proof of IUT III, Theorem 3.11.
> The paper-level M3 milestone remains open.

## What It Tests

`IUTStage1ConstructedTheorem311.lean` tests finite `ZMod l` translations,
generated quotients, a natural-number preorder, and bijections between finite
discrete coordinate sets. These are useful regression tests for variance,
quotient, and orientation choices.

## Missing Paper Mathematics

The model has no LGP Gaussian log-theta lattice, D-prime-strip processions,
topological modules, integral structures, tensor packets, splitting monoids,
number fields, global/local Frobenioids, normalized log volumes, actual
Ind1/Ind2 actions, vertical Kummer isomorphisms, permutation/bi-coric
poly-isomorphisms, or horizontal automorphism equivariance. IPL, SHE, and APT
are names on finite transport laws, not the algorithms of Remark 3.11.1.

The canonical manifest therefore classifies the Theorem 3.11 packet,
symmetry, vertical log-Kummer, and Hodge-evaluation entries as source
obligations. The clause-level source of truth is
`Iut/SourceTrace/M1M3PaperLedger.lean`.
