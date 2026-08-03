/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.Species
import Mathlib.Data.Real.Basic

/-!
Stage 1 interface: the target shape of the implication from IUT III,
Theorem 3.11 to Corollary 3.12.

The structures below do not assert IUT. They isolate the real-valued comparison
that a later formalization must justify from explicit multiradial, hull, and
indeterminacy hypotheses.
-/

namespace Iut.Stage1

/-- Names for the two pilot sides whose comparison is central in Corollary 3.12. -/
inductive PilotSide where
  | q
  | theta
deriving DecidableEq, Repr

/-- A real log-volume value tagged by its pilot side. -/
structure PilotLogVolume where
  side : PilotSide
  value : Real

/-- The bare real inequality appearing in the statement of Corollary 3.12. -/
def Corollary312Inequality (theta q : PilotLogVolume) : Prop :=
  -theta.value >= -q.value

/--
Minimal endpoint package for a Stage 1 comparison.

The field `comparison` is the Corollary-3.12-shaped conclusion itself. Thus
`corollary312_from_stage1_comparison` is only a projection from this endpoint
package, not a source proof of the comparison. Source-facing routes must derive
such a package from descent, hull+det, simultaneous holomorphic expressibility,
input prime-strip links, and allowed indeterminacies.
-/
structure Stage1Comparison where
  theta : PilotLogVolume
  q : PilotLogVolume
  theta_side : theta.side = PilotSide.theta
  q_side : q.side = PilotSide.q
  q_positive : 0 < q.value
  comparison : Corollary312Inequality theta q

/-- Projection of the conclusion stored in a completed endpoint package. -/
theorem corollary312_from_stage1_comparison (data : Stage1Comparison) :
    Corollary312Inequality data.theta data.q :=
  data.comparison

end Iut.Stage1
