import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
  A source-facing vocabulary layer for IUT III, Theorem 3.11 and Corollary
  3.12.  The records in this file are deliberately small: they name the
  histories, links, indeterminacies, and volume regions without pretending to
  construct the anabelian/Frobenioid objects from a number field.

  This is the boundary we want in a formalization: a later construction can
  fill these records, while the downstream ordered-real lemmas remain reusable.
-/

namespace LeanFormal.IUT

inductive Side
  | theta
  | q
  deriving DecidableEq, Repr

/-- A labelled copy of an arithmetic holomorphic history. -/
structure Copy where
  side : Side
  column : Int
  vertical : Int
  deriving DecidableEq, Repr

/-- The two portions of a prime strip that the Theta-link exposes. -/
structure PrimeStrip where
  owner : Copy
  unitLabel : String
  valueLabel : String

/-- A link is an isomorphism of the exposed portions; ring compatibility is not
  included, because a horizontal Theta-link is not a ring morphism. -/
structure PrimeStripLink (source target : PrimeStrip) where
  unitCompatible : Prop
  valueCompatible : Prop
  sourceToTarget : Prop

/-- A deliberately abstract action group for an indeterminacy. -/
structure Indeterminacy where
  name : String
  actionDescription : String

/-- A possible output region of the multiradial algorithm. -/
structure VolumeRegion where
  signedVolume : Real

/-- The output promised by Theorem 3.11.  `ipl`, `she`, and `apt` are
  obligations, not consequences of this record. -/
structure Theorem311Output where
  index : Type
  region : index -> VolumeRegion
  index_nonempty : Nonempty index
  ind1 : Indeterminacy
  ind2 : Indeterminacy
  ind3 : Indeterminacy
  ipl : Prop
  she : Prop
  apt : Prop

/-- A holomorphic hull records the only order fact used by the final
  Corollary-3.12 calculation. -/
structure HolomorphicHull (output : Theorem311Output) where
  hullSignedVolume : Real
  region_le_hull : ∀ i, (output.region i).signedVolume ≤ hullSignedVolume

/-- A source obligation ledger for the last step.  The fields named `ipl`,
  `she`, and `apt` force a caller to provide the paper's qualitative claims;
  the real inequalities are kept separate and visible. -/
structure Corollary312Evidence where
  qSigned : Real
  thetaSigned : Real
  targetSigned : Real
  q_negative : qSigned < 0
  ipl : Prop
  she : Prop
  apt : Prop
  ipl_evidence : ipl
  she_evidence : she
  apt_evidence : apt
  q_le_target : qSigned ≤ targetSigned
  target_le_theta : targetSigned ≤ thetaSigned

theorem Corollary312Evidence.q_le_theta (e : Corollary312Evidence) :
    e.qSigned ≤ e.thetaSigned :=
  le_trans e.q_le_target e.target_le_theta

theorem Corollary312Evidence.q_positive (e : Corollary312Evidence) :
    0 < -e.qSigned := by
  exact neg_pos.mpr e.q_negative

end LeanFormal.IUT
