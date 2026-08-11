import LeanFormal.IUT.IUTI.InitialTheta.Definition31D0D11FromSource
import LeanFormal.IUT.IUTIII.Theorem311.SourceH1H2Construction
import LeanFormal.IUT.IUTIII.Theorem311.SourceK1K2Construction

/-!
# Theorem 3.11 prerequisite axiom audit

This audit covers the completed source-conditional Definition 3.1 adapter and
the H1/H2/K1/K2 prerequisite boundaries.  The selected endpoints exercise the
dependent prime-strip transports, procession and spoke laws, vertical
inclusion/surjection directions, and Frobenioid realification/comparison
maps.  It does not claim the arithmetic-to-source existence gate or Theorem
3.11 itself.
-/

/-! Definition 3.1 source-conditional serial adapter. -/
#print axioms LeanFormal.IUT.Theorem311Source.Definition31D0D11FromSource.serial_conclusion_is_source_faithful
#print axioms LeanFormal.IUT.Theorem311Source.Definition31D0D11FromSource.d5_image_contains
#print axioms LeanFormal.IUT.Theorem311Source.Definition31D0D11FromSource.d7_finite_local
#print axioms LeanFormal.IUT.Theorem311Source.Definition31D0D11FromSource.d8_derived_naturality

/-! H1/H2 source projection and dependent spoke/procession transport. -/
#print axioms LeanFormal.IUT.Theorem311Source.OriginalInput.dThetaAt_compatibility
#print axioms LeanFormal.IUT.Theorem311Source.OriginalInput.H2SpokePermutation.inverse_comp_fSpoke
#print axioms LeanFormal.IUT.Theorem311Source.OriginalInput.H2SpokePermutation.comp_inverse_dSpoke
#print axioms LeanFormal.IUT.Theorem311Source.OriginalInput.H2FProcession.spoke_inclusion_naturality
#print axioms LeanFormal.IUT.Theorem311Source.OriginalInput.h2_complete_at_stage
#print axioms LeanFormal.IUT.Theorem311Source.OriginalInput.column_procession_spoke_projection
#print axioms LeanFormal.IUT.Theorem311Source.OriginalInput.h1_h2_before_theorem311_output

/-! K1 vertical log-Kummer boundary. -/
#print axioms LeanFormal.IUT.Theorem311Source.k1OfRealization_toSource
#print axioms LeanFormal.IUT.Theorem311Source.K1VerticalBoundary.nonarchimedean_upper
#print axioms LeanFormal.IUT.Theorem311Source.K1VerticalBoundary.archimedean_target_lift
#print axioms LeanFormal.IUT.Theorem311Source.K1VerticalBoundary.labelled_bijective

/-! K2 Frobenioid, realification, and comparison boundary. -/
#print axioms LeanFormal.IUT.Theorem311Source.K2FrobenioidBoundary.mod_realification_degree
#print axioms LeanFormal.IUT.Theorem311Source.K2FrobenioidBoundary.comparison_square
#print axioms LeanFormal.IUT.Theorem311Source.K2FrobenioidBoundary.k1_nonarchimedean_upper
#print axioms LeanFormal.IUT.Theorem311Source.K2FrobenioidBoundary.k1_archimedean_upper
#print axioms LeanFormal.IUT.Theorem311Source.k2FromFields_local
