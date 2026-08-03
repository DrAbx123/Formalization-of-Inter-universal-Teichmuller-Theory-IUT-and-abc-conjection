import Iut.Foundations.SourceGluedAnabelioid
import Iut.Foundations.SourceGluedGalois
import Iut.Foundations.SourceAnabelioidSlice
import Iut.Foundations.SourceSemiGraphResidualSeparation

/-!
  Trust-boundary audit for the imported semi-graph-of-anabelioids foundation.
  These declarations cover the pointwise finite-limit and supported finite-
  colimit constructions repaired for Lean/Mathlib 4.32.2, their preservation
  by vertex evaluation, and the resulting pre-Galois structure.
-/

#print axioms Iut.SourceSemiGraphOfAnabelioids.GluedObject.limitCone
#print axioms Iut.SourceSemiGraphOfAnabelioids.GluedObject.limitConeIsLimit
#print axioms Iut.SourceSemiGraphOfAnabelioids.GluedObject.evaluationMapLimitConeIsLimit
#print axioms Iut.SourceSemiGraphOfAnabelioids.GluedObject.evaluationPreservesFiniteLimits
#print axioms Iut.SourceSemiGraphOfAnabelioids.GluedObject.colimitCocone
#print axioms Iut.SourceSemiGraphOfAnabelioids.GluedObject.colimitCoconeIsColimit
#print axioms Iut.SourceSemiGraphOfAnabelioids.GluedObject.evaluationMapColimitCoconeIsColimit
#print axioms Iut.SourceSemiGraphOfAnabelioids.GluedObject.evaluationPreservesFiniteCoproducts
#print axioms Iut.SourceSemiGraphOfAnabelioids.GluedObject.evaluationPreservesFiniteGroupQuotientSmall
#print axioms Iut.SourceSemiGraphOfAnabelioids.GluedObject.preGaloisCategory
#print axioms Iut.SourceSemiGraphOfAnabelioids.GluedObject.complementFiberIsEmptyOfEpi
#print axioms Iut.SourceSemiGraphOfAnabelioids.GluedObject.rootFiberFunctor
#print axioms Iut.SourceSemiGraphOfAnabelioids.GluedObject.galoisCategory

#print axioms Iut.sourceInducedIdentityFiber_first_mem
#print axioms Iut.sourceInducedIdentityFiberToOriginal_original
#print axioms Iut.sourceInducedSliceFiberEvaluation_injective
#print axioms Iut.sourceContinuousAction_comp_apply
#print axioms Iut.sourceOpenCosetSliceEquivalence
#print axioms Iut.sourceSliceProductAdjDependentSection
#print axioms Iut.sourceInductionRestrictionAdjunction
#print axioms Iut.sourceOpenSubgroupFiniteEtaleFactorization

/-! Countable-base and finite-separator kernels ported from
`promachina/iut-lean@36ef280d`. -/

#print axioms Iut.SourceFiniteSheetSemiGraphCover.projection_vertexFiber_finite
#print axioms Iut.SourceFiniteSheetSemiGraphCover.projection_edgeFiber_finite
#print axioms Iut.SourceSemiGraphOfAnabelioids.GluedObject.GaloisLevel.vertex_countable
#print axioms Iut.SourceSemiGraphOfAnabelioids.GluedObject.GaloisLevel.edge_countable
#print axioms Iut.SourceCombinatorialUniversalCover.SourceGaloisCombinatorialUniversalCover.deckGroup_countable
#print axioms Iut.SourceSemiGraphResidualSeparation.separationCover_vertex_countable
#print axioms Iut.SourceSemiGraphResidualSeparation.separationCover_edge_countable
#print axioms Iut.SourceSemiGraphResidualSeparation.separationTreeProjection_liftUniversalVertex
