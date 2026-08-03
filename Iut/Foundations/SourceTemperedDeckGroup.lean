/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceCombinatorialUniversalCover
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.Algebra.Category.Grp.Shrink
import Mathlib.CategoryTheory.Limits.Final
import Mathlib.Order.Filter.Bases.Finite
import Mathlib.Topology.Algebra.Group.Basic

/-!
# Tempered deck-group inverse limits

This module constructs the topological inverse limit used immediately before
Proposition 3.6 of *Semi-graphs of Anabelioids*.  A presentation consists of a
genuine functor of groups whose transition maps are proved surjective and whose
levels are countable.  The underlying group is the categorical limit.  Its
topology is constructed as the infimum of the topologies induced by the
coordinate maps to the discrete levels.

No limit carrier, group law, topology, or compatibility equation is accepted
as independent input data.
-/

namespace Iut

universe u v

open CategoryTheory CategoryTheory.Limits
open scoped Topology

/-- An inverse system of surjections of countable discrete groups, exactly as
in Definition 3.1(i).  Discreteness is imposed canonically below, so it is not
an input field. -/
structure SourceTemperedGroupPresentation
    (Index : Type u) [Category.{v} Index] where
  diagram : Index ⥤ GrpCat.{max u v}
  transition_surjective :
    ∀ {finer coarser : Index} (map : finer ⟶ coarser),
      Function.Surjective (diagram.map map)
  level_countable : ∀ level, Countable (diagram.obj level)

namespace SourceTemperedGroupPresentation

variable {Index : Type u} [Category.{v} Index]
    (system : SourceTemperedGroupPresentation Index)

/-- The group underlying one level, equipped canonically with the discrete
topology.  The wrapper prevents this local topology from overlapping with
topologies that the same abstract group may carry elsewhere. -/
def DiscreteLevel (level : Index) := system.diagram.obj level

instance discreteLevelGroup (level : Index) :
    Group (system.DiscreteLevel level) :=
  inferInstanceAs (Group (system.diagram.obj level))

instance discreteLevelTopologicalSpace (level : Index) :
    TopologicalSpace (system.DiscreteLevel level) :=
  ⊥

instance discreteLevelDiscreteTopology (level : Index) :
    DiscreteTopology (system.DiscreteLevel level) :=
  discreteTopology_bot _

instance discreteLevelCountable (level : Index) :
    Countable (system.DiscreteLevel level) :=
  system.level_countable level

/-- The transition homomorphism between canonically discrete level groups. -/
def transition {finer coarser : Index} (map : finer ⟶ coarser) :
    system.DiscreteLevel finer →* system.DiscreteLevel coarser :=
  (system.diagram.map map).hom

theorem transition_isSurjective {finer coarser : Index}
    (map : finer ⟶ coarser) :
    Function.Surjective (system.transition map) :=
  system.transition_surjective map

theorem transition_continuous {finer coarser : Index}
    (map : finer ⟶ coarser) :
    Continuous (system.transition map) :=
  continuous_of_discreteTopology

/-- The inverse-limit group.  Its carrier and componentwise group operations
are constructed by the categorical limit in `GrpCat`. -/
noncomputable abbrev Limit : Type (max u v) :=
  (limit system.diagram : GrpCat.{max u v})

/-- The coordinate homomorphism from the inverse limit to a discrete level. -/
noncomputable def projection (level : Index) :
    system.Limit →* system.DiscreteLevel level :=
  (limit.π system.diagram level).hom

/-- The inverse-limit topology is the coarsest topology making every
coordinate projection continuous. -/
noncomputable instance limitTopologicalSpace :
    TopologicalSpace system.Limit :=
  ⨅ level, TopologicalSpace.induced (system.projection level)
    (inferInstance : TopologicalSpace (system.DiscreteLevel level))

/-- Coordinate projections are continuous by construction. -/
theorem continuous_projection (level : Index) :
    Continuous (system.projection level) := by
  rw [continuous_iff_le_induced]
  exact iInf_le _ level

/-- A coordinate projection bundled as a continuous group homomorphism. -/
noncomputable def continuousProjection (level : Index) :
    system.Limit →ₜ* system.DiscreteLevel level where
  toMonoidHom := system.projection level
  continuous_toFun := system.continuous_projection level

/-- The inverse-limit topology is literally the infimum of the coordinate
topologies, rather than merely an equivalent separately supplied topology. -/
theorem limit_topology_eq :
    (inferInstance : TopologicalSpace system.Limit) =
      ⨅ level, TopologicalSpace.induced (system.projection level)
        (inferInstance : TopologicalSpace (system.DiscreteLevel level)) :=
  rfl

/-- Componentwise multiplication and inversion are continuous in the
inverse-limit topology. -/
noncomputable instance limitIsTopologicalGroup :
    IsTopologicalGroup system.Limit := by
  apply topologicalGroup_iInf
  intro level
  exact topologicalGroup_induced (system.projection level)

/-- The coordinates satisfy the transition equation of the inverse system. -/
theorem projection_transition {finer coarser : Index}
    (map : finer ⟶ coarser) (value : system.Limit) :
    system.transition map (system.projection finer value) =
      system.projection coarser value := by
  have equality := limit.w system.diagram map
  exact ConcreteCategory.congr_hom equality value

/-- Compatible coordinates determine an inverse-limit element uniquely. -/
theorem ext {first second : system.Limit}
    (coordinates : ∀ level,
      system.projection level first = system.projection level second) :
    first = second :=
  Concrete.limit_ext system.diagram first second coordinates

/-- The kernel of one coordinate projection. -/
noncomputable def projectionKernel (level : Index) :
    Subgroup system.Limit :=
  (system.projection level).ker

/-- The subgroup fixing a finite set of coordinates. -/
noncomputable def finiteProjectionKernel (levels : Finset Index) :
    Subgroup system.Limit :=
  levels.inf system.projectionKernel

theorem mem_finiteProjectionKernel_iff
    (levels : Finset Index) (value : system.Limit) :
    value ∈ system.finiteProjectionKernel levels ↔
      ∀ level ∈ levels, system.projection level value = 1 := by
  classical
  induction levels using Finset.cons_induction with
  | empty => simp [finiteProjectionKernel]
  | cons level levels notMem induction =>
      rw [finiteProjectionKernel, Finset.inf_cons]
      change
        ((system.projection level value = 1) ∧
          value ∈ levels.inf system.projectionKernel) ↔ _
      rw [show value ∈ levels.inf system.projectionKernel ↔
          ∀ other ∈ levels, system.projection other value = 1 by
        change value ∈ system.finiteProjectionKernel levels ↔ _
        exact induction]
      simp

/-- At the identity, the inverse-limit neighborhood filter is generated by
the kernels of the individual discrete coordinate projections. -/
theorem nhds_one_eq_iInf_projectionKernel :
    𝓝 (1 : system.Limit) =
      ⨅ level, Filter.principal
        (system.projectionKernel level : Set system.Limit) := by
  change @nhds system.Limit
      (⨅ level, TopologicalSpace.induced (system.projection level)
        (inferInstance : TopologicalSpace (system.DiscreteLevel level))) 1 = _
  rw [nhds_iInf]
  apply iInf_congr
  intro level
  rw [nhds_induced, nhds_discrete]
  rw [← Filter.principal_singleton, Filter.comap_principal]
  congr 1
  ext value
  simp [projectionKernel]

/-- Finite intersections of coordinate kernels form a neighborhood basis at
the identity.  This is the concrete finite-projection-kernel basis of the
inverse-limit topology. -/
theorem nhds_one_hasBasis_projectionKernels :
    (𝓝 (1 : system.Limit)).HasBasis
      (fun levels : Set Index ↦ levels.Finite)
      (fun levels ↦ ⋂ level ∈ levels,
        (system.projectionKernel level : Set system.Limit)) := by
  rw [system.nhds_one_eq_iInf_projectionKernel]
  exact Filter.hasBasis_iInf_principal_finite _

/-- Refining a level can only shrink the corresponding projection kernel. -/
theorem projectionKernel_mono {finer coarser : Index}
    (map : finer ⟶ coarser) :
    system.projectionKernel finer ≤ system.projectionKernel coarser := by
  intro value finerTrivial
  change system.projection coarser value = 1
  rw [← system.projection_transition map value, finerTrivial, map_one]

/-- In a cofiltered presentation, one sufficiently fine coordinate kernel
lies inside every identity neighborhood.  This is the inverse-limit step
used to reduce a connected continuous action to a discrete level in
Proposition 3.6(ii). -/
theorem exists_projectionKernel_le_of_mem_nhds_one
    [IsCofiltered Index] {neighborhood : Set system.Limit}
    (mem_nhds : neighborhood ∈ 𝓝 (1 : system.Limit)) :
    ∃ level : Index,
      (system.projectionKernel level : Set system.Limit) ⊆ neighborhood := by
  classical
  obtain ⟨levels, levelsFinite, intersectionSubset⟩ :=
    system.nhds_one_hasBasis_projectionKernels.mem_iff.mp mem_nhds
  let finiteLevels : Finset Index := levelsFinite.toFinset
  obtain ⟨finer, maps⟩ := IsCofiltered.inf_objs_exists finiteLevels
  refine ⟨finer, fun value finerTrivial ↦ intersectionSubset ?_⟩
  simp only [Set.mem_iInter]
  intro level levelMem
  have finiteLevelMem : level ∈ finiteLevels := by
    simpa only [finiteLevels, Set.Finite.mem_toFinset] using levelMem
  let refinement : finer ⟶ level := (maps finiteLevelMem).some
  exact system.projectionKernel_mono refinement finerTrivial

/-- Reindex a presentation along a functor. -/
def reindex
    {Other : Type u} [Category.{v} Other]
    (change : Other ⥤ Index) : SourceTemperedGroupPresentation Other where
  diagram := change ⋙ system.diagram
  transition_surjective := fun map ↦
    system.transition_surjective (change.map map)
  level_countable := fun level ↦ system.level_countable (change.obj level)

/-- The canonical extension map from the limit of a cofinal reindexing to
the original inverse limit. -/
noncomputable def cofinalExtension
    {Other : Type u} [Category.{v} Other]
    (change : Other ⥤ Index) [change.Initial] :
    (system.reindex change).Limit →* system.Limit :=
  (Functor.Initial.limitIso change system.diagram).hom.hom

/-- Restriction along an initial (cofinal-for-inverse-limits) change of
index is a group isomorphism. -/
noncomputable def cofinalGroupIso
    {Other : Type u} [Category.{v} Other]
    (change : Other ⥤ Index) [change.Initial] :
    (system.reindex change).Limit ≃*
      system.Limit :=
  (Functor.Initial.limitIso change system.diagram).groupIsoToMulEquiv

@[simp]
theorem cofinalGroupIso_projection_obj
    {Other : Type u} [Category.{v} Other]
    (change : Other ⥤ Index) [change.Initial]
    (level : Other) (value : (system.reindex change).Limit) :
    system.projection (change.obj level)
        (system.cofinalGroupIso change value) =
      (system.reindex change).projection level value := by
  let comparison := Functor.Initial.limitIso change system.diagram
  have equality : comparison.hom ≫ limit.π system.diagram (change.obj level) =
      limit.π (change ⋙ system.diagram) level := by
    rw [← limit.pre_π system.diagram change level,
      ← Functor.Initial.limitIso_inv]
    simp
  exact ConcreteCategory.congr_hom equality value

@[simp]
theorem cofinalGroupIso_symm_projection
    {Other : Type u} [Category.{v} Other]
    (change : Other ⥤ Index) [change.Initial]
    (level : Other) (value : system.Limit) :
    (system.reindex change).projection level
        ((system.cofinalGroupIso change).symm value) =
      system.projection (change.obj level) value := by
  exact ConcreteCategory.congr_hom
    (limit.pre_π system.diagram change level) value

/-- A coordinate outside the displayed cofinal subsystem factors through a
chosen finer coordinate supplied by initiality. -/
theorem cofinalGroupIso_projection
    {Other : Type u} [Category.{v} Other]
    (change : Other ⥤ Index) [change.Initial]
    (level : Index) (value : (system.reindex change).Limit) :
    system.projection level (system.cofinalGroupIso change value) =
      system.transition (Functor.Initial.homToLift change level)
        ((system.reindex change).projection
          (Functor.Initial.lift change level) value) := by
  symm
  rw [← system.cofinalGroupIso_projection_obj change]
  exact system.projection_transition
    (Functor.Initial.homToLift change level)
    (system.cofinalGroupIso change value)

/-- Restriction to an initial (cofinal-for-inverse-limits) subsystem is an
isomorphism of topological groups. -/
noncomputable def cofinalContinuousMulEquiv
    {Other : Type u} [Category.{v} Other]
    (change : Other ⥤ Index) [change.Initial] :
    (system.reindex change).Limit ≃ₜ* system.Limit where
  toMulEquiv := system.cofinalGroupIso change
  continuous_toFun := by
    change @Continuous (system.reindex change).Limit system.Limit
      (system.reindex change).limitTopologicalSpace
      (⨅ level, TopologicalSpace.induced (system.projection level)
        (inferInstance : TopologicalSpace (system.DiscreteLevel level)))
      (system.cofinalGroupIso change)
    rw [continuous_iInf_rng]
    intro level
    rw [continuous_induced_rng]
    change Continuous (fun value ↦
      system.projection level (system.cofinalGroupIso change value))
    rw [show (fun value ↦
        system.projection level (system.cofinalGroupIso change value)) =
      fun value ↦ system.transition
        (Functor.Initial.homToLift change level)
        ((system.reindex change).projection
          (Functor.Initial.lift change level) value) by
        funext value
        exact system.cofinalGroupIso_projection change level value]
    exact (system.transition_continuous
      (Functor.Initial.homToLift change level)).comp
        ((system.reindex change).continuous_projection
          (Functor.Initial.lift change level))
  continuous_invFun := by
    change @Continuous system.Limit (system.reindex change).Limit
      system.limitTopologicalSpace
      (⨅ level, TopologicalSpace.induced
        ((system.reindex change).projection level)
        (inferInstance : TopologicalSpace
          ((system.reindex change).DiscreteLevel level)))
      (system.cofinalGroupIso change).symm
    rw [continuous_iInf_rng]
    intro level
    rw [continuous_induced_rng]
    change Continuous (fun value ↦
      (system.reindex change).projection level
        ((system.cofinalGroupIso change).symm value))
    rw [show (fun value ↦
        (system.reindex change).projection level
          ((system.cofinalGroupIso change).symm value)) =
      fun value ↦ system.projection (change.obj level) value by
        funext value
        exact system.cofinalGroupIso_symm_projection change level value]
    exact system.continuous_projection (change.obj level)

end SourceTemperedGroupPresentation

/-- A lawful inverse diagram of countable groups.  Its transition maps need
not themselves be surjective; the canonical image presentation below replaces
each level by the actual image of the inverse limit and is surjective without
changing the limit. -/
structure SourceCountableGroupDiagram
    (Index : Type u) [Category.{v} Index] where
  diagram : Index ⥤ GrpCat.{max u v}
  level_countable : ∀ level, Countable (diagram.obj level)

namespace SourceCountableGroupDiagram

variable {Index : Type u} [Category.{v} Index]
    (system : SourceCountableGroupDiagram Index)

/-- The raw inverse limit of the original countable group diagram. -/
noncomputable abbrev RawLimit : Type (max u v) :=
  (limit system.diagram : GrpCat.{max u v})

/-- Canonically discrete topology on an original level group. -/
def RawDiscreteLevel (level : Index) := system.diagram.obj level

/-- A coordinate of the raw inverse limit. -/
noncomputable def rawProjection (level : Index) :
    system.RawLimit →* system.RawDiscreteLevel level :=
  (limit.π system.diagram level).hom

instance rawDiscreteLevelGroup (level : Index) :
    Group (system.RawDiscreteLevel level) :=
  inferInstanceAs (Group (system.diagram.obj level))

instance rawDiscreteLevelTopologicalSpace (level : Index) :
    TopologicalSpace (system.RawDiscreteLevel level) := ⊥

instance rawDiscreteLevelDiscreteTopology (level : Index) :
    DiscreteTopology (system.RawDiscreteLevel level) :=
  discreteTopology_bot _

/-- The raw limit receives the same initial topology from its original
discrete coordinates. -/
noncomputable instance rawLimitTopologicalSpace :
    TopologicalSpace system.RawLimit :=
  ⨅ level, TopologicalSpace.induced (system.rawProjection level)
    (inferInstance : TopologicalSpace (system.RawDiscreteLevel level))

theorem continuous_rawProjection (level : Index) :
    Continuous (system.rawProjection level) := by
  rw [continuous_iff_le_induced]
  exact iInf_le _ level

noncomputable instance rawLimitIsTopologicalGroup :
    IsTopologicalGroup system.RawLimit := by
  apply topologicalGroup_iInf
  intro level
  exact topologicalGroup_induced (system.rawProjection level)

/-- The part of a level group that actually occurs as a coordinate of a
compatible point of the full inverse limit. -/
noncomputable abbrev ProjectionImage (level : Index) :=
  (system.rawProjection level).range

instance projectionImageCountable (level : Index) :
    Countable (system.ProjectionImage level) := by
  letI : Countable (system.RawDiscreteLevel level) :=
    system.level_countable level
  exact Subtype.countable

/-- A transition restricts to the images of the raw inverse-limit
projections. -/
noncomputable def imageTransition {finer coarser : Index}
    (map : finer ⟶ coarser) :
    system.ProjectionImage finer →* system.ProjectionImage coarser where
  toFun value := by
    refine ⟨system.diagram.map map value.1, ?_⟩
    rcases value.2 with ⟨source, equality⟩
    refine ⟨source, ?_⟩
    have compatibility := limit.w system.diagram map
    exact (ConcreteCategory.congr_hom compatibility source).symm.trans
      (congrArg (system.diagram.map map) equality)
  map_one' := by
    apply Subtype.ext
    exact map_one (system.diagram.map map).hom
  map_mul' first second := by
    apply Subtype.ext
    exact map_mul (system.diagram.map map).hom first.1 second.1

/-- The projection-image groups and their restricted transitions form a
lawful inverse diagram. -/
noncomputable def imageDiagram : Index ⥤ GrpCat.{max u v} where
  obj level := GrpCat.of (system.ProjectionImage level)
  map map := GrpCat.ofHom (system.imageTransition map)
  map_id level := by
    change GrpCat.ofHom (system.imageTransition (𝟙 level)) =
      GrpCat.ofHom (MonoidHom.id _)
    apply congrArg GrpCat.ofHom
    apply MonoidHom.ext
    intro value
    apply Subtype.ext
    simp [imageTransition]
  map_comp firstMap secondMap := by
    change GrpCat.ofHom (system.imageTransition (firstMap ≫ secondMap)) =
      GrpCat.ofHom ((system.imageTransition secondMap).comp
        (system.imageTransition firstMap))
    apply congrArg GrpCat.ofHom
    apply MonoidHom.ext
    intro value
    apply Subtype.ext
    simp [imageTransition]

/-- Every image transition is surjective: a target image element comes from
one raw-limit point, whose finer coordinate is a preimage. -/
theorem imageTransition_surjective {finer coarser : Index}
    (map : finer ⟶ coarser) :
    Function.Surjective (system.imageTransition map) := by
  rintro ⟨target, source, source_eq⟩
  let finerValue : system.ProjectionImage finer :=
    ⟨system.rawProjection finer source, source, rfl⟩
  refine ⟨finerValue, ?_⟩
  apply Subtype.ext
  change system.diagram.map map (system.rawProjection finer source) = target
  rw [show system.diagram.map map (system.rawProjection finer source) =
      system.rawProjection coarser source by
    exact ConcreteCategory.congr_hom (limit.w system.diagram map) source]
  exact source_eq

/-- The canonical surjective presentation extracted from an arbitrary
countable inverse diagram. -/
noncomputable def imagePresentation :
    SourceTemperedGroupPresentation Index where
  diagram := system.imageDiagram
  transition_surjective := fun map ↦ system.imageTransition_surjective map
  level_countable := fun level ↦ system.projectionImageCountable level

/-- The raw-limit cone whose coordinates land in their actual images. -/
noncomputable def imageCone : Cone system.imageDiagram where
  pt := GrpCat.of system.RawLimit
  π :=
    { app := fun level ↦ GrpCat.ofHom
        ((system.rawProjection level).rangeRestrict)
      naturality := by
        intro finer coarser map
        apply GrpCat.hom_ext
        apply MonoidHom.ext
        intro value
        apply Subtype.ext
        exact (ConcreteCategory.congr_hom (limit.w system.diagram map)
          value).symm }

/-- Map a raw compatible point to the same coordinates, now regarded in the
actual coordinate images. -/
noncomputable def toImageLimit :
    system.RawLimit →* system.imagePresentation.Limit :=
  (limit.lift system.imageDiagram system.imageCone).hom

/-- The image-limit cone in the original level groups. -/
noncomputable def originalCone : Cone system.diagram where
  pt := GrpCat.of system.imagePresentation.Limit
  π :=
    { app := fun level ↦ GrpCat.ofHom
        ((Subgroup.subtype
          (system.rawProjection level).range).comp
            (system.imagePresentation.projection level))
      naturality := by
        intro finer coarser map
        apply GrpCat.hom_ext
        apply MonoidHom.ext
        intro value
        exact (congrArg Subtype.val
          (system.imagePresentation.projection_transition map value)).symm }

/-- Forget that an image coordinate lies in the image and view it in the
original level group. -/
noncomputable def fromImageLimit :
    system.imagePresentation.Limit →* system.RawLimit :=
  (limit.lift system.diagram system.originalCone).hom

@[simp]
theorem toImageLimit_projection (level : Index) (value : system.RawLimit) :
    system.imagePresentation.projection level (system.toImageLimit value) =
      (system.rawProjection level).rangeRestrict value := by
  change (limit.π system.imageDiagram level).hom
      (system.toImageLimit value) = _
  exact ConcreteCategory.congr_hom
    (limit.lift_π system.imageCone level) value

/-- Every coordinate of the canonical image presentation is attained by a
compatible inverse-limit point.  This is true by construction: the carrier
of a level is the image of the corresponding raw projection. -/
theorem imagePresentation_projection_surjective (level : Index) :
    Function.Surjective
      (system.imagePresentation.projection level) := by
  rintro ⟨target, source, source_eq⟩
  refine ⟨system.toImageLimit source, ?_⟩
  apply Subtype.ext
  rw [system.toImageLimit_projection]
  exact source_eq

@[simp]
theorem rawProjection_fromImageLimit (level : Index)
    (value : system.imagePresentation.Limit) :
    system.rawProjection level (system.fromImageLimit value) =
      (system.imagePresentation.projection level value).1 := by
  change (limit.π system.diagram level).hom
      (system.fromImageLimit value) = _
  exact ConcreteCategory.congr_hom
    (limit.lift_π system.originalCone level) value

/-- Replacing every level by the image of the raw inverse limit does not
change the inverse-limit group. -/
noncomputable def rawLimitMulEquivImageLimit :
    system.RawLimit ≃* system.imagePresentation.Limit where
  toFun := system.toImageLimit
  invFun := system.fromImageLimit
  map_mul' := map_mul system.toImageLimit
  left_inv value := by
    apply Concrete.limit_ext system.diagram
    intro level
    change system.rawProjection level
        (system.fromImageLimit (system.toImageLimit value)) =
      system.rawProjection level value
    simp
  right_inv value := by
    apply system.imagePresentation.ext
    intro level
    apply Subtype.ext
    simp

/-- The canonical identification with the surjective image presentation is
also a homeomorphism for the two inverse-limit topologies. -/
noncomputable def rawLimitContinuousMulEquivImageLimit :
    system.RawLimit ≃ₜ* system.imagePresentation.Limit where
  toMulEquiv := system.rawLimitMulEquivImageLimit
  continuous_toFun := by
    change @Continuous system.RawLimit system.imagePresentation.Limit
      system.rawLimitTopologicalSpace
      (⨅ level, TopologicalSpace.induced
        (system.imagePresentation.projection level)
        (inferInstance : TopologicalSpace
          (system.imagePresentation.DiscreteLevel level)))
      system.toImageLimit
    rw [continuous_iInf_rng]
    intro level
    rw [continuous_induced_rng]
    change Continuous
      (fun value ↦ system.imagePresentation.projection level
        (system.toImageLimit value))
    rw [show (fun value ↦ system.imagePresentation.projection level
        (system.toImageLimit value)) =
      fun value ↦ (system.rawProjection level).rangeRestrict value by
        funext value
        exact system.toImageLimit_projection level value]
    rw [continuous_discrete_rng]
    intro target
    have openPreimage : IsOpen
        ((system.rawProjection level) ⁻¹'
          ({target.1} : Set (system.RawDiscreteLevel level))) :=
      (isOpen_discrete _).preimage (system.continuous_rawProjection level)
    convert openPreimage using 1
    ext value
    constructor
    · intro equality
      exact congrArg Subtype.val equality
    · intro equality
      exact Subtype.ext equality
  continuous_invFun := by
    change @Continuous system.imagePresentation.Limit system.RawLimit
      system.imagePresentation.limitTopologicalSpace
      (⨅ level, TopologicalSpace.induced (system.rawProjection level)
        (inferInstance : TopologicalSpace
          (system.RawDiscreteLevel level)))
      system.fromImageLimit
    rw [continuous_iInf_rng]
    intro level
    rw [continuous_induced_rng]
    change Continuous
      (fun value ↦ system.rawProjection level
        (system.fromImageLimit value))
    rw [show (fun value ↦ system.rawProjection level
        (system.fromImageLimit value)) =
      fun value ↦ (system.imagePresentation.projection level value).1 by
        funext value
        exact system.rawProjection_fromImageLimit level value]
    exact continuous_of_discreteTopology.comp
      (system.imagePresentation.continuous_projection level)

end SourceCountableGroupDiagram

namespace SourceCombinatorialUniversalCover.SourceGaloisCombinatorialUniversalCover

variable (diagram : SourceSemiGraphOfAnabelioids.{u})
    (root : diagram.base.Vertex)

/-- The lawful group-valued inverse diagram attached to the pointed Galois
levels.  Its objects and arrows are exactly the deck groups and transitions
constructed from the source data in `SourceCombinatorialUniversalCover`. -/
noncomputable def deckDiagramSmall :
    SourceSemiGraphOfAnabelioids.GluedObject.GaloisLevel diagram root ⥤
      GrpCat.{u} where
  obj level := GrpCat.of (DeckGroup diagram root level)
  map refinement := GrpCat.ofHom (deckTransition diagram root refinement)
  map_id level := by
    change GrpCat.ofHom (deckTransition diagram root (𝟙 level)) =
      GrpCat.ofHom (MonoidHom.id _)
    exact congrArg GrpCat.ofHom (deckTransition_id diagram root level)
  map_comp firstMap secondMap := by
    change GrpCat.ofHom (deckTransition diagram root (firstMap ≫ secondMap)) =
      GrpCat.ofHom ((deckTransition diagram root secondMap).comp
        (deckTransition diagram root firstMap))
    exact congrArg GrpCat.ofHom
      (deckTransition_comp diagram root firstMap secondMap)

/-- Universe-lift the concrete deck diagram so its group category is large
enough to support the limit over the category of Galois levels. -/
noncomputable def deckDiagram :
    SourceSemiGraphOfAnabelioids.GluedObject.GaloisLevel diagram root ⥤
      GrpCat.{u + 1} :=
  deckDiagramSmall diagram root ⋙ GrpCat.uliftFunctor.{u + 1, u}

/-- Every object in the actual Galois deck diagram is countable when the
underlying semigraph is countable. -/
theorem deckDiagram_obj_countable
    [Countable diagram.base.Vertex] [Countable diagram.base.Edge]
    (level :
      SourceSemiGraphOfAnabelioids.GluedObject.GaloisLevel diagram root) :
    Countable ((deckDiagram diagram root).obj level) :=
  by
    change Countable (ULift (DeckGroup diagram root level))
    letI : Countable (DeckGroup diagram root level) :=
      deckGroup_countable diagram root level
    infer_instance

/-- The complete pointed-Galois deck diagram as a lawful countable inverse
system. -/
noncomputable def countableDeckSystem
    [Countable diagram.base.Vertex] [Countable diagram.base.Edge] :
    SourceCountableGroupDiagram
      (SourceSemiGraphOfAnabelioids.GluedObject.GaloisLevel diagram root) where
  diagram := deckDiagram diagram root
  level_countable := fun level ↦ deckDiagram_obj_countable diagram root level

/-- The canonical inverse system of surjective countable image groups that
presents the same limit as the actual deck diagram. -/
noncomputable def temperedPresentation
    [Countable diagram.base.Vertex] [Countable diagram.base.Edge] :
    SourceTemperedGroupPresentation
      (SourceSemiGraphOfAnabelioids.GluedObject.GaloisLevel diagram root) :=
  (countableDeckSystem diagram root).imagePresentation

/-- The source's tempered deck-group inverse limit. -/
noncomputable abbrev TemperedDeckGroup
    [Countable diagram.base.Vertex] [Countable diagram.base.Edge] : Type (u + 1) :=
  (temperedPresentation diagram root).Limit

/-- The constructed tempered group is topologically isomorphic to the raw
inverse limit of the literal groups `Gal(G^{∞,i}/G)`. -/
noncomputable def rawDeckLimitContinuousMulEquiv
    [Countable diagram.base.Vertex] [Countable diagram.base.Edge] :
    (countableDeckSystem diagram root).RawLimit ≃ₜ*
      TemperedDeckGroup diagram root :=
  (countableDeckSystem diagram root).rawLimitContinuousMulEquivImageLimit

end SourceCombinatorialUniversalCover.SourceGaloisCombinatorialUniversalCover

namespace SourceCombinatorialUniversalCover.SourceIsolatedGaloisCombinatorialUniversalCover

variable (diagram : SourceSemiGraphOfAnabelioids.{u})
    (noVertex : ¬Nonempty diagram.base.Vertex)

/-- The lawful inverse diagram of full isolated-edge Galois deck groups. -/
noncomputable def deckDiagramSmall :
    diagram.IsolatedGaloisLevel noVertex ⥤ GrpCat.{u} where
  obj level := GrpCat.of (DeckGroup diagram noVertex level)
  map refinement := GrpCat.ofHom (deckTransition diagram noVertex refinement)
  map_id level := by
    change GrpCat.ofHom (deckTransition diagram noVertex (𝟙 level)) =
      GrpCat.ofHom (MonoidHom.id _)
    exact congrArg GrpCat.ofHom
      (isolatedDeckTransition_id diagram noVertex level)
  map_comp firstMap secondMap := by
    change GrpCat.ofHom
        (deckTransition diagram noVertex (firstMap ≫ secondMap)) =
      GrpCat.ofHom ((deckTransition diagram noVertex secondMap).comp
        (deckTransition diagram noVertex firstMap))
    exact congrArg GrpCat.ofHom
      (isolatedDeckTransition_comp diagram noVertex firstMap secondMap)

/-- Universe-lift the concrete isolated diagram so its limit exists in the
required group category. -/
noncomputable def deckDiagram :
    diagram.IsolatedGaloisLevel noVertex ⥤ GrpCat.{u + 1} :=
  deckDiagramSmall diagram noVertex ⋙ GrpCat.uliftFunctor.{u + 1, u}

/-- The isolated-edge system is already an inverse system of surjections of
countable discrete groups, so it directly presents a tempered group. -/
noncomputable def temperedPresentation :
    SourceTemperedGroupPresentation
      (diagram.IsolatedGaloisLevel noVertex) where
  diagram := deckDiagram diagram noVertex
  transition_surjective := by
    intro finer coarser refinement target
    rcases target with ⟨target⟩
    obtain ⟨source, equality⟩ :=
      deckTransition_surjective diagram noVertex refinement target
    exact ⟨ULift.up source, congrArg ULift.up equality⟩
  level_countable := by
    intro level
    letI : Countable (DeckGroup diagram noVertex level) :=
      deckGroup_countable diagram noVertex level
    change Countable (ULift (DeckGroup diagram noVertex level))
    infer_instance

/-- The tempered fundamental group in the isolated-edge case. -/
noncomputable abbrev TemperedDeckGroup : Type (u + 1) :=
  (temperedPresentation diagram noVertex).Limit

end SourceCombinatorialUniversalCover.SourceIsolatedGaloisCombinatorialUniversalCover

end Iut
