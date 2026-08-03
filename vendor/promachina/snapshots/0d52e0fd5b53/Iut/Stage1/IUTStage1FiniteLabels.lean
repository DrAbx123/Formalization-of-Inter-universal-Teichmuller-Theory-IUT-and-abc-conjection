/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Stage1.IUTStage1IUTIVAlgebra

/-!
Finite-label and bad-local cusp-label source objects for the Stage 1 corridor.

This module is a mechanical extraction from `Iut.Stage1.IUTStage1Source`.  It
keeps the finite local log-volume endpoints, `F_l` label/torsor/sign/cusp-label
models, `ZMod` cusp full labels, theta-root cusp-label source packages, and
label-averaged log-volume compatibility separate from Step (x), Hodge/SHE, IPL,
and Step (xi) route declarations.
-/

namespace Iut
namespace Stage1

open RealLineCopy
open scoped BigOperators

universe u v w x

namespace IUTStage1FiniteLocalLogVolumeObject

variable {kind : IUTStage1PlaceKind}

theorem logVolume_eq
    (data : IUTStage1FiniteLocalLogVolumeObject kind) :
    data.localObject.logVolume = data.finiteLogVolume :=
  data.finite_log_volume_eq

def place
    (data : IUTStage1FiniteLocalLogVolumeObject kind) :
    IUTStage1PlaceId kind :=
  data.localObject.object.place

theorem finiteLocalLogVolume_endpoint
    (data : IUTStage1FiniteLocalLogVolumeObject kind) :
    data.localObject.logVolume = data.finiteLogVolume ∧
      data.place = data.localObject.object.place :=
  ⟨data.logVolume_eq, rfl⟩

end IUTStage1FiniteLocalLogVolumeObject

namespace IUTStage1ProcessionNormalizedLogVolume

variable {kind : IUTStage1PlaceKind}

theorem normalized_eq
    (data : IUTStage1ProcessionNormalizedLogVolume kind) :
    data.normalizedLogVolume =
      data.totalLogVolume / (data.capsuleCount : Real) :=
  data.normalized_eq_average

theorem capsuleCount_pos
    (data : IUTStage1ProcessionNormalizedLogVolume kind) :
    0 < data.capsuleCount :=
  data.positive_capsule_count

def toFiniteLocalLogVolumeObject
    (data : IUTStage1ProcessionNormalizedLogVolume kind) :
    IUTStage1FiniteLocalLogVolumeObject kind :=
  data.localObject

theorem processionNormalized_endpoint
    (data : IUTStage1ProcessionNormalizedLogVolume kind) :
    0 < data.capsuleCount ∧
      data.normalizedLogVolume =
        data.totalLogVolume / (data.capsuleCount : Real) ∧
      data.toFiniteLocalLogVolumeObject = data.localObject :=
  ⟨data.capsuleCount_pos, data.normalized_eq, rfl⟩

end IUTStage1ProcessionNormalizedLogVolume

namespace IUTStage1LocalContainerLogVolumeEstimate

variable {targetSigned localLogVolume : Real}

theorem targetSigned_le_localLogVolume
    (estimate :
      IUTStage1LocalContainerLogVolumeEstimate targetSigned localLogVolume) :
    targetSigned <= localLogVolume := by
  rw [estimate.localLogVolume_eq_container]
  exact estimate.targetSigned_le_containerLogVolume

theorem localContainerLogVolume_endpoint
    (estimate :
      IUTStage1LocalContainerLogVolumeEstimate targetSigned localLogVolume) :
    localLogVolume = estimate.containerLogVolume ∧
      targetSigned <= estimate.containerLogVolume ∧
      targetSigned <= localLogVolume :=
  ⟨estimate.localLogVolume_eq_container,
    estimate.targetSigned_le_containerLogVolume,
    estimate.targetSigned_le_localLogVolume⟩

end IUTStage1LocalContainerLogVolumeEstimate

namespace IUTStage1LocalObjectContainerLogVolumeEstimate

variable {kind : IUTStage1PlaceKind}
variable {targetSigned localLogVolume : Real}

def toLocalContainerEstimate
    (estimate :
      IUTStage1LocalObjectContainerLogVolumeEstimate
        kind targetSigned localLogVolume) :
    IUTStage1LocalContainerLogVolumeEstimate
      targetSigned localLogVolume :=
  { containerLogVolume :=
      estimate.object_container_estimate.containerLogVolume,
    localLogVolume_eq_container :=
      estimate.localLogVolume_eq_object.trans
        estimate.object_container_estimate.localLogVolume_eq_container,
    targetSigned_le_containerLogVolume :=
      estimate.object_container_estimate.targetSigned_le_containerLogVolume }

theorem targetSigned_le_localLogVolume
    (estimate :
      IUTStage1LocalObjectContainerLogVolumeEstimate
        kind targetSigned localLogVolume) :
    targetSigned <= localLogVolume :=
  estimate.toLocalContainerEstimate.targetSigned_le_localLogVolume

theorem localObjectContainerLogVolume_endpoint
    (estimate :
      IUTStage1LocalObjectContainerLogVolumeEstimate
        kind targetSigned localLogVolume) :
    localLogVolume = estimate.localObject.finiteLogVolume ∧
      targetSigned <= estimate.object_container_estimate.containerLogVolume ∧
      targetSigned <= estimate.localObject.finiteLogVolume ∧
      targetSigned <= localLogVolume :=
  ⟨estimate.localLogVolume_eq_object,
    estimate.object_container_estimate.targetSigned_le_containerLogVolume,
    estimate.object_container_estimate.targetSigned_le_localLogVolume,
    estimate.targetSigned_le_localLogVolume⟩

def transportLocalLogVolume
    {newLocalLogVolume : Real}
    (estimate :
      IUTStage1LocalObjectContainerLogVolumeEstimate
        kind targetSigned localLogVolume)
    (hlog : newLocalLogVolume = localLogVolume) :
    IUTStage1LocalObjectContainerLogVolumeEstimate
      kind targetSigned newLocalLogVolume :=
  { localObject := estimate.localObject,
    localLogVolume_eq_object :=
      hlog.trans estimate.localLogVolume_eq_object,
    object_container_estimate := estimate.object_container_estimate }

end IUTStage1LocalObjectContainerLogVolumeEstimate

namespace IUTStage1FLLabelModel

variable {label : Type u}

/-- The canonical `F_l` label model supplied by the foundations layer. -/
def zmod (l : PrimeGeFive) :
    IUTStage1FLLabelModel (ZMod l.value) :=
  { prime := l,
    labelEquiv := Equiv.refl _ }

theorem card_eq_primeValue
    [Fintype label]
    (model : IUTStage1FLLabelModel label) :
    Fintype.card label = model.prime.value := by
  haveI : NeZero model.prime.value := ⟨model.prime.ne_zero⟩
  calc
    Fintype.card label = Fintype.card (ZMod model.prime.value) :=
      Fintype.card_congr model.labelEquiv
    _ = model.prime.value := by
      rw [ZMod.card]

def toZMod
    (model : IUTStage1FLLabelModel label) :
    label -> ZMod model.prime.value :=
  model.labelEquiv

def fromZMod
    (model : IUTStage1FLLabelModel label) :
    ZMod model.prime.value -> label :=
  model.labelEquiv.symm

theorem fromZMod_toZMod
    (model : IUTStage1FLLabelModel label) (j : label) :
    model.fromZMod (model.toZMod j) = j :=
  model.labelEquiv.left_inv j

theorem toZMod_fromZMod
    (model : IUTStage1FLLabelModel label)
    (j : ZMod model.prime.value) :
    model.toZMod (model.fromZMod j) = j :=
  model.labelEquiv.right_inv j

theorem labelModel_endpoint
    [Fintype label]
    (model : IUTStage1FLLabelModel label)
    (j : label) (z : ZMod model.prime.value) :
    Fintype.card label = model.prime.value ∧
      model.fromZMod (model.toZMod j) = j ∧
      model.toZMod (model.fromZMod z) = z :=
  ⟨model.card_eq_primeValue,
    model.fromZMod_toZMod j,
    model.toZMod_fromZMod z⟩

end IUTStage1FLLabelModel

/--
`F_l` label model together with the additive torsor action transported from
the concrete `ZMod l` model.

The universe is kept at `Type` because `AdditiveTorsorData` in the foundations
layer currently takes both the acting group and carrier in the same universe,
and `ZMod l.value` is a small type.
-/
structure IUTStage1FLLabelTorsorModel
    (label : Type) where
  label_model : IUTStage1FLLabelModel label
  torsor : AdditiveTorsorData (ZMod label_model.prime.value) label
  torsor_vadd_eq_zmod :
    ∀ (t : ZMod label_model.prime.value) (j : label),
      torsor.vadd t j =
        label_model.fromZMod (t + label_model.toZMod j)

namespace IUTStage1FLLabelTorsorModel

variable {label : Type}

/-- The canonical additive `F_l` torsor model on `ZMod l`. -/
def zmod (l : PrimeGeFive) :
    IUTStage1FLLabelTorsorModel (ZMod l.value) :=
  { label_model := IUTStage1FLLabelModel.zmod l,
    torsor := zmodLabelAdditiveTorsorData l,
    torsor_vadd_eq_zmod := by
      intro t j
      rfl }

theorem vadd_eq_zmod
    (model : IUTStage1FLLabelTorsorModel label)
    (t : ZMod model.label_model.prime.value) (j : label) :
    model.torsor.vadd t j =
      model.label_model.fromZMod (t + model.label_model.toZMod j) :=
  model.torsor_vadd_eq_zmod t j

theorem zero_vadd
    (model : IUTStage1FLLabelTorsorModel label) (j : label) :
    model.torsor.vadd 0 j = j :=
  model.torsor.zero_vadd j

theorem add_vadd
    (model : IUTStage1FLLabelTorsorModel label)
    (g h : ZMod model.label_model.prime.value) (j : label) :
    model.torsor.vadd (g + h) j =
      model.torsor.vadd g (model.torsor.vadd h j) :=
  model.torsor.add_vadd g h j

theorem exists_unique_vadd_eq
    (model : IUTStage1FLLabelTorsorModel label)
    (j₁ j₂ : label) :
    ∃! t : ZMod model.label_model.prime.value,
      model.torsor.vadd t j₁ = j₂ :=
  model.torsor.exists_unique_vadd_eq j₁ j₂

theorem torsorModel_endpoint
    (model : IUTStage1FLLabelTorsorModel label)
    (t g h : ZMod model.label_model.prime.value) (j j₁ j₂ : label) :
    model.torsor.vadd t j =
        model.label_model.fromZMod (t + model.label_model.toZMod j) ∧
      model.torsor.vadd 0 j = j ∧
      model.torsor.vadd (g + h) j =
        model.torsor.vadd g (model.torsor.vadd h j) ∧
      (∃! u : ZMod model.label_model.prime.value,
        model.torsor.vadd u j₁ = j₂) :=
  ⟨model.vadd_eq_zmod t j,
    model.zero_vadd j,
    model.add_vadd g h j,
    model.exists_unique_vadd_eq j₁ j₂⟩

theorem zmod_vadd_eq_translate
    (l : PrimeGeFive) (t j : ZMod l.value) :
    (zmod l).torsor.vadd t j = zmodLabelTranslate l t j :=
  rfl

theorem zmod_two_ne_one (l : PrimeGeFive) :
    (2 : ZMod l.value) ≠ (1 : ZMod l.value) := by
  haveI : Fact (1 < l.value) := ⟨by
    have hge : 5 ≤ l.value := l.ge_five
    omega⟩
  intro h
  have h10 : (1 : ZMod l.value) = 0 := by
    calc
      (1 : ZMod l.value) = (2 : ZMod l.value) - 1 := by norm_num
      _ = (1 : ZMod l.value) - 1 := by rw [h]
      _ = 0 := by ring
  exact (one_ne_zero : (1 : ZMod l.value) ≠ 0) h10

theorem zmodLabelTranslate_one_one_eq_two (l : PrimeGeFive) :
    zmodLabelTranslate l (1 : ZMod l.value) (1 : ZMod l.value) = 2 := by
  change (1 : ZMod l.value) + 1 = 2
  norm_num

/--
The singleton restriction to the coordinate `j = 1` is not stable under the
additive `F_l`-torsor symmetry in the concrete finite model.
-/
theorem singletonOne_not_closed_under_translation_one (l : PrimeGeFive) :
    ¬ ∀ j : ZMod l.value,
        j = 1 -> zmodLabelTranslate l (1 : ZMod l.value) j = 1 := by
  intro hclosed
  have h := hclosed (1 : ZMod l.value) rfl
  rw [zmodLabelTranslate_one_one_eq_two] at h
  exact zmod_two_ne_one l h

theorem zmod_subset_eq_univ_of_nonempty_translation_closed
    (l : PrimeGeFive) (s : Finset (ZMod l.value))
    (hne : s.Nonempty)
    (hclosed :
      ∀ (t j : ZMod l.value), j ∈ s -> zmodLabelTranslate l t j ∈ s) :
    s = Finset.univ := by
  classical
  rcases hne with ⟨base, hbase⟩
  ext x
  constructor
  · intro _hx
    exact Finset.mem_univ x
  · intro _hx
    have hmem := hclosed (x - base) base hbase
    rw [zmodLabelTranslate_eq_add] at hmem
    simpa [sub_add_cancel] using hmem

theorem zmod_proper_nonempty_subset_not_translation_closed
    (l : PrimeGeFive) (s : Finset (ZMod l.value))
    (hne : s.Nonempty)
    (hproper : s ≠ Finset.univ) :
    ¬ ∀ (t j : ZMod l.value), j ∈ s -> zmodLabelTranslate l t j ∈ s := by
  intro hclosed
  exact hproper
    (zmod_subset_eq_univ_of_nonempty_translation_closed l s hne hclosed)

theorem zmodTranslationClosure_endpoint
    (l : PrimeGeFive) (s : Finset (ZMod l.value))
    (hne : s.Nonempty) :
    (¬ ∀ j : ZMod l.value,
        j = 1 -> zmodLabelTranslate l (1 : ZMod l.value) j = 1) ∧
      ((∀ (t j : ZMod l.value), j ∈ s ->
          zmodLabelTranslate l t j ∈ s) -> s = Finset.univ) :=
  ⟨singletonOne_not_closed_under_translation_one l,
    fun hclosed => zmod_subset_eq_univ_of_nonempty_translation_closed
      l s hne hclosed⟩

end IUTStage1FLLabelTorsorModel

/--
The `ZMod l` label model together with the unit action and sign quotient data
used for label classes.

This records the action of `(ZMod l)^×`, the sign action, their compatibility
via the unit `-1`, and the subgroup `{1,-1}` whose orbits are exactly sign
orbits.
-/
structure IUTStage1FLZModUnitSignLabelModel
    (l : PrimeGeFive) where
  torsor_model : IUTStage1FLLabelTorsorModel (ZMod l.value)
  signUnitCompatibility :
    QuotientSignUnitCompatibility
      (zmodPointedQuotient l) (zmodUnitActionData l) (zmodSignAction l)
  signUnitSubgroup : Subgroup (ZMod l.value)ˣ
  signUnitSubgroup_smul_eq_self_or_neg :
    ∀ {a : (ZMod l.value)ˣ},
      a ∈ signUnitSubgroup ->
        ∀ x : ZMod l.value,
          (zmodUnitActionData l).smul a x = x ∨
            (zmodUnitActionData l).smul a x = (zmodSignAction l).neg x
  signUnitSubgroup_orbit_iff_signOrbit :
    ∀ x generator : ZMod l.value,
      (∃ a : (ZMod l.value)ˣ,
        a ∈ signUnitSubgroup ∧
          (zmodUnitActionData l).smul a generator = x) ↔
        (zmodSignAction l).InSignOrbit x generator

namespace IUTStage1FLZModUnitSignLabelModel

/-- The canonical unit/sign label model supplied by the foundations layer. -/
def zmod (l : PrimeGeFive) :
    IUTStage1FLZModUnitSignLabelModel l :=
  { torsor_model := IUTStage1FLLabelTorsorModel.zmod l,
    signUnitCompatibility := zmodSignUnitCompatibility l,
    signUnitSubgroup := zmodSignUnitSubgroup l,
    signUnitSubgroup_smul_eq_self_or_neg := by
      intro a ha x
      exact zmodSignUnitSubgroup_smul_eq_self_or_neg l ha x,
    signUnitSubgroup_orbit_iff_signOrbit := by
      intro x generator
      exact zmodSignUnitSubgroup_orbit_iff_signOrbit l x generator }

theorem signUnit_smul_eq_neg
    {l : PrimeGeFive}
    (model : IUTStage1FLZModUnitSignLabelModel l)
    (x : ZMod l.value) :
    (zmodUnitActionData l).smul model.signUnitCompatibility.signUnit x =
      (zmodSignAction l).neg x :=
  model.signUnitCompatibility.signUnit_smul_eq_neg x

theorem signUnitSubgroup_smul_eq_self_or_neg'
    {l : PrimeGeFive}
    (model : IUTStage1FLZModUnitSignLabelModel l)
    {a : (ZMod l.value)ˣ}
    (ha : a ∈ model.signUnitSubgroup)
    (x : ZMod l.value) :
    (zmodUnitActionData l).smul a x = x ∨
      (zmodUnitActionData l).smul a x = (zmodSignAction l).neg x :=
  model.signUnitSubgroup_smul_eq_self_or_neg ha x

theorem signUnitSubgroup_orbit_iff_signOrbit'
    {l : PrimeGeFive}
    (model : IUTStage1FLZModUnitSignLabelModel l)
    (x generator : ZMod l.value) :
    (∃ a : (ZMod l.value)ˣ,
      a ∈ model.signUnitSubgroup ∧
        (zmodUnitActionData l).smul a generator = x) ↔
      (zmodSignAction l).InSignOrbit x generator :=
  model.signUnitSubgroup_orbit_iff_signOrbit x generator

theorem zmod_signUnitSubgroup_orbit_iff_signOrbit
    (l : PrimeGeFive) (x generator : ZMod l.value) :
    (∃ a : (ZMod l.value)ˣ,
      a ∈ (zmod l).signUnitSubgroup ∧
        (zmodUnitActionData l).smul a generator = x) ↔
      (zmodSignAction l).InSignOrbit x generator :=
  (zmod l).signUnitSubgroup_orbit_iff_signOrbit' x generator

theorem unitSignLabelModel_endpoint
    {l : PrimeGeFive}
    (model : IUTStage1FLZModUnitSignLabelModel l)
    (x generator : ZMod l.value) :
    (zmodUnitActionData l).smul model.signUnitCompatibility.signUnit x =
        (zmodSignAction l).neg x ∧
      ((∃ a : (ZMod l.value)ˣ,
        a ∈ model.signUnitSubgroup ∧
          (zmodUnitActionData l).smul a generator = x) ↔
        (zmodSignAction l).InSignOrbit x generator) :=
  ⟨model.signUnit_smul_eq_neg x,
    model.signUnitSubgroup_orbit_iff_signOrbit' x generator⟩

end IUTStage1FLZModUnitSignLabelModel

/--
The canonical `F_l` label/cusp bridge at the `ZMod l` model.

This packages the Stage 1 unit/sign label bridge with the foundations
`LocalLabCuspModel` and its canonical `CuspLabelClassData`.
-/
structure IUTStage1FLZModCuspLabelClassModel
    (l : PrimeGeFive) where
  unit_sign_model : IUTStage1FLZModUnitSignLabelModel l
  local_lab_cusp_model : LocalLabCuspModel l
  local_lab_cusp_model_eq_zmod :
    local_lab_cusp_model = zmodLocalLabCuspModel l
  cusp_label_class_data : CuspLabelClassData l
  cusp_label_class_data_eq_zmod :
    cusp_label_class_data = zmodCanonicalCuspLabelClassData l

namespace IUTStage1FLZModCuspLabelClassModel

/-- The canonical `ZMod l` cusp-label bridge supplied by the foundations layer. -/
def zmod (l : PrimeGeFive) :
    IUTStage1FLZModCuspLabelClassModel l :=
  { unit_sign_model := IUTStage1FLZModUnitSignLabelModel.zmod l,
    local_lab_cusp_model := zmodLocalLabCuspModel l,
    local_lab_cusp_model_eq_zmod := rfl,
    cusp_label_class_data := zmodCanonicalCuspLabelClassData l,
    cusp_label_class_data_eq_zmod := rfl }

theorem localLabCuspModel_eq_zmod
    {l : PrimeGeFive}
    (model : IUTStage1FLZModCuspLabelClassModel l) :
    model.local_lab_cusp_model = zmodLocalLabCuspModel l :=
  model.local_lab_cusp_model_eq_zmod

theorem cuspLabelClassData_eq_zmod
    {l : PrimeGeFive}
    (model : IUTStage1FLZModCuspLabelClassModel l) :
    model.cusp_label_class_data = zmodCanonicalCuspLabelClassData l :=
  model.cusp_label_class_data_eq_zmod

theorem canonicalLabelTranslate
    {l : PrimeGeFive}
    (model : IUTStage1FLZModCuspLabelClassModel l) :
    model.local_lab_cusp_model.canonicalNonzeroLabel.1 =
      model.local_lab_cusp_model.additiveTorsor.vadd
        model.local_lab_cusp_model.canonicalCoordinate
        model.local_lab_cusp_model.labelQuotient.zero :=
  model.local_lab_cusp_model.canonicalLabelTranslate

theorem canonicalSignLabelEq
    {l : PrimeGeFive}
    (model : IUTStage1FLZModCuspLabelClassModel l) :
    model.local_lab_cusp_model.canonicalSignLabel =
      model.local_lab_cusp_model.signAction.toSignLabelQuotient
        model.local_lab_cusp_model.canonicalNonzeroLabel :=
  model.local_lab_cusp_model.canonicalSignLabelEq

theorem labelClass_eq_model_quotient
    {l : PrimeGeFive}
    (model : IUTStage1FLZModCuspLabelClassModel l) :
    model.cusp_label_class_data.labelClass =
      model.cusp_label_class_data.model.signAction.toSignLabelQuotient
        model.cusp_label_class_data.model.canonicalNonzeroLabel :=
  model.cusp_label_class_data.labelClass_eq_model_quotient

theorem zmod_canonicalSignLabel_eq
    (l : PrimeGeFive) :
    (zmod l).local_lab_cusp_model.canonicalSignLabel =
      zmodCanonicalSignLabelQuotient l :=
  rfl

theorem zmod_canonicalCoordinate_eq_one
    (l : PrimeGeFive) :
    (zmod l).local_lab_cusp_model.canonicalCoordinate =
      (1 : ZMod l.value) :=
  rfl

theorem zmod_canonicalSignLabel_eq_fromCoordinate_one
    (l : PrimeGeFive) :
    (zmod l).local_lab_cusp_model.canonicalSignLabel =
      zmodSignLabelFromCoordinate l (1 : ZMod l.value)
        (zmodOneNonzeroLabel l).2 := by
  calc
    (zmod l).local_lab_cusp_model.canonicalSignLabel =
        zmodCanonicalSignLabelQuotient l :=
      zmod_canonicalSignLabel_eq l
    _ = zmodSignLabelFromCoordinate l (1 : ZMod l.value)
          (zmodOneNonzeroLabel l).2 :=
      (zmodSignLabelFromCoordinate_one_eq_canonical l).symm

theorem zmod_cuspLabelClass_eq_canonical
    (l : PrimeGeFive) :
    (zmod l).cusp_label_class_data.labelClass =
      (zmod l).cusp_label_class_data.model.canonicalSignLabel :=
  (zmod l).cusp_label_class_data.labelClass_eq_canonical

theorem zmod_cuspLabelClass_eq_fromCoordinate_one
    (l : PrimeGeFive) :
    (zmod l).cusp_label_class_data.labelClass =
      zmodSignLabelFromCoordinate l (1 : ZMod l.value)
        (zmodOneNonzeroLabel l).2 := by
  calc
    (zmod l).cusp_label_class_data.labelClass =
        (zmod l).cusp_label_class_data.model.canonicalSignLabel :=
      zmod_cuspLabelClass_eq_canonical l
    _ = zmodSignLabelFromCoordinate l (1 : ZMod l.value)
          (zmodOneNonzeroLabel l).2 :=
      zmod_canonicalSignLabel_eq_fromCoordinate_one l

theorem cuspLabelClassModel_endpoint
    {l : PrimeGeFive}
    (model : IUTStage1FLZModCuspLabelClassModel l) :
    model.local_lab_cusp_model = zmodLocalLabCuspModel l ∧
      model.cusp_label_class_data = zmodCanonicalCuspLabelClassData l ∧
      model.local_lab_cusp_model.canonicalNonzeroLabel.1 =
        model.local_lab_cusp_model.additiveTorsor.vadd
          model.local_lab_cusp_model.canonicalCoordinate
          model.local_lab_cusp_model.labelQuotient.zero ∧
      model.local_lab_cusp_model.canonicalSignLabel =
        model.local_lab_cusp_model.signAction.toSignLabelQuotient
          model.local_lab_cusp_model.canonicalNonzeroLabel ∧
      model.cusp_label_class_data.labelClass =
        model.cusp_label_class_data.model.signAction.toSignLabelQuotient
          model.cusp_label_class_data.model.canonicalNonzeroLabel :=
  ⟨model.localLabCuspModel_eq_zmod,
    model.cuspLabelClassData_eq_zmod,
    model.canonicalLabelTranslate,
    model.canonicalSignLabelEq,
    model.labelClass_eq_model_quotient⟩

end IUTStage1FLZModCuspLabelClassModel

theorem zmod_toSignLabelQuotient_eq_fromCoordinate
    {l : PrimeGeFive}
    (x : (zmodPointedQuotient l).NonzeroCarrier) :
    (zmodSignAction l).toSignLabelQuotient x =
      zmodSignLabelFromCoordinate l x.1 x.2 := by
  apply Quotient.sound
  left
  exact (zmodNonzeroLabelFromCoordinate_val l x.1 x.2).symm

noncomputable instance zmodNonzeroCarrierFintype
    (l : PrimeGeFive) :
    Fintype (zmodPointedQuotient l).NonzeroCarrier := by
  classical
  unfold PointedEtaleQuotient.NonzeroCarrier zmodPointedQuotient
  infer_instance

instance zmodNonzeroCarrierNonempty
    (l : PrimeGeFive) :
    Nonempty (zmodPointedQuotient l).NonzeroCarrier :=
  ⟨zmodOneNonzeroLabel l⟩

theorem zmodNonzeroCarrier_card_eq
    (l : PrimeGeFive) :
    Fintype.card (zmodPointedQuotient l).NonzeroCarrier = l.value - 1 := by
  classical
  change Fintype.card {x : ZMod l.value // x ≠ 0} = l.value - 1
  rw [Fintype.card_subtype_compl (fun x : ZMod l.value => x = 0)]
  rw [Fintype.card_subtype_eq (0 : ZMod l.value), ZMod.card]

/--
The Stage 1 zero/nonzero cusp-label split for the concrete `F_l = ZMod l`
model.

The zero label is kept as its own constructor.  Nonzero labels enter only through
the sign-label quotient.
-/
inductive IUTStage1ZModCuspFullLabel (l : PrimeGeFive) where
  | zero
  | nonzero : (zmodSignAction l).SignLabelQuotient -> IUTStage1ZModCuspFullLabel l

namespace IUTStage1ZModCuspFullLabel

variable {l : PrimeGeFive}

def fromCoordinate (l : PrimeGeFive) (j : ZMod l.value) :
    IUTStage1ZModCuspFullLabel l :=
  if hj : j = 0 then
    zero
  else
    nonzero (zmodSignLabelFromCoordinate l j hj)

theorem fromCoordinate_zero (l : PrimeGeFive) :
    fromCoordinate l (0 : ZMod l.value) = zero := by
  simp [fromCoordinate]

theorem fromCoordinate_nonzero
    (l : PrimeGeFive) (j : ZMod l.value) (hj : j ≠ 0) :
    fromCoordinate l j = nonzero (zmodSignLabelFromCoordinate l j hj) := by
  simp [fromCoordinate, hj]

theorem fromCoordinate_one (l : PrimeGeFive) :
    fromCoordinate l (1 : ZMod l.value) =
      nonzero (zmodCanonicalSignLabelQuotient l) := by
  rw [fromCoordinate_nonzero l (1 : ZMod l.value) (zmodOneNonzeroLabel l).2]
  rw [zmodSignLabelFromCoordinate_one_eq_canonical]

theorem fromCoordinate_neg
    (l : PrimeGeFive) (j : ZMod l.value) (hj : j ≠ 0) :
    fromCoordinate l (-j) = fromCoordinate l j := by
  rw [fromCoordinate_nonzero l (-j) (zmod_neg_ne_zero_of_ne_zero l hj)]
  rw [fromCoordinate_nonzero l j hj]
  rw [zmodSignLabelFromCoordinate_neg_eq]

theorem fromCoordinate_eq_zero_iff
    (j : ZMod l.value) :
    fromCoordinate l j = IUTStage1ZModCuspFullLabel.zero ↔ j = 0 := by
  constructor
  · intro h
    by_cases hj : j = 0
    · exact hj
    · rw [fromCoordinate_nonzero l j hj] at h
      contradiction
  · intro h
    subst j
    rw [fromCoordinate_zero]

theorem fromCoordinate_ne_zero_iff
    (j : ZMod l.value) :
    fromCoordinate l j ≠ IUTStage1ZModCuspFullLabel.zero ↔ j ≠ 0 := by
  rw [ne_eq, ne_eq, fromCoordinate_eq_zero_iff]

theorem fromCoordinate_eq_iff
    (j k : ZMod l.value) :
    fromCoordinate l j = fromCoordinate l k ↔ j = k ∨ j = -k := by
  constructor
  · intro h
    by_cases hj : j = 0
    · subst j
      rw [fromCoordinate_zero] at h
      have hk : k = 0 :=
        (fromCoordinate_eq_zero_iff (l := l) k).mp h.symm
      exact Or.inl hk.symm
    · by_cases hk : k = 0
      · subst k
        rw [fromCoordinate_zero] at h
        have hj_zero : j = 0 :=
          (fromCoordinate_eq_zero_iff (l := l) j).mp h
        exact False.elim (hj hj_zero)
      · have hlabel :
            zmodSignLabelFromCoordinate l j hj =
              zmodSignLabelFromCoordinate l k hk := by
          simpa [fromCoordinate_nonzero l j hj,
            fromCoordinate_nonzero l k hk] using h
        unfold zmodSignLabelFromCoordinate at hlabel
        have hrel := Quotient.exact hlabel
        change
          (zmodSignAction l).InSignOrbit
            (zmodNonzeroLabelFromCoordinate l j hj).1
            (zmodNonzeroLabelFromCoordinate l k hk).1 at hrel
        rw [zmodNonzeroLabelFromCoordinate_val,
          zmodNonzeroLabelFromCoordinate_val] at hrel
        exact hrel
  · intro h
    rcases h with rfl | hneg
    · rfl
    · subst j
      by_cases hk : k = 0
      · subst k
        rw [neg_zero]
      · exact fromCoordinate_neg l k hk

theorem fromCoordinate_surjective :
    Function.Surjective (fromCoordinate l) := by
  intro label
  cases label with
  | zero =>
      exact ⟨0, fromCoordinate_zero l⟩
  | nonzero label =>
      refine Quotient.inductionOn label ?_
      intro x
      refine ⟨x.1, ?_⟩
      rw [fromCoordinate_nonzero l x.1 x.2]
      rw [← zmod_toSignLabelQuotient_eq_fromCoordinate x]
      rfl

theorem nonzero_fromCoordinate_surjective
    (label : (zmodSignAction l).SignLabelQuotient) :
    ∃ (j : ZMod l.value) (_hj : j ≠ 0),
      fromCoordinate l j = nonzero label := by
  refine Quotient.inductionOn label ?_
  intro x
  refine ⟨x.1, x.2, ?_⟩
  rw [fromCoordinate_nonzero l x.1 x.2]
  rw [← zmod_toSignLabelQuotient_eq_fromCoordinate x]
  rfl

theorem nonzero_fullLabel_fiber_eq_sign_pair
    (label : (zmodSignAction l).SignLabelQuotient) :
    ∃ (j : ZMod l.value) (_hj : j ≠ 0),
      ∀ k : ZMod l.value,
        fromCoordinate l k = nonzero label ↔ k = j ∨ k = -j := by
  refine Quotient.inductionOn label ?_
  intro x
  refine ⟨x.1, x.2, ?_⟩
  intro k
  have hxlabel :
      fromCoordinate l x.1 = nonzero ((zmodSignAction l).toSignLabelQuotient x) := by
    rw [fromCoordinate_nonzero l x.1 x.2]
    rw [← zmod_toSignLabelQuotient_eq_fromCoordinate x]
  constructor
  · intro hk
    have hsame : fromCoordinate l k = fromCoordinate l x.1 :=
      hk.trans hxlabel.symm
    exact (fromCoordinate_eq_iff (l := l) k x.1).mp hsame
  · intro hk
    have hsame : fromCoordinate l k = fromCoordinate l x.1 :=
      (fromCoordinate_eq_iff (l := l) k x.1).mpr hk
    exact hsame.trans hxlabel

theorem fromCoordinate_fullLabel_endpoint
    (j k : ZMod l.value) :
    fromCoordinate l (0 : ZMod l.value) = zero ∧
      fromCoordinate l (1 : ZMod l.value) =
        nonzero (zmodCanonicalSignLabelQuotient l) ∧
      (fromCoordinate l j = zero ↔ j = 0) ∧
      (fromCoordinate l j = fromCoordinate l k ↔ j = k ∨ j = -k) ∧
      Function.Surjective (fromCoordinate l) :=
  ⟨fromCoordinate_zero l,
    fromCoordinate_one l,
    fromCoordinate_eq_zero_iff j,
    fromCoordinate_eq_iff j k,
    fromCoordinate_surjective⟩

theorem fromCoordinate_natAbs_valMinAbs
    (j : ZMod l.value) :
    fromCoordinate l (j.valMinAbs.natAbs : ZMod l.value) =
      fromCoordinate l j := by
  rw [ZMod.natCast_natAbs_valMinAbs]
  split_ifs with hhalf
  · rfl
  · have hj : j ≠ 0 := by
      intro hj
      subst j
      exact hhalf (by simp)
    rw [fromCoordinate_neg l j hj]

def unitActionOnFullLabel
    (l : PrimeGeFive) (a : (ZMod l.value)ˣ) :
    IUTStage1ZModCuspFullLabel l -> IUTStage1ZModCuspFullLabel l
  | zero => zero
  | nonzero label =>
      nonzero (zmodUnitActionOnSignLabelQuotient l a label)

theorem unitActionOnFullLabel_zero
    (l : PrimeGeFive) (a : (ZMod l.value)ˣ) :
    unitActionOnFullLabel l a zero = zero :=
  rfl

theorem unitActionOnFullLabel_nonzero
    (l : PrimeGeFive) (a : (ZMod l.value)ˣ)
    (label : (zmodSignAction l).SignLabelQuotient) :
    unitActionOnFullLabel l a (nonzero label) =
      nonzero (zmodUnitActionOnSignLabelQuotient l a label) :=
  rfl

theorem unitActionOnFullLabel_fromCoordinate
    (l : PrimeGeFive) (a : (ZMod l.value)ˣ) (j : ZMod l.value) :
    unitActionOnFullLabel l a (fromCoordinate l j) =
      fromCoordinate l ((zmodUnitActionData l).smul a j) := by
  by_cases hj : j = 0
  · subst j
    rw [fromCoordinate_zero, unitActionOnFullLabel_zero]
    simp [zmodUnitActionData, fromCoordinate_zero]
  · have hsmul :
        (zmodUnitActionData l).smul a j ≠ 0 :=
      (zmodUnitActionData l).smul_nonzero a j hj
    rw [fromCoordinate_nonzero l j hj]
    rw [unitActionOnFullLabel_nonzero]
    rw [fromCoordinate_nonzero l ((zmodUnitActionData l).smul a j) hsmul]
    unfold zmodSignLabelFromCoordinate
    rw [zmodUnitActionOnSignLabelQuotient_apply]
    have hx :
        zmodUnitSmulNonzeroLabel l a (zmodNonzeroLabelFromCoordinate l j hj) =
          zmodNonzeroLabelFromCoordinate l
            ((zmodUnitActionData l).smul a j) hsmul := by
      apply Subtype.ext
      simp [zmodUnitSmulNonzeroLabel, zmodNonzeroLabelFromCoordinate,
        zmodLabelTranslate_eq_add]
    rw [hx]

theorem finiteSymmetrySplit_endpoint
    (l : PrimeGeFive)
    (t j k x generator : ZMod l.value)
    (a : (ZMod l.value)ˣ) :
    (IUTStage1FLLabelTorsorModel.zmod l).torsor.vadd t j =
        zmodLabelTranslate l t j ∧
      (zmodUnitActionData l).smul
          (IUTStage1FLZModUnitSignLabelModel.zmod l).signUnitCompatibility.signUnit
          x =
        (zmodSignAction l).neg x ∧
      ((∃ b : (ZMod l.value)ˣ,
        b ∈ (IUTStage1FLZModUnitSignLabelModel.zmod l).signUnitSubgroup ∧
          (zmodUnitActionData l).smul b generator = x) ↔
        (zmodSignAction l).InSignOrbit x generator) ∧
      (fromCoordinate l j = fromCoordinate l k ↔ j = k ∨ j = -k) ∧
      unitActionOnFullLabel l a (fromCoordinate l j) =
        fromCoordinate l ((zmodUnitActionData l).smul a j) :=
  ⟨IUTStage1FLLabelTorsorModel.zmod_vadd_eq_translate l t j,
    (IUTStage1FLZModUnitSignLabelModel.zmod l).signUnit_smul_eq_neg x,
    (IUTStage1FLZModUnitSignLabelModel.zmod l).signUnitSubgroup_orbit_iff_signOrbit'
      x generator,
    fromCoordinate_eq_iff j k,
    unitActionOnFullLabel_fromCoordinate l a j⟩

theorem unitActionOnFullLabel_one
    (l : PrimeGeFive) (label : IUTStage1ZModCuspFullLabel l) :
    unitActionOnFullLabel l 1 label = label := by
  cases label with
  | zero => rfl
  | nonzero label =>
      rw [unitActionOnFullLabel_nonzero,
        zmodUnitActionOnSignLabelQuotient_one]

theorem unitActionOnFullLabel_mul
    (l : PrimeGeFive) (a b : (ZMod l.value)ˣ)
    (label : IUTStage1ZModCuspFullLabel l) :
    unitActionOnFullLabel l (a * b) label =
      unitActionOnFullLabel l a (unitActionOnFullLabel l b label) := by
  cases label with
  | zero => rfl
  | nonzero label =>
      rw [unitActionOnFullLabel_nonzero, unitActionOnFullLabel_nonzero,
        unitActionOnFullLabel_nonzero,
        zmodUnitActionOnSignLabelQuotient_mul]

theorem unitActionOnFullLabel_signSubgroup_trivial
    (l : PrimeGeFive) {a : (ZMod l.value)ˣ}
    (ha : a ∈ zmodSignUnitSubgroup l)
    (label : IUTStage1ZModCuspFullLabel l) :
    unitActionOnFullLabel l a label = label := by
  cases label with
  | zero => rfl
  | nonzero label =>
      rw [unitActionOnFullLabel_nonzero]
      rw [zmodSignUnitSubgroup_action_trivial_on_signLabelQuotient l ha label]

theorem unitActionOnFullLabel_inv_mul
    (l : PrimeGeFive) (a : (ZMod l.value)ˣ)
    (label : IUTStage1ZModCuspFullLabel l) :
    unitActionOnFullLabel l a⁻¹ (unitActionOnFullLabel l a label) =
      label := by
  rw [← unitActionOnFullLabel_mul]
  rw [inv_mul_cancel]
  exact unitActionOnFullLabel_one l label

theorem unitActionOnFullLabel_mul_inv
    (l : PrimeGeFive) (a : (ZMod l.value)ˣ)
    (label : IUTStage1ZModCuspFullLabel l) :
    unitActionOnFullLabel l a (unitActionOnFullLabel l a⁻¹ label) =
      label := by
  rw [← unitActionOnFullLabel_mul]
  rw [mul_inv_cancel]
  exact unitActionOnFullLabel_one l label

noncomputable def unitActionOnFullLabelEquiv
    (l : PrimeGeFive) (a : (ZMod l.value)ˣ) :
    IUTStage1ZModCuspFullLabel l ≃ IUTStage1ZModCuspFullLabel l where
  toFun := unitActionOnFullLabel l a
  invFun := unitActionOnFullLabel l a⁻¹
  left_inv := unitActionOnFullLabel_inv_mul l a
  right_inv := unitActionOnFullLabel_mul_inv l a

theorem unitActionOnFullLabelEquiv_apply
    (l : PrimeGeFive) (a : (ZMod l.value)ˣ)
    (label : IUTStage1ZModCuspFullLabel l) :
    unitActionOnFullLabelEquiv l a label =
      unitActionOnFullLabel l a label :=
  rfl

theorem unitActionOnFullLabel_eq_zero_iff
    (l : PrimeGeFive) (a : (ZMod l.value)ˣ)
    (label : IUTStage1ZModCuspFullLabel l) :
    unitActionOnFullLabel l a label =
        IUTStage1ZModCuspFullLabel.zero ↔
      label = IUTStage1ZModCuspFullLabel.zero := by
  cases label <;> simp [unitActionOnFullLabel]

theorem two_ne_zero (l : PrimeGeFive) :
    (2 : ZMod l.value) ≠ 0 := by
  intro hzero
  have hzero' : ((2 : Nat) : ZMod l.value) = 0 := by
    simpa using hzero
  rw [ZMod.natCast_eq_zero_iff] at hzero'
  have hle : l.value ≤ 2 := Nat.le_of_dvd (by norm_num) hzero'
  have hge : 5 ≤ l.value := l.ge_five
  omega

theorem two_mul_ne_zero_of_ne_zero
    (l : PrimeGeFive) (t : ZMod l.value) (ht : t ≠ 0) :
    (2 : ZMod l.value) * t ≠ 0 := by
  haveI : Fact l.value.Prime := ⟨l.prime⟩
  exact mul_ne_zero (two_ne_zero l) ht

theorem nonzero_fullLabel_fiber_card
    (label : (zmodSignAction l).SignLabelQuotient) :
    (@Finset.filter (ZMod l.value)
      (fun k : ZMod l.value => fromCoordinate l k = nonzero label)
      (Classical.decPred _) Finset.univ).card = 2 := by
  classical
  rcases nonzero_fullLabel_fiber_eq_sign_pair (l := l) label with
    ⟨j, hj, hfiber⟩
  have hnot_neg : j ≠ -j := by
    intro h
    have hsum : j + j = 0 := by
      have hrewrite : j + j = j + -j := congrArg (fun x => j + x) h
      rw [hrewrite]
      simp
    have htwo : (2 : ZMod l.value) * j = 0 := by
      rw [show (2 : ZMod l.value) * j = j + j by ring, hsum]
    exact two_mul_ne_zero_of_ne_zero l j hj htwo
  have hset :
      (@Finset.filter (ZMod l.value)
        (fun k : ZMod l.value => fromCoordinate l k = nonzero label)
        (Classical.decPred _) Finset.univ) =
        ({j, -j} : Finset (ZMod l.value)) := by
    ext k
    simp [hfiber k]
  rw [hset]
  simp [hnot_neg]

theorem zero_fullLabel_fiber_card :
    (@Finset.filter (ZMod l.value)
      (fun k : ZMod l.value => fromCoordinate l k = zero)
      (Classical.decPred _) Finset.univ).card = 1 := by
  classical
  have hset :
      (@Finset.filter (ZMod l.value)
        (fun k : ZMod l.value => fromCoordinate l k = zero)
        (Classical.decPred _) Finset.univ) =
        ({0} : Finset (ZMod l.value)) := by
    ext k
    simp [fromCoordinate_eq_zero_iff]
  rw [hset]
  simp

theorem no_fullLabel_map_descends_nonzero_translation
    (l : PrimeGeFive) (t : ZMod l.value) (ht : t ≠ 0) :
    ¬ ∃ T : IUTStage1ZModCuspFullLabel l -> IUTStage1ZModCuspFullLabel l,
      ∀ j : ZMod l.value,
        T (fromCoordinate l j) =
          fromCoordinate l (zmodLabelTranslate l t j) := by
  rintro ⟨T, hT⟩
  have hsame :
      fromCoordinate l (-t) = fromCoordinate l t :=
    fromCoordinate_neg l t ht
  have hneg := hT (-t)
  have hpos := hT t
  rw [hsame] at hneg
  have htranslated :
      fromCoordinate l (zmodLabelTranslate l t (-t)) =
        fromCoordinate l (zmodLabelTranslate l t t) := by
    rw [← hneg, hpos]
  rw [zmodLabelTranslate_eq_add, zmodLabelTranslate_eq_add] at htranslated
  rw [add_neg_cancel] at htranslated
  have hdouble : t + t = (2 : ZMod l.value) * t := by ring
  rw [hdouble] at htranslated
  rw [fromCoordinate_zero] at htranslated
  have htwo_zero :
      (2 : ZMod l.value) * t = 0 := by
    exact (fromCoordinate_eq_zero_iff
      (l := l) ((2 : ZMod l.value) * t)).mp htranslated.symm
  exact two_mul_ne_zero_of_ne_zero l t ht htwo_zero

theorem no_fullLabel_map_descends_translation_one
    (l : PrimeGeFive) :
    ¬ ∃ T : IUTStage1ZModCuspFullLabel l -> IUTStage1ZModCuspFullLabel l,
      ∀ j : ZMod l.value,
        T (fromCoordinate l j) =
          fromCoordinate l (zmodLabelTranslate l (1 : ZMod l.value) j) := by
  exact no_fullLabel_map_descends_nonzero_translation l
    (1 : ZMod l.value) (zmodOneNonzeroLabel l).2

theorem fullLabel_map_descends_zero_translation
    (l : PrimeGeFive) :
    ∃ T : IUTStage1ZModCuspFullLabel l -> IUTStage1ZModCuspFullLabel l,
      ∀ j : ZMod l.value,
        T (fromCoordinate l j) =
          fromCoordinate l (zmodLabelTranslate l (0 : ZMod l.value) j) := by
  refine ⟨id, ?_⟩
  intro j
  rw [zmodLabelTranslate_zero]
  rfl

theorem fullLabel_map_descends_translation_iff
    (l : PrimeGeFive) (t : ZMod l.value) :
    (∃ T : IUTStage1ZModCuspFullLabel l -> IUTStage1ZModCuspFullLabel l,
      ∀ j : ZMod l.value,
        T (fromCoordinate l j) =
          fromCoordinate l (zmodLabelTranslate l t j)) ↔
      t = 0 := by
  constructor
  · intro hdesc
    by_contra ht
    exact no_fullLabel_map_descends_nonzero_translation l t ht hdesc
  · intro ht
    subst t
    exact fullLabel_map_descends_zero_translation l

theorem fullLabel_map_descends_unitAffine_iff_zero_translation
    (l : PrimeGeFive) (a : (ZMod l.value)ˣ) (t : ZMod l.value) :
    (∃ T : IUTStage1ZModCuspFullLabel l -> IUTStage1ZModCuspFullLabel l,
      ∀ j : ZMod l.value,
        T (fromCoordinate l j) =
          fromCoordinate l
            (zmodLabelTranslate l t ((zmodUnitActionData l).smul a j))) ↔
      t = 0 := by
  constructor
  · rintro ⟨T, hT⟩
    have htrans :
        ∃ S : IUTStage1ZModCuspFullLabel l -> IUTStage1ZModCuspFullLabel l,
          ∀ k : ZMod l.value,
            S (fromCoordinate l k) =
              fromCoordinate l (zmodLabelTranslate l t k) := by
      refine ⟨fun label => T (unitActionOnFullLabel l a⁻¹ label), ?_⟩
      intro k
      change T (unitActionOnFullLabel l a⁻¹ (fromCoordinate l k)) =
        fromCoordinate l (zmodLabelTranslate l t k)
      rw [unitActionOnFullLabel_fromCoordinate]
      rw [hT]
      congr 1
      simp [zmodLabelTranslate_eq_add, zmodUnitActionData]
    exact (fullLabel_map_descends_translation_iff l t).mp htrans
  · intro ht
    subst t
    refine ⟨unitActionOnFullLabel l a, ?_⟩
    intro j
    rw [zmodLabelTranslate_zero]
    exact unitActionOnFullLabel_fromCoordinate l a j

theorem no_fullLabel_map_descends_unitAffine_nonzero_translation
    (l : PrimeGeFive) (a : (ZMod l.value)ˣ)
    {t : ZMod l.value} (ht : t ≠ 0) :
    ¬ ∃ T : IUTStage1ZModCuspFullLabel l -> IUTStage1ZModCuspFullLabel l,
      ∀ j : ZMod l.value,
        T (fromCoordinate l j) =
          fromCoordinate l
            (zmodLabelTranslate l t ((zmodUnitActionData l).smul a j)) := by
  intro hdesc
  exact ht
    ((fullLabel_map_descends_unitAffine_iff_zero_translation l a t).mp hdesc)

theorem unitActionAndAffineDescent_endpoint
    (l : PrimeGeFive) (a b : (ZMod l.value)ˣ) (t j : ZMod l.value)
    (label : IUTStage1ZModCuspFullLabel l) :
    unitActionOnFullLabel l 1 label = label ∧
      unitActionOnFullLabel l (a * b) label =
        unitActionOnFullLabel l a (unitActionOnFullLabel l b label) ∧
      unitActionOnFullLabel l a (fromCoordinate l j) =
        fromCoordinate l ((zmodUnitActionData l).smul a j) ∧
      (unitActionOnFullLabel l a label = zero ↔ label = zero) ∧
      ((∃ T : IUTStage1ZModCuspFullLabel l -> IUTStage1ZModCuspFullLabel l,
        ∀ k : ZMod l.value,
          T (fromCoordinate l k) =
            fromCoordinate l
              (zmodLabelTranslate l t ((zmodUnitActionData l).smul a k))) ↔
        t = 0) :=
  ⟨unitActionOnFullLabel_one l label,
    unitActionOnFullLabel_mul l a b label,
    unitActionOnFullLabel_fromCoordinate l a j,
    unitActionOnFullLabel_eq_zero_iff l a label,
    fullLabel_map_descends_unitAffine_iff_zero_translation l a t⟩

/--
Stage 1 shadow of the weighted-volume relation `F_l ∋ j ≪ 0` from IUT II,
Remark 4.7.3(iii).

The relation is intentionally not symmetric: nonzero Gaussian components are
subordinate to the zero/coric label, while the zero label is not subordinate to
itself.
-/
def WeightedVolumeSubordinate :
    IUTStage1ZModCuspFullLabel l -> IUTStage1ZModCuspFullLabel l -> Prop
  | nonzero _, zero => True
  | _, _ => False

theorem nonzero_weightedVolumeSubordinate_zero
    (label : (zmodSignAction l).SignLabelQuotient) :
    WeightedVolumeSubordinate
      (IUTStage1ZModCuspFullLabel.nonzero label)
      IUTStage1ZModCuspFullLabel.zero :=
  trivial

theorem not_zero_weightedVolumeSubordinate_zero :
    ¬ WeightedVolumeSubordinate
      (l := l) IUTStage1ZModCuspFullLabel.zero
      IUTStage1ZModCuspFullLabel.zero := by
  intro h
  exact h

theorem not_zero_weightedVolumeSubordinate_nonzero
    (label : (zmodSignAction l).SignLabelQuotient) :
    ¬ WeightedVolumeSubordinate
      (l := l) IUTStage1ZModCuspFullLabel.zero
      (IUTStage1ZModCuspFullLabel.nonzero label) := by
  intro h
  exact h

theorem not_weightedVolumeSubordinate_symmetric_at_nonzero_zero
    (label : (zmodSignAction l).SignLabelQuotient) :
    ¬ (WeightedVolumeSubordinate
          (IUTStage1ZModCuspFullLabel.nonzero label)
          IUTStage1ZModCuspFullLabel.zero ->
        WeightedVolumeSubordinate
          (l := l) IUTStage1ZModCuspFullLabel.zero
          (IUTStage1ZModCuspFullLabel.nonzero label)) := by
  intro hsym
  exact not_zero_weightedVolumeSubordinate_nonzero label
    (hsym (nonzero_weightedVolumeSubordinate_zero label))

theorem weightedVolumeSubordinate_zero_iff_ne_zero
    (label : IUTStage1ZModCuspFullLabel l) :
    WeightedVolumeSubordinate label IUTStage1ZModCuspFullLabel.zero ↔
      label ≠ IUTStage1ZModCuspFullLabel.zero := by
  cases label <;> simp [WeightedVolumeSubordinate]

theorem unitActionOnFullLabel_preserves_subordinate_zero
    (l : PrimeGeFive) (a : (ZMod l.value)ˣ)
    (label : IUTStage1ZModCuspFullLabel l) :
    WeightedVolumeSubordinate
        (unitActionOnFullLabel l a label)
        IUTStage1ZModCuspFullLabel.zero ↔
      WeightedVolumeSubordinate label IUTStage1ZModCuspFullLabel.zero := by
  cases label <;> simp [unitActionOnFullLabel, WeightedVolumeSubordinate]

theorem fromCoordinate_nonzero_weightedVolumeSubordinate_zero
    (l : PrimeGeFive) (j : ZMod l.value) (hj : j ≠ 0) :
    WeightedVolumeSubordinate
      (fromCoordinate l j) IUTStage1ZModCuspFullLabel.zero := by
  rw [fromCoordinate_nonzero l j hj]
  exact nonzero_weightedVolumeSubordinate_zero
    (zmodSignLabelFromCoordinate l j hj)

theorem fromCoordinate_weightedVolumeSubordinate_zero_iff
    (l : PrimeGeFive) (j : ZMod l.value) :
    WeightedVolumeSubordinate
        (fromCoordinate l j) IUTStage1ZModCuspFullLabel.zero ↔
      j ≠ 0 := by
  rw [weightedVolumeSubordinate_zero_iff_ne_zero]
  exact fromCoordinate_ne_zero_iff j

theorem unit_smul_fromCoordinate_weightedVolumeSubordinate_zero_iff
    (l : PrimeGeFive) (a : (ZMod l.value)ˣ) (j : ZMod l.value) :
    WeightedVolumeSubordinate
        (fromCoordinate l ((zmodUnitActionData l).smul a j))
        IUTStage1ZModCuspFullLabel.zero ↔
      WeightedVolumeSubordinate
        (fromCoordinate l j) IUTStage1ZModCuspFullLabel.zero := by
  rw [← unitActionOnFullLabel_fromCoordinate l a j]
  exact unitActionOnFullLabel_preserves_subordinate_zero l a
    (fromCoordinate l j)

theorem translation_fromCoordinate_weightedVolumeSubordinate_zero_iff_zero
    (l : PrimeGeFive) (t : ZMod l.value) :
    (∀ j : ZMod l.value,
      WeightedVolumeSubordinate
          (fromCoordinate l (zmodLabelTranslate l t j))
          IUTStage1ZModCuspFullLabel.zero ↔
        WeightedVolumeSubordinate
          (fromCoordinate l j) IUTStage1ZModCuspFullLabel.zero) ↔
      t = 0 := by
  constructor
  · intro hpres
    have hzero := hpres 0
    have hzero' :
        WeightedVolumeSubordinate
            (fromCoordinate l t) IUTStage1ZModCuspFullLabel.zero ↔
          WeightedVolumeSubordinate
            (fromCoordinate l (0 : ZMod l.value))
            IUTStage1ZModCuspFullLabel.zero := by
      simpa [zmodLabelTranslate_eq_add] using hzero
    have hzero_not :
        ¬ WeightedVolumeSubordinate
            (fromCoordinate l (0 : ZMod l.value))
            IUTStage1ZModCuspFullLabel.zero := by
      rw [fromCoordinate_weightedVolumeSubordinate_zero_iff]
      simp
    have ht_not :
        ¬ WeightedVolumeSubordinate
            (fromCoordinate l t) IUTStage1ZModCuspFullLabel.zero := by
      intro htSub
      exact hzero_not (hzero'.mp htSub)
    by_contra ht
    exact ht_not
      ((fromCoordinate_weightedVolumeSubordinate_zero_iff l t).mpr ht)
  · intro ht j
    subst t
    rw [zmodLabelTranslate_zero]

theorem nonzero_translation_not_preserves_fromCoordinate_weightedVolumeSubordinate_zero
    (l : PrimeGeFive) {t : ZMod l.value} (ht : t ≠ 0) :
    ¬ ∀ j : ZMod l.value,
      WeightedVolumeSubordinate
          (fromCoordinate l (zmodLabelTranslate l t j))
          IUTStage1ZModCuspFullLabel.zero ↔
        WeightedVolumeSubordinate
          (fromCoordinate l j) IUTStage1ZModCuspFullLabel.zero := by
  intro hpres
  exact ht
    ((translation_fromCoordinate_weightedVolumeSubordinate_zero_iff_zero
      l t).mp hpres)

theorem unitAffine_fromCoordinate_weightedVolumeSubordinate_zero_iff_zero_translation
    (l : PrimeGeFive) (a : (ZMod l.value)ˣ) (t : ZMod l.value) :
    (∀ j : ZMod l.value,
      WeightedVolumeSubordinate
          (fromCoordinate l
            (zmodLabelTranslate l t ((zmodUnitActionData l).smul a j)))
          IUTStage1ZModCuspFullLabel.zero ↔
        WeightedVolumeSubordinate
          (fromCoordinate l j) IUTStage1ZModCuspFullLabel.zero) ↔
      t = 0 := by
  constructor
  · intro hpres
    have hzero := hpres 0
    have hzero' :
        WeightedVolumeSubordinate
            (fromCoordinate l t) IUTStage1ZModCuspFullLabel.zero ↔
          WeightedVolumeSubordinate
            (fromCoordinate l (0 : ZMod l.value))
            IUTStage1ZModCuspFullLabel.zero := by
      simpa [zmodLabelTranslate_eq_add, zmodUnitActionData] using hzero
    have hzero_not :
        ¬ WeightedVolumeSubordinate
            (fromCoordinate l (0 : ZMod l.value))
            IUTStage1ZModCuspFullLabel.zero := by
      rw [fromCoordinate_weightedVolumeSubordinate_zero_iff]
      simp
    have ht_not :
        ¬ WeightedVolumeSubordinate
            (fromCoordinate l t) IUTStage1ZModCuspFullLabel.zero := by
      intro htSub
      exact hzero_not (hzero'.mp htSub)
    by_contra ht
    exact ht_not
      ((fromCoordinate_weightedVolumeSubordinate_zero_iff l t).mpr ht)
  · intro ht j
    subst t
    rw [zmodLabelTranslate_zero]
    exact unit_smul_fromCoordinate_weightedVolumeSubordinate_zero_iff l a j

theorem not_forall_coordinate_weightedVolumeSubordinate_zero
    (l : PrimeGeFive) :
    ¬ ∀ j : ZMod l.value,
        WeightedVolumeSubordinate
          (fromCoordinate l j) IUTStage1ZModCuspFullLabel.zero := by
  intro hall
  have hzero := hall (0 : ZMod l.value)
  rw [fromCoordinate_zero] at hzero
  exact not_zero_weightedVolumeSubordinate_zero hzero

theorem weightedVolumeSubordinate_endpoint
    (l : PrimeGeFive) (a : (ZMod l.value)ˣ) (t j : ZMod l.value)
    (label : IUTStage1ZModCuspFullLabel l) :
    (WeightedVolumeSubordinate label zero ↔ label ≠ zero) ∧
      (WeightedVolumeSubordinate (fromCoordinate l j) zero ↔ j ≠ 0) ∧
      (WeightedVolumeSubordinate
          (fromCoordinate l ((zmodUnitActionData l).smul a j)) zero ↔
        WeightedVolumeSubordinate (fromCoordinate l j) zero) ∧
      ((∀ k : ZMod l.value,
        WeightedVolumeSubordinate
            (fromCoordinate l
              (zmodLabelTranslate l t ((zmodUnitActionData l).smul a k)))
            zero ↔
          WeightedVolumeSubordinate (fromCoordinate l k) zero) ↔
        t = 0) ∧
      ¬ ∀ k : ZMod l.value,
        WeightedVolumeSubordinate (fromCoordinate l k) zero :=
  ⟨weightedVolumeSubordinate_zero_iff_ne_zero label,
    fromCoordinate_weightedVolumeSubordinate_zero_iff l j,
    unit_smul_fromCoordinate_weightedVolumeSubordinate_zero_iff l a j,
    unitAffine_fromCoordinate_weightedVolumeSubordinate_zero_iff_zero_translation
      l a t,
    not_forall_coordinate_weightedVolumeSubordinate_zero l⟩

def localObject
    {kind : IUTStage1PlaceKind}
    (zeroObject : IUTStage1FiniteLocalLogVolumeObject kind)
    (cuspClassObject :
      (zmodSignAction l).SignLabelQuotient ->
        IUTStage1FiniteLocalLogVolumeObject kind) :
    IUTStage1ZModCuspFullLabel l ->
      IUTStage1FiniteLocalLogVolumeObject kind
  | zero => zeroObject
  | nonzero label => cuspClassObject label

theorem localObject_zero
    {kind : IUTStage1PlaceKind}
    (zeroObject : IUTStage1FiniteLocalLogVolumeObject kind)
    (cuspClassObject :
      (zmodSignAction l).SignLabelQuotient ->
        IUTStage1FiniteLocalLogVolumeObject kind) :
    localObject zeroObject cuspClassObject zero = zeroObject :=
  rfl

theorem localObject_nonzero
    {kind : IUTStage1PlaceKind}
    (zeroObject : IUTStage1FiniteLocalLogVolumeObject kind)
    (cuspClassObject :
      (zmodSignAction l).SignLabelQuotient ->
        IUTStage1FiniteLocalLogVolumeObject kind)
    (label : (zmodSignAction l).SignLabelQuotient) :
    localObject zeroObject cuspClassObject (nonzero label) =
      cuspClassObject label :=
  rfl

theorem localObject_fromCoordinate_zero
    {kind : IUTStage1PlaceKind}
    (zeroObject : IUTStage1FiniteLocalLogVolumeObject kind)
    (cuspClassObject :
      (zmodSignAction l).SignLabelQuotient ->
        IUTStage1FiniteLocalLogVolumeObject kind) :
    localObject zeroObject cuspClassObject (fromCoordinate l (0 : ZMod l.value)) =
      zeroObject := by
  rw [fromCoordinate_zero]
  rfl

theorem localObject_fromCoordinate_nonzero
    {kind : IUTStage1PlaceKind}
    (zeroObject : IUTStage1FiniteLocalLogVolumeObject kind)
    (cuspClassObject :
      (zmodSignAction l).SignLabelQuotient ->
        IUTStage1FiniteLocalLogVolumeObject kind)
    (j : ZMod l.value) (hj : j ≠ 0) :
    localObject zeroObject cuspClassObject (fromCoordinate l j) =
      cuspClassObject (zmodSignLabelFromCoordinate l j hj) := by
  rw [fromCoordinate_nonzero l j hj]
  rfl

theorem localObject_fromCoordinate_neg_eq
    {kind : IUTStage1PlaceKind}
    (zeroObject : IUTStage1FiniteLocalLogVolumeObject kind)
    (cuspClassObject :
      (zmodSignAction l).SignLabelQuotient ->
        IUTStage1FiniteLocalLogVolumeObject kind)
    (j : ZMod l.value) (hj : j ≠ 0) :
    localObject zeroObject cuspClassObject (fromCoordinate l (-j)) =
      localObject zeroObject cuspClassObject (fromCoordinate l j) := by
  rw [fromCoordinate_neg l j hj]

theorem localObject_endpoint
    {kind : IUTStage1PlaceKind}
    (zeroObject : IUTStage1FiniteLocalLogVolumeObject kind)
    (cuspClassObject :
      (zmodSignAction l).SignLabelQuotient ->
        IUTStage1FiniteLocalLogVolumeObject kind)
    (j : ZMod l.value) (hj : j ≠ 0) :
    localObject zeroObject cuspClassObject zero = zeroObject ∧
      localObject zeroObject cuspClassObject
          (fromCoordinate l (0 : ZMod l.value)) = zeroObject ∧
      localObject zeroObject cuspClassObject (fromCoordinate l j) =
        cuspClassObject (zmodSignLabelFromCoordinate l j hj) ∧
      localObject zeroObject cuspClassObject (fromCoordinate l (-j)) =
        localObject zeroObject cuspClassObject (fromCoordinate l j) :=
  ⟨localObject_zero zeroObject cuspClassObject,
    localObject_fromCoordinate_zero zeroObject cuspClassObject,
    localObject_fromCoordinate_nonzero zeroObject cuspClassObject j hj,
    localObject_fromCoordinate_neg_eq zeroObject cuspClassObject j hj⟩

end IUTStage1ZModCuspFullLabel

/--
Stage 1 source package connecting the IUT I bad-local theta-root data to the
`|F_l|` full-label model used by the Corollary 3.12 corridor.

IUT I, Definition 3.1(e),(f), supplies at a bad place local theta-root models
of type `(1,(Z/lZ)_Theta)` and `(1,(Z/lZ)_Theta)^±`, together with the
condition that the local cusp comes from the canonical generator, up to sign, of
the quotient `Z`.  This package uses the quotient-`Z` coordinate carried by
`BadLocalThetaRootData` to produce the Stage 1 zero/nonzero full label.
-/
structure IUTStage1ThetaRootCuspLabelSourcePackage
    (l : PrimeGeFive) {F : Type u} [Field F]
    (X C : HyperbolicOrbicurveModel F) where
  thetaRootData : BadLocalThetaRootData l X C

namespace IUTStage1ThetaRootCuspLabelSourcePackage

variable {l : PrimeGeFive} {F : Type u} [Field F]
variable {X C : HyperbolicOrbicurveModel F}
variable (package : IUTStage1ThetaRootCuspLabelSourcePackage l X C)

def quotientZData : BadLocalQuotientZData l :=
  package.thetaRootData.quotientZData

def localLabCuspModel : LocalLabCuspModel l :=
  package.quotientZData.toLocalLabCuspModel

def cuspLabelClassData : CuspLabelClassData l :=
  CuspLabelClassData.canonical package.localLabCuspModel

def canonicalGenerator : CanonicalGeneratorUpToSignElement :=
  package.quotientZData.canonicalGeneratorUpToSignElement

def canonicalCoordinate : ZMod l.value :=
  package.quotientZData.canonicalCoordinateZ

theorem canonicalCoordinate_ne_zero :
    package.canonicalCoordinate ≠ 0 :=
  package.quotientZData.canonicalCoordinateZ_ne_zero

def canonicalFullLabel : IUTStage1ZModCuspFullLabel l :=
  IUTStage1ZModCuspFullLabel.fromCoordinate l package.canonicalCoordinate

theorem quotientZData_constructedFromThetaRoot :
    package.thetaRootData.quotientZData_constructedFromThetaRoot :=
  package.thetaRootData.quotientZDataSource

theorem thetaRootXType_holds :
    package.thetaRootData.thetaRootXType.hasType :=
  package.thetaRootData.thetaRootXType_holds

theorem thetaRootCType_holds :
    package.thetaRootData.thetaRootCType.hasType :=
  package.thetaRootData.thetaRootCType_holds

theorem canonicalGeneratorUpToSign :
    package.canonicalGenerator.canonicalGeneratorUpToSign :=
  package.quotientZData.canonicalGeneratorUpToSign

theorem localLabCuspModel_eq_quotientZ :
    package.localLabCuspModel =
      package.thetaRootData.quotientZData.toLocalLabCuspModel :=
  rfl

theorem cuspLabelClass_eq_model_canonical :
    package.cuspLabelClassData.labelClass =
      package.localLabCuspModel.canonicalSignLabel :=
  rfl

theorem cuspLabelClass_eq_model_quotient :
    package.cuspLabelClassData.labelClass =
      package.localLabCuspModel.signAction.toSignLabelQuotient
        package.localLabCuspModel.canonicalNonzeroLabel :=
  CuspLabelClassData.labelClass_eq_model_quotient package.cuspLabelClassData

theorem canonicalFullLabel_eq_nonzero :
    package.canonicalFullLabel =
      IUTStage1ZModCuspFullLabel.nonzero
        (zmodSignLabelFromCoordinate l package.canonicalCoordinate
          package.canonicalCoordinate_ne_zero) := by
  rw [canonicalFullLabel]
  exact
    IUTStage1ZModCuspFullLabel.fromCoordinate_nonzero
      l package.canonicalCoordinate package.canonicalCoordinate_ne_zero

theorem canonicalFullLabel_ne_zero :
    package.canonicalFullLabel ≠ IUTStage1ZModCuspFullLabel.zero := by
  rw [canonicalFullLabel,
    IUTStage1ZModCuspFullLabel.fromCoordinate_ne_zero_iff]
  exact package.canonicalCoordinate_ne_zero

/--
The concrete `ZMod l` quotient-`Z` case gives the canonical nonzero full label.

This is the point at which the abstract bad-local theta-root package feeds the
Stage 1 `|F_l|` label model: once its quotient-`Z` data is the concrete
`ZMod l` package, the canonical generator up to sign maps to the full label
coming from coordinate `1`.
-/
theorem canonicalFullLabel_eq_zmodCanonical_of_quotientZData_eq_zmod
    (hquot : package.quotientZData = zmodBadLocalQuotientZData l) :
    package.canonicalFullLabel =
      IUTStage1ZModCuspFullLabel.nonzero
        (zmodCanonicalSignLabelQuotient l) := by
  have hcoord : package.canonicalCoordinate = (1 : ZMod l.value) := by
    change package.quotientZData.canonicalCoordinateZ = (1 : ZMod l.value)
    rw [hquot]
    rfl
  rw [canonicalFullLabel, hcoord]
  exact IUTStage1ZModCuspFullLabel.fromCoordinate_one l

theorem thetaRootCuspLabelSource_endpoint :
    package.thetaRootData.quotientZData_constructedFromThetaRoot ∧
      package.canonicalGenerator.canonicalGeneratorUpToSign ∧
      package.canonicalFullLabel ≠ IUTStage1ZModCuspFullLabel.zero ∧
      package.cuspLabelClassData.labelClass =
        package.localLabCuspModel.signAction.toSignLabelQuotient
          package.localLabCuspModel.canonicalNonzeroLabel :=
  ⟨package.quotientZData_constructedFromThetaRoot,
    package.canonicalGeneratorUpToSign,
    package.canonicalFullLabel_ne_zero,
    package.cuspLabelClass_eq_model_quotient⟩

def ofBadLocalOrbicurveTypeData
    (typeData : BadLocalOrbicurveTypeData l X C) :
    IUTStage1ThetaRootCuspLabelSourcePackage l X C :=
  { thetaRootData := typeData.thetaRootData }

theorem ofBadLocalOrbicurveTypeData_canonicalGenerator_eq
    (typeData : BadLocalOrbicurveTypeData l X C) :
    (ofBadLocalOrbicurveTypeData typeData).canonicalGenerator =
      typeData.canonicalGenerator := by
  rw [canonicalGenerator, quotientZData, ofBadLocalOrbicurveTypeData]
  exact typeData.canonicalGeneratorEqModel.symm

end IUTStage1ThetaRootCuspLabelSourcePackage

/--
Compatibility between a `ZMod l`-indexed normalized log-volume family and a
description by nonzero cusp sign-label classes.

The zero label is recorded separately because the sign-label quotient in the
foundations layer is defined on nonzero labels.
-/
structure IUTStage1ZModCuspLabelLogVolumeCompatibility
    (l : PrimeGeFive) where
  normalizedLogVolume : ZMod l.value -> Real
  cuspClassLogVolume :
    (zmodSignAction l).SignLabelQuotient -> Real
  zeroLogVolume : Real
  nonzero_eq_cuspClass :
    ∀ (j : ZMod l.value) (hj : j ≠ 0),
      normalizedLogVolume j =
        cuspClassLogVolume (zmodSignLabelFromCoordinate l j hj)
  zero_eq : normalizedLogVolume 0 = zeroLogVolume

namespace IUTStage1ZModCuspLabelLogVolumeCompatibility

variable {l : PrimeGeFive}

def constant (c : Real) :
    IUTStage1ZModCuspLabelLogVolumeCompatibility l :=
  { normalizedLogVolume := fun _ => c,
    cuspClassLogVolume := fun _ => c,
    zeroLogVolume := c,
    nonzero_eq_cuspClass := by
      intro j hj
      rfl,
    zero_eq := rfl }

theorem nonzero_eq
    (compat : IUTStage1ZModCuspLabelLogVolumeCompatibility l)
    (j : ZMod l.value) (hj : j ≠ 0) :
    compat.normalizedLogVolume j =
      compat.cuspClassLogVolume (zmodSignLabelFromCoordinate l j hj) :=
  compat.nonzero_eq_cuspClass j hj

theorem zero_eq_zeroLogVolume
    (compat : IUTStage1ZModCuspLabelLogVolumeCompatibility l) :
    compat.normalizedLogVolume 0 = compat.zeroLogVolume :=
  compat.zero_eq

theorem neg_nonzero_eq
    (compat : IUTStage1ZModCuspLabelLogVolumeCompatibility l)
    (j : ZMod l.value) (hj : j ≠ 0) :
    compat.normalizedLogVolume (-j) =
      compat.cuspClassLogVolume (zmodSignLabelFromCoordinate l j hj) := by
  rw [compat.nonzero_eq (-j) (zmod_neg_ne_zero_of_ne_zero l hj)]
  rw [zmodSignLabelFromCoordinate_neg_eq]

def fullLabelLogVolume
    (compat : IUTStage1ZModCuspLabelLogVolumeCompatibility l) :
    IUTStage1ZModCuspFullLabel l -> Real
  | IUTStage1ZModCuspFullLabel.zero => compat.zeroLogVolume
  | IUTStage1ZModCuspFullLabel.nonzero label =>
      compat.cuspClassLogVolume label

theorem fullLabelLogVolume_zero
    (compat : IUTStage1ZModCuspLabelLogVolumeCompatibility l) :
    compat.fullLabelLogVolume IUTStage1ZModCuspFullLabel.zero =
      compat.zeroLogVolume :=
  rfl

theorem fullLabelLogVolume_nonzero
    (compat : IUTStage1ZModCuspLabelLogVolumeCompatibility l)
    (label : (zmodSignAction l).SignLabelQuotient) :
    compat.fullLabelLogVolume (IUTStage1ZModCuspFullLabel.nonzero label) =
      compat.cuspClassLogVolume label :=
  rfl

theorem constant_fullLabelLogVolume
    (c : Real) (label : IUTStage1ZModCuspFullLabel l) :
    (constant (l := l) c).fullLabelLogVolume label = c := by
  cases label <;> rfl

theorem constant_fullLabelLogVolume_fromCoordinate
    (c : Real) (j : ZMod l.value) :
    (constant (l := l) c).fullLabelLogVolume
        (IUTStage1ZModCuspFullLabel.fromCoordinate l j) = c := by
  rw [constant_fullLabelLogVolume]

theorem normalizedLogVolume_eq_fullLabelLogVolume_fromCoordinate
    (compat : IUTStage1ZModCuspLabelLogVolumeCompatibility l)
    (j : ZMod l.value) :
    compat.normalizedLogVolume j =
      compat.fullLabelLogVolume
        (IUTStage1ZModCuspFullLabel.fromCoordinate l j) := by
  by_cases hj : j = 0
  · subst j
    rw [IUTStage1ZModCuspFullLabel.fromCoordinate_zero]
    exact compat.zero_eq_zeroLogVolume
  · rw [IUTStage1ZModCuspFullLabel.fromCoordinate_nonzero l j hj]
    exact compat.nonzero_eq j hj

theorem fullLabelLogVolume_fromCoordinate_zero
    (compat : IUTStage1ZModCuspLabelLogVolumeCompatibility l) :
    compat.fullLabelLogVolume
        (IUTStage1ZModCuspFullLabel.fromCoordinate l (0 : ZMod l.value)) =
      compat.zeroLogVolume := by
  rw [IUTStage1ZModCuspFullLabel.fromCoordinate_zero]
  rfl

theorem fullLabelLogVolume_fromCoordinate_nonzero
    (compat : IUTStage1ZModCuspLabelLogVolumeCompatibility l)
    (j : ZMod l.value) (hj : j ≠ 0) :
    compat.fullLabelLogVolume (IUTStage1ZModCuspFullLabel.fromCoordinate l j) =
      compat.cuspClassLogVolume (zmodSignLabelFromCoordinate l j hj) := by
  rw [IUTStage1ZModCuspFullLabel.fromCoordinate_nonzero l j hj]
  rfl

theorem fullLabelLogVolume_fromCoordinate_neg_eq
    (compat : IUTStage1ZModCuspLabelLogVolumeCompatibility l)
    (j : ZMod l.value) (hj : j ≠ 0) :
    compat.fullLabelLogVolume (IUTStage1ZModCuspFullLabel.fromCoordinate l (-j)) =
      compat.fullLabelLogVolume (IUTStage1ZModCuspFullLabel.fromCoordinate l j) := by
  rw [IUTStage1ZModCuspFullLabel.fromCoordinate_neg l j hj]

theorem fullLabelLogVolumeCompatibility_endpoint
    (compat : IUTStage1ZModCuspLabelLogVolumeCompatibility l)
    (j : ZMod l.value) (hj : j ≠ 0) :
    compat.normalizedLogVolume j =
        compat.fullLabelLogVolume
          (IUTStage1ZModCuspFullLabel.fromCoordinate l j) ∧
      compat.fullLabelLogVolume
          (IUTStage1ZModCuspFullLabel.fromCoordinate l (0 : ZMod l.value)) =
        compat.zeroLogVolume ∧
      compat.fullLabelLogVolume
          (IUTStage1ZModCuspFullLabel.fromCoordinate l j) =
        compat.cuspClassLogVolume (zmodSignLabelFromCoordinate l j hj) ∧
      compat.fullLabelLogVolume
          (IUTStage1ZModCuspFullLabel.fromCoordinate l (-j)) =
        compat.fullLabelLogVolume
          (IUTStage1ZModCuspFullLabel.fromCoordinate l j) ∧
      compat.normalizedLogVolume (-j) =
        compat.cuspClassLogVolume (zmodSignLabelFromCoordinate l j hj) :=
  ⟨compat.normalizedLogVolume_eq_fullLabelLogVolume_fromCoordinate j,
    compat.fullLabelLogVolume_fromCoordinate_zero,
    compat.fullLabelLogVolume_fromCoordinate_nonzero j hj,
    compat.fullLabelLogVolume_fromCoordinate_neg_eq j hj,
    compat.neg_nonzero_eq j hj⟩

theorem fullLabelLogVolume_le_of_zero_and_cuspClass_le
    (compat : IUTStage1ZModCuspLabelLogVolumeCompatibility l)
    {c : Real}
    (hzero : compat.zeroLogVolume <= c)
    (hcusp : ∀ label : (zmodSignAction l).SignLabelQuotient,
      compat.cuspClassLogVolume label <= c)
    (label : IUTStage1ZModCuspFullLabel l) :
    compat.fullLabelLogVolume label <= c := by
  cases label with
  | zero => exact hzero
  | nonzero label => exact hcusp label

theorem fullLabelLogVolume_fromCoordinate_le_of_zero_and_cuspClass_le
    (compat : IUTStage1ZModCuspLabelLogVolumeCompatibility l)
    {c : Real}
    (hzero : compat.zeroLogVolume <= c)
    (hcusp : ∀ label : (zmodSignAction l).SignLabelQuotient,
      compat.cuspClassLogVolume label <= c)
    (j : ZMod l.value) :
    compat.fullLabelLogVolume (IUTStage1ZModCuspFullLabel.fromCoordinate l j) <=
      c :=
  compat.fullLabelLogVolume_le_of_zero_and_cuspClass_le
    hzero hcusp (IUTStage1ZModCuspFullLabel.fromCoordinate l j)

theorem cuspClass_eq_of_normalizedLogVolume_eq
    (compat : IUTStage1ZModCuspLabelLogVolumeCompatibility l)
    {c : Real}
    (hnormalized : ∀ j : ZMod l.value, compat.normalizedLogVolume j = c)
    (label : (zmodSignAction l).SignLabelQuotient) :
    compat.cuspClassLogVolume label = c := by
  refine Quotient.inductionOn label ?_
  intro x
  calc
    compat.cuspClassLogVolume ((zmodSignAction l).toSignLabelQuotient x) =
        compat.cuspClassLogVolume (zmodSignLabelFromCoordinate l x.1 x.2) := by
      rw [zmod_toSignLabelQuotient_eq_fromCoordinate x]
    _ = compat.normalizedLogVolume x.1 :=
      (compat.nonzero_eq x.1 x.2).symm
    _ = c :=
      hnormalized x.1

theorem zeroLogVolume_eq_of_normalizedLogVolume_eq
    (compat : IUTStage1ZModCuspLabelLogVolumeCompatibility l)
    {c : Real}
    (hnormalized : ∀ j : ZMod l.value, compat.normalizedLogVolume j = c) :
    compat.zeroLogVolume = c := by
  calc
    compat.zeroLogVolume = compat.normalizedLogVolume 0 :=
      compat.zero_eq_zeroLogVolume.symm
    _ = c :=
      hnormalized 0

/--
Coordinate-level preservation of the zero/nonzero full-label branch.

This condition is about the label map only: after applying the coordinate
equivalence, the associated full label is the same zero/nonzero/sign-class label.
-/
def FullLabelMapPreserving
    (coordinateEquiv : ZMod l.value ≃ ZMod l.value) : Prop :=
  ∀ j : ZMod l.value,
    IUTStage1ZModCuspFullLabel.fromCoordinate l (coordinateEquiv j) =
      IUTStage1ZModCuspFullLabel.fromCoordinate l j

theorem fullLabelMapPreserving_refl :
    FullLabelMapPreserving (l := l) (Equiv.refl (ZMod l.value)) := by
  intro j
  rfl

theorem fullLabelMapPreserving_neg :
    FullLabelMapPreserving (l := l) (Equiv.neg (ZMod l.value)) := by
  intro j
  by_cases hj : j = 0
  · subst j
    simp [IUTStage1ZModCuspFullLabel.fromCoordinate_zero]
  · exact IUTStage1ZModCuspFullLabel.fromCoordinate_neg l j hj

def zmodTranslationEquiv
    (l : PrimeGeFive) (t : ZMod l.value) :
    ZMod l.value ≃ ZMod l.value where
  toFun := fun j => t + j
  invFun := fun j => -t + j
  left_inv := by
    intro j
    simp
  right_inv := by
    intro j
    simp

theorem zmodTranslationEquiv_apply
    (l : PrimeGeFive) (t j : ZMod l.value) :
    zmodTranslationEquiv l t j = zmodLabelTranslate l t j := by
  rw [zmodLabelTranslate_eq_add]
  rfl

def zmodUnitSmulEquiv
    (l : PrimeGeFive) (a : (ZMod l.value)ˣ) :
    ZMod l.value ≃ ZMod l.value where
  toFun := fun j => (zmodUnitActionData l).smul a j
  invFun := fun j =>
    (zmodUnitActionData l).smul (a⁻¹ : (ZMod l.value)ˣ) j
  left_inv := by
    intro j
    simp [zmodUnitActionData]
  right_inv := by
    intro j
    simp [zmodUnitActionData]

theorem zmodUnitSmulEquiv_apply
    (l : PrimeGeFive) (a : (ZMod l.value)ˣ) (j : ZMod l.value) :
    zmodUnitSmulEquiv l a j = (zmodUnitActionData l).smul a j :=
  rfl

def zmodUnitAffineEquiv
    (l : PrimeGeFive) (a : (ZMod l.value)ˣ) (t : ZMod l.value) :
    ZMod l.value ≃ ZMod l.value where
  toFun := fun j => zmodLabelTranslate l t ((zmodUnitActionData l).smul a j)
  invFun := fun j =>
    (zmodUnitActionData l).smul (a⁻¹ : (ZMod l.value)ˣ)
      (zmodLabelTranslate l (-t) j)
  left_inv := by
    intro j
    simp [zmodLabelTranslate_eq_add, zmodUnitActionData]
  right_inv := by
    intro j
    simp [zmodLabelTranslate_eq_add, zmodUnitActionData]

theorem zmodUnitAffineEquiv_apply
    (l : PrimeGeFive) (a : (ZMod l.value)ˣ)
    (t j : ZMod l.value) :
    zmodUnitAffineEquiv l a t j =
      zmodLabelTranslate l t ((zmodUnitActionData l).smul a j) :=
  rfl

theorem zmodTranslation_sum_eq
    (t : ZMod l.value) (f : ZMod l.value -> Real) :
    (Finset.univ.sum fun j : ZMod l.value => f (zmodLabelTranslate l t j)) =
      Finset.univ.sum f :=
  Fintype.sum_equiv (zmodTranslationEquiv l t)
    (fun j : ZMod l.value => f (zmodLabelTranslate l t j))
    (fun j : ZMod l.value => f j)
    (fun j => by rw [zmodTranslationEquiv_apply])

theorem zmodUnitSmul_sum_eq
    (a : (ZMod l.value)ˣ) (f : ZMod l.value -> Real) :
    (Finset.univ.sum fun j : ZMod l.value =>
      f ((zmodUnitActionData l).smul a j)) =
      Finset.univ.sum f :=
  Fintype.sum_equiv (zmodUnitSmulEquiv l a)
    (fun j : ZMod l.value => f ((zmodUnitActionData l).smul a j))
    (fun j : ZMod l.value => f j)
    (fun j => by rw [zmodUnitSmulEquiv_apply])

theorem zmodUnitAffine_sum_eq
    (a : (ZMod l.value)ˣ) (t : ZMod l.value)
    (f : ZMod l.value -> Real) :
    (Finset.univ.sum fun j : ZMod l.value =>
      f (zmodLabelTranslate l t ((zmodUnitActionData l).smul a j))) =
      Finset.univ.sum f :=
  Fintype.sum_equiv (zmodUnitAffineEquiv l a t)
    (fun j : ZMod l.value =>
      f (zmodLabelTranslate l t ((zmodUnitActionData l).smul a j)))
    (fun j : ZMod l.value => f j)
    (fun j => by rw [zmodUnitAffineEquiv_apply])

theorem fullLabelMapPreserving_unitSmul_of_signSubgroup
    {a : (ZMod l.value)ˣ}
    (ha : a ∈ zmodSignUnitSubgroup l) :
    FullLabelMapPreserving (l := l) (zmodUnitSmulEquiv l a) := by
  intro j
  rcases zmodSignUnitSubgroup_smul_eq_self_or_neg l ha j with h | h
  · rw [zmodUnitSmulEquiv_apply, h]
  · rw [zmodUnitSmulEquiv_apply, h]
    by_cases hj : j = 0
    · subst j
      simp [zmodSignAction, IUTStage1ZModCuspFullLabel.fromCoordinate_zero]
    · exact IUTStage1ZModCuspFullLabel.fromCoordinate_neg l j hj

theorem signSubgroup_of_fullLabelMapPreserving_unitSmul
    {a : (ZMod l.value)ˣ}
    (hpres : FullLabelMapPreserving (l := l) (zmodUnitSmulEquiv l a)) :
    a ∈ zmodSignUnitSubgroup l := by
  have hone := hpres (1 : ZMod l.value)
  rw [zmodUnitSmulEquiv_apply] at hone
  have ha_coord :
      (a : ZMod l.value) = 1 ∨ (a : ZMod l.value) = -1 := by
    have hsame :
        IUTStage1ZModCuspFullLabel.fromCoordinate l
            ((zmodUnitActionData l).smul a (1 : ZMod l.value)) =
          IUTStage1ZModCuspFullLabel.fromCoordinate l (1 : ZMod l.value) :=
      hone
    simpa [zmodUnitActionData] using
      (IUTStage1ZModCuspFullLabel.fromCoordinate_eq_iff (l := l)
        ((zmodUnitActionData l).smul a (1 : ZMod l.value))
        (1 : ZMod l.value)).mp hsame
  rw [mem_zmodSignUnitSubgroup_iff]
  rcases ha_coord with ha1 | haneg
  · left
    ext
    simpa using ha1
  · right
    ext
    simpa using haneg

theorem fullLabelMapPreserving_unitSmul_iff_signSubgroup
    (a : (ZMod l.value)ˣ) :
    FullLabelMapPreserving (l := l) (zmodUnitSmulEquiv l a) ↔
      a ∈ zmodSignUnitSubgroup l :=
  ⟨signSubgroup_of_fullLabelMapPreserving_unitSmul,
    fullLabelMapPreserving_unitSmul_of_signSubgroup⟩

theorem fullLabelMapPreserving_translation_iff_zero
    (t : ZMod l.value) :
    FullLabelMapPreserving (l := l) (zmodTranslationEquiv l t) ↔
      t = 0 := by
  constructor
  · intro hpres
    have hzero := hpres 0
    rw [zmodTranslationEquiv_apply, zmodLabelTranslate_eq_add] at hzero
    have hzero' :
        IUTStage1ZModCuspFullLabel.fromCoordinate l t =
          IUTStage1ZModCuspFullLabel.fromCoordinate l 0 := by
      simpa using hzero
    rw [IUTStage1ZModCuspFullLabel.fromCoordinate_zero] at hzero'
    exact (IUTStage1ZModCuspFullLabel.fromCoordinate_eq_zero_iff
      (l := l) t).mp hzero'
  · intro ht
    subst t
    intro j
    rw [zmodTranslationEquiv_apply, zmodLabelTranslate_zero]

theorem zero_translation_of_fullLabelMapPreserving_unitAffine
    (a : (ZMod l.value)ˣ) {t : ZMod l.value}
    (hpres : FullLabelMapPreserving (l := l) (zmodUnitAffineEquiv l a t)) :
    t = 0 := by
  have hzero := hpres 0
  rw [zmodUnitAffineEquiv_apply, zmodLabelTranslate_eq_add] at hzero
  have hzero' :
      IUTStage1ZModCuspFullLabel.fromCoordinate l t =
        IUTStage1ZModCuspFullLabel.fromCoordinate l 0 := by
    simpa [zmodUnitActionData] using hzero
  rw [IUTStage1ZModCuspFullLabel.fromCoordinate_zero] at hzero'
  exact (IUTStage1ZModCuspFullLabel.fromCoordinate_eq_zero_iff
    (l := l) t).mp hzero'

theorem fullLabelMapPreserving_unitAffine_iff
    (a : (ZMod l.value)ˣ) (t : ZMod l.value) :
    FullLabelMapPreserving (l := l) (zmodUnitAffineEquiv l a t) ↔
      t = 0 ∧ a ∈ zmodSignUnitSubgroup l := by
  constructor
  · intro hpres
    have ht := zero_translation_of_fullLabelMapPreserving_unitAffine
      (l := l) a hpres
    have hunit :
        FullLabelMapPreserving (l := l) (zmodUnitSmulEquiv l a) := by
      intro j
      have hj := hpres j
      rw [zmodUnitAffineEquiv_apply] at hj
      subst t
      simpa [zmodLabelTranslate_zero, zmodUnitSmulEquiv_apply] using hj
    exact ⟨ht, signSubgroup_of_fullLabelMapPreserving_unitSmul hunit⟩
  · rintro ⟨ht, ha⟩
    intro j
    subst t
    rw [zmodUnitAffineEquiv_apply, zmodLabelTranslate_zero]
    exact fullLabelMapPreserving_unitSmul_of_signSubgroup
      (l := l) ha j

/--
Labelwise preservation of the full-label log-volume branch.

This is separate from coordinate preservation: it says that once a full label has
been matched, the target and source log-volume functions assign the same real
value to it.
-/
def FullLabelLogVolumeValuePreserving
    (sourceLogVolume targetLogVolume :
      IUTStage1ZModCuspLabelLogVolumeCompatibility l) : Prop :=
  ∀ label : IUTStage1ZModCuspFullLabel l,
    targetLogVolume.fullLabelLogVolume label =
      sourceLogVolume.fullLabelLogVolume label

theorem transportedFullLabelLogVolume_preserved_of_fullLabelMap
    (sourceLogVolume targetLogVolume :
      IUTStage1ZModCuspLabelLogVolumeCompatibility l)
    {coordinateEquiv : ZMod l.value ≃ ZMod l.value}
    (hmap : FullLabelMapPreserving (l := l) coordinateEquiv)
    (hvalue :
      FullLabelLogVolumeValuePreserving
        sourceLogVolume targetLogVolume) :
    ∀ j : ZMod l.value,
      targetLogVolume.fullLabelLogVolume
          (IUTStage1ZModCuspFullLabel.fromCoordinate l (coordinateEquiv j)) =
        sourceLogVolume.fullLabelLogVolume
          (IUTStage1ZModCuspFullLabel.fromCoordinate l j) := by
  intro j
  rw [hmap j]
  exact hvalue (IUTStage1ZModCuspFullLabel.fromCoordinate l j)

theorem fullLabelLogVolumeValuePreserving_refl
    (logVolume : IUTStage1ZModCuspLabelLogVolumeCompatibility l) :
    FullLabelLogVolumeValuePreserving logVolume logVolume := by
  intro label
  rfl

theorem ext_of_fullLabelLogVolume_eq
    (source target : IUTStage1ZModCuspLabelLogVolumeCompatibility l)
    (hfull :
      ∀ label : IUTStage1ZModCuspFullLabel l,
        target.fullLabelLogVolume label = source.fullLabelLogVolume label) :
    target = source := by
  cases source with
  | mk sourceNormalized sourceCusp sourceZero sourceNonzero sourceZeroEq =>
    cases target with
    | mk targetNormalized targetCusp targetZero targetNonzero targetZeroEq =>
      have hzero : targetZero = sourceZero := hfull IUTStage1ZModCuspFullLabel.zero
      have hcusp : targetCusp = sourceCusp := by
        funext label
        exact hfull (IUTStage1ZModCuspFullLabel.nonzero label)
      have hnormalized : targetNormalized = sourceNormalized := by
        funext j
        by_cases hj : j = 0
        · subst j
          calc
            targetNormalized 0 = targetZero := targetZeroEq
            _ = sourceZero := hzero
            _ = sourceNormalized 0 := sourceZeroEq.symm
        · calc
            targetNormalized j =
                targetCusp (zmodSignLabelFromCoordinate l j hj) :=
              targetNonzero j hj
            _ = sourceCusp (zmodSignLabelFromCoordinate l j hj) := by
              rw [hcusp]
            _ = sourceNormalized j :=
              (sourceNonzero j hj).symm
      cases hnormalized
      cases hcusp
      cases hzero
      simp

end IUTStage1ZModCuspLabelLogVolumeCompatibility

namespace IUTStage1LabelAveragedProcessionLogVolume

variable {label : Type u} [Fintype label]

def constant [Nonempty label] (c : Real) :
    IUTStage1LabelAveragedProcessionLogVolume label :=
  { normalizedLogVolume := fun _ => c,
    averageLogVolume := c,
    average_eq := by
      have hcard_nat : 0 < Fintype.card label := Fintype.card_pos
      have hcard_ne : (Fintype.card label : Real) ≠ 0 := by
        exact_mod_cast (ne_of_gt hcard_nat)
      calc
        c = ((Fintype.card label : Real) * c) /
            (Fintype.card label : Real) := by
          field_simp [hcard_ne]
        _ = (Finset.univ.sum fun _ : label => c) /
            (Fintype.card label : Real) := by
          rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ] }

theorem average_eq_formula
    (data : IUTStage1LabelAveragedProcessionLogVolume label) :
    data.averageLogVolume =
      (Finset.univ.sum data.normalizedLogVolume) /
        (Fintype.card label : Real) :=
  data.average_eq

theorem average_eq_zmod_prime_formula
    (l : PrimeGeFive)
    (data : IUTStage1LabelAveragedProcessionLogVolume (ZMod l.value)) :
    data.averageLogVolume =
      (Finset.univ.sum data.normalizedLogVolume) / (l.value : Real) := by
  rw [data.average_eq, ZMod.card]

theorem average_eq_of_pointwise
    {data₁ data₂ : IUTStage1LabelAveragedProcessionLogVolume label}
    (hpointwise :
      ∀ j : label,
        data₁.normalizedLogVolume j =
          data₂.normalizedLogVolume j) :
    data₁.averageLogVolume = data₂.averageLogVolume := by
  calc
    data₁.averageLogVolume =
        (Finset.univ.sum data₁.normalizedLogVolume) /
          (Fintype.card label : Real) :=
      data₁.average_eq
    _ =
        (Finset.univ.sum data₂.normalizedLogVolume) /
          (Fintype.card label : Real) := by
      congr 1
      exact Finset.sum_congr rfl (by
        intro j _hj
        exact hpointwise j)
    _ = data₂.averageLogVolume :=
      data₂.average_eq.symm

theorem eq_constant_of_forall_eq
    [Nonempty label]
    (data : IUTStage1LabelAveragedProcessionLogVolume label)
    {c : Real}
    (hpointwise : ∀ j : label, data.normalizedLogVolume j = c) :
    data = constant c := by
  have haverage :
      data.averageLogVolume = (constant (label := label) c).averageLogVolume :=
    average_eq_of_pointwise hpointwise
  cases data with
  | mk normalized average average_eq =>
      simp only [constant] at hpointwise haverage ⊢
      have hnormalized : normalized = fun _ => c :=
        funext hpointwise
      subst normalized
      subst average
      rfl

theorem const_le_average_of_forall_le
    [Nonempty label]
    (data : IUTStage1LabelAveragedProcessionLogVolume label)
    {c : Real}
    (hpointwise : ∀ j : label, c <= data.normalizedLogVolume j) :
    c <= data.averageLogVolume := by
  rw [data.average_eq]
  have hcard_nat : 0 < Fintype.card label := Fintype.card_pos
  have hcard_real : 0 < (Fintype.card label : Real) :=
    Nat.cast_pos.mpr hcard_nat
  rw [le_div_iff₀ hcard_real]
  have hsum :
      (Fintype.card label : Real) * c <=
        Finset.univ.sum data.normalizedLogVolume := by
    simpa [Finset.sum_const, nsmul_eq_mul] using
      (Finset.sum_le_sum (fun j _hj => hpointwise j) :
        Finset.univ.sum (fun _ : label => c) <=
        Finset.univ.sum data.normalizedLogVolume)
  simpa [mul_comm] using hsum

theorem average_le_const_of_forall_le
    [Nonempty label]
    (data : IUTStage1LabelAveragedProcessionLogVolume label)
    {c : Real}
    (hpointwise : ∀ j : label, data.normalizedLogVolume j <= c) :
    data.averageLogVolume <= c := by
  rw [data.average_eq]
  have hcard_nat : 0 < Fintype.card label := Fintype.card_pos
  have hcard_real : 0 < (Fintype.card label : Real) :=
    Nat.cast_pos.mpr hcard_nat
  rw [div_le_iff₀ hcard_real]
  have hsum :
      Finset.univ.sum data.normalizedLogVolume <=
        (Fintype.card label : Real) * c := by
    simpa [Finset.sum_const, nsmul_eq_mul] using
      (Finset.sum_le_sum (fun j _hj => hpointwise j) :
        Finset.univ.sum data.normalizedLogVolume <=
          Finset.univ.sum (fun _ : label => c))
  simpa [mul_comm] using hsum

end IUTStage1LabelAveragedProcessionLogVolume

namespace IUTStage1ZModCuspLabelLogVolumeCompatibility

variable {l : PrimeGeFive}

/--
Uniform `F_l` average associated to a cusp-label log-volume compatibility.

This keeps the zero label in the averaging set.  It is the finite model of the
IUT II convention that all `j ∈ F_l` receive weight `1 / l`, with the zero
label recorded separately from nonzero sign-label classes.
-/
noncomputable def toLabelAveraged
    (compat : IUTStage1ZModCuspLabelLogVolumeCompatibility l) :
    IUTStage1LabelAveragedProcessionLogVolume (ZMod l.value) :=
  { normalizedLogVolume := compat.normalizedLogVolume,
    averageLogVolume :=
      (Finset.univ.sum compat.normalizedLogVolume) / (l.value : Real),
    average_eq := by
      rw [ZMod.card] }

theorem toLabelAveraged_eq_constant_of_zero_and_cusp_eq
    (compat : IUTStage1ZModCuspLabelLogVolumeCompatibility l)
    {c : Real}
    (hzero : compat.zeroLogVolume = c)
    (hcusp : ∀ label : (zmodSignAction l).SignLabelQuotient,
      compat.cuspClassLogVolume label = c) :
    compat.toLabelAveraged =
      IUTStage1LabelAveragedProcessionLogVolume.constant
        (label := ZMod l.value) c := by
  haveI : Nonempty (ZMod l.value) := ⟨0⟩
  exact IUTStage1LabelAveragedProcessionLogVolume.eq_constant_of_forall_eq
    compat.toLabelAveraged
    (by
      intro j
      by_cases hj : j = 0
      · subst j
        exact (compat.zero_eq.trans hzero)
      · exact (compat.nonzero_eq j hj).trans
          (hcusp (zmodSignLabelFromCoordinate l j hj)))

theorem constant_toLabelAveraged_eq_constant
    (c : Real) :
    (constant (l := l) c).toLabelAveraged =
      IUTStage1LabelAveragedProcessionLogVolume.constant
        (label := ZMod l.value) c := by
  exact toLabelAveraged_eq_constant_of_zero_and_cusp_eq
    (constant (l := l) c) rfl (by intro label; rfl)

theorem toLabelAveraged_average_eq_fullLabelCoordinateAverage
    (compat : IUTStage1ZModCuspLabelLogVolumeCompatibility l) :
    compat.toLabelAveraged.averageLogVolume =
      (Finset.univ.sum fun j : ZMod l.value =>
        compat.fullLabelLogVolume
          (IUTStage1ZModCuspFullLabel.fromCoordinate l j)) /
        (l.value : Real) := by
  calc
    compat.toLabelAveraged.averageLogVolume =
        (Finset.univ.sum compat.normalizedLogVolume) / (l.value : Real) := by
      exact IUTStage1LabelAveragedProcessionLogVolume.average_eq_zmod_prime_formula
        l compat.toLabelAveraged
    _ =
        (Finset.univ.sum fun j : ZMod l.value =>
          compat.fullLabelLogVolume
            (IUTStage1ZModCuspFullLabel.fromCoordinate l j)) /
          (l.value : Real) := by
      congr 1
      exact Finset.sum_congr rfl (by
        intro j _hj
        exact compat.normalizedLogVolume_eq_fullLabelLogVolume_fromCoordinate j)

theorem toLabelAveraged_average_le_of_zero_and_cuspClass_le
    (compat : IUTStage1ZModCuspLabelLogVolumeCompatibility l)
    {c : Real}
    (hzero : compat.zeroLogVolume <= c)
    (hcusp : ∀ label : (zmodSignAction l).SignLabelQuotient,
      compat.cuspClassLogVolume label <= c) :
    compat.toLabelAveraged.averageLogVolume <= c := by
  haveI : Nonempty (ZMod l.value) := ⟨0⟩
  exact IUTStage1LabelAveragedProcessionLogVolume.average_le_const_of_forall_le
    compat.toLabelAveraged
    (by
      intro j
      by_cases hj : j = 0
      · subst j
        simpa [toLabelAveraged] using compat.zero_eq_zeroLogVolume.trans_le hzero
      · simpa [toLabelAveraged] using
          (compat.nonzero_eq j hj).trans_le
            (hcusp (zmodSignLabelFromCoordinate l j hj)))

theorem toLabelAveraged_fullLabel_average_endpoint
    (compat : IUTStage1ZModCuspLabelLogVolumeCompatibility l)
    {c : Real}
    (hzero : compat.zeroLogVolume <= c)
    (hcusp : ∀ label : (zmodSignAction l).SignLabelQuotient,
      compat.cuspClassLogVolume label <= c) :
    compat.toLabelAveraged.averageLogVolume =
        (Finset.univ.sum fun j : ZMod l.value =>
          compat.fullLabelLogVolume
            (IUTStage1ZModCuspFullLabel.fromCoordinate l j)) /
          (l.value : Real) ∧
      compat.toLabelAveraged.averageLogVolume <= c :=
  ⟨compat.toLabelAveraged_average_eq_fullLabelCoordinateAverage,
    compat.toLabelAveraged_average_le_of_zero_and_cuspClass_le hzero hcusp⟩

end IUTStage1ZModCuspLabelLogVolumeCompatibility
end Stage1
end Iut
