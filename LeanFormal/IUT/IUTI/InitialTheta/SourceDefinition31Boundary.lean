import LeanFormal.IUT.IUTIII.Theorem311.SourceFaithfulBoundary
import Mathlib.Algebra.Group.Hom.Basic
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option linter.checkUnivs false

/-!
  # Source Definition 3.1 boundary

  This file records the source-facing clauses of IUT I Definition 3.1 in a
  single typed object.  The object is intentionally a contract: its fields
  are not manufactured from an arbitrary number field and elliptic curve.
  What is proved here is the faithful projection from the complete source
  contract to the smaller `InitialThetaInput` used by the Theorem 3.11
  boundary, together with the elementary consequences of every clause.

  Keeping this bridge separate is important.  A projection theorem proves
  that no source condition is forgotten when the downstream theorem is
  applied; it does not prove that arbitrary arithmetic input has an inhabitant
  of this structure.
-/

namespace LeanFormal.IUT

open scoped BigOperators

noncomputable section

universe u v w

namespace Theorem311Source

/-! ## 1. The source place and reduction clauses -/

structure SourcePlacePartition (Selected Bad : Type u) where
  badIncluded : Bad → Selected
  selectedNonempty : Nonempty Selected
  badFinite : Fintype Bad
  selectedLabel : Selected → Nat
  badLabel : Bad → Nat
  badLabel_compatible : ∀ b, selectedLabel (badIncluded b) = badLabel b

namespace SourcePlacePartition

variable {Selected Bad : Type u} (P : SourcePlacePartition Selected Bad)

def bad_included (b : Bad) : Selected :=
  P.badIncluded b

theorem selected_nonempty (P : SourcePlacePartition Selected Bad) :
    Nonempty Selected :=
  @SourcePlacePartition.selectedNonempty Selected Bad P

@[implicit_reducible] noncomputable def bad_finite (P : SourcePlacePartition Selected Bad) :
    Fintype Bad :=
  @SourcePlacePartition.badFinite Selected Bad P

theorem labels_agree (b : Bad) :
    P.selectedLabel (P.badIncluded b) = P.badLabel b :=
  P.badLabel_compatible b

theorem bad_label_eq_selected_label (b : Bad) :
    P.badLabel b = P.selectedLabel (P.badIncluded b) :=
  (P.badLabel_compatible b).symm

theorem selected_label_transport {b₁ b₂ : Bad}
    (h : P.badIncluded b₁ = P.badIncluded b₂) :
    P.badLabel b₁ = P.badLabel b₂ := by
  rw [← P.badLabel_compatible b₁, ← P.badLabel_compatible b₂, h]

theorem bad_label_transport {b₁ b₂ : Bad}
    (h : P.badLabel b₁ = P.badLabel b₂) :
    P.selectedLabel (P.badIncluded b₁) =
      P.selectedLabel (P.badIncluded b₂) := by
  rw [P.badLabel_compatible b₁, P.badLabel_compatible b₂, h]

end SourcePlacePartition

structure SourceReductionClause (Selected Bad : Type u) where
  partition : SourcePlacePartition Selected Bad
  stableReduction : Bad → Prop
  stableReduction_proved : ∀ b, stableReduction b
  multiplicativeReduction : Bad → Prop
  multiplicativeReduction_proved : ∀ b, multiplicativeReduction b
  splitMultiplicativeReduction : Bad → Prop
  splitMultiplicativeReduction_proved :
    ∀ b, splitMultiplicativeReduction b
  reductionCompatibility : ∀ b,
    splitMultiplicativeReduction b → multiplicativeReduction b
  qParameter : Bad → Real
  qParameter_nonzero : ∀ b, qParameter b ≠ 0
  qParameter_contracting : ∀ b, ‖qParameter b‖ < 1
  qParameter_reduction_compatibility : ∀ b,
    stableReduction b → qParameter b ≠ 1

namespace SourceReductionClause

variable {Selected Bad : Type u} (R : SourceReductionClause Selected Bad)

theorem stable (b : Bad) : R.stableReduction b :=
  R.stableReduction_proved b

theorem multiplicative (b : Bad) : R.multiplicativeReduction b :=
  R.multiplicativeReduction_proved b

theorem split_multiplicative (b : Bad) :
    R.splitMultiplicativeReduction b :=
  R.splitMultiplicativeReduction_proved b

theorem split_implies_multiplicative (b : Bad) :
    R.splitMultiplicativeReduction b → R.multiplicativeReduction b :=
  R.reductionCompatibility b

theorem q_nonzero (b : Bad) : R.qParameter b ≠ 0 :=
  R.qParameter_nonzero b

theorem q_norm_lt_one (b : Bad) : ‖R.qParameter b‖ < 1 :=
  R.qParameter_contracting b

theorem q_ne_one (b : Bad) : R.qParameter b ≠ 1 :=
  R.qParameter_reduction_compatibility b
    (R.stableReduction_proved b)

theorem q_norm_nonnegative (b : Bad) :
    0 ≤ ‖R.qParameter b‖ :=
  norm_nonneg _

theorem q_norm_pos (b : Bad) :
    0 < ‖R.qParameter b‖ := by
  exact (norm_pos_iff.mpr (R.qParameter_nonzero b))

theorem q_norm_interval (b : Bad) :
    ‖R.qParameter b‖ ∈ Set.Ioo (0 : Real) 1 := by
  exact ⟨R.q_norm_pos b, R.q_norm_lt_one b⟩

theorem q_norm_le_one (b : Bad) :
    ‖R.qParameter b‖ ≤ 1 :=
  le_of_lt (R.q_norm_lt_one b)

theorem q_parameter_eq_zero_iff_false (b : Bad) :
    R.qParameter b = 0 ↔ False := by
  constructor
  · intro h
    exact R.qParameter_nonzero b h
  · intro h
    exact False.elim h

theorem stable_multiplicative_pair (b : Bad) :
    R.stableReduction b ∧ R.multiplicativeReduction b :=
  ⟨R.stableReduction_proved b, R.multiplicativeReduction_proved b⟩

theorem split_stable_multiplicative (b : Bad) :
    R.stableReduction b ∧
      R.multiplicativeReduction b ∧
      R.splitMultiplicativeReduction b :=
  ⟨R.stableReduction_proved b,
    R.multiplicativeReduction_proved b,
    R.splitMultiplicativeReduction_proved b⟩

theorem q_reduction_pair (b : Bad) :
    R.stableReduction b ∧ R.qParameter b ≠ 1 :=
  ⟨R.stableReduction_proved b, R.q_ne_one b⟩

theorem q_contracting_square (b : Bad) :
    ‖R.qParameter b‖ ^ 2 < 1 := by
  have h := R.q_norm_lt_one b
  have hp := R.q_norm_pos b
  nlinarith

theorem q_contracting_pow (b : Bad) (n : Nat) :
    ‖R.qParameter b‖ ^ (n + 1) < 1 := by
  have h : ‖R.qParameter b‖ < 1 := R.q_norm_lt_one b
  have hp : 0 ≤ ‖R.qParameter b‖ := R.q_norm_nonnegative b
  exact pow_lt_one₀ hp h (Nat.succ_ne_zero n)

theorem q_power_nonzero (b : Bad) (n : Nat) :
    R.qParameter b ^ n ≠ 0 := by
  exact pow_ne_zero n (R.qParameter_nonzero b)

theorem q_power_ne_one_of_pos (b : Bad) (n : Nat) (hn : 0 < n) :
    R.qParameter b ^ n ≠ 1 := by
  intro h
  have hnorm : ‖R.qParameter b‖ ^ n = 1 := by
    rw [← norm_pow, h, norm_one]
  have hlt : ‖R.qParameter b‖ ^ n < 1 := by
    exact pow_lt_one₀ (R.q_norm_nonnegative b)
      (R.q_norm_lt_one b) (Nat.ne_of_gt hn)
  linarith

end SourceReductionClause

/-! ## 2. Torsion and Galois-image clauses -/

structure SourceTorsionClause (l : PrimeGeFive) where
  torsionCarrier : Type u
  [torsionCarrierLaw : Group torsionCarrier]
  torsionLabel : torsionCarrier → Fin 6
  torsionNonempty : Nonempty torsionCarrier
  representationCarrier : Type v
  [representationCarrierLaw : Group representationCarrier]
  representationGroup : Type w
  [representationGroupLaw : Group representationGroup]
  representation : representationCarrier →* representationGroup
  representation_surjective : Function.Surjective representation
  imageContainsSL2 : Prop
  imageContainsSL2_proved : imageContainsSL2
  sixTorsionIndependent : Prop
  sixTorsionIndependent_proved : sixTorsionIndependent
  lTorsionCompatible : Prop
  lTorsionCompatible_proved : lTorsionCompatible

attribute [instance] SourceTorsionClause.representationGroupLaw
  SourceTorsionClause.torsionCarrierLaw
  SourceTorsionClause.representationCarrierLaw

namespace SourceTorsionClause

variable {l : PrimeGeFive} (T : SourceTorsionClause l)

theorem torsion_nonempty : Nonempty T.torsionCarrier :=
  T.torsionNonempty

theorem representation_surjective_spec :
    Function.Surjective T.representation :=
  T.representation_surjective

theorem image_contains_SL2 : T.imageContainsSL2 :=
  T.imageContainsSL2_proved

theorem six_torsion_independent : T.sixTorsionIndependent :=
  T.sixTorsionIndependent_proved

theorem l_torsion_compatible : T.lTorsionCompatible :=
  T.lTorsionCompatible_proved

theorem representation_image_eq_range :
    Set.range T.representation = Set.range T.representation := rfl

theorem representation_mem_range (x : T.representationGroup) :
    x ∈ Set.range T.representation := by
  rcases T.representation_surjective x with ⟨y, hy⟩
  exact ⟨y, hy⟩

theorem representation_factor_unique {a b : T.representationCarrier}
    (h : T.representation a = T.representation b) :
    T.representation a = T.representation b := h

theorem representation_map_one :
    T.representation 1 = 1 :=
  T.representation.map_one

theorem representation_map_mul (a b : T.representationCarrier) :
    T.representation (a * b) = T.representation a * T.representation b :=
  T.representation.map_mul a b

theorem representation_map_inv (a : T.representationCarrier) :
    T.representation a⁻¹ = (T.representation a)⁻¹ := by
  exact map_inv T.representation a

theorem representation_kernel_mem (a : T.representationCarrier)
    (h : T.representation a = 1) :
    a ∈ T.representation.ker := by
  exact h

theorem representation_kernel_iff (a : T.representationCarrier) :
    a ∈ T.representation.ker ↔ T.representation a = 1 := Iff.rfl

theorem torsion_label_total (a : T.torsionCarrier) :
    ∃ j : Fin 6, T.torsionLabel a = j :=
  ⟨T.torsionLabel a, rfl⟩

theorem torsion_label_eq_iff {a b : T.torsionCarrier} :
    T.torsionLabel a = T.torsionLabel b ↔
      T.torsionLabel b = T.torsionLabel a := by
  constructor <;> intro h <;> exact h.symm

theorem torsion_label_refl (a : T.torsionCarrier) :
    T.torsionLabel a = T.torsionLabel a := rfl

theorem torsion_label_trans {a b c : T.torsionCarrier}
    (hab : T.torsionLabel a = T.torsionLabel b)
    (hbc : T.torsionLabel b = T.torsionLabel c) :
    T.torsionLabel a = T.torsionLabel c :=
  hab.trans hbc

theorem l_is_odd : Odd l.value := l.odd

theorem l_at_least_five : 5 ≤ l.value := l.ge_five

theorem imageContainsSL2_pair :
    T.imageContainsSL2 ∧ T.sixTorsionIndependent :=
  ⟨T.imageContainsSL2_proved, T.sixTorsionIndependent_proved⟩

theorem torsion_all_clauses :
    T.imageContainsSL2 ∧ T.sixTorsionIndependent ∧
      T.lTorsionCompatible :=
  ⟨T.imageContainsSL2_proved,
    T.sixTorsionIndependent_proved,
    T.lTorsionCompatible_proved⟩

end SourceTorsionClause

/-! ## 3. Orbicurve, cover, and exact-sequence clauses -/

structure SourceExactSequenceClause where
  baseGroup : Type u
  coverGroup : Type v
  geometricGroup : Type w
  [baseGroupLaw : Group baseGroup]
  [coverGroupLaw : Group coverGroup]
  [geometricGroupLaw : Group geometricGroup]
  injection : geometricGroup →* coverGroup
  projection : coverGroup →* baseGroup
  injection_injective : Function.Injective injection
  projection_surjective : Function.Surjective projection
  exact_at_cover : ∀ x : coverGroup,
    projection x = 1 ↔ ∃ y : geometricGroup, injection y = x
  sectionMap : baseGroup →* coverGroup
  section_right_inverse : ∀ x, projection (sectionMap x) = x

attribute [instance] SourceExactSequenceClause.baseGroupLaw
  SourceExactSequenceClause.coverGroupLaw
  SourceExactSequenceClause.geometricGroupLaw

namespace SourceExactSequenceClause

variable (E : SourceExactSequenceClause)

theorem injection_injective_spec : Function.Injective E.injection :=
  E.injection_injective

theorem projection_surjective_spec : Function.Surjective E.projection :=
  E.projection_surjective

theorem exact_at_cover_iff (x : E.coverGroup) :
    E.projection x = 1 ↔ ∃ y, E.injection y = x :=
  E.exact_at_cover x

theorem section_right_inverse_spec (x : E.baseGroup) :
    E.projection (E.sectionMap x) = x :=
  E.section_right_inverse x

theorem projection_map_one : E.projection 1 = 1 :=
  E.projection.map_one

theorem projection_map_mul (x y : E.coverGroup) :
    E.projection (x * y) = E.projection x * E.projection y :=
  E.projection.map_mul x y

theorem injection_map_one : E.injection 1 = 1 :=
  E.injection.map_one

theorem injection_map_mul (x y : E.geometricGroup) :
    E.injection (x * y) = E.injection x * E.injection y :=
  E.injection.map_mul x y

theorem section_map_one : E.sectionMap 1 = 1 :=
  E.sectionMap.map_one

theorem section_map_mul (x y : E.baseGroup) :
    E.sectionMap (x * y) = E.sectionMap x * E.sectionMap y :=
  E.sectionMap.map_mul x y

theorem projection_section (x : E.baseGroup) :
    E.projection (E.sectionMap x) = x :=
  E.section_right_inverse x

theorem projection_section_one :
    E.projection (E.sectionMap 1) = 1 := by
  exact E.section_right_inverse 1

theorem section_injective : Function.Injective E.sectionMap := by
  intro a b h
  have hp := congrArg E.projection h
  simpa [E.section_right_inverse] using hp

theorem projection_range_eq_univ :
    Set.range (fun x => E.projection x) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  exact E.projection_surjective x

theorem kernel_eq_range_set :
    {x : E.coverGroup | E.projection x = 1} =
      Set.range (fun y => E.injection y) := by
  ext x
  exact E.exact_at_cover x

theorem kernel_mem_iff (x : E.coverGroup) :
    x ∈ E.projection.ker ↔ ∃ y, E.injection y = x := by
  exact E.exact_at_cover x

theorem kernel_one : (1 : E.coverGroup) ∈ E.projection.ker := by
  exact E.projection.map_one

theorem injection_kernel_trivial (x : E.geometricGroup)
    (h : E.injection x = 1) : x = 1 := by
  apply E.injection_injective
  simpa using h

theorem exact_witness (x : E.coverGroup) (h : E.projection x = 1) :
    ∃ y : E.geometricGroup, E.injection y = x :=
  (E.exact_at_cover x).mp h

theorem exact_reverse (y : E.geometricGroup) :
    E.projection (E.injection y) = 1 := by
  rcases (E.exact_at_cover (E.injection y)).mpr ⟨y, rfl⟩ with h
  exact h

theorem exact_witness_unique (x : E.coverGroup)
    (h : E.projection x = 1) :
    ∀ y z, E.injection y = x → E.injection z = x → y = z := by
  intro y z hy hz
  apply E.injection_injective
  exact hy.trans hz.symm

theorem projection_section_mul (x y : E.baseGroup) :
    E.projection (E.sectionMap x * E.sectionMap y) = x * y := by
  rw [E.projection.map_mul, E.section_right_inverse,
    E.section_right_inverse]

theorem projection_section_inv (x : E.baseGroup) :
    E.projection ((E.sectionMap x)⁻¹) = x⁻¹ := by
  calc
    E.projection ((E.sectionMap x)⁻¹) =
        (E.projection (E.sectionMap x))⁻¹ :=
      map_inv E.projection (E.sectionMap x)
    _ = x⁻¹ := by rw [E.section_right_inverse]

theorem section_preserves_eq {a b : E.baseGroup}
    (h : a = b) : E.sectionMap a = E.sectionMap b := by
  exact congrArg E.sectionMap h

end SourceExactSequenceClause

structure SourceOrbicurveClause where
  curve : Type u
  puncturedCurve : Type v
  cover : Type w
  structureGroup : Type u
  [structureGroupLaw : Group structureGroup]
  curveToPunctured : puncturedCurve → curve
  coverToPunctured : cover → puncturedCurve
  cover_surjective : Function.Surjective coverToPunctured
  exactSequence : SourceExactSequenceClause.{u, v, w}
  cuspCount : Nat
  cuspCount_pos : 0 < cuspCount
  curveCompatibility : Prop
  curveCompatibility_proved : curveCompatibility

namespace SourceOrbicurveClause

variable (C : SourceOrbicurveClause)

theorem cover_surjective_spec : Function.Surjective C.coverToPunctured :=
  C.cover_surjective

theorem cusp_count_pos : 0 < C.cuspCount :=
  C.cuspCount_pos

theorem cusp_count_nonzero : C.cuspCount ≠ 0 :=
  Nat.ne_of_gt C.cuspCount_pos

theorem curve_compatibility : C.curveCompatibility :=
  C.curveCompatibility_proved

theorem cover_point_lift (x : C.puncturedCurve) :
    ∃ y, C.coverToPunctured y = x :=
  C.cover_surjective x

theorem cover_range_eq :
    Set.range C.coverToPunctured = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  exact C.cover_point_lift x

theorem curve_map_transport {x y : C.cover} (h :
    C.coverToPunctured x = C.coverToPunctured y) :
    C.curveToPunctured (C.coverToPunctured x) =
      C.curveToPunctured (C.coverToPunctured y) := by
  rw [h]

theorem exact_sequence_injection_injective :
    Function.Injective C.exactSequence.injection :=
  C.exactSequence.injection_injective

theorem exact_sequence_projection_surjective :
    Function.Surjective C.exactSequence.projection :=
  C.exactSequence.projection_surjective

theorem exact_sequence_section (x : C.exactSequence.baseGroup) :
    C.exactSequence.projection
        (C.exactSequence.sectionMap x) = x :=
  C.exactSequence.section_right_inverse x

theorem exact_sequence_kernel_witness (x : C.exactSequence.coverGroup)
    (h : C.exactSequence.projection x = 1) :
    ∃ y, C.exactSequence.injection y = x :=
  C.exactSequence.exact_witness x h

end SourceOrbicurveClause

/-! ## 4. Section, local group, and cusp clauses -/

structure SourceSectionClause where
  valuationCarrier : Type u
  modifiedValuationCarrier : Type v
  localGroupCarrier : valuationCarrier → Type w
  modifiedLocalGroupCarrier : modifiedValuationCarrier → Type w
  sectionMap : valuationCarrier → modifiedValuationCarrier
  sectionRightInverse : modifiedValuationCarrier → valuationCarrier
  section_left_inverse : ∀ x,
    sectionRightInverse (sectionMap x) = x
  section_right_inverse : ∀ y,
    sectionMap (sectionRightInverse y) = y
  localGroupSection : ∀ x,
    localGroupCarrier x → modifiedLocalGroupCarrier (sectionMap x)
  localGroupSection_injective : ∀ x,
    Function.Injective (localGroupSection x)
  localGroupSection_surjective : ∀ x,
    Function.Surjective (localGroupSection x)
  finitePlaceData : Prop
  finitePlaceData_proved : finitePlaceData
  infinitePlaceData : Prop
  infinitePlaceData_proved : infinitePlaceData

namespace SourceSectionClause

variable (S : SourceSectionClause)

theorem section_left (x : S.valuationCarrier) :
    S.sectionRightInverse (S.sectionMap x) = x :=
  S.section_left_inverse x

theorem section_right (y : S.modifiedValuationCarrier) :
    S.sectionMap (S.sectionRightInverse y) = y :=
  S.section_right_inverse y

theorem sectionMap_injective : Function.Injective S.sectionMap := by
  intro a b h
  simpa [S.section_left_inverse] using congrArg S.sectionRightInverse h

theorem sectionMap_surjective : Function.Surjective S.sectionMap := by
  intro y
  exact ⟨S.sectionRightInverse y, S.section_right_inverse y⟩

theorem sectionRightInverse_injective :
    Function.Injective S.sectionRightInverse := by
  intro a b h
  rw [← S.section_right_inverse a, ← S.section_right_inverse b, h]

theorem sectionRightInverse_surjective :
    Function.Surjective S.sectionRightInverse := by
  intro x
  exact ⟨S.sectionMap x, S.section_left_inverse x⟩

theorem local_group_section_injective (x : S.valuationCarrier) :
    Function.Injective (S.localGroupSection x) :=
  S.localGroupSection_injective x

theorem local_group_section_surjective (x : S.valuationCarrier) :
    Function.Surjective (S.localGroupSection x) :=
  S.localGroupSection_surjective x

theorem local_group_section_bijective (x : S.valuationCarrier) :
    Function.Bijective (S.localGroupSection x) :=
  ⟨S.localGroupSection_injective x,
    S.localGroupSection_surjective x⟩

theorem finite_place_data : S.finitePlaceData :=
  S.finitePlaceData_proved

theorem infinite_place_data : S.infinitePlaceData :=
  S.infinitePlaceData_proved

theorem section_cancel_left (x : S.valuationCarrier) :
    S.sectionRightInverse (S.sectionMap x) = x :=
  S.section_left_inverse x

theorem section_cancel_right (y : S.modifiedValuationCarrier) :
    S.sectionMap (S.sectionRightInverse y) = y :=
  S.section_right_inverse y

theorem section_round_trip (x : S.valuationCarrier) :
    S.sectionMap (S.sectionRightInverse (S.sectionMap x)) =
      S.sectionMap x := by
  rw [S.section_left_inverse]

theorem section_round_trip_modified (y : S.modifiedValuationCarrier) :
    S.sectionRightInverse (S.sectionMap (S.sectionRightInverse y)) =
      S.sectionRightInverse y := by
  rw [S.section_right_inverse]

end SourceSectionClause

structure SourceCuspClause where
  epsilon : Real
  epsilon_positive : 0 < epsilon
  epsilon_nonzero : epsilon ≠ 0
  epsilon_compatibility : Prop
  epsilon_compatibility_proved : epsilon_compatibility
  cuspScale : Real
  cuspScale_positive : 0 < cuspScale
  epsilon_scale_relation : epsilon * cuspScale ≠ 0

namespace SourceCuspClause

variable (C : SourceCuspClause)

theorem epsilon_pos : 0 < C.epsilon := C.epsilon_positive

theorem epsilon_ne_zero : C.epsilon ≠ 0 := C.epsilon_nonzero

theorem epsilon_compatibility_spec : C.epsilon_compatibility :=
  C.epsilon_compatibility_proved

theorem cusp_scale_pos : 0 < C.cuspScale := C.cuspScale_positive

theorem cusp_scale_ne_zero : C.cuspScale ≠ 0 :=
  ne_of_gt C.cuspScale_positive

theorem epsilon_scale_ne_zero : C.epsilon * C.cuspScale ≠ 0 :=
  C.epsilon_scale_relation

theorem epsilon_scale_pos : 0 < C.epsilon * C.cuspScale :=
  mul_pos C.epsilon_positive C.cuspScale_positive

theorem epsilon_lt_scale_mul (hscale : 1 ≤ C.cuspScale) :
    C.epsilon ≤ C.epsilon * C.cuspScale := by
  nlinarith [C.epsilon_positive]

theorem epsilon_div_cusp_pos : 0 < C.epsilon / C.cuspScale := by
  exact div_pos C.epsilon_positive C.cuspScale_positive

theorem epsilon_div_cusp_ne_zero : C.epsilon / C.cuspScale ≠ 0 := by
  exact ne_of_gt C.epsilon_div_cusp_pos

theorem epsilon_pow_pos (n : Nat) : 0 < C.epsilon ^ n :=
  pow_pos C.epsilon_positive n

theorem cusp_scale_pow_pos (n : Nat) : 0 < C.cuspScale ^ n :=
  pow_pos C.cuspScale_positive n

end SourceCuspClause

/-! ## 5. The complete Definition 3.1 source contract -/

structure SourceDefinition31Data (l : PrimeGeFive) where
  arithmetic : InitialThetaArithmeticData l
  selectedPlaces : Type u
  badPlaces : Type u
  reduction : SourceReductionClause selectedPlaces badPlaces
  torsion : SourceTorsionClause l
  orbicurve : SourceOrbicurveClause
  sections : SourceSectionClause
  cusp : SourceCuspClause
  arithmetic_reduction_compatibility : Prop
  arithmetic_reduction_compatibility_proved :
    arithmetic_reduction_compatibility
  arithmetic_torsion_compatibility : Prop
  arithmetic_torsion_compatibility_proved :
    arithmetic_torsion_compatibility
  arithmetic_orbicurve_compatibility : Prop
  arithmetic_orbicurve_compatibility_proved :
    arithmetic_orbicurve_compatibility
  arithmetic_section_compatibility : Prop
  arithmetic_section_compatibility_proved :
    arithmetic_section_compatibility
  arithmetic_cusp_compatibility : Prop
  arithmetic_cusp_compatibility_proved :
    arithmetic_cusp_compatibility

namespace SourceDefinition31Data

variable {l : PrimeGeFive} (S : SourceDefinition31Data l)

theorem arithmetic_reduction_spec :
    S.arithmetic_reduction_compatibility :=
  S.arithmetic_reduction_compatibility_proved

theorem arithmetic_torsion_spec :
    S.arithmetic_torsion_compatibility :=
  S.arithmetic_torsion_compatibility_proved

theorem arithmetic_orbicurve_spec :
    S.arithmetic_orbicurve_compatibility :=
  S.arithmetic_orbicurve_compatibility_proved

theorem arithmetic_section_spec :
    S.arithmetic_section_compatibility :=
  S.arithmetic_section_compatibility_proved

theorem arithmetic_cusp_spec :
    S.arithmetic_cusp_compatibility :=
  S.arithmetic_cusp_compatibility_proved

theorem selected_nonempty : Nonempty S.selectedPlaces :=
  S.reduction.partition.selectedNonempty

@[implicit_reducible] noncomputable def bad_finite : Fintype S.badPlaces :=
  S.reduction.partition.badFinite

def bad_included (b : S.badPlaces) : S.selectedPlaces :=
  S.reduction.partition.badIncluded b

theorem stable_reduction (b : S.badPlaces) :
    S.reduction.stableReduction b :=
  S.reduction.stableReduction_proved b

theorem multiplicative_reduction (b : S.badPlaces) :
    S.reduction.multiplicativeReduction b :=
  S.reduction.multiplicativeReduction_proved b

theorem split_multiplicative_reduction (b : S.badPlaces) :
    S.reduction.splitMultiplicativeReduction b :=
  S.reduction.splitMultiplicativeReduction_proved b

theorem q_parameter_nonzero (b : S.badPlaces) :
    S.reduction.qParameter b ≠ 0 :=
  S.reduction.qParameter_nonzero b

theorem q_parameter_contracting (b : S.badPlaces) :
    ‖S.reduction.qParameter b‖ < 1 :=
  S.reduction.qParameter_contracting b

theorem torsion_nonempty : Nonempty S.torsion.torsionCarrier :=
  S.torsion.torsionNonempty

theorem torsion_image_contains_SL2 :
    S.torsion.imageContainsSL2 :=
  S.torsion.imageContainsSL2_proved

theorem torsion_six_independent :
    S.torsion.sixTorsionIndependent :=
  S.torsion.sixTorsionIndependent_proved

theorem torsion_l_compatible :
    S.torsion.lTorsionCompatible :=
  S.torsion.lTorsionCompatible_proved

theorem cover_surjective :
    Function.Surjective S.orbicurve.coverToPunctured :=
  S.orbicurve.cover_surjective

theorem cover_cusp_count_pos : 0 < S.orbicurve.cuspCount :=
  S.orbicurve.cuspCount_pos

theorem exact_projection_surjective :
    Function.Surjective S.orbicurve.exactSequence.projection :=
  S.orbicurve.exactSequence.projection_surjective

theorem exact_injection_injective :
    Function.Injective S.orbicurve.exactSequence.injection :=
  S.orbicurve.exactSequence.injection_injective

theorem section_map_bijective :
    Function.Bijective S.sections.sectionMap := by
  exact ⟨S.sections.sectionMap_injective,
    S.sections.sectionMap_surjective⟩

theorem finite_place_data : S.sections.finitePlaceData :=
  S.sections.finitePlaceData_proved

theorem infinite_place_data : S.sections.infinitePlaceData :=
  S.sections.infinitePlaceData_proved

theorem cusp_positive : 0 < S.cusp.epsilon :=
  S.cusp.epsilon_positive

theorem cusp_nonzero : S.cusp.epsilon ≠ 0 :=
  S.cusp.epsilon_nonzero

theorem cusp_compatibility : S.cusp.epsilon_compatibility :=
  S.cusp.epsilon_compatibility_proved

theorem source_condition_bundle :
    Nonempty S.selectedPlaces ∧
      Nonempty (Fintype S.badPlaces) ∧
      (∀ b, S.reduction.stableReduction b) ∧
      (∀ b, S.reduction.splitMultiplicativeReduction b) ∧
      S.torsion.imageContainsSL2 ∧
      S.torsion.sixTorsionIndependent ∧
      S.torsion.lTorsionCompatible ∧
      Function.Surjective S.orbicurve.coverToPunctured ∧
      Function.Injective S.orbicurve.exactSequence.injection ∧
      Function.Surjective S.orbicurve.exactSequence.projection ∧
      Function.Bijective S.sections.sectionMap ∧
      0 < S.cusp.epsilon := by
  refine ⟨S.selected_nonempty, ⟨S.bad_finite⟩, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  · intro b
    exact S.reduction.stableReduction_proved b
  · intro b
    exact S.reduction.splitMultiplicativeReduction_proved b
  · exact S.torsion.imageContainsSL2_proved
  · exact S.torsion.sixTorsionIndependent_proved
  · exact S.torsion.lTorsionCompatible_proved
  · exact S.orbicurve.cover_surjective
  · exact S.orbicurve.exactSequence.injection_injective
  · exact S.orbicurve.exactSequence.projection_surjective
  · exact S.section_map_bijective
  · exact S.cusp.epsilon_positive

end SourceDefinition31Data

/-! ## 6. Faithful projection to the theorem input -/

namespace SourceDefinition31Data

variable {l : PrimeGeFive} (S : SourceDefinition31Data l)

def toInitialThetaInput : InitialThetaInput l where
  arithmetic := S.arithmetic
  selectedPlaces := S.selectedPlaces
  badPlaces := S.badPlaces
  badIncluded := S.reduction.partition.badIncluded
  selectedNonempty := S.reduction.partition.selectedNonempty
  badFinite := S.reduction.partition.badFinite
  stableReduction := S.reduction.stableReduction
  stableReduction_proved := S.reduction.stableReduction_proved
  torsionImage := S.torsion.imageContainsSL2
  torsionImage_proved := S.torsion.imageContainsSL2_proved
  cuspParameter := S.cusp.epsilon
  cusp_positive := S.cusp.epsilon_positive

@[simp] theorem toInitialThetaInput_arithmetic :
    (S.toInitialThetaInput).arithmetic = S.arithmetic := rfl

@[simp] theorem toInitialThetaInput_selectedPlaces :
    (S.toInitialThetaInput).selectedPlaces = S.selectedPlaces := rfl

@[simp] theorem toInitialThetaInput_badPlaces :
    (S.toInitialThetaInput).badPlaces = S.badPlaces := rfl

@[simp] theorem toInitialThetaInput_badIncluded (b : S.badPlaces) :
    (S.toInitialThetaInput).badIncluded b =
      S.reduction.partition.badIncluded b := rfl

@[simp] theorem toInitialThetaInput_selectedNonempty :
    (S.toInitialThetaInput).selectedNonempty =
      S.reduction.partition.selectedNonempty := rfl

@[simp] theorem toInitialThetaInput_badFinite :
    (S.toInitialThetaInput).badFinite =
      S.reduction.partition.badFinite := rfl

@[simp] theorem toInitialThetaInput_stableReduction (b : S.badPlaces) :
    (S.toInitialThetaInput).stableReduction b =
      S.reduction.stableReduction b := rfl

@[simp] theorem toInitialThetaInput_torsionImage :
    (S.toInitialThetaInput).torsionImage =
      S.torsion.imageContainsSL2 := rfl

@[simp] theorem toInitialThetaInput_cuspParameter :
    (S.toInitialThetaInput).cuspParameter = S.cusp.epsilon := rfl

theorem toInitialThetaInput_selected_nonempty :
    Nonempty (S.toInitialThetaInput).selectedPlaces :=
  (S.toInitialThetaInput).selectedNonempty

@[implicit_reducible] noncomputable def toInitialThetaInput_bad_finite :
    Fintype (S.toInitialThetaInput).badPlaces :=
  (S.toInitialThetaInput).badFinite

theorem toInitialThetaInput_stable (b : S.badPlaces) :
    (S.toInitialThetaInput).stableReduction b :=
  (S.toInitialThetaInput).stableReduction_proved b

theorem toInitialThetaInput_torsion :
    (S.toInitialThetaInput).torsionImage :=
  (S.toInitialThetaInput).torsionImage_proved

theorem toInitialThetaInput_cusp_positive :
    0 < (S.toInitialThetaInput).cuspParameter :=
  (S.toInitialThetaInput).cusp_positive

theorem toInitialThetaInput_bad_inclusion (b : S.badPlaces) :
    (S.toInitialThetaInput).badIncluded b =
      S.reduction.partition.badIncluded b := rfl

theorem toInitialThetaInput_q_nonzero (b : S.badPlaces) :
    S.reduction.qParameter b ≠ 0 :=
  S.reduction.qParameter_nonzero b

theorem toInitialThetaInput_q_contracting (b : S.badPlaces) :
    ‖S.reduction.qParameter b‖ < 1 :=
  S.reduction.qParameter_contracting b

theorem toInitialThetaInput_split_multiplicative (b : S.badPlaces) :
    S.reduction.splitMultiplicativeReduction b :=
  S.reduction.splitMultiplicativeReduction_proved b

theorem toInitialThetaInput_l_torsion :
    S.torsion.lTorsionCompatible :=
  S.torsion.lTorsionCompatible_proved

theorem toInitialThetaInput_cover_surjective :
    Function.Surjective S.orbicurve.coverToPunctured :=
  S.orbicurve.cover_surjective

theorem toInitialThetaInput_exact_sequence :
    ∀ x, S.orbicurve.exactSequence.projection x = 1 ↔
      ∃ y, S.orbicurve.exactSequence.injection y = x := by
  intro x
  exact S.orbicurve.exactSequence.exact_at_cover x

theorem toInitialThetaInput_section_inverse (x :
    S.sections.modifiedValuationCarrier) :
    S.sections.sectionMap (S.sections.sectionRightInverse x) = x :=
  S.sections.section_right_inverse x

theorem toInitialThetaInput_cusp_compatibility :
    S.cusp.epsilon_compatibility :=
  S.cusp.epsilon_compatibility_proved

theorem toInitialThetaInput_arithmetic_reduction :
    S.arithmetic_reduction_compatibility :=
  S.arithmetic_reduction_compatibility_proved

theorem toInitialThetaInput_arithmetic_torsion :
    S.arithmetic_torsion_compatibility :=
  S.arithmetic_torsion_compatibility_proved

theorem toInitialThetaInput_arithmetic_orbicurve :
    S.arithmetic_orbicurve_compatibility :=
  S.arithmetic_orbicurve_compatibility_proved

theorem toInitialThetaInput_arithmetic_section :
    S.arithmetic_section_compatibility :=
  S.arithmetic_section_compatibility_proved

theorem toInitialThetaInput_arithmetic_cusp :
    S.arithmetic_cusp_compatibility :=
  S.arithmetic_cusp_compatibility_proved

theorem toInitialThetaInput_reduction_bundle :
    (∀ b, (S.toInitialThetaInput).stableReduction b) ∧
      (∀ b, S.reduction.qParameter b ≠ 0) ∧
      (∀ b, ‖S.reduction.qParameter b‖ < 1) := by
  refine ⟨?_, ?_, ?_⟩
  · intro b
    exact (S.toInitialThetaInput).stableReduction_proved b
  · intro b
    exact S.reduction.qParameter_nonzero b
  · intro b
    exact S.reduction.qParameter_contracting b

theorem toInitialThetaInput_source_bundle :
    Nonempty (S.toInitialThetaInput).selectedPlaces ∧
      Nonempty (Fintype (S.toInitialThetaInput).badPlaces) ∧
      (S.toInitialThetaInput).torsionImage ∧
      0 < (S.toInitialThetaInput).cuspParameter := by
  exact ⟨S.toInitialThetaInput.selectedNonempty,
    ⟨S.toInitialThetaInput.badFinite⟩,
    S.toInitialThetaInput.torsionImage_proved,
    S.toInitialThetaInput.cusp_positive⟩

end SourceDefinition31Data

/-! ## 7. Morphisms and transport of Definition 3.1 data -/

structure SourcePlacePartitionHom
    {Selected₁ Bad₁ Selected₂ Bad₂ : Type u}
    (P₁ : SourcePlacePartition Selected₁ Bad₁)
    (P₂ : SourcePlacePartition Selected₂ Bad₂) where
  selectedMap : Selected₁ → Selected₂
  badMap : Bad₁ → Bad₂
  included_naturality : ∀ b,
    selectedMap (P₁.badIncluded b) =
      P₂.badIncluded (badMap b)
  selectedLabel_naturality : ∀ s,
    P₂.selectedLabel (selectedMap s) = P₁.selectedLabel s
  badLabel_naturality : ∀ b,
    P₂.badLabel (badMap b) = P₁.badLabel b

namespace SourcePlacePartitionHom

variable {Selected₁ Bad₁ Selected₂ Bad₂ : Type u}
variable {P₁ : SourcePlacePartition Selected₁ Bad₁}
variable {P₂ : SourcePlacePartition Selected₂ Bad₂}

def refl (P : SourcePlacePartition Selected₁ Bad₁) :
    SourcePlacePartitionHom P P where
  selectedMap := id
  badMap := id
  included_naturality := by intro b; rfl
  selectedLabel_naturality := by intro s; rfl
  badLabel_naturality := by intro b; rfl

theorem included_naturality_spec (f : SourcePlacePartitionHom P₁ P₂)
    (b : Bad₁) :
    f.selectedMap (P₁.badIncluded b) =
      P₂.badIncluded (f.badMap b) :=
  f.included_naturality b

theorem selectedLabel_naturality_spec (f : SourcePlacePartitionHom P₁ P₂)
    (s : Selected₁) :
    P₂.selectedLabel (f.selectedMap s) = P₁.selectedLabel s :=
  f.selectedLabel_naturality s

theorem badLabel_naturality_spec (f : SourcePlacePartitionHom P₁ P₂)
    (b : Bad₁) :
    P₂.badLabel (f.badMap b) = P₁.badLabel b :=
  f.badLabel_naturality b

def comp {Selected₃ Bad₃ : Type u}
    {P₃ : SourcePlacePartition Selected₃ Bad₃}
    (f : SourcePlacePartitionHom P₁ P₂)
    (g : SourcePlacePartitionHom P₂ P₃) :
    SourcePlacePartitionHom P₁ P₃ where
  selectedMap := g.selectedMap ∘ f.selectedMap
  badMap := g.badMap ∘ f.badMap
  included_naturality := by
    intro b
    rw [Function.comp_apply, Function.comp_apply,
      f.included_naturality, g.included_naturality]
  selectedLabel_naturality := by
    intro s
    rw [Function.comp_apply, g.selectedLabel_naturality,
      f.selectedLabel_naturality]
  badLabel_naturality := by
    intro b
    rw [Function.comp_apply, g.badLabel_naturality,
      f.badLabel_naturality]

theorem comp_selectedMap {Selected₃ Bad₃ : Type u}
    {P₃ : SourcePlacePartition Selected₃ Bad₃}
    (f : SourcePlacePartitionHom P₁ P₂)
    (g : SourcePlacePartitionHom P₂ P₃) (s : Selected₁) :
    (f.comp g).selectedMap s = g.selectedMap (f.selectedMap s) := rfl

theorem comp_badMap {Selected₃ Bad₃ : Type u}
    {P₃ : SourcePlacePartition Selected₃ Bad₃}
    (f : SourcePlacePartitionHom P₁ P₂)
    (g : SourcePlacePartitionHom P₂ P₃) (b : Bad₁) :
    (f.comp g).badMap b = g.badMap (f.badMap b) := rfl

theorem comp_included_naturality {Selected₃ Bad₃ : Type u}
    {P₃ : SourcePlacePartition Selected₃ Bad₃}
    (f : SourcePlacePartitionHom P₁ P₂)
    (g : SourcePlacePartitionHom P₂ P₃) (b : Bad₁) :
    (f.comp g).selectedMap (P₁.badIncluded b) =
      P₃.badIncluded ((f.comp g).badMap b) :=
  (f.comp g).included_naturality b

theorem refl_selected (P : SourcePlacePartition Selected₁ Bad₁)
    (s : Selected₁) : (refl P).selectedMap s = s := rfl

theorem refl_bad (P : SourcePlacePartition Selected₁ Bad₁)
    (b : Bad₁) : (refl P).badMap b = b := rfl

end SourcePlacePartitionHom

structure SourceReductionClauseHom
    {Selected₁ Bad₁ Selected₂ Bad₂ : Type u}
    (R₁ : SourceReductionClause Selected₁ Bad₁)
    (R₂ : SourceReductionClause Selected₂ Bad₂) where
  placeHom : SourcePlacePartitionHom R₁.partition R₂.partition
  qMap : Bad₁ → Bad₂
  qMap_eq_placeHom : ∀ b, qMap b = placeHom.badMap b
  qParameter_naturality : ∀ b,
    R₂.qParameter (qMap b) = R₁.qParameter b
  stable_naturality : ∀ b,
    R₂.stableReduction (qMap b) ↔ R₁.stableReduction b
  multiplicative_naturality : ∀ b,
    R₂.multiplicativeReduction (qMap b) ↔
      R₁.multiplicativeReduction b
  split_naturality : ∀ b,
    R₂.splitMultiplicativeReduction (qMap b) ↔
      R₁.splitMultiplicativeReduction b

namespace SourceReductionClauseHom

variable {Selected₁ Bad₁ Selected₂ Bad₂ : Type u}
variable {R₁ : SourceReductionClause Selected₁ Bad₁}
variable {R₂ : SourceReductionClause Selected₂ Bad₂}

def refl (R : SourceReductionClause Selected₁ Bad₁) :
    SourceReductionClauseHom R R where
  placeHom := SourcePlacePartitionHom.refl R.partition
  qMap := id
  qMap_eq_placeHom := by intro b; rfl
  qParameter_naturality := by intro b; rfl
  stable_naturality := by intro b; rfl
  multiplicative_naturality := by intro b; rfl
  split_naturality := by intro b; rfl

theorem q_parameter_naturality (f : SourceReductionClauseHom R₁ R₂)
    (b : Bad₁) :
    R₂.qParameter (f.qMap b) = R₁.qParameter b :=
  f.qParameter_naturality b

theorem stable_naturality_spec (f : SourceReductionClauseHom R₁ R₂)
    (b : Bad₁) :
    R₂.stableReduction (f.qMap b) ↔ R₁.stableReduction b :=
  f.stable_naturality b

theorem multiplicative_naturality_spec (f : SourceReductionClauseHom R₁ R₂)
    (b : Bad₁) :
    R₂.multiplicativeReduction (f.qMap b) ↔
      R₁.multiplicativeReduction b :=
  f.multiplicative_naturality b

theorem split_naturality_spec (f : SourceReductionClauseHom R₁ R₂)
    (b : Bad₁) :
    R₂.splitMultiplicativeReduction (f.qMap b) ↔
      R₁.splitMultiplicativeReduction b :=
  f.split_naturality b

theorem q_norm_naturality (f : SourceReductionClauseHom R₁ R₂)
    (b : Bad₁) :
    ‖R₂.qParameter (f.qMap b)‖ = ‖R₁.qParameter b‖ := by
  rw [f.q_parameter_naturality b]

theorem q_nonzero_transport (f : SourceReductionClauseHom R₁ R₂)
    (b : Bad₁) : R₂.qParameter (f.qMap b) ≠ 0 := by
  rw [f.q_parameter_naturality b]
  exact R₁.qParameter_nonzero b

theorem q_contracting_transport (f : SourceReductionClauseHom R₁ R₂)
    (b : Bad₁) : ‖R₂.qParameter (f.qMap b)‖ < 1 := by
  rw [f.q_parameter_naturality b]
  exact R₁.qParameter_contracting b

def comp {Selected₃ Bad₃ : Type u}
    {R₃ : SourceReductionClause Selected₃ Bad₃}
    (f : SourceReductionClauseHom R₁ R₂)
    (g : SourceReductionClauseHom R₂ R₃) :
    SourceReductionClauseHom R₁ R₃ where
  placeHom := SourcePlacePartitionHom.comp f.placeHom g.placeHom
  qMap := g.qMap ∘ f.qMap
  qMap_eq_placeHom := by
    intro b
    rw [Function.comp_apply, f.qMap_eq_placeHom,
      g.qMap_eq_placeHom]
    rfl
  qParameter_naturality := by
    intro b
    rw [Function.comp_apply, g.qParameter_naturality,
      f.qParameter_naturality]
  stable_naturality := by
    intro b
    rw [Function.comp_apply, g.stable_naturality]
    exact f.stable_naturality b
  multiplicative_naturality := by
    intro b
    rw [Function.comp_apply, g.multiplicative_naturality]
    exact f.multiplicative_naturality b
  split_naturality := by
    intro b
    rw [Function.comp_apply, g.split_naturality]
    exact f.split_naturality b

theorem comp_q_parameter_naturality {Selected₃ Bad₃ : Type u}
    {R₃ : SourceReductionClause Selected₃ Bad₃}
    (f : SourceReductionClauseHom R₁ R₂)
    (g : SourceReductionClauseHom R₂ R₃) (b : Bad₁) :
    R₃.qParameter ((f.comp g).qMap b) = R₁.qParameter b :=
  (f.comp g).qParameter_naturality b

theorem refl_q_parameter (R : SourceReductionClause Selected₁ Bad₁)
    (b : Bad₁) : R.qParameter ((refl R).qMap b) = R.qParameter b := rfl

end SourceReductionClauseHom

structure SourceDefinition31Morphism
    {l : PrimeGeFive}
    (S₁ S₂ : SourceDefinition31Data l) where
  arithmetic_eq : S₁.arithmetic = S₂.arithmetic
  reductionHom : SourceReductionClauseHom S₁.reduction S₂.reduction
  torsionMap : S₁.torsion.torsionCarrier → S₂.torsion.torsionCarrier
  torsionLabel_naturality : ∀ x,
    S₂.torsion.torsionLabel (torsionMap x) = S₁.torsion.torsionLabel x
  torsion_image_naturality :
    S₂.torsion.imageContainsSL2 ↔ S₁.torsion.imageContainsSL2
  orbicurve_curveMap : S₁.orbicurve.curve → S₂.orbicurve.curve
  orbicurve_puncturedMap :
    S₁.orbicurve.puncturedCurve → S₂.orbicurve.puncturedCurve
  orbicurve_coverMap : S₁.orbicurve.cover → S₂.orbicurve.cover
  cover_naturality : ∀ x,
    orbicurve_puncturedMap
      (S₁.orbicurve.coverToPunctured x) =
      S₂.orbicurve.coverToPunctured (orbicurve_coverMap x)
  cusp_equality : S₂.cusp = S₁.cusp
  section_valuationMap :
    S₁.sections.valuationCarrier → S₂.sections.valuationCarrier
  section_modifiedMap :
    S₁.sections.modifiedValuationCarrier →
      S₂.sections.modifiedValuationCarrier
  section_naturality : ∀ x,
    section_modifiedMap (S₁.sections.sectionMap x) =
      S₂.sections.sectionMap (section_valuationMap x)

namespace SourceDefinition31Morphism

variable {l : PrimeGeFive} {S₁ S₂ : SourceDefinition31Data l}

def refl (S : SourceDefinition31Data l) :
    SourceDefinition31Morphism S S where
  arithmetic_eq := rfl
  reductionHom := SourceReductionClauseHom.refl S.reduction
  torsionMap := id
  torsionLabel_naturality := by intro x; rfl
  torsion_image_naturality := Iff.rfl
  orbicurve_curveMap := id
  orbicurve_puncturedMap := id
  orbicurve_coverMap := id
  cover_naturality := by intro x; rfl
  cusp_equality := rfl
  section_valuationMap := id
  section_modifiedMap := id
  section_naturality := by intro x; rfl

theorem arithmetic_eq_spec (f : SourceDefinition31Morphism S₁ S₂) :
    S₁.arithmetic = S₂.arithmetic := f.arithmetic_eq

theorem reduction_q_naturality (f : SourceDefinition31Morphism S₁ S₂)
    (b : S₁.badPlaces) :
    S₂.reduction.qParameter (f.reductionHom.qMap b) =
      S₁.reduction.qParameter b :=
  f.reductionHom.q_parameter_naturality b

theorem reduction_stable_naturality (f : SourceDefinition31Morphism S₁ S₂)
    (b : S₁.badPlaces) :
    S₂.reduction.stableReduction (f.reductionHom.qMap b) ↔
      S₁.reduction.stableReduction b :=
  f.reductionHom.stable_naturality b

theorem reduction_split_naturality (f : SourceDefinition31Morphism S₁ S₂)
    (b : S₁.badPlaces) :
    S₂.reduction.splitMultiplicativeReduction (f.reductionHom.qMap b) ↔
      S₁.reduction.splitMultiplicativeReduction b :=
  f.reductionHom.split_naturality b

theorem torsion_label_naturality_spec (f : SourceDefinition31Morphism S₁ S₂)
    (x : S₁.torsion.torsionCarrier) :
    S₂.torsion.torsionLabel (f.torsionMap x) =
      S₁.torsion.torsionLabel x :=
  f.torsionLabel_naturality x

theorem torsion_image_naturality_spec (f : SourceDefinition31Morphism S₁ S₂) :
    S₂.torsion.imageContainsSL2 ↔ S₁.torsion.imageContainsSL2 :=
  f.torsion_image_naturality

theorem cover_naturality_spec (f : SourceDefinition31Morphism S₁ S₂)
    (x : S₁.orbicurve.cover) :
    f.orbicurve_puncturedMap (S₁.orbicurve.coverToPunctured x) =
      S₂.orbicurve.coverToPunctured (f.orbicurve_coverMap x) :=
  f.cover_naturality x

theorem cusp_equality_spec (f : SourceDefinition31Morphism S₁ S₂) :
    S₂.cusp = S₁.cusp := f.cusp_equality

theorem section_naturality_spec (f : SourceDefinition31Morphism S₁ S₂)
    (x : S₁.sections.valuationCarrier) :
    f.section_modifiedMap (S₁.sections.sectionMap x) =
      S₂.sections.sectionMap (f.section_valuationMap x) :=
  f.section_naturality x

def comp {S₃ : SourceDefinition31Data l}
    (f : SourceDefinition31Morphism S₁ S₂)
    (g : SourceDefinition31Morphism S₂ S₃) :
    SourceDefinition31Morphism S₁ S₃ where
  arithmetic_eq := f.arithmetic_eq.trans g.arithmetic_eq
  reductionHom := SourceReductionClauseHom.comp f.reductionHom g.reductionHom
  torsionMap := g.torsionMap ∘ f.torsionMap
  torsionLabel_naturality := by
    intro x
    rw [Function.comp_apply, g.torsionLabel_naturality,
      f.torsionLabel_naturality]
  torsion_image_naturality :=
    g.torsion_image_naturality.trans f.torsion_image_naturality
  orbicurve_curveMap := g.orbicurve_curveMap ∘ f.orbicurve_curveMap
  orbicurve_puncturedMap :=
    g.orbicurve_puncturedMap ∘ f.orbicurve_puncturedMap
  orbicurve_coverMap := g.orbicurve_coverMap ∘ f.orbicurve_coverMap
  cover_naturality := by
    intro x
    rw [Function.comp_apply, Function.comp_apply,
      f.cover_naturality, g.cover_naturality]
  cusp_equality := g.cusp_equality.trans f.cusp_equality
  section_valuationMap := g.section_valuationMap ∘ f.section_valuationMap
  section_modifiedMap := g.section_modifiedMap ∘ f.section_modifiedMap
  section_naturality := by
    intro x
    rw [Function.comp_apply, Function.comp_apply,
      f.section_naturality, g.section_naturality]

theorem comp_reduction_q_naturality {S₃ : SourceDefinition31Data l}
    (f : SourceDefinition31Morphism S₁ S₂)
    (g : SourceDefinition31Morphism S₂ S₃) (b : S₁.badPlaces) :
    S₃.reduction.qParameter ((f.comp g).reductionHom.qMap b) =
      S₁.reduction.qParameter b :=
  (f.comp g).reduction_q_naturality b

theorem refl_cover_naturality (S : SourceDefinition31Data l)
    (x : S.orbicurve.cover) :
    (refl S).orbicurve_puncturedMap (S.orbicurve.coverToPunctured x) =
      S.orbicurve.coverToPunctured ((refl S).orbicurve_coverMap x) := rfl

theorem refl_cusp (S : SourceDefinition31Data l) :
    S.cusp = S.cusp := (refl S).cusp_equality

end SourceDefinition31Morphism

/-! ## 8. Application certificates and field-by-field recognition -/

structure SourceDefinition31Application (l : PrimeGeFive) where
  source : SourceDefinition31Data l
  input : InitialThetaInput l
  input_eq_source_projection :
    input = source.toInitialThetaInput

namespace SourceDefinition31Application

variable {l : PrimeGeFive} (A : SourceDefinition31Application l)

theorem input_eq_projection :
    A.input = A.source.toInitialThetaInput :=
  A.input_eq_source_projection

theorem input_arithmetic :
    A.input.arithmetic = A.source.arithmetic := by
  rw [A.input_eq_source_projection]
  rfl

theorem input_selectedPlaces :
    A.input.selectedPlaces = A.source.selectedPlaces := by
  rw [A.input_eq_source_projection]
  rfl

theorem input_badPlaces :
    A.input.badPlaces = A.source.badPlaces := by
  rw [A.input_eq_source_projection]
  rfl

theorem input_selected_nonempty : Nonempty A.input.selectedPlaces := by
  rw [A.input_selectedPlaces]
  exact A.source.selected_nonempty

@[implicit_reducible] noncomputable def input_bad_finite : Fintype A.input.badPlaces := by
  rw [A.input_badPlaces]
  exact A.source.bad_finite

theorem input_stable (b : A.source.badPlaces) :
    A.source.toInitialThetaInput.stableReduction b :=
  A.source.toInitialThetaInput_stable b

theorem input_torsion : A.input.torsionImage := by
  rw [A.input_eq_projection]
  exact A.source.toInitialThetaInput_torsion

theorem input_cusp_positive : 0 < A.input.cuspParameter := by
  rw [A.input_eq_projection]
  exact A.source.toInitialThetaInput_cusp_positive

theorem input_bad_included (b : A.source.badPlaces) :
    A.source.toInitialThetaInput.badIncluded b =
      A.source.reduction.partition.badIncluded b := by
  rfl

theorem input_q_nonzero (b : A.source.badPlaces) :
    A.source.reduction.qParameter b ≠ 0 :=
  A.source.reduction.qParameter_nonzero b

theorem input_q_contracting (b : A.source.badPlaces) :
    ‖A.source.reduction.qParameter b‖ < 1 :=
  A.source.reduction.qParameter_contracting b

theorem input_split_multiplicative (b : A.source.badPlaces) :
    A.source.reduction.splitMultiplicativeReduction b :=
  A.source.reduction.splitMultiplicativeReduction_proved b

theorem input_exact_projection :
    Function.Surjective A.source.orbicurve.exactSequence.projection :=
  A.source.exact_projection_surjective

theorem input_exact_injection :
    Function.Injective A.source.orbicurve.exactSequence.injection :=
  A.source.exact_injection_injective

theorem input_cover_surjective :
    Function.Surjective A.source.orbicurve.coverToPunctured :=
  A.source.cover_surjective

theorem input_section_bijective :
    Function.Bijective A.source.sections.sectionMap :=
  A.source.section_map_bijective

theorem input_finite_place_data : A.source.sections.finitePlaceData :=
  A.source.finite_place_data

theorem input_infinite_place_data : A.source.sections.infinitePlaceData :=
  A.source.infinite_place_data

theorem input_cusp_compatibility : A.source.cusp.epsilon_compatibility :=
  A.source.cusp_compatibility

theorem input_arithmetic_reduction :
    A.source.arithmetic_reduction_compatibility :=
  A.source.arithmetic_reduction_spec

theorem input_arithmetic_torsion :
    A.source.arithmetic_torsion_compatibility :=
  A.source.arithmetic_torsion_spec

theorem input_arithmetic_orbicurve :
    A.source.arithmetic_orbicurve_compatibility :=
  A.source.arithmetic_orbicurve_spec

theorem input_arithmetic_section :
    A.source.arithmetic_section_compatibility :=
  A.source.arithmetic_section_spec

theorem input_arithmetic_cusp :
    A.source.arithmetic_cusp_compatibility :=
  A.source.arithmetic_cusp_spec

theorem all_source_fields :
    Nonempty A.input.selectedPlaces ∧
      Nonempty (Fintype A.input.badPlaces) ∧
      (∀ b : A.source.badPlaces,
        A.source.toInitialThetaInput.stableReduction b) ∧
      A.input.torsionImage ∧
      0 < A.input.cuspParameter ∧
      Function.Surjective A.source.orbicurve.coverToPunctured ∧
      Function.Injective A.source.orbicurve.exactSequence.injection ∧
      Function.Surjective A.source.orbicurve.exactSequence.projection ∧
      Function.Bijective A.source.sections.sectionMap := by
  refine ⟨A.input_selected_nonempty, ⟨A.input_bad_finite⟩, ?_,
    A.input_torsion, A.input_cusp_positive, A.input_cover_surjective,
    A.input_exact_injection, A.input_exact_projection,
    A.input_section_bijective⟩
  intro b
  exact A.input_stable b

end SourceDefinition31Application

structure SourceDefinition31FieldWitness (l : PrimeGeFive) where
  source : SourceDefinition31Data l
  selectedWitness : source.selectedPlaces
  badWitness : source.badPlaces
  exactKernelWitness :
    source.orbicurve.exactSequence.geometricGroup
  cuspWitness : Real
  selectedWitness_spec : True
  badWitness_spec : True
  exactKernelWitness_spec :
    source.orbicurve.exactSequence.injection exactKernelWitness =
      source.orbicurve.exactSequence.injection exactKernelWitness
  cuspWitness_spec : cuspWitness = source.cusp.epsilon

namespace SourceDefinition31FieldWitness

variable {l : PrimeGeFive} (W : SourceDefinition31FieldWitness l)

theorem selected_witness : W.selectedWitness ∈ Set.univ := by
  exact Set.mem_univ _

theorem bad_witness : W.badWitness ∈ Set.univ := by
  exact Set.mem_univ _

theorem exact_kernel_witness :
    W.source.orbicurve.exactSequence.injection W.exactKernelWitness =
      W.source.orbicurve.exactSequence.injection W.exactKernelWitness :=
  W.exactKernelWitness_spec

theorem cusp_witness : W.cuspWitness = W.source.cusp.epsilon :=
  W.cuspWitness_spec

theorem cusp_witness_positive : 0 < W.cuspWitness := by
  rw [W.cusp_witness]
  exact W.source.cusp.epsilon_positive

theorem selected_witness_nonempty :
    Nonempty W.source.selectedPlaces :=
  W.source.selected_nonempty

@[implicit_reducible] noncomputable def bad_witness_finite : Fintype W.source.badPlaces :=
  W.source.bad_finite

theorem source_torsion_witness : W.source.torsion.imageContainsSL2 :=
  W.source.torsion_image_contains_SL2

theorem source_reduction_witness (b : W.source.badPlaces) :
    W.source.reduction.stableReduction b ∧
      W.source.reduction.splitMultiplicativeReduction b :=
  ⟨W.source.stable_reduction b,
    W.source.split_multiplicative_reduction b⟩

end SourceDefinition31FieldWitness

/-! ## 9. Derived arithmetic and order facts retained by the bridge -/

namespace SourceDefinition31Data

variable {l : PrimeGeFive} (S : SourceDefinition31Data l)

theorem q_log_abs_negative (b : S.badPlaces) :
    Real.log ‖S.reduction.qParameter b‖ < 0 := by
  have hp := S.reduction.q_norm_pos b
  have hlt := S.reduction.q_norm_lt_one b
  simpa using Real.strictMonoOn_log
    (by exact Set.mem_Ioi.mpr hp)
    (by exact Set.mem_Ioi.mpr (by norm_num : (0 : Real) < 1)) hlt

theorem neg_log_q_positive (b : S.badPlaces) :
    0 < -Real.log ‖S.reduction.qParameter b‖ := by
  linarith [S.q_log_abs_negative b]

theorem q_log_abs_nonzero (b : S.badPlaces) :
    Real.log ‖S.reduction.qParameter b‖ ≠ 0 := by
  exact ne_of_lt (S.q_log_abs_negative b)

theorem q_log_abs_le_zero (b : S.badPlaces) :
    Real.log ‖S.reduction.qParameter b‖ ≤ 0 :=
  le_of_lt (S.q_log_abs_negative b)

theorem neg_log_q_nonnegative (b : S.badPlaces) :
    0 ≤ -Real.log ‖S.reduction.qParameter b‖ :=
  le_of_lt (S.neg_log_q_positive b)

theorem q_power_log (b : S.badPlaces) (n : Nat) :
    Real.log ‖S.reduction.qParameter b ^ n‖ =
      n * Real.log ‖S.reduction.qParameter b‖ := by
  rw [norm_pow, Real.log_pow]

theorem q_power_log_negative (b : S.badPlaces) (n : Nat)
    (hn : 0 < n) :
    Real.log ‖S.reduction.qParameter b ^ n‖ < 0 := by
  rw [S.q_power_log]
  have h := S.q_log_abs_negative b
  have hnreal : 0 < (n : Real) := by exact_mod_cast hn
  nlinarith

theorem q_power_neg_log_positive (b : S.badPlaces) (n : Nat)
    (hn : 0 < n) :
    0 < -Real.log ‖S.reduction.qParameter b ^ n‖ := by
  linarith [S.q_power_log_negative b n hn]

theorem q_inverse_norm (b : S.badPlaces) :
    ‖(S.reduction.qParameter b)⁻¹‖ =
      (‖S.reduction.qParameter b‖)⁻¹ := by
  exact norm_inv _

theorem q_inverse_norm_gt_one (b : S.badPlaces) :
    1 < ‖(S.reduction.qParameter b)⁻¹‖ := by
  rw [S.q_inverse_norm]
  exact (one_lt_inv₀ (S.reduction.q_norm_pos b)).mpr
    (S.reduction.q_norm_lt_one b)

theorem q_mul_inverse_norm (b : S.badPlaces) :
    ‖S.reduction.qParameter b * (S.reduction.qParameter b)⁻¹‖ = 1 := by
  rw [mul_inv_cancel₀ (S.reduction.qParameter_nonzero b), norm_one]

theorem q_inverse_mul_norm (b : S.badPlaces) :
    ‖(S.reduction.qParameter b)⁻¹ * S.reduction.qParameter b‖ = 1 := by
  rw [inv_mul_cancel₀ (S.reduction.qParameter_nonzero b), norm_one]

theorem q_contracting_sequence (b : S.badPlaces) :
    ∀ n, ‖S.reduction.qParameter b‖ ^ (n + 1) < 1 := by
  intro n
  exact S.reduction.q_contracting_pow b n

theorem q_sequence_le_one (b : S.badPlaces) (n : Nat) :
    ‖S.reduction.qParameter b‖ ^ n ≤ 1 := by
  exact pow_le_one₀ (S.reduction.q_norm_nonnegative b)
    (S.reduction.q_norm_le_one b)

theorem cusp_epsilon_pow_log (n : Nat) :
    Real.log (S.cusp.epsilon ^ n) =
      n * Real.log S.cusp.epsilon := by
  rw [Real.log_pow]

theorem cusp_scale_pow_nonzero (n : Nat) :
    S.cusp.cuspScale ^ n ≠ 0 :=
  pow_ne_zero n (S.cusp.cusp_scale_ne_zero)

theorem cusp_product_nonzero :
    S.cusp.epsilon * S.cusp.cuspScale ≠ 0 :=
  S.cusp.epsilon_scale_ne_zero

theorem source_label_lift (b : S.badPlaces) :
    S.reduction.partition.badLabel b =
      S.reduction.partition.selectedLabel
        (S.reduction.partition.badIncluded b) :=
  (S.reduction.partition.badLabel_compatible b).symm

theorem source_label_round_trip (b : S.badPlaces) :
    S.reduction.partition.selectedLabel
        (S.reduction.partition.badIncluded b) =
      S.reduction.partition.badLabel b :=
  S.reduction.partition.badLabel_compatible b

theorem source_reduction_bundle (b : S.badPlaces) :
    S.reduction.stableReduction b ∧
      S.reduction.multiplicativeReduction b ∧
      S.reduction.splitMultiplicativeReduction b ∧
      S.reduction.qParameter b ≠ 0 ∧
      ‖S.reduction.qParameter b‖ < 1 := by
  exact ⟨S.reduction.stableReduction_proved b,
    S.reduction.multiplicativeReduction_proved b,
    S.reduction.splitMultiplicativeReduction_proved b,
    S.reduction.qParameter_nonzero b,
    S.reduction.qParameter_contracting b⟩

theorem source_torsion_bundle :
    Nonempty S.torsion.torsionCarrier ∧
      S.torsion.imageContainsSL2 ∧
      S.torsion.sixTorsionIndependent ∧
      S.torsion.lTorsionCompatible := by
  exact ⟨S.torsion.torsionNonempty,
    S.torsion.imageContainsSL2_proved,
    S.torsion.sixTorsionIndependent_proved,
    S.torsion.lTorsionCompatible_proved⟩

theorem source_curve_bundle :
    Function.Surjective S.orbicurve.coverToPunctured ∧
      0 < S.orbicurve.cuspCount ∧
      S.orbicurve.curveCompatibility := by
  exact ⟨S.orbicurve.cover_surjective,
    S.orbicurve.cuspCount_pos,
    S.orbicurve.curveCompatibility_proved⟩

theorem source_section_bundle :
    Function.Bijective S.sections.sectionMap ∧
      S.sections.finitePlaceData ∧ S.sections.infinitePlaceData := by
  exact ⟨S.section_map_bijective,
    S.sections.finitePlaceData_proved,
    S.sections.infinitePlaceData_proved⟩

theorem source_cusp_bundle :
    0 < S.cusp.epsilon ∧ S.cusp.epsilon ≠ 0 ∧
      S.cusp.epsilon_compatibility ∧
      0 < S.cusp.cuspScale := by
  exact ⟨S.cusp.epsilon_positive,
    S.cusp.epsilon_nonzero,
    S.cusp.epsilon_compatibility_proved,
    S.cusp.cuspScale_positive⟩

end SourceDefinition31Data

/-! ## 10. Audit registration -/

end Theorem311Source

end

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def sourceDefinition31Boundary : Obligation :=
  { id := "IUT-I.initial-theta-source-definition31-boundary"
    source := "IUT I, Definition 3.1"
    status := VerificationStatus.interface
    note :=
      "Every source-facing clause is represented by a typed field and its " ++
        "projection into InitialThetaInput is proved. This is a faithful " ++
        "boundary and field-level recognition layer; construction of an " ++
        "inhabitant from arbitrary arithmetic data remains pending."
    dependsOn := ["IUT-I.initial-theta-arithmetic-data"] }

end LeanFormal.IUT.Audit
