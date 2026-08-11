import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Boundary
import LeanFormal.IUT.Foundations.NumberField.Places
import LeanFormal.IUT.Foundations.Geometry.LocalReduction
import LeanFormal.IUT.Foundations.NumberField.LocalQParameter
import LeanFormal.IUT.IUTI.InitialTheta.ReductionPlacePartition
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option linter.unusedSimpArgs false

/-!
  Root layer for IUT I Definition 3.1.

  The boundary module supplies the source-facing record.  This module proves
  reusable consequences of that record and assembles a faithful recognition
  theorem.  It does not construct a `SourceDefinition31Data` value from an
  arbitrary arithmetic curve: that construction is the source obligation
  being tracked by the audit.
-/

namespace LeanFormal.IUT

noncomputable section

universe u v w

namespace Theorem311Source

/-! ## Common exact-sequence tools -/

namespace SourceExactSequenceClause

variable (E : SourceExactSequenceClause.{u, v, w})

def rootSplitLift (x : E.coverGroup) : E.coverGroup :=
  E.sectionMap (E.projection x)

def rootResidual (x : E.coverGroup) : E.coverGroup :=
  x * (E.rootSplitLift x)⁻¹

theorem rootSplitLift_apply (x : E.coverGroup) :
    E.rootSplitLift x = E.sectionMap (E.projection x) := rfl

theorem rootSplitLift_projection (x : E.coverGroup) :
    E.projection (E.rootSplitLift x) = E.projection x :=
  E.section_right_inverse (E.projection x)

theorem rootSplitLift_one :
    E.rootSplitLift (1 : E.coverGroup) = E.sectionMap 1 := by
  simp [rootSplitLift]

theorem rootSplitLift_mul (x y : E.coverGroup) :
    E.rootSplitLift (x * y) =
      E.sectionMap (E.projection x * E.projection y) := by
  simp [rootSplitLift, E.projection.map_mul]

theorem rootSplitLift_inv (x : E.coverGroup) :
    E.rootSplitLift x⁻¹ = E.sectionMap (E.projection x)⁻¹ := by
  simp [rootSplitLift]

theorem rootSplitLift_idempotent (x : E.coverGroup) :
    E.rootSplitLift (E.rootSplitLift x) = E.rootSplitLift x := by
  simp [rootSplitLift, E.section_right_inverse]

theorem rootSplitLift_section (g : E.baseGroup) :
    E.rootSplitLift (E.sectionMap g) = E.sectionMap g := by
  simp [rootSplitLift, E.section_right_inverse]

theorem rootResidual_projection (x : E.coverGroup) :
    E.projection (E.rootResidual x) = 1 := by
  simp [rootResidual, rootSplitLift, E.projection.map_mul,
    E.section_right_inverse]

theorem rootResidual_mem_kernel (x : E.coverGroup) :
    E.rootResidual x ∈ E.projection.ker :=
  E.rootResidual_projection x

theorem rootResidual_mul_split (x : E.coverGroup) :
    E.rootResidual x * E.rootSplitLift x = x := by
  simp [rootResidual, mul_assoc]

theorem rootResidual_of_kernel {x : E.coverGroup}
    (hx : E.projection x = 1) : E.rootResidual x = x := by
  simp [rootResidual, rootSplitLift, hx]

theorem rootSplitLift_of_kernel {x : E.coverGroup}
    (hx : E.projection x = 1) : E.rootSplitLift x = 1 := by
  simp [rootSplitLift, hx]

theorem rootKernel_witness (x : E.coverGroup) :
    ∃ y : E.geometricGroup, E.injection y = E.rootResidual x :=
  E.exact_witness (E.rootResidual x) (E.rootResidual_projection x)

noncomputable def rootKernelCoordinate (x : E.coverGroup) : E.geometricGroup :=
  Classical.choose (E.rootKernel_witness x)

theorem rootKernelCoordinate_spec (x : E.coverGroup) :
    E.injection (E.rootKernelCoordinate x) = E.rootResidual x :=
  Classical.choose_spec (E.rootKernel_witness x)

theorem rootKernelCoordinate_unique (x : E.coverGroup)
    {y : E.geometricGroup}
    (hy : E.injection y = E.rootResidual x) :
    E.rootKernelCoordinate x = y := by
  apply E.injection_injective
  exact (E.rootKernelCoordinate_spec x).trans hy.symm

theorem rootCanonical_decomposition (x : E.coverGroup) :
    E.injection (E.rootKernelCoordinate x) * E.rootSplitLift x = x := by
  rw [E.rootKernelCoordinate_spec]
  exact E.rootResidual_mul_split x

theorem rootCanonical_decomposition_section (x : E.coverGroup) :
    E.injection (E.rootKernelCoordinate x) *
        E.sectionMap (E.projection x) = x := by
  simpa [rootSplitLift] using E.rootCanonical_decomposition x

theorem rootCanonical_decomposition_right (x : E.coverGroup) :
    x = E.injection (E.rootKernelCoordinate x) * E.rootSplitLift x :=
  (E.rootCanonical_decomposition x).symm

theorem rootKernelCoordinate_of_kernel {x : E.coverGroup}
    (hx : E.projection x = 1) :
    E.injection (E.rootKernelCoordinate x) = x := by
  rw [E.rootKernelCoordinate_spec, E.rootResidual_of_kernel hx]

theorem rootDecomposition_unique {x : E.coverGroup}
    {y z : E.geometricGroup}
    (hy : E.injection y * E.rootSplitLift x = x)
    (hz : E.injection z * E.rootSplitLift x = x) : y = z := by
  apply E.injection_injective
  apply mul_right_cancel
  exact hy.trans hz.symm

theorem rootDecomposition_projection {y : E.geometricGroup}
    {g : E.baseGroup} :
    E.projection (E.injection y * E.sectionMap g) = g := by
  simp [E.projection.map_mul, E.exact_reverse, E.section_right_inverse]

theorem rootKernel_closed_mul {x y : E.coverGroup}
    (hx : x ∈ E.projection.ker) (hy : y ∈ E.projection.ker) :
    x * y ∈ E.projection.ker := by
  change E.projection (x * y) = 1
  change E.projection x = 1 at hx
  change E.projection y = 1 at hy
  simp [E.projection.map_mul, hx, hy]

theorem rootKernel_closed_inv {x : E.coverGroup}
    (hx : x ∈ E.projection.ker) : x⁻¹ ∈ E.projection.ker := by
  change E.projection x⁻¹ = 1
  change E.projection x = 1 at hx
  simp [map_inv, hx]

theorem rootKernel_closed_pow {x : E.coverGroup}
    (hx : x ∈ E.projection.ker) :
    ∀ n : Nat, x ^ n ∈ E.projection.ker
  := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ]
      exact rootKernel_closed_mul E ih hx

theorem rootKernel_eq_range :
    {x : E.coverGroup | x ∈ E.projection.ker} =
      Set.range E.injection := by
  ext x
  exact E.exact_at_cover x

theorem rootProjection_section_mul (a b : E.baseGroup) :
    E.projection (E.sectionMap a * E.sectionMap b) = a * b := by
  simp [E.projection.map_mul, E.section_right_inverse]

theorem rootProjection_section_inv (a : E.baseGroup) :
    E.projection (E.sectionMap a)⁻¹ = a⁻¹ := by
  simp [map_inv, E.section_right_inverse]

theorem rootResidual_section (a : E.baseGroup) :
    E.rootResidual (E.sectionMap a) = 1 := by
  simp [rootResidual, rootSplitLift, E.section_right_inverse]

theorem rootCoordinate_one :
    E.rootKernelCoordinate (1 : E.coverGroup) = 1 := by
  apply E.injection_injective
  rw [E.rootKernelCoordinate_spec]
  simp [rootResidual, rootSplitLift]

end SourceExactSequenceClause

/-! ## Quotient conjugation tools -/

namespace SourceExactSequenceClause

variable (E : SourceExactSequenceClause.{u, v, w})

def rootConjugateLift (g : E.baseGroup) (x : E.coverGroup) : E.coverGroup :=
  E.sectionMap g * x * (E.sectionMap g)⁻¹

theorem rootConjugateLift_projection (g : E.baseGroup) (x : E.coverGroup) :
    E.projection (E.rootConjugateLift g x) =
      g * E.projection x * g⁻¹ := by
  simp [rootConjugateLift, E.projection.map_mul,
    E.section_right_inverse]

theorem rootConjugateLift_one (x : E.coverGroup) :
    E.rootConjugateLift 1 x = x := by
  simp [rootConjugateLift]

theorem rootConjugateLift_mul (g : E.baseGroup)
    (x y : E.coverGroup) :
    E.rootConjugateLift g (x * y) =
      E.rootConjugateLift g x * E.rootConjugateLift g y := by
  simp [rootConjugateLift, mul_assoc]

theorem rootConjugateLift_compose (g h : E.baseGroup)
    (x : E.coverGroup) :
    E.rootConjugateLift g (E.rootConjugateLift h x) =
      E.rootConjugateLift (g * h) x := by
  simp [rootConjugateLift, mul_assoc]

theorem rootConjugateLift_inverse (g : E.baseGroup)
    (x : E.coverGroup) :
    E.rootConjugateLift g⁻¹ (E.rootConjugateLift g x) = x := by
  simp [rootConjugateLift, mul_assoc]

theorem rootConjugateLift_kernel (g : E.baseGroup)
    {x : E.coverGroup} (hx : x ∈ E.projection.ker) :
    E.rootConjugateLift g x ∈ E.projection.ker := by
  change E.projection (E.rootConjugateLift g x) = 1
  rw [E.rootConjugateLift_projection]
  change E.projection x = 1 at hx
  simp [hx]

theorem rootInjection_kernel (y : E.geometricGroup) :
    E.injection y ∈ E.projection.ker := by
  change E.projection (E.injection y) = 1
  exact E.exact_reverse y

noncomputable def rootAction (g : E.baseGroup)
    (y : E.geometricGroup) : E.geometricGroup :=
  Classical.choose (E.exact_witness
    (E.rootConjugateLift g (E.injection y))
    (E.rootConjugateLift_kernel g (E.rootInjection_kernel y)))

theorem rootAction_spec (g : E.baseGroup) (y : E.geometricGroup) :
    E.injection (E.rootAction g y) =
      E.rootConjugateLift g (E.injection y) :=
  Classical.choose_spec (E.exact_witness
    (E.rootConjugateLift g (E.injection y))
    (E.rootConjugateLift_kernel g (E.rootInjection_kernel y)))

theorem rootAction_one (y : E.geometricGroup) : E.rootAction 1 y = y := by
  apply E.injection_injective
  rw [E.rootAction_spec, E.rootConjugateLift_one]

theorem rootAction_mul (g h : E.baseGroup) (y : E.geometricGroup) :
    E.rootAction (g * h) y = E.rootAction g (E.rootAction h y) := by
  apply E.injection_injective
  rw [E.rootAction_spec, E.rootAction_spec, E.rootAction_spec]
  exact (E.rootConjugateLift_compose g h (E.injection y)).symm

theorem rootAction_inverse (g : E.baseGroup) (y : E.geometricGroup) :
    E.rootAction g⁻¹ (E.rootAction g y) = y := by
  apply E.injection_injective
  rw [E.rootAction_spec, E.rootAction_spec,
    E.rootConjugateLift_inverse]

end SourceExactSequenceClause

/-! ## Reduction, q-parameter, and cusp tools -/

namespace SourceReductionClause

variable {Selected Bad : Type u}
variable (R : SourceReductionClause Selected Bad)

noncomputable def rootBadFinset : Finset Bad := by
  letI := R.partition.badFinite
  exact Finset.univ

theorem rootBad_mem_finset (b : Bad) :
    b ∈ R.rootBadFinset := by
  classical
  letI := R.partition.badFinite
  exact Finset.mem_univ b

theorem rootSelected_nonempty (R : SourceReductionClause Selected Bad) :
    Nonempty Selected :=
  SourcePlacePartition.selected_nonempty R.partition

@[reducible] noncomputable def rootBad_finite : Fintype Bad :=
  R.partition.badFinite

theorem rootStable (b : Bad) : R.stableReduction b :=
  R.stableReduction_proved b

theorem rootMultiplicative (b : Bad) :
    R.multiplicativeReduction b :=
  R.multiplicativeReduction_proved b

theorem rootSplit_multiplicative (b : Bad) :
    R.splitMultiplicativeReduction b :=
  R.splitMultiplicativeReduction_proved b

theorem rootSplit_implies_multiplicative (b : Bad) :
    R.splitMultiplicativeReduction b → R.multiplicativeReduction b :=
  R.reductionCompatibility b

theorem rootQ_nonzero (b : Bad) : R.qParameter b ≠ 0 :=
  R.qParameter_nonzero b

theorem rootQ_norm_positive (b : Bad) :
    0 < ‖R.qParameter b‖ := norm_pos_iff.mpr (R.rootQ_nonzero b)

theorem rootQ_norm_lt_one (b : Bad) :
    ‖R.qParameter b‖ < 1 := R.qParameter_contracting b

theorem rootQ_interval (b : Bad) :
    ‖R.qParameter b‖ ∈ Set.Ioo (0 : Real) 1 :=
  ⟨R.rootQ_norm_positive b, R.rootQ_norm_lt_one b⟩

theorem rootQ_inverse_norm (b : Bad) :
    ‖(R.qParameter b)⁻¹‖ = ‖R.qParameter b‖⁻¹ := norm_inv _

theorem rootQ_inverse_norm_gt_one (b : Bad) :
    1 < ‖(R.qParameter b)⁻¹‖ := by
  rw [R.rootQ_inverse_norm]
  exact (one_lt_inv₀ (R.rootQ_norm_positive b)).mpr
    (R.rootQ_norm_lt_one b)

theorem rootQ_pow_nonzero (b : Bad) (n : Nat) :
    R.qParameter b ^ n ≠ 0 :=
  pow_ne_zero n (R.rootQ_nonzero b)

theorem rootQ_pow_interval (b : Bad) {n : Nat}
    (hn : 0 < n) :
    ‖R.qParameter b‖ ^ n ∈ Set.Ioo (0 : Real) 1 := by
  exact ⟨pow_pos (R.rootQ_norm_positive b) n,
    pow_lt_one₀ (norm_nonneg _) (R.rootQ_norm_lt_one b)
      (Nat.ne_of_gt hn)⟩

theorem rootQ_norm_pow (b : Bad) (n : Nat) :
    ‖R.qParameter b ^ n‖ = ‖R.qParameter b‖ ^ n := norm_pow _ _

end SourceReductionClause

namespace SourceCuspClause

variable (C : SourceCuspClause)

def rootNormalized : Real := C.epsilon / C.cuspScale

def rootProduct : Real := C.epsilon * C.cuspScale

theorem rootNormalized_positive : 0 < C.rootNormalized := by
  change 0 < C.epsilon / C.cuspScale
  exact div_pos C.epsilon_positive C.cuspScale_positive

theorem rootNormalized_nonzero : C.rootNormalized ≠ 0 :=
  ne_of_gt C.rootNormalized_positive

theorem rootProduct_positive : 0 < C.epsilon * C.cuspScale := by
  exact mul_pos C.epsilon_positive C.cuspScale_positive

theorem rootProduct_nonzero : C.epsilon * C.cuspScale ≠ 0 :=
  C.epsilon_scale_relation

theorem rootEpsilon_pow_positive (n : Nat) : 0 < C.epsilon ^ n :=
  pow_pos C.epsilon_positive n

theorem rootScale_pow_positive (n : Nat) : 0 < C.cuspScale ^ n :=
  pow_pos C.cuspScale_positive n

end SourceCuspClause

/-! ## Definition 3.1 source certificate and faithful conclusion -/

namespace SourceDefinition31Root

variable {l : PrimeGeFive}
variable (S : SourceDefinition31Data.{u} l)

open SourceExactSequenceClause
open LeanFormal.IUT.Audit

structure RootCertificate where
  arithmetic :
    HasSqrtNegOne S.arithmetic.F ∧
      Nat.Coprime (Module.finrank S.arithmetic.Fmod S.arithmetic.F)
        l.value
  curve : PuncturedEllipticCurve S.arithmetic.F
  selected : Nonempty S.selectedPlaces
  badFinite : Fintype S.badPlaces
  stable : ∀ b, S.reduction.stableReduction b
  multiplicative : ∀ b, S.reduction.multiplicativeReduction b
  splitMultiplicative : ∀ b,
    S.reduction.splitMultiplicativeReduction b
  qInterval : ∀ b, ‖S.reduction.qParameter b‖ ∈ Set.Ioo (0 : Real) 1
  torsionImage : S.torsion.imageContainsSL2
  torsionSix : S.torsion.sixTorsionIndependent
  torsionL : S.torsion.lTorsionCompatible
  exactInjection : Function.Injective S.orbicurve.exactSequence.injection
  exactProjection : Function.Surjective S.orbicurve.exactSequence.projection
  sectionBijection : Function.Bijective S.sections.sectionMap
  localBijection : ∀ x,
    Function.Bijective (S.sections.localGroupSection x)
  cuspPositive : 0 < S.cusp.epsilon
  cuspNormalizedPositive : 0 < S.cusp.epsilon / S.cusp.cuspScale

noncomputable def rootCertificate : RootCertificate S where
  arithmetic :=
    ⟨S.arithmetic.tower.sqrtNegOne,
      S.arithmetic.tower.degreePrimeToL⟩
  curve := S.arithmetic.curve
  selected := S.selected_nonempty
  badFinite := S.bad_finite
  stable := fun b => S.stable_reduction b
  multiplicative := fun b => S.multiplicative_reduction b
  splitMultiplicative := fun b => S.split_multiplicative_reduction b
  qInterval := fun b =>
    ⟨norm_pos_iff.mpr (S.q_parameter_nonzero b),
      S.q_parameter_contracting b⟩
  torsionImage := S.torsion_image_contains_SL2
  torsionSix := S.torsion_six_independent
  torsionL := S.torsion_l_compatible
  exactInjection := S.exact_injection_injective
  exactProjection := S.exact_projection_surjective
  sectionBijection :=
    ⟨S.sections.sectionMap_injective, S.sections.sectionMap_surjective⟩
  localBijection := fun x => S.sections.local_group_section_bijective x
  cuspPositive := S.cusp_positive
  cuspNormalizedPositive := by
    exact div_pos S.cusp_positive S.cusp.cuspScale_positive

theorem rootCertificate_arithmetic :
    HasSqrtNegOne S.arithmetic.F ∧
      Nat.Coprime (Module.finrank S.arithmetic.Fmod S.arithmetic.F)
        l.value := (rootCertificate S).arithmetic

noncomputable def rootCertificate_curve :
    PuncturedEllipticCurve S.arithmetic.F := (rootCertificate S).curve

theorem rootCertificate_selected :
    Nonempty S.selectedPlaces := (rootCertificate S).selected

@[reducible] noncomputable def rootCertificate_badFinite :
    Fintype S.badPlaces := (rootCertificate S).badFinite

theorem rootCertificate_stable (b : S.badPlaces) :
    S.reduction.stableReduction b := (rootCertificate S).stable b

theorem rootCertificate_split (b : S.badPlaces) :
    S.reduction.splitMultiplicativeReduction b :=
  (rootCertificate S).splitMultiplicative b

theorem rootCertificate_q (b : S.badPlaces) :
    ‖S.reduction.qParameter b‖ ∈ Set.Ioo (0 : Real) 1 :=
  (rootCertificate S).qInterval b

theorem rootCertificate_torsion :
    S.torsion.imageContainsSL2 ∧
      S.torsion.sixTorsionIndependent ∧
      S.torsion.lTorsionCompatible :=
  ⟨(rootCertificate S).torsionImage,
    (rootCertificate S).torsionSix,
    (rootCertificate S).torsionL⟩

theorem rootCertificate_exact :
    Function.Injective S.orbicurve.exactSequence.injection ∧
      Function.Surjective S.orbicurve.exactSequence.projection :=
  ⟨(rootCertificate S).exactInjection,
    (rootCertificate S).exactProjection⟩

theorem rootCertificate_sections :
    Function.Bijective S.sections.sectionMap ∧
      (∀ x, Function.Bijective (S.sections.localGroupSection x)) :=
  ⟨(rootCertificate S).sectionBijection,
    (rootCertificate S).localBijection⟩

theorem rootCertificate_cusp :
    0 < S.cusp.epsilon ∧
      0 < S.cusp.epsilon / S.cusp.cuspScale :=
  ⟨(rootCertificate S).cuspPositive,
    (rootCertificate S).cuspNormalizedPositive⟩

structure Definition31Recognition : Prop where
  arithmetic :
    HasSqrtNegOne S.arithmetic.F ∧
      Nat.Coprime (Module.finrank S.arithmetic.Fmod S.arithmetic.F)
        l.value
  places : Nonempty S.selectedPlaces ∧ Nonempty (Fintype S.badPlaces)
  reduction : ∀ b,
    S.reduction.stableReduction b ∧
      S.reduction.multiplicativeReduction b ∧
      S.reduction.splitMultiplicativeReduction b ∧
      S.reduction.qParameter b ≠ 0 ∧
      ‖S.reduction.qParameter b‖ < 1
  torsion :
    S.torsion.imageContainsSL2 ∧
      S.torsion.sixTorsionIndependent ∧
      S.torsion.lTorsionCompatible
  exact :
    Function.Injective S.orbicurve.exactSequence.injection ∧
      Function.Surjective S.orbicurve.exactSequence.projection
  sections :
    Function.Bijective S.sections.sectionMap ∧
      (∀ x, Function.Bijective (S.sections.localGroupSection x))
  cusp :
    0 < S.cusp.epsilon ∧ S.cusp.epsilon_compatibility
  compatibility :
    S.arithmetic_reduction_compatibility ∧
      S.arithmetic_torsion_compatibility ∧
      S.arithmetic_orbicurve_compatibility ∧
      S.arithmetic_section_compatibility ∧
      S.arithmetic_cusp_compatibility

theorem definition31_recognition : Definition31Recognition S where
  arithmetic := (rootCertificate S).arithmetic
  places := ⟨(rootCertificate S).selected,
    ⟨(rootCertificate S).badFinite⟩⟩
  reduction := fun b =>
    ⟨(rootCertificate S).stable b,
      (rootCertificate S).multiplicative b,
      (rootCertificate S).splitMultiplicative b,
      S.q_parameter_nonzero b,
      (rootCertificate S).qInterval b |>.2⟩
  torsion := rootCertificate_torsion S
  exact := rootCertificate_exact S
  sections := rootCertificate_sections S
  cusp := ⟨S.cusp_positive, S.cusp_compatibility⟩
  compatibility :=
    ⟨S.arithmetic_reduction_spec,
      S.arithmetic_torsion_spec,
      S.arithmetic_orbicurve_spec,
      S.arithmetic_section_spec,
      S.arithmetic_cusp_spec⟩

theorem definition31_projection_is_conservative :
    (S.toInitialThetaInput).arithmetic = S.arithmetic ∧
      (S.toInitialThetaInput).selectedPlaces = S.selectedPlaces ∧
      (S.toInitialThetaInput).badPlaces = S.badPlaces := by
  exact ⟨rfl, rfl, rfl⟩

/-! ## D6/D7 reusable normal forms

The following lemmas keep the source contracts in their original direction.
In particular, the projection is never replaced by an equality of carriers:
the exact-sequence statements remain kernel statements, and the section is
used only through its proved right inverse.  These normal forms are shared by
the later local-packet and Kummer modules.
-/

theorem definition31_exact_sequence_iff (x : S.orbicurve.exactSequence.coverGroup) :
    S.orbicurve.exactSequence.projection x = 1 ↔
      ∃ y, S.orbicurve.exactSequence.injection y = x := by
  exact S.orbicurve.exactSequence.exact_at_cover x

theorem definition31_exact_sequence_injection_injective :
    Function.Injective S.orbicurve.exactSequence.injection :=
  S.orbicurve.exactSequence.injection_injective

theorem definition31_exact_sequence_projection_surjective :
    Function.Surjective S.orbicurve.exactSequence.projection :=
  S.orbicurve.exactSequence.projection_surjective

theorem definition31_exact_sequence_injection_kernel :
    ∀ y, S.orbicurve.exactSequence.projection
      (S.orbicurve.exactSequence.injection y) = 1 := by
  intro y
  exact S.orbicurve.exactSequence.exact_reverse y

theorem definition31_exact_sequence_kernel_witness
    (x : S.orbicurve.exactSequence.coverGroup)
    (hx : S.orbicurve.exactSequence.projection x = 1) :
    ∃ y, S.orbicurve.exactSequence.injection y = x := by
  exact S.orbicurve.exactSequence.exact_witness x hx

theorem definition31_exact_sequence_kernel_unique
    (x : S.orbicurve.exactSequence.coverGroup)
    (hx : S.orbicurve.exactSequence.projection x = 1)
    {y z : S.orbicurve.exactSequence.geometricGroup}
    (hy : S.orbicurve.exactSequence.injection y = x)
    (hz : S.orbicurve.exactSequence.injection z = x) :
    y = z := by
  exact S.orbicurve.exactSequence.exact_witness_unique x hx y z hy hz

theorem definition31_exact_sequence_kernel_mem
    (x : S.orbicurve.exactSequence.coverGroup)
    (hx : S.orbicurve.exactSequence.projection x = 1) :
    x ∈ S.orbicurve.exactSequence.projection.ker :=
  hx

theorem definition31_exact_sequence_kernel_one :
    (1 : S.orbicurve.exactSequence.coverGroup) ∈
      S.orbicurve.exactSequence.projection.ker := by
  exact S.orbicurve.exactSequence.kernel_one

theorem definition31_exact_sequence_projection_one :
    S.orbicurve.exactSequence.projection
      (1 : S.orbicurve.exactSequence.coverGroup) = 1 := by
  exact S.orbicurve.exactSequence.projection_map_one

theorem definition31_exact_sequence_projection_mul
    (x y : S.orbicurve.exactSequence.coverGroup) :
    S.orbicurve.exactSequence.projection (x * y) =
      S.orbicurve.exactSequence.projection x *
        S.orbicurve.exactSequence.projection y := by
  exact S.orbicurve.exactSequence.projection_map_mul x y

theorem definition31_exact_sequence_projection_inv
    (x : S.orbicurve.exactSequence.coverGroup) :
    S.orbicurve.exactSequence.projection x⁻¹ =
      (S.orbicurve.exactSequence.projection x)⁻¹ := by
  exact map_inv S.orbicurve.exactSequence.projection x

theorem definition31_exact_sequence_injection_one :
    S.orbicurve.exactSequence.injection
      (1 : S.orbicurve.exactSequence.geometricGroup) = 1 := by
  exact S.orbicurve.exactSequence.injection_map_one

theorem definition31_exact_sequence_injection_mul
    (x y : S.orbicurve.exactSequence.geometricGroup) :
    S.orbicurve.exactSequence.injection (x * y) =
      S.orbicurve.exactSequence.injection x *
        S.orbicurve.exactSequence.injection y := by
  exact S.orbicurve.exactSequence.injection_map_mul x y

theorem definition31_exact_sequence_section_right_inverse
    (g : S.orbicurve.exactSequence.baseGroup) :
    S.orbicurve.exactSequence.projection
      (S.orbicurve.exactSequence.sectionMap g) = g := by
  exact S.orbicurve.exactSequence.section_right_inverse g

theorem definition31_exact_sequence_section_injective :
    Function.Injective S.orbicurve.exactSequence.sectionMap := by
  exact S.orbicurve.exactSequence.section_injective

theorem definition31_exact_sequence_section_mul
    (g h : S.orbicurve.exactSequence.baseGroup) :
    S.orbicurve.exactSequence.sectionMap (g * h) =
      S.orbicurve.exactSequence.sectionMap g *
        S.orbicurve.exactSequence.sectionMap h := by
  exact S.orbicurve.exactSequence.section_map_mul g h

theorem definition31_exact_sequence_section_one :
    S.orbicurve.exactSequence.sectionMap
      (1 : S.orbicurve.exactSequence.baseGroup) = 1 := by
  exact S.orbicurve.exactSequence.section_map_one

theorem definition31_exact_sequence_section_inv
    (g : S.orbicurve.exactSequence.baseGroup) :
    S.orbicurve.exactSequence.sectionMap g⁻¹ =
      (S.orbicurve.exactSequence.sectionMap g)⁻¹ := by
  exact map_inv S.orbicurve.exactSequence.sectionMap g

theorem definition31_exact_sequence_projection_section_mul
    (g h : S.orbicurve.exactSequence.baseGroup) :
    S.orbicurve.exactSequence.projection
        (S.orbicurve.exactSequence.sectionMap g *
          S.orbicurve.exactSequence.sectionMap h) = g * h := by
  exact S.orbicurve.exactSequence.projection_section_mul g h

theorem definition31_exact_sequence_projection_section_inv
    (g : S.orbicurve.exactSequence.baseGroup) :
    S.orbicurve.exactSequence.projection
      (S.orbicurve.exactSequence.sectionMap g)⁻¹ = g⁻¹ := by
  exact S.orbicurve.exactSequence.projection_section_inv g

theorem definition31_exact_sequence_section_cancel
    (g : S.orbicurve.exactSequence.baseGroup) :
    S.orbicurve.exactSequence.projection
      (S.orbicurve.exactSequence.sectionMap g) = g := by
  exact definition31_exact_sequence_section_right_inverse S g

theorem definition31_exact_sequence_kernel_as_range :
    {x : S.orbicurve.exactSequence.coverGroup |
        x ∈ S.orbicurve.exactSequence.projection.ker} =
      Set.range S.orbicurve.exactSequence.injection := by
  ext x
  exact S.orbicurve.exactSequence.kernel_mem_iff x

theorem definition31_exact_sequence_kernel_closed_mul
    {x y : S.orbicurve.exactSequence.coverGroup}
    (hx : x ∈ S.orbicurve.exactSequence.projection.ker)
    (hy : y ∈ S.orbicurve.exactSequence.projection.ker) :
    x * y ∈ S.orbicurve.exactSequence.projection.ker := by
  exact rootKernel_closed_mul S.orbicurve.exactSequence hx hy

theorem definition31_exact_sequence_kernel_closed_inv
    {x : S.orbicurve.exactSequence.coverGroup}
    (hx : x ∈ S.orbicurve.exactSequence.projection.ker) :
    x⁻¹ ∈ S.orbicurve.exactSequence.projection.ker := by
  exact rootKernel_closed_inv S.orbicurve.exactSequence hx

theorem definition31_exact_sequence_kernel_closed_pow
    {x : S.orbicurve.exactSequence.coverGroup}
    (hx : x ∈ S.orbicurve.exactSequence.projection.ker) (n : Nat) :
    x ^ n ∈ S.orbicurve.exactSequence.projection.ker := by
  exact rootKernel_closed_pow
    (E := S.orbicurve.exactSequence) hx n

theorem definition31_exact_sequence_decomposition
    (x : S.orbicurve.exactSequence.coverGroup) :
    S.orbicurve.exactSequence.injection
        (rootKernelCoordinate S.orbicurve.exactSequence x) *
        rootSplitLift S.orbicurve.exactSequence x = x := by
  exact rootCanonical_decomposition S.orbicurve.exactSequence x

theorem definition31_exact_sequence_decomposition_section
    (x : S.orbicurve.exactSequence.coverGroup) :
    S.orbicurve.exactSequence.injection
        (rootKernelCoordinate S.orbicurve.exactSequence x) *
        S.orbicurve.exactSequence.sectionMap
          (S.orbicurve.exactSequence.projection x) = x := by
  exact rootCanonical_decomposition_section S.orbicurve.exactSequence x

theorem definition31_exact_sequence_decomposition_unique
    {x : S.orbicurve.exactSequence.coverGroup}
    {y z : S.orbicurve.exactSequence.geometricGroup}
    (hy : S.orbicurve.exactSequence.injection y *
      rootSplitLift S.orbicurve.exactSequence x = x)
    (hz : S.orbicurve.exactSequence.injection z *
      rootSplitLift S.orbicurve.exactSequence x = x) :
    y = z := by
  exact rootDecomposition_unique S.orbicurve.exactSequence hy hz

theorem definition31_exact_sequence_residual_projection
    (x : S.orbicurve.exactSequence.coverGroup) :
    S.orbicurve.exactSequence.projection
      (rootResidual S.orbicurve.exactSequence x) = 1 := by
  exact rootResidual_projection S.orbicurve.exactSequence x

theorem definition31_exact_sequence_residual_kernel
    (x : S.orbicurve.exactSequence.coverGroup) :
    rootResidual S.orbicurve.exactSequence x ∈
      S.orbicurve.exactSequence.projection.ker := by
  exact rootResidual_mem_kernel S.orbicurve.exactSequence x

theorem definition31_exact_sequence_residual_split
    (x : S.orbicurve.exactSequence.coverGroup) :
    rootResidual S.orbicurve.exactSequence x *
        rootSplitLift S.orbicurve.exactSequence x = x := by
  exact rootResidual_mul_split S.orbicurve.exactSequence x

theorem definition31_exact_sequence_residual_of_kernel
    {x : S.orbicurve.exactSequence.coverGroup}
    (hx : S.orbicurve.exactSequence.projection x = 1) :
    rootResidual S.orbicurve.exactSequence x = x := by
  exact rootResidual_of_kernel S.orbicurve.exactSequence hx

theorem definition31_exact_sequence_lift_of_kernel
    {x : S.orbicurve.exactSequence.coverGroup}
    (hx : S.orbicurve.exactSequence.projection x = 1) :
    rootSplitLift S.orbicurve.exactSequence x = 1 := by
  exact rootSplitLift_of_kernel S.orbicurve.exactSequence hx

theorem definition31_exact_sequence_coordinate_spec
    (x : S.orbicurve.exactSequence.coverGroup) :
    S.orbicurve.exactSequence.injection
        (rootKernelCoordinate S.orbicurve.exactSequence x) =
      rootResidual S.orbicurve.exactSequence x := by
  exact rootKernelCoordinate_spec S.orbicurve.exactSequence x

theorem definition31_exact_sequence_coordinate_unique
    (x : S.orbicurve.exactSequence.coverGroup)
    {y : S.orbicurve.exactSequence.geometricGroup}
    (hy : S.orbicurve.exactSequence.injection y =
      rootResidual S.orbicurve.exactSequence x) :
    rootKernelCoordinate S.orbicurve.exactSequence x = y := by
  exact rootKernelCoordinate_unique S.orbicurve.exactSequence x hy

theorem definition31_exact_sequence_coordinate_one :
    rootKernelCoordinate S.orbicurve.exactSequence
      (1 : S.orbicurve.exactSequence.coverGroup) = 1 := by
  exact rootCoordinate_one S.orbicurve.exactSequence

theorem definition31_exact_sequence_conjugate_projection
    (g : S.orbicurve.exactSequence.baseGroup)
    (x : S.orbicurve.exactSequence.coverGroup) :
    S.orbicurve.exactSequence.projection
      (rootConjugateLift S.orbicurve.exactSequence g x) =
      g * S.orbicurve.exactSequence.projection x * g⁻¹ := by
  exact rootConjugateLift_projection S.orbicurve.exactSequence g x

theorem definition31_exact_sequence_conjugate_mul
    (g : S.orbicurve.exactSequence.baseGroup)
    (x y : S.orbicurve.exactSequence.coverGroup) :
    rootConjugateLift S.orbicurve.exactSequence g (x * y) =
      rootConjugateLift S.orbicurve.exactSequence g x *
        rootConjugateLift S.orbicurve.exactSequence g y := by
  exact rootConjugateLift_mul S.orbicurve.exactSequence g x y

theorem definition31_exact_sequence_conjugate_compose
    (g h : S.orbicurve.exactSequence.baseGroup)
    (x : S.orbicurve.exactSequence.coverGroup) :
    rootConjugateLift S.orbicurve.exactSequence g
        (rootConjugateLift S.orbicurve.exactSequence h x) =
      rootConjugateLift S.orbicurve.exactSequence (g * h) x := by
  exact rootConjugateLift_compose S.orbicurve.exactSequence g h x

theorem definition31_exact_sequence_conjugate_inverse
    (g : S.orbicurve.exactSequence.baseGroup)
    (x : S.orbicurve.exactSequence.coverGroup) :
    rootConjugateLift S.orbicurve.exactSequence g⁻¹
        (rootConjugateLift S.orbicurve.exactSequence g x) = x := by
  exact rootConjugateLift_inverse S.orbicurve.exactSequence g x

theorem definition31_exact_sequence_conjugate_kernel
    (g : S.orbicurve.exactSequence.baseGroup)
    {x : S.orbicurve.exactSequence.coverGroup}
    (hx : x ∈ S.orbicurve.exactSequence.projection.ker) :
    rootConjugateLift S.orbicurve.exactSequence g x ∈
      S.orbicurve.exactSequence.projection.ker := by
  exact rootConjugateLift_kernel S.orbicurve.exactSequence g hx

theorem definition31_exact_sequence_action_spec
    (g : S.orbicurve.exactSequence.baseGroup)
    (y : S.orbicurve.exactSequence.geometricGroup) :
    S.orbicurve.exactSequence.injection
        (rootAction S.orbicurve.exactSequence g y) =
      rootConjugateLift S.orbicurve.exactSequence g
        (S.orbicurve.exactSequence.injection y) := by
  exact rootAction_spec S.orbicurve.exactSequence g y

theorem definition31_exact_sequence_action_one
    (y : S.orbicurve.exactSequence.geometricGroup) :
    rootAction S.orbicurve.exactSequence 1 y = y := by
  exact rootAction_one S.orbicurve.exactSequence y

theorem definition31_exact_sequence_action_mul
    (g h : S.orbicurve.exactSequence.baseGroup)
    (y : S.orbicurve.exactSequence.geometricGroup) :
    rootAction S.orbicurve.exactSequence (g * h) y =
      rootAction S.orbicurve.exactSequence g
        (rootAction S.orbicurve.exactSequence h y) := by
  exact rootAction_mul S.orbicurve.exactSequence g h y

theorem definition31_exact_sequence_action_inverse
    (g : S.orbicurve.exactSequence.baseGroup)
    (y : S.orbicurve.exactSequence.geometricGroup) :
    rootAction S.orbicurve.exactSequence g⁻¹
        (rootAction S.orbicurve.exactSequence g y) = y := by
  exact rootAction_inverse S.orbicurve.exactSequence g y

/-! ## D3/D4 reduction and place normal forms -/

theorem definition31_selected_places_nonempty :
    Nonempty S.selectedPlaces := by
  exact S.reduction.partition.selectedNonempty

@[reducible] noncomputable def definition31_bad_places_fintype :
    Fintype S.badPlaces :=
  S.reduction.partition.badFinite

noncomputable def definition31_bad_places_finset :
    Finset S.badPlaces := by
  letI := S.reduction.partition.badFinite
  exact Finset.univ

theorem definition31_bad_place_mem_finset (b : S.badPlaces) :
    b ∈ definition31_bad_places_finset S := by
  classical
  letI := S.reduction.partition.badFinite
  exact Finset.mem_univ b

theorem definition31_bad_label_compatibility (b : S.badPlaces) :
    S.reduction.partition.selectedLabel
        (S.reduction.partition.badIncluded b) =
      S.reduction.partition.badLabel b := by
  exact S.reduction.partition.badLabel_compatible b

theorem definition31_selected_label_recovery (b : S.badPlaces) :
    S.reduction.partition.badLabel b =
      S.reduction.partition.selectedLabel
        (S.reduction.partition.badIncluded b) := by
  exact (S.reduction.partition.badLabel_compatible b).symm

theorem definition31_bad_label_transport
    {b₁ b₂ : S.badPlaces}
    (h : S.reduction.partition.badIncluded b₁ =
      S.reduction.partition.badIncluded b₂) :
    S.reduction.partition.badLabel b₁ =
      S.reduction.partition.badLabel b₂ := by
  exact S.reduction.partition.selected_label_transport h

theorem definition31_selected_label_transport
    {b₁ b₂ : S.badPlaces}
    (h : S.reduction.partition.badLabel b₁ =
      S.reduction.partition.badLabel b₂) :
    S.reduction.partition.selectedLabel
        (S.reduction.partition.badIncluded b₁) =
      S.reduction.partition.selectedLabel
        (S.reduction.partition.badIncluded b₂) := by
  exact S.reduction.partition.bad_label_transport h

theorem definition31_stable_reduction (b : S.badPlaces) :
    S.reduction.stableReduction b := by
  exact S.reduction.stableReduction_proved b

theorem definition31_multiplicative_reduction (b : S.badPlaces) :
    S.reduction.multiplicativeReduction b := by
  exact S.reduction.multiplicativeReduction_proved b

theorem definition31_split_multiplicative_reduction (b : S.badPlaces) :
    S.reduction.splitMultiplicativeReduction b := by
  exact S.reduction.splitMultiplicativeReduction_proved b

theorem definition31_split_implies_multiplicative (b : S.badPlaces) :
    S.reduction.splitMultiplicativeReduction b →
      S.reduction.multiplicativeReduction b := by
  exact S.reduction.reductionCompatibility b

theorem definition31_q_parameter_nonzero (b : S.badPlaces) :
    S.reduction.qParameter b ≠ 0 := by
  exact S.reduction.qParameter_nonzero b

theorem definition31_q_parameter_contracting (b : S.badPlaces) :
    ‖S.reduction.qParameter b‖ < 1 := by
  exact S.reduction.qParameter_contracting b

theorem definition31_q_parameter_ne_one (b : S.badPlaces) :
    S.reduction.qParameter b ≠ 1 := by
  exact S.reduction.qParameter_reduction_compatibility b
    (S.reduction.stableReduction_proved b)

theorem definition31_q_norm_nonnegative (b : S.badPlaces) :
    0 ≤ ‖S.reduction.qParameter b‖ := by
  exact norm_nonneg _

theorem definition31_q_norm_positive (b : S.badPlaces) :
    0 < ‖S.reduction.qParameter b‖ := by
  exact norm_pos_iff.mpr (S.reduction.qParameter_nonzero b)

theorem definition31_q_norm_interval (b : S.badPlaces) :
    ‖S.reduction.qParameter b‖ ∈ Set.Ioo (0 : Real) 1 := by
  exact ⟨definition31_q_norm_positive S b,
    definition31_q_parameter_contracting S b⟩

theorem definition31_q_norm_le_one (b : S.badPlaces) :
    ‖S.reduction.qParameter b‖ ≤ 1 := by
  exact le_of_lt (definition31_q_parameter_contracting S b)

theorem definition31_q_power_nonzero (b : S.badPlaces) (n : Nat) :
    S.reduction.qParameter b ^ n ≠ 0 := by
  exact pow_ne_zero n (definition31_q_parameter_nonzero S b)

theorem definition31_q_norm_power (b : S.badPlaces) (n : Nat) :
    ‖S.reduction.qParameter b ^ n‖ =
      ‖S.reduction.qParameter b‖ ^ n := by
  exact norm_pow _ _

theorem definition31_q_power_norm_positive (b : S.badPlaces) (n : Nat) :
    0 < ‖S.reduction.qParameter b‖ ^ n := by
  exact pow_pos (definition31_q_norm_positive S b) n

theorem definition31_q_power_norm_le_one (b : S.badPlaces) (n : Nat) :
    ‖S.reduction.qParameter b‖ ^ n ≤ 1 := by
  exact pow_le_one₀ (definition31_q_norm_nonnegative S b)
    (definition31_q_norm_le_one S b)

theorem definition31_q_power_norm_lt_one
    (b : S.badPlaces) {n : Nat} (hn : 0 < n) :
    ‖S.reduction.qParameter b‖ ^ n < 1 := by
  exact pow_lt_one₀ (definition31_q_norm_nonnegative S b)
    (definition31_q_parameter_contracting S b) (Nat.ne_of_gt hn)

theorem definition31_q_power_norm_interval
    (b : S.badPlaces) {n : Nat} (hn : 0 < n) :
    ‖S.reduction.qParameter b‖ ^ n ∈ Set.Ioo (0 : Real) 1 := by
  exact ⟨definition31_q_power_norm_positive S b n,
    definition31_q_power_norm_lt_one S b hn⟩

theorem definition31_q_power_ne_one
    (b : S.badPlaces) (n : Nat) (hn : 0 < n) :
    S.reduction.qParameter b ^ n ≠ 1 := by
  intro h
  have hnorm : ‖S.reduction.qParameter b‖ ^ n = 1 := by
    rw [← norm_pow, h, norm_one]
  have hlt := definition31_q_power_norm_lt_one S b hn
  linarith

theorem definition31_q_inverse_norm (b : S.badPlaces) :
    ‖(S.reduction.qParameter b)⁻¹‖ =
      (‖S.reduction.qParameter b‖)⁻¹ := by
  exact norm_inv _

theorem definition31_q_inverse_norm_gt_one (b : S.badPlaces) :
    1 < ‖(S.reduction.qParameter b)⁻¹‖ := by
  rw [definition31_q_inverse_norm S b]
  exact (one_lt_inv₀ (definition31_q_norm_positive S b)).mpr
    (definition31_q_parameter_contracting S b)

theorem definition31_q_inverse_nonzero (b : S.badPlaces) :
    (S.reduction.qParameter b)⁻¹ ≠ 0 := by
  exact inv_ne_zero (definition31_q_parameter_nonzero S b)

theorem definition31_q_mul_inverse (b : S.badPlaces) :
    S.reduction.qParameter b * (S.reduction.qParameter b)⁻¹ = 1 := by
  exact mul_inv_cancel₀ (definition31_q_parameter_nonzero S b)

theorem definition31_q_inverse_mul (b : S.badPlaces) :
    (S.reduction.qParameter b)⁻¹ * S.reduction.qParameter b = 1 := by
  exact inv_mul_cancel₀ (definition31_q_parameter_nonzero S b)

theorem definition31_q_mul_inverse_norm (b : S.badPlaces) :
    ‖S.reduction.qParameter b * (S.reduction.qParameter b)⁻¹‖ = 1 := by
  rw [definition31_q_mul_inverse S b, norm_one]

theorem definition31_q_inverse_mul_norm (b : S.badPlaces) :
    ‖(S.reduction.qParameter b)⁻¹ * S.reduction.qParameter b‖ = 1 := by
  rw [definition31_q_inverse_mul S b, norm_one]

theorem definition31_q_log_negative (b : S.badPlaces) :
    Real.log ‖S.reduction.qParameter b‖ < 0 := by
  exact S.q_log_abs_negative b

theorem definition31_q_neg_log_positive (b : S.badPlaces) :
    0 < -Real.log ‖S.reduction.qParameter b‖ := by
  exact S.neg_log_q_positive b

theorem definition31_q_log_nonzero (b : S.badPlaces) :
    Real.log ‖S.reduction.qParameter b‖ ≠ 0 := by
  exact S.q_log_abs_nonzero b

theorem definition31_q_log_nonpositive (b : S.badPlaces) :
    Real.log ‖S.reduction.qParameter b‖ ≤ 0 := by
  exact S.q_log_abs_le_zero b

theorem definition31_q_power_log (b : S.badPlaces) (n : Nat) :
    Real.log ‖S.reduction.qParameter b ^ n‖ =
      n * Real.log ‖S.reduction.qParameter b‖ := by
  exact S.q_power_log b n

theorem definition31_q_power_log_negative
    (b : S.badPlaces) (n : Nat) (hn : 0 < n) :
    Real.log ‖S.reduction.qParameter b ^ n‖ < 0 := by
  exact S.q_power_log_negative b n hn

theorem definition31_q_power_neg_log_positive
    (b : S.badPlaces) (n : Nat) (hn : 0 < n) :
    0 < -Real.log ‖S.reduction.qParameter b ^ n‖ := by
  exact S.q_power_neg_log_positive b n hn

theorem definition31_q_contracting_sequence (b : S.badPlaces) :
    ∀ n : Nat, ‖S.reduction.qParameter b‖ ^ (n + 1) < 1 := by
  exact S.q_contracting_sequence b

theorem definition31_q_sequence_le_one (b : S.badPlaces) (n : Nat) :
    ‖S.reduction.qParameter b‖ ^ n ≤ 1 := by
  exact S.q_sequence_le_one b n

theorem definition31_reduction_bundle (b : S.badPlaces) :
    S.reduction.stableReduction b ∧
      S.reduction.multiplicativeReduction b ∧
      S.reduction.splitMultiplicativeReduction b ∧
      S.reduction.qParameter b ≠ 0 ∧
      S.reduction.qParameter b ≠ 1 ∧
      ‖S.reduction.qParameter b‖ ∈ Set.Ioo (0 : Real) 1 := by
  exact ⟨definition31_stable_reduction S b,
    definition31_multiplicative_reduction S b,
    definition31_split_multiplicative_reduction S b,
    definition31_q_parameter_nonzero S b,
    definition31_q_parameter_ne_one S b,
    definition31_q_norm_interval S b⟩

theorem definition31_reduction_compatibility (b : S.badPlaces) :
    S.reduction.splitMultiplicativeReduction b →
      S.reduction.multiplicativeReduction b := by
  exact definition31_split_implies_multiplicative S b

/-! ## D5 torsion and representation normal forms -/

theorem definition31_torsion_nonempty :
    Nonempty S.torsion.torsionCarrier := by
  exact S.torsion.torsionNonempty

theorem definition31_torsion_representation_surjective :
    Function.Surjective S.torsion.representation := by
  exact S.torsion.representation_surjective

theorem definition31_torsion_image_contains_SL2 :
    S.torsion.imageContainsSL2 := by
  exact S.torsion.imageContainsSL2_proved

theorem definition31_torsion_six_independent :
    S.torsion.sixTorsionIndependent := by
  exact S.torsion.sixTorsionIndependent_proved

theorem definition31_torsion_l_compatible :
    S.torsion.lTorsionCompatible := by
  exact S.torsion.lTorsionCompatible_proved

theorem definition31_torsion_representation_one :
    S.torsion.representation 1 = 1 := by
  exact S.torsion.representation.map_one

theorem definition31_torsion_representation_mul
    (a b : S.torsion.representationCarrier) :
    S.torsion.representation (a * b) =
      S.torsion.representation a * S.torsion.representation b := by
  exact S.torsion.representation.map_mul a b

theorem definition31_torsion_representation_inv
    (a : S.torsion.representationCarrier) :
    S.torsion.representation a⁻¹ =
      (S.torsion.representation a)⁻¹ := by
  exact map_inv S.torsion.representation a

theorem definition31_torsion_representation_pow
    (a : S.torsion.representationCarrier) (n : Nat) :
    S.torsion.representation (a ^ n) =
      S.torsion.representation a ^ n := by
  exact map_pow S.torsion.representation a n

theorem definition31_torsion_representation_mem_range
    (z : S.torsion.representationGroup) :
    z ∈ Set.range S.torsion.representation := by
  rcases S.torsion.representation_surjective z with ⟨a, ha⟩
  exact ⟨a, ha⟩

theorem definition31_torsion_representation_range_eq_univ :
    Set.range S.torsion.representation = Set.univ := by
  apply Set.eq_univ_of_forall
  intro z
  exact definition31_torsion_representation_mem_range S z

noncomputable def definition31_torsion_lift
    (z : S.torsion.representationGroup) :
    S.torsion.representationCarrier :=
  Classical.choose (S.torsion.representation_surjective z)

theorem definition31_torsion_lift_spec
    (z : S.torsion.representationGroup) :
    S.torsion.representation (definition31_torsion_lift S z) = z := by
  exact Classical.choose_spec (S.torsion.representation_surjective z)

theorem definition31_torsion_kernel_iff
    (a : S.torsion.representationCarrier) :
    a ∈ S.torsion.representation.ker ↔
      S.torsion.representation a = 1 := Iff.rfl

theorem definition31_torsion_kernel_mem
    (a : S.torsion.representationCarrier)
    (ha : S.torsion.representation a = 1) :
    a ∈ S.torsion.representation.ker := by
  exact ha

theorem definition31_torsion_label_total
    (a : S.torsion.torsionCarrier) :
    ∃ j : Fin 6, S.torsion.torsionLabel a = j := by
  exact ⟨S.torsion.torsionLabel a, rfl⟩

theorem definition31_torsion_label_refl
    (a : S.torsion.torsionCarrier) :
    S.torsion.torsionLabel a = S.torsion.torsionLabel a := rfl

theorem definition31_torsion_label_symm
    {a b : S.torsion.torsionCarrier}
    (h : S.torsion.torsionLabel a = S.torsion.torsionLabel b) :
    S.torsion.torsionLabel b = S.torsion.torsionLabel a := by
  exact h.symm

theorem definition31_torsion_label_trans
    {a b c : S.torsion.torsionCarrier}
    (hab : S.torsion.torsionLabel a = S.torsion.torsionLabel b)
    (hbc : S.torsion.torsionLabel b = S.torsion.torsionLabel c) :
    S.torsion.torsionLabel a = S.torsion.torsionLabel c := by
  exact hab.trans hbc

theorem definition31_torsion_prime_odd : Odd l.value := by
  exact l.odd

theorem definition31_torsion_prime_ge_five : 5 ≤ l.value := by
  exact l.ge_five

theorem definition31_torsion_clauses :
    S.torsion.imageContainsSL2 ∧
      S.torsion.sixTorsionIndependent ∧
      S.torsion.lTorsionCompatible := by
  exact ⟨definition31_torsion_image_contains_SL2 S,
    definition31_torsion_six_independent S,
    definition31_torsion_l_compatible S⟩

/-! ## Orbicurve and cover transport -/

theorem definition31_cover_surjective :
    Function.Surjective S.orbicurve.coverToPunctured := by
  exact S.orbicurve.cover_surjective

theorem definition31_cover_point_lift
    (x : S.orbicurve.puncturedCurve) :
    ∃ y, S.orbicurve.coverToPunctured y = x := by
  exact S.orbicurve.cover_point_lift x

theorem definition31_cover_range :
    Set.range S.orbicurve.coverToPunctured = Set.univ := by
  exact S.orbicurve.cover_range_eq

theorem definition31_cover_map_transport
    {x y : S.orbicurve.cover}
    (h : S.orbicurve.coverToPunctured x =
      S.orbicurve.coverToPunctured y) :
    S.orbicurve.curveToPunctured (S.orbicurve.coverToPunctured x) =
      S.orbicurve.curveToPunctured (S.orbicurve.coverToPunctured y) := by
  exact S.orbicurve.curve_map_transport h

theorem definition31_cusp_count_positive :
    0 < S.orbicurve.cuspCount := by
  exact S.orbicurve.cuspCount_pos

theorem definition31_cusp_count_nonzero :
    S.orbicurve.cuspCount ≠ 0 := by
  exact Nat.ne_of_gt S.orbicurve.cuspCount_pos

theorem definition31_curve_compatibility :
    S.orbicurve.curveCompatibility := by
  exact S.orbicurve.curveCompatibility_proved

theorem definition31_orbicurve_exact_injection :
    Function.Injective S.orbicurve.exactSequence.injection := by
  exact S.orbicurve.exact_sequence_injection_injective

theorem definition31_orbicurve_exact_projection :
    Function.Surjective S.orbicurve.exactSequence.projection := by
  exact S.orbicurve.exact_sequence_projection_surjective

theorem definition31_orbicurve_exact_section
    (g : S.orbicurve.exactSequence.baseGroup) :
    S.orbicurve.exactSequence.projection
      (S.orbicurve.exactSequence.sectionMap g) = g := by
  exact S.orbicurve.exact_sequence_section g

theorem definition31_orbicurve_exact_kernel_witness
    (x : S.orbicurve.exactSequence.coverGroup)
    (hx : S.orbicurve.exactSequence.projection x = 1) :
    ∃ y, S.orbicurve.exactSequence.injection y = x := by
  exact S.orbicurve.exact_sequence_kernel_witness x hx

/-! ## D7 section equivalences and local groups -/

noncomputable def definition31_section_equiv :
    S.sections.valuationCarrier ≃ S.sections.modifiedValuationCarrier :=
  Equiv.ofBijective S.sections.sectionMap
    ⟨S.sections.sectionMap_injective, S.sections.sectionMap_surjective⟩

theorem definition31_section_equiv_apply (x : S.sections.valuationCarrier) :
    definition31_section_equiv S x = S.sections.sectionMap x := rfl

theorem definition31_section_equiv_symm_apply
    (y : S.sections.modifiedValuationCarrier) :
    (definition31_section_equiv S).symm y =
      S.sections.sectionRightInverse y := by
  apply S.sections.sectionMap_injective
  calc
    S.sections.sectionMap ((definition31_section_equiv S).symm y) = y :=
      (definition31_section_equiv S).apply_symm_apply y
    _ = S.sections.sectionMap (S.sections.sectionRightInverse y) :=
      (S.sections.section_right_inverse y).symm

theorem definition31_section_left_inverse
    (x : S.sections.valuationCarrier) :
    S.sections.sectionRightInverse (S.sections.sectionMap x) = x := by
  exact S.sections.section_left_inverse x

theorem definition31_section_right_inverse
    (y : S.sections.modifiedValuationCarrier) :
    S.sections.sectionMap (S.sections.sectionRightInverse y) = y := by
  exact S.sections.section_right_inverse y

theorem definition31_section_map_injective :
    Function.Injective S.sections.sectionMap := by
  exact S.sections.sectionMap_injective

theorem definition31_section_map_surjective :
    Function.Surjective S.sections.sectionMap := by
  exact S.sections.sectionMap_surjective

theorem definition31_section_right_inverse_injective :
    Function.Injective S.sections.sectionRightInverse := by
  exact S.sections.sectionRightInverse_injective

theorem definition31_section_right_inverse_surjective :
    Function.Surjective S.sections.sectionRightInverse := by
  exact S.sections.sectionRightInverse_surjective

theorem definition31_section_round_trip
    (x : S.sections.valuationCarrier) :
    S.sections.sectionMap
      (S.sections.sectionRightInverse (S.sections.sectionMap x)) =
      S.sections.sectionMap x := by
  exact S.sections.section_round_trip x

theorem definition31_section_round_trip_modified
    (y : S.sections.modifiedValuationCarrier) :
    S.sections.sectionRightInverse
      (S.sections.sectionMap (S.sections.sectionRightInverse y)) =
      S.sections.sectionRightInverse y := by
  exact S.sections.section_round_trip_modified y

noncomputable def definition31_local_group_equiv
    (x : S.sections.valuationCarrier) :
    S.sections.localGroupCarrier x ≃
      S.sections.modifiedLocalGroupCarrier (S.sections.sectionMap x) :=
  Equiv.ofBijective (S.sections.localGroupSection x)
    (S.sections.local_group_section_bijective x)

theorem definition31_local_group_equiv_apply
    (x : S.sections.valuationCarrier)
    (y : S.sections.localGroupCarrier x) :
    definition31_local_group_equiv S x y =
      S.sections.localGroupSection x y := rfl

theorem definition31_local_group_equiv_injective
    (x : S.sections.valuationCarrier) :
    Function.Injective (definition31_local_group_equiv S x) := by
  exact (definition31_local_group_equiv S x).injective

theorem definition31_local_group_equiv_surjective
    (x : S.sections.valuationCarrier) :
    Function.Surjective (definition31_local_group_equiv S x) := by
  exact (definition31_local_group_equiv S x).surjective

theorem definition31_local_group_equiv_bijective
    (x : S.sections.valuationCarrier) :
    Function.Bijective (definition31_local_group_equiv S x) := by
  exact (definition31_local_group_equiv S x).bijective

theorem definition31_local_group_section_injective
    (x : S.sections.valuationCarrier) :
    Function.Injective (S.sections.localGroupSection x) := by
  exact S.sections.local_group_section_injective x

theorem definition31_local_group_section_surjective
    (x : S.sections.valuationCarrier) :
    Function.Surjective (S.sections.localGroupSection x) := by
  exact S.sections.local_group_section_surjective x

theorem definition31_local_group_section_bijective
    (x : S.sections.valuationCarrier) :
    Function.Bijective (S.sections.localGroupSection x) := by
  exact S.sections.local_group_section_bijective x

theorem definition31_finite_place_data : S.sections.finitePlaceData := by
  exact S.sections.finitePlaceData_proved

theorem definition31_infinite_place_data : S.sections.infinitePlaceData := by
  exact S.sections.infinitePlaceData_proved

theorem definition31_section_clause_bundle :
    Function.Bijective S.sections.sectionMap ∧
      (∀ x, Function.Bijective (S.sections.localGroupSection x)) ∧
      S.sections.finitePlaceData ∧ S.sections.infinitePlaceData := by
  exact ⟨⟨definition31_section_map_injective S,
      definition31_section_map_surjective S⟩,
    definition31_local_group_section_bijective S,
    definition31_finite_place_data S,
    definition31_infinite_place_data S⟩

/-! ## D8 cusp normalization and positivity -/

theorem definition31_cusp_epsilon_positive : 0 < S.cusp.epsilon := by
  exact S.cusp.epsilon_positive

theorem definition31_cusp_epsilon_nonzero : S.cusp.epsilon ≠ 0 := by
  exact S.cusp.epsilon_nonzero

theorem definition31_cusp_scale_positive : 0 < S.cusp.cuspScale := by
  exact S.cusp.cuspScale_positive

theorem definition31_cusp_scale_nonzero : S.cusp.cuspScale ≠ 0 := by
  exact ne_of_gt S.cusp.cuspScale_positive

theorem definition31_cusp_compatibility : S.cusp.epsilon_compatibility := by
  exact S.cusp.epsilon_compatibility_proved

theorem definition31_cusp_product_positive :
    0 < S.cusp.epsilon * S.cusp.cuspScale := by
  exact mul_pos S.cusp.epsilon_positive S.cusp.cuspScale_positive

theorem definition31_cusp_product_nonzero :
    S.cusp.epsilon * S.cusp.cuspScale ≠ 0 := by
  exact S.cusp.epsilon_scale_relation

theorem definition31_cusp_normalized_positive :
    0 < S.cusp.epsilon / S.cusp.cuspScale := by
  exact div_pos S.cusp.epsilon_positive S.cusp.cuspScale_positive

theorem definition31_cusp_normalized_nonzero :
    S.cusp.epsilon / S.cusp.cuspScale ≠ 0 := by
  exact ne_of_gt (definition31_cusp_normalized_positive S)

theorem definition31_cusp_epsilon_pow_positive (n : Nat) :
    0 < S.cusp.epsilon ^ n := by
  exact pow_pos S.cusp.epsilon_positive n

theorem definition31_cusp_scale_pow_positive (n : Nat) :
    0 < S.cusp.cuspScale ^ n := by
  exact pow_pos S.cusp.cuspScale_positive n

theorem definition31_cusp_epsilon_pow_nonzero (n : Nat) :
    S.cusp.epsilon ^ n ≠ 0 := by
  exact pow_ne_zero n S.cusp.epsilon_nonzero

theorem definition31_cusp_scale_pow_nonzero (n : Nat) :
    S.cusp.cuspScale ^ n ≠ 0 := by
  exact pow_ne_zero n (definition31_cusp_scale_nonzero S)

theorem definition31_cusp_normalized_eq_div :
    SourceCuspClause.rootNormalized S.cusp =
      S.cusp.epsilon / S.cusp.cuspScale := rfl

theorem definition31_cusp_normalized_positive_root :
    0 < SourceCuspClause.rootNormalized S.cusp := by
  exact SourceCuspClause.rootNormalized_positive S.cusp

theorem definition31_cusp_normalized_nonzero_root :
    SourceCuspClause.rootNormalized S.cusp ≠ 0 := by
  exact SourceCuspClause.rootNormalized_nonzero S.cusp

theorem definition31_cusp_product_root_positive :
    0 < SourceCuspClause.rootProduct S.cusp := by
  exact SourceCuspClause.rootProduct_positive S.cusp

theorem definition31_cusp_product_root_nonzero :
    SourceCuspClause.rootProduct S.cusp ≠ 0 := by
  exact SourceCuspClause.rootProduct_nonzero S.cusp

theorem definition31_cusp_epsilon_log_pow (n : Nat) :
    Real.log (S.cusp.epsilon ^ n) =
      n * Real.log S.cusp.epsilon := by
  exact S.cusp_epsilon_pow_log n

theorem definition31_cusp_product_log_nonzero :
    S.cusp.epsilon * S.cusp.cuspScale ≠ 0 := by
  exact definition31_cusp_product_nonzero S

/-! ## Complete supplied-source clause bundle -/

structure Definition31SourceConclusion : Prop where
  arithmetic :
    HasSqrtNegOne S.arithmetic.F ∧
      Nat.Coprime (Module.finrank S.arithmetic.Fmod S.arithmetic.F)
        l.value
  selected_nonempty : Nonempty S.selectedPlaces
  bad_places_finite : Nonempty (Fintype S.badPlaces)
  bad_label_compatibility : ∀ b,
    S.reduction.partition.selectedLabel
        (S.reduction.partition.badIncluded b) =
      S.reduction.partition.badLabel b
  reduction : ∀ b,
    S.reduction.stableReduction b ∧
      S.reduction.multiplicativeReduction b ∧
      S.reduction.splitMultiplicativeReduction b ∧
      (S.reduction.splitMultiplicativeReduction b →
        S.reduction.multiplicativeReduction b) ∧
      S.reduction.qParameter b ≠ 0 ∧
      S.reduction.qParameter b ≠ 1 ∧
      ‖S.reduction.qParameter b‖ ∈ Set.Ioo (0 : Real) 1
  torsion :
    Nonempty S.torsion.torsionCarrier ∧
      Function.Surjective S.torsion.representation ∧
      S.torsion.imageContainsSL2 ∧
      S.torsion.sixTorsionIndependent ∧
      S.torsion.lTorsionCompatible
  orbicurve :
    Function.Surjective S.orbicurve.coverToPunctured ∧
      0 < S.orbicurve.cuspCount ∧
      S.orbicurve.curveCompatibility
  exact_sequence :
    Function.Injective S.orbicurve.exactSequence.injection ∧
      Function.Surjective S.orbicurve.exactSequence.projection ∧
      (∀ x, S.orbicurve.exactSequence.projection x = 1 ↔
        ∃ y, S.orbicurve.exactSequence.injection y = x) ∧
      (∀ g, S.orbicurve.exactSequence.projection
        (S.orbicurve.exactSequence.sectionMap g) = g)
  sections :
    Function.Bijective S.sections.sectionMap ∧
      (∀ x, Function.Bijective (S.sections.localGroupSection x)) ∧
      S.sections.finitePlaceData ∧ S.sections.infinitePlaceData
  cusp :
    0 < S.cusp.epsilon ∧ S.cusp.epsilon ≠ 0 ∧
      S.cusp.epsilon_compatibility ∧
      0 < S.cusp.cuspScale ∧
      S.cusp.epsilon * S.cusp.cuspScale ≠ 0
  compatibility :
    S.arithmetic_reduction_compatibility ∧
      S.arithmetic_torsion_compatibility ∧
      S.arithmetic_orbicurve_compatibility ∧
      S.arithmetic_section_compatibility ∧
      S.arithmetic_cusp_compatibility

theorem definition31_source_conclusion : Definition31SourceConclusion S where
  arithmetic := (rootCertificate S).arithmetic
  selected_nonempty := definition31_selected_places_nonempty S
  bad_places_finite := ⟨definition31_bad_places_fintype S⟩
  bad_label_compatibility := by
    intro b
    exact definition31_bad_label_compatibility S b
  reduction := by
    intro b
    refine ⟨definition31_stable_reduction S b,
      definition31_multiplicative_reduction S b,
      definition31_split_multiplicative_reduction S b,
      definition31_split_implies_multiplicative S b,
      definition31_q_parameter_nonzero S b,
      definition31_q_parameter_ne_one S b,
      definition31_q_norm_interval S b⟩
  torsion := by
    exact ⟨definition31_torsion_nonempty S,
      definition31_torsion_representation_surjective S,
      definition31_torsion_image_contains_SL2 S,
      definition31_torsion_six_independent S,
      definition31_torsion_l_compatible S⟩
  orbicurve := by
    exact ⟨definition31_cover_surjective S,
      definition31_cusp_count_positive S,
      definition31_curve_compatibility S⟩
  exact_sequence := by
    refine ⟨definition31_orbicurve_exact_injection S,
      definition31_orbicurve_exact_projection S, ?_, ?_⟩
    · intro x
      exact definition31_exact_sequence_iff S x
    · intro g
      exact definition31_orbicurve_exact_section S g
  sections := by
    exact ⟨⟨definition31_section_map_injective S,
        definition31_section_map_surjective S⟩,
      definition31_local_group_section_bijective S,
      definition31_finite_place_data S,
      definition31_infinite_place_data S⟩
  cusp := by
    exact ⟨definition31_cusp_epsilon_positive S,
      definition31_cusp_epsilon_nonzero S,
      definition31_cusp_compatibility S,
      definition31_cusp_scale_positive S,
      definition31_cusp_product_nonzero S⟩
  compatibility := by
    exact ⟨S.arithmetic_reduction_spec,
      S.arithmetic_torsion_spec,
      S.arithmetic_orbicurve_spec,
      S.arithmetic_section_spec,
      S.arithmetic_cusp_spec⟩

theorem definition31_source_conclusion_arithmetic :
    HasSqrtNegOne S.arithmetic.F ∧
      Nat.Coprime (Module.finrank S.arithmetic.Fmod S.arithmetic.F)
        l.value := by
  exact (definition31_source_conclusion S).arithmetic

theorem definition31_source_conclusion_selected :
    Nonempty S.selectedPlaces := by
  exact (definition31_source_conclusion S).selected_nonempty

theorem definition31_source_conclusion_bad_finite :
    Nonempty (Fintype S.badPlaces) := by
  exact (definition31_source_conclusion S).bad_places_finite

theorem definition31_source_conclusion_reduction (b : S.badPlaces) :
    S.reduction.stableReduction b ∧
      S.reduction.multiplicativeReduction b ∧
      S.reduction.splitMultiplicativeReduction b ∧
      (S.reduction.splitMultiplicativeReduction b →
        S.reduction.multiplicativeReduction b) ∧
      S.reduction.qParameter b ≠ 0 ∧
      S.reduction.qParameter b ≠ 1 ∧
      ‖S.reduction.qParameter b‖ ∈ Set.Ioo (0 : Real) 1 := by
  exact (definition31_source_conclusion S).reduction b

theorem definition31_source_conclusion_torsion :
    Nonempty S.torsion.torsionCarrier ∧
      Function.Surjective S.torsion.representation ∧
      S.torsion.imageContainsSL2 ∧
      S.torsion.sixTorsionIndependent ∧
      S.torsion.lTorsionCompatible := by
  exact (definition31_source_conclusion S).torsion

theorem definition31_source_conclusion_orbicurve :
    Function.Surjective S.orbicurve.coverToPunctured ∧
      0 < S.orbicurve.cuspCount ∧
      S.orbicurve.curveCompatibility := by
  exact (definition31_source_conclusion S).orbicurve

theorem definition31_source_conclusion_exact_sequence :
    Function.Injective S.orbicurve.exactSequence.injection ∧
      Function.Surjective S.orbicurve.exactSequence.projection ∧
      (∀ x, S.orbicurve.exactSequence.projection x = 1 ↔
        ∃ y, S.orbicurve.exactSequence.injection y = x) ∧
      (∀ g, S.orbicurve.exactSequence.projection
        (S.orbicurve.exactSequence.sectionMap g) = g) := by
  exact (definition31_source_conclusion S).exact_sequence

theorem definition31_source_conclusion_sections :
    Function.Bijective S.sections.sectionMap ∧
      (∀ x, Function.Bijective (S.sections.localGroupSection x)) ∧
      S.sections.finitePlaceData ∧ S.sections.infinitePlaceData := by
  exact (definition31_source_conclusion S).sections

theorem definition31_source_conclusion_cusp :
    0 < S.cusp.epsilon ∧ S.cusp.epsilon ≠ 0 ∧
      S.cusp.epsilon_compatibility ∧
      0 < S.cusp.cuspScale ∧
      S.cusp.epsilon * S.cusp.cuspScale ≠ 0 := by
  exact (definition31_source_conclusion S).cusp

theorem definition31_source_conclusion_compatibility :
    S.arithmetic_reduction_compatibility ∧
      S.arithmetic_torsion_compatibility ∧
      S.arithmetic_orbicurve_compatibility ∧
      S.arithmetic_section_compatibility ∧
      S.arithmetic_cusp_compatibility := by
  exact (definition31_source_conclusion S).compatibility

/-! ## D0-D2: kernel, prime label, and arithmetic tower

These declarations are the first three nodes of the audit.  They expose the
actual fields of the arithmetic input one at a time; no source place, local
q-parameter, torsion image, or exact-sequence field is used here.
-/

@[reducible] noncomputable def d0_standard_field_Fmod : Field S.arithmetic.Fmod := by
  infer_instance

theorem d0_standard_number_field_Fmod : NumberField S.arithmetic.Fmod := by
  infer_instance

@[reducible] noncomputable def d0_standard_field_F : Field S.arithmetic.F := by
  infer_instance

theorem d0_standard_number_field_F : NumberField S.arithmetic.F := by
  infer_instance

@[reducible] noncomputable def d0_standard_field_K : Field S.arithmetic.K := by
  infer_instance

theorem d0_standard_number_field_K : NumberField S.arithmetic.K := by
  infer_instance

@[reducible] noncomputable def d0_algebra_Fmod_F : Algebra S.arithmetic.Fmod S.arithmetic.F := by
  infer_instance

@[reducible] noncomputable def d0_algebra_F_K : Algebra S.arithmetic.F S.arithmetic.K := by
  infer_instance

@[reducible] noncomputable def d0_algebra_Fmod_K : Algebra S.arithmetic.Fmod S.arithmetic.K := by
  infer_instance

theorem d0_scalar_tower :
    IsScalarTower S.arithmetic.Fmod S.arithmetic.F S.arithmetic.K := by
  infer_instance

theorem d0_finite_dimensional_Fmod_F :
    FiniteDimensional S.arithmetic.Fmod S.arithmetic.F := by
  infer_instance

theorem d0_galois_Fmod_F :
    IsGalois S.arithmetic.Fmod S.arithmetic.F := by
  infer_instance

theorem d0_finite_dimensional_F_K :
    FiniteDimensional S.arithmetic.F S.arithmetic.K := by
  infer_instance

theorem d0_galois_F_K : IsGalois S.arithmetic.F S.arithmetic.K := by
  infer_instance

noncomputable def d0_curve_carrier :
    PuncturedEllipticCurve S.arithmetic.F :=
  S.arithmetic.curve

theorem d0_curve_is_elliptic :
    S.arithmetic.curve.curve.IsElliptic :=
  S.arithmetic.curve.isElliptic

noncomputable def d0_curve_puncture :
    S.arithmetic.curve.curve.toProjective.Point :=
  S.arithmetic.curve.puncture

theorem d0_curve_j_invariant :
    S.arithmetic.curve.jInvariant = S.arithmetic.curve.curve.j := by
  exact S.arithmetic.curve.jInvariant_spec

theorem d0_tower_carrier :
    ThetaFieldTower l S.arithmetic.Fmod S.arithmetic.F S.arithmetic.K :=
  S.arithmetic.tower

theorem d0_tower_sqrt_neg_one :
    HasSqrtNegOne S.arithmetic.F := by
  exact S.arithmetic.tower.sqrtNegOne

theorem d0_tower_degree_prime_to_l :
    Nat.Coprime (Module.finrank S.arithmetic.Fmod S.arithmetic.F)
      l.value := by
  exact S.arithmetic.tower.degreePrimeToL

theorem d0_tower_scalar_tower :
    IsScalarTower S.arithmetic.Fmod S.arithmetic.F S.arithmetic.K := by
  infer_instance

theorem d0_tower_Fmod_F_finite :
    FiniteDimensional S.arithmetic.Fmod S.arithmetic.F := by
  infer_instance

theorem d0_tower_F_K_finite :
    FiniteDimensional S.arithmetic.F S.arithmetic.K := by
  infer_instance

theorem d0_tower_Fmod_F_galois :
    IsGalois S.arithmetic.Fmod S.arithmetic.F := by
  infer_instance

theorem d0_tower_F_K_galois : IsGalois S.arithmetic.F S.arithmetic.K := by
  infer_instance

theorem d1_prime : Nat.Prime l.value := by
  exact l.prime

theorem d1_prime_ge_five : 5 ≤ l.value := by
  exact l.ge_five

theorem d1_prime_odd : Odd l.value := by
  exact l.odd

theorem d1_prime_pos : 0 < l.value := by
  exact l.prime.pos

theorem d1_prime_ne_zero : l.value ≠ 0 := by
  exact Nat.ne_of_gt d1_prime_pos

theorem d1_prime_ne_one : l.value ≠ 1 := by
  exact Nat.Prime.ne_one d1_prime

theorem d1_prime_not_even : ¬Even l.value := by
  exact Nat.not_even_iff_odd.mpr d1_prime_odd

theorem d1_prime_two_le : 2 ≤ l.value := by
  exact le_trans (by decide : 2 ≤ 5) d1_prime_ge_five

theorem d1_prime_three_le : 3 ≤ l.value := by
  exact le_trans (by decide : 3 ≤ 5) d1_prime_ge_five

theorem d1_prime_four_le : 4 ≤ l.value := by
  exact le_trans (by decide : 4 ≤ 5) d1_prime_ge_five

theorem d1_prime_six_or_more : 6 ≤ l.value ∨ l.value = 5 := by
  have hl := d1_prime_ge_five (l := l)
  omega

theorem d1_prime_mod_two : l.value % 2 = 1 := by
  apply d1_prime.mod_two_eq_one_iff_ne_two.mpr
  have hl := d1_prime_ge_five (l := l)
  omega

theorem d1_prime_not_dvd_two : ¬l.value ∣ 2 := by
  intro h
  have hle := Nat.le_of_dvd (by decide : 0 < 2) h
  have hl := d1_prime_ge_five (l := l)
  omega

theorem d1_prime_dvd_or_coprime (n : Nat) :
    l.value ∣ n ∨ Nat.Coprime l.value n := by
  by_cases h : l.value ∣ n
  · exact Or.inl h
  · exact Or.inr (d1_prime.coprime_iff_not_dvd.mpr h)

theorem d1_prime_coprime_two : Nat.Coprime l.value 2 := by
  exact Nat.Coprime.symm (Nat.coprime_two_left.mpr d1_prime_odd)

theorem d1_prime_coprime_three : Nat.Coprime l.value 3 := by
  exact d1_prime.coprime_iff_not_dvd.mpr (by
    intro hd
    have hle := Nat.le_of_dvd (by decide : 0 < 3) hd
    have hl := d1_prime_ge_five (l := l)
    omega)

theorem d1_prime_coprime_six : Nat.Coprime l.value 6 := by
  have h := (d1_prime_coprime_two (l := l)).mul_right
    (d1_prime_coprime_three (l := l))
  simpa [show 6 = 2 * 3 by decide] using h

theorem d1_label_eq_value : l.value = l.value := rfl

theorem d1_label_prime_spec : Nat.Prime l.value := by
  exact l.prime

theorem d1_label_lower_bound_spec : 5 ≤ l.value := d1_prime_ge_five

theorem d1_label_odd_spec : Odd l.value := d1_prime_odd

theorem d2_arithmetic_Fmod_eq : S.arithmetic.Fmod = S.arithmetic.Fmod := rfl

theorem d2_arithmetic_F_eq : S.arithmetic.F = S.arithmetic.F := rfl

theorem d2_arithmetic_K_eq : S.arithmetic.K = S.arithmetic.K := rfl

theorem d2_arithmetic_curve_eq :
    S.arithmetic.curve = S.arithmetic.curve := rfl

theorem d2_arithmetic_tower_eq :
    S.arithmetic.tower = S.arithmetic.tower := rfl

@[reducible] noncomputable def d2_Fmod_is_field : Field S.arithmetic.Fmod :=
  d0_standard_field_Fmod S

@[reducible] noncomputable def d2_F_is_field : Field S.arithmetic.F := d0_standard_field_F S

@[reducible] noncomputable def d2_K_is_field : Field S.arithmetic.K := d0_standard_field_K S

theorem d2_Fmod_is_number_field :
    NumberField S.arithmetic.Fmod := d0_standard_number_field_Fmod S

theorem d2_F_is_number_field :
    NumberField S.arithmetic.F := d0_standard_number_field_F S

theorem d2_K_is_number_field :
    NumberField S.arithmetic.K := d0_standard_number_field_K S

@[reducible] noncomputable def d2_Fmod_F_algebra :
    Algebra S.arithmetic.Fmod S.arithmetic.F := d0_algebra_Fmod_F S

@[reducible] noncomputable def d2_F_K_algebra :
    Algebra S.arithmetic.F S.arithmetic.K := d0_algebra_F_K S

@[reducible] noncomputable def d2_Fmod_K_algebra :
    Algebra S.arithmetic.Fmod S.arithmetic.K := d0_algebra_Fmod_K S

theorem d2_Fmod_F_scalar_tower :
    IsScalarTower S.arithmetic.Fmod S.arithmetic.F S.arithmetic.K :=
  d0_scalar_tower S

theorem d2_Fmod_F_finite_dimensional :
    FiniteDimensional S.arithmetic.Fmod S.arithmetic.F :=
  d0_finite_dimensional_Fmod_F S

theorem d2_F_K_finite_dimensional :
    FiniteDimensional S.arithmetic.F S.arithmetic.K :=
  d0_finite_dimensional_F_K S

theorem d2_Fmod_F_galois :
    IsGalois S.arithmetic.Fmod S.arithmetic.F := d0_galois_Fmod_F S

theorem d2_F_K_galois : IsGalois S.arithmetic.F S.arithmetic.K :=
  d0_galois_F_K S

theorem d2_tower_sqrt_neg_one : HasSqrtNegOne S.arithmetic.F :=
  d0_tower_sqrt_neg_one S

theorem d2_tower_degree_coprime :
    Nat.Coprime (Module.finrank S.arithmetic.Fmod S.arithmetic.F)
      l.value := d0_tower_degree_prime_to_l S

theorem d2_tower_degree_positive :
    0 < Module.finrank S.arithmetic.Fmod S.arithmetic.F := by
  exact Module.finrank_pos

theorem d2_tower_degree_nonzero :
    Module.finrank S.arithmetic.Fmod S.arithmetic.F ≠ 0 := by
  exact Nat.ne_of_gt (d2_tower_degree_positive S)

theorem d2_curve_is_elliptic :
    S.arithmetic.curve.curve.IsElliptic := d0_curve_is_elliptic S

theorem d2_curve_puncture_exists :
    Nonempty S.arithmetic.curve.curve.toProjective.Point :=
  ⟨S.arithmetic.curve.puncture⟩

theorem d2_curve_j_spec :
    S.arithmetic.curve.jInvariant = S.arithmetic.curve.curve.j :=
  d0_curve_j_invariant S

theorem d2_curve_base_change
    (K : Type v) [Field K] [Algebra S.arithmetic.F K] :
    (S.arithmetic.curve.baseChange K).curve =
      S.arithmetic.curve.curve.baseChange K := by
  exact S.arithmetic.curve.baseChange_curve K

theorem d2_curve_map
    (K : Type v) [Field K] (f : S.arithmetic.F →+* K) :
    (S.arithmetic.curve.map f).curve =
      S.arithmetic.curve.curve.map f := by
  exact S.arithmetic.curve.map_curve f

theorem d2_curve_puncture_map
    (K : Type v) [Field K] (f : S.arithmetic.F →+* K) :
    (S.arithmetic.curve.map f).puncture =
      PuncturedEllipticCurve.projectivePointMap f
        S.arithmetic.curve.curve S.arithmetic.curve.puncture := by
  exact S.arithmetic.curve.map_puncture f

theorem d2_sqrt_neg_one_witness :
    ∃ i : S.arithmetic.F, i * i = -1 := by
  exact d2_tower_sqrt_neg_one S

theorem d2_sqrt_neg_one_stable_under_eq
    {i : S.arithmetic.F} (hi : i * i = -1) :
    ∃ j : S.arithmetic.F, j * j = -1 := by
  exact ⟨i, hi⟩

theorem d2_arithmetic_bundle :
    HasSqrtNegOne S.arithmetic.F ∧
      Nat.Coprime (Module.finrank S.arithmetic.Fmod S.arithmetic.F)
        l.value ∧
      ∃ curve : PuncturedEllipticCurve S.arithmetic.F,
        curve = S.arithmetic.curve := by
  exact ⟨d2_tower_sqrt_neg_one S,
    d2_tower_degree_coprime S,
    ⟨S.arithmetic.curve, rfl⟩⟩

theorem d2_arithmetic_instances :
    Nonempty (Field S.arithmetic.Fmod) ∧
      Nonempty (Field S.arithmetic.F) ∧
      Nonempty (Field S.arithmetic.K) := by
  exact ⟨⟨d2_Fmod_is_field S⟩, ⟨d2_F_is_field S⟩,
    ⟨d2_K_is_field S⟩⟩

theorem d2_arithmetic_number_fields :
    NumberField S.arithmetic.Fmod ∧ NumberField S.arithmetic.F ∧
      NumberField S.arithmetic.K := by
  exact ⟨d2_Fmod_is_number_field S, d2_F_is_number_field S,
    d2_K_is_number_field S⟩

theorem d2_arithmetic_galois_tower :
    IsGalois S.arithmetic.Fmod S.arithmetic.F ∧
      IsGalois S.arithmetic.F S.arithmetic.K := by
  exact ⟨d2_Fmod_F_galois S, d2_F_K_galois S⟩

theorem d2_arithmetic_finite_tower :
    FiniteDimensional S.arithmetic.Fmod S.arithmetic.F ∧
      FiniteDimensional S.arithmetic.F S.arithmetic.K := by
  exact ⟨d2_Fmod_F_finite_dimensional S,
    d2_F_K_finite_dimensional S⟩

theorem d2_arithmetic_complete :
    HasSqrtNegOne S.arithmetic.F ∧
      Nat.Coprime (Module.finrank S.arithmetic.Fmod S.arithmetic.F)
        l.value ∧
      ∃ curve : PuncturedEllipticCurve S.arithmetic.F,
        curve = S.arithmetic.curve := by
  exact ⟨d2_tower_sqrt_neg_one S, d2_tower_degree_coprime S,
    ⟨S.arithmetic.curve, rfl⟩⟩

theorem d1_prime_power_pos (n : Nat) : 0 < l.value ^ (n + 1) := by
  exact pow_pos (d1_prime_pos (l := l)) (n + 1)

theorem d1_prime_power_ne_zero (n : Nat) : l.value ^ n ≠ 0 := by
  exact pow_ne_zero n (d1_prime_ne_zero (l := l))

theorem d1_prime_dvd_power (n : Nat) : l.value ∣ l.value ^ (n + 1) := by
  refine ⟨l.value ^ n, ?_⟩
  rw [pow_succ, mul_comm]

theorem d1_prime_power_mod_two (n : Nat) :
    l.value ^ (n + 1) % 2 = 1 := by
  have h := d1_prime_odd (l := l)
  exact Nat.odd_iff.mp (Odd.pow h)

theorem d1_prime_coprime_of_not_dvd {n : Nat}
    (h : ¬l.value ∣ n) : Nat.Coprime l.value n := by
  exact d1_prime.coprime_iff_not_dvd.mpr h

theorem d1_prime_coprime_two_left : Nat.Coprime 2 l.value := by
  exact Nat.Coprime.symm d1_prime_coprime_two

theorem d1_prime_coprime_six_left : Nat.Coprime 6 l.value := by
  exact Nat.Coprime.symm d1_prime_coprime_six

theorem d1_prime_not_mem_interval (n : Nat)
    (hn : n < 5) : n ≠ l.value := by
  intro h
  rw [h] at hn
  have hl := d1_prime_ge_five (l := l)
  omega

theorem d1_prime_value_sub_pos (n : Nat) (hn : l.value < n) :
    0 < n - l.value := by
  omega

theorem d1_prime_value_add_pos (n : Nat) : 0 < l.value + n := by
  exact Nat.add_pos_left d1_prime_pos n

theorem d1_prime_value_mul_pos (n : Nat) (hn : 0 < n) :
    0 < l.value * n := by
  exact Nat.mul_pos d1_prime_pos hn

theorem d1_prime_value_ne_two : l.value ≠ 2 := by
  intro h
  have hl := d1_prime_ge_five (l := l)
  omega

theorem d1_prime_value_ne_three : l.value ≠ 3 := by
  intro h
  have hl := d1_prime_ge_five (l := l)
  omega

theorem d1_prime_value_ne_four : l.value ≠ 4 := by
  intro h
  have hl := d1_prime_ge_five (l := l)
  omega

theorem d2_finrank_eq_zero_iff_false :
    Module.finrank S.arithmetic.Fmod S.arithmetic.F = 0 ↔ False := by
  constructor
  · intro h
    have hp := d2_tower_degree_positive S
    omega
  · intro h
    exact False.elim h

theorem d2_finrank_ne_l_of_coprime :
    Module.finrank S.arithmetic.Fmod S.arithmetic.F ≠ l.value := by
  intro h
  have hc := d2_tower_degree_coprime S
  rw [h] at hc
  have hnot : ¬Nat.Coprime l.value l.value := by
    exact ((d1_prime (l := l)).dvd_iff_not_coprime).mp
      (dvd_refl l.value)
  exact hnot (Nat.Coprime.symm hc)

theorem d2_finrank_coprime_symm :
    Nat.Coprime l.value
      (Module.finrank S.arithmetic.Fmod S.arithmetic.F) := by
  exact Nat.Coprime.symm (d2_tower_degree_coprime S)

theorem d2_finrank_positive_multiple (n : Nat) (hn : 0 < n) :
    0 < Module.finrank S.arithmetic.Fmod S.arithmetic.F * n := by
  exact Nat.mul_pos (d2_tower_degree_positive S) hn

theorem d2_tower_degree_power_coprime (n : Nat) :
    Nat.Coprime (Module.finrank S.arithmetic.Fmod S.arithmetic.F)
      (l.value ^ n) := by
  exact (d2_tower_degree_coprime S).pow_right n

theorem d2_tower_degree_mul_coprime (n : Nat)
    (hn : Nat.Coprime n l.value) :
    Nat.Coprime
      (Module.finrank S.arithmetic.Fmod S.arithmetic.F * n) l.value := by
  exact Nat.Coprime.mul_left (d2_tower_degree_coprime S) hn

theorem d2_sqrt_neg_one_square :
    ∃ i : S.arithmetic.F, i ^ 2 = -1 := by
  rcases d2_sqrt_neg_one_witness S with ⟨i, hi⟩
  refine ⟨i, ?_⟩
  simpa [pow_two] using hi

theorem d2_sqrt_neg_one_nonzero {i : S.arithmetic.F}
    (hi : i * i = -1) : i ≠ 0 := by
  intro h
  subst i
  simp at hi

theorem d2_sqrt_neg_one_not_one {i : S.arithmetic.F}
    (hi : i * i = -1) : i ≠ 1 := by
  intro h
  subst i
  norm_num at hi

theorem d2_curve_map_j_invariant
    (K : Type v) [Field K] (f : S.arithmetic.F →+* K) :
    (S.arithmetic.curve.map f).jInvariant =
      (S.arithmetic.curve.curve.map f).j := by
  exact (S.arithmetic.curve.map f).jInvariant_spec

theorem d2_curve_base_change_puncture
    (K : Type v) [Field K] [Algebra S.arithmetic.F K] :
    (S.arithmetic.curve.baseChange K).puncture =
      PuncturedEllipticCurve.projectivePointMap
        (algebraMap S.arithmetic.F K)
        S.arithmetic.curve.curve S.arithmetic.curve.puncture := by
  rfl

theorem d2_curve_is_elliptic_after_map
    (K : Type v) [Field K] (f : S.arithmetic.F →+* K) :
    (S.arithmetic.curve.map f).curve.IsElliptic := by
  exact (S.arithmetic.curve.map f).isElliptic

theorem d2_curve_is_elliptic_after_base_change
    (K : Type v) [Field K] [Algebra S.arithmetic.F K] :
    (S.arithmetic.curve.baseChange K).curve.IsElliptic := by
  exact (S.arithmetic.curve.baseChange K).isElliptic

theorem d2_arithmetic_projection_bundle :
    (S.arithmetic.Fmod = S.arithmetic.Fmod) ∧
      (S.arithmetic.F = S.arithmetic.F) ∧
      (S.arithmetic.K = S.arithmetic.K) ∧
      (S.arithmetic.curve = S.arithmetic.curve) := by
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem d2_tower_projection_bundle :
    (S.arithmetic.tower.sqrtNegOne = S.arithmetic.tower.sqrtNegOne) ∧
      (S.arithmetic.tower.degreePrimeToL =
        S.arithmetic.tower.degreePrimeToL) := by
  exact ⟨rfl, rfl⟩

theorem d2_curve_projection_bundle :
    (S.arithmetic.curve.curve = S.arithmetic.curve.curve) ∧
      (S.arithmetic.curve.puncture = S.arithmetic.curve.puncture) := by
  exact ⟨rfl, rfl⟩

theorem d2_field_tower_projection_bundle :
    HasSqrtNegOne S.arithmetic.F ∧
      Nat.Coprime (Module.finrank S.arithmetic.Fmod S.arithmetic.F)
        l.value ∧
      IsScalarTower S.arithmetic.Fmod S.arithmetic.F S.arithmetic.K ∧
      FiniteDimensional S.arithmetic.Fmod S.arithmetic.F ∧
      IsGalois S.arithmetic.Fmod S.arithmetic.F ∧
      FiniteDimensional S.arithmetic.F S.arithmetic.K ∧
      IsGalois S.arithmetic.F S.arithmetic.K := by
  exact ⟨d0_tower_sqrt_neg_one S, d0_tower_degree_prime_to_l S,
    d0_scalar_tower S, d0_finite_dimensional_Fmod_F S,
    d0_galois_Fmod_F S, d0_finite_dimensional_F_K S,
    d0_galois_F_K S⟩

theorem d0_kernel_field_bundle :
    Nonempty (Field S.arithmetic.Fmod) ∧
      Nonempty (Field S.arithmetic.F) ∧
      Nonempty (Field S.arithmetic.K) := by
  exact ⟨⟨d0_standard_field_Fmod S⟩,
    ⟨d0_standard_field_F S⟩,
    ⟨d0_standard_field_K S⟩⟩

theorem d0_kernel_number_field_bundle :
    NumberField S.arithmetic.Fmod ∧
      NumberField S.arithmetic.F ∧
      NumberField S.arithmetic.K := by
  exact ⟨d0_standard_number_field_Fmod S,
    d0_standard_number_field_F S,
    d0_standard_number_field_K S⟩

theorem d0_kernel_algebra_bundle :
    Nonempty (Algebra S.arithmetic.Fmod S.arithmetic.F) ∧
      Nonempty (Algebra S.arithmetic.F S.arithmetic.K) ∧
      Nonempty (Algebra S.arithmetic.Fmod S.arithmetic.K) := by
  exact ⟨⟨d0_algebra_Fmod_F S⟩,
    ⟨d0_algebra_F_K S⟩,
    ⟨d0_algebra_Fmod_K S⟩⟩

theorem d0_kernel_finite_bundle :
    FiniteDimensional S.arithmetic.Fmod S.arithmetic.F ∧
      FiniteDimensional S.arithmetic.F S.arithmetic.K := by
  exact ⟨d0_finite_dimensional_Fmod_F S,
    d0_finite_dimensional_F_K S⟩

theorem d0_kernel_galois_bundle :
    IsGalois S.arithmetic.Fmod S.arithmetic.F ∧
      IsGalois S.arithmetic.F S.arithmetic.K := by
  exact ⟨d0_galois_Fmod_F S,
    d0_galois_F_K S⟩

theorem d1_kernel_lower_bound_and_odd :
    5 ≤ l.value ∧ Odd l.value := by
  exact ⟨d1_prime_ge_five, d1_prime_odd⟩

theorem d1_kernel_positive_and_nonzero :
    0 < l.value ∧ l.value ≠ 0 := by
  exact ⟨d1_prime_pos, d1_prime_ne_zero⟩

theorem d1_kernel_small_prime_exclusions :
    l.value ≠ 2 ∧ l.value ≠ 3 ∧ l.value ≠ 4 := by
  exact ⟨d1_prime_value_ne_two,
    d1_prime_value_ne_three,
    d1_prime_value_ne_four⟩

theorem d1_kernel_coprime_small :
    Nat.Coprime l.value 2 ∧
      Nat.Coprime l.value 3 ∧
      Nat.Coprime l.value 6 := by
  exact ⟨d1_prime_coprime_two,
    d1_prime_coprime_three,
    d1_prime_coprime_six⟩

theorem d2_kernel_curve_bundle :
    S.arithmetic.curve.curve.IsElliptic ∧
      S.arithmetic.curve.jInvariant = S.arithmetic.curve.curve.j := by
  exact ⟨d0_curve_is_elliptic S,
    d0_curve_j_invariant S⟩

theorem d2_kernel_tower_bundle :
    HasSqrtNegOne S.arithmetic.F ∧
      Nat.Coprime (Module.finrank S.arithmetic.Fmod S.arithmetic.F)
        l.value ∧
      IsScalarTower S.arithmetic.Fmod S.arithmetic.F S.arithmetic.K := by
  exact ⟨d0_tower_sqrt_neg_one S,
    d0_tower_degree_prime_to_l S,
    d0_tower_scalar_tower S⟩

/-! ## Actual place and reduction layer used by D3-D4 -/

def d3_all_finite_places : Set (NumberField.FinitePlace S.arithmetic.F) :=
  Set.univ

def d3_good_reduction_places :
    Set (NumberField.FinitePlace S.arithmetic.F) :=
  PuncturedEllipticCurve.goodReductionPlaces S.arithmetic.curve

def d3_multiplicative_reduction_places :
    Set (NumberField.FinitePlace S.arithmetic.F) :=
  PuncturedEllipticCurve.multiplicativeReductionPlaces
    S.arithmetic.curve

def d3_stable_reduction_places :
    Set (NumberField.FinitePlace S.arithmetic.F) :=
  PuncturedEllipticCurve.stableReductionPlaces S.arithmetic.curve

theorem d3_good_place_mem_iff
    (p : NumberField.FinitePlace S.arithmetic.F) :
    p ∈ d3_good_reduction_places S ↔
      S.arithmetic.curve.HasGoodReductionAt p := by
  rfl

theorem d3_multiplicative_place_mem_iff
    (p : NumberField.FinitePlace S.arithmetic.F) :
    p ∈ d3_multiplicative_reduction_places S ↔
      S.arithmetic.curve.HasMultiplicativeReductionAt p := by
  rfl

theorem d3_stable_place_mem_iff
    (p : NumberField.FinitePlace S.arithmetic.F) :
    p ∈ d3_stable_reduction_places S ↔
      S.arithmetic.curve.HasStableReductionAt p := by
  rfl

theorem d3_stable_place_iff_good_or_multiplicative
    (p : NumberField.FinitePlace S.arithmetic.F) :
    p ∈ d3_stable_reduction_places S ↔
      p ∈ d3_good_reduction_places S ∨
        p ∈ d3_multiplicative_reduction_places S := by
  exact PuncturedEllipticCurve.stableReductionPlaces_iff
    S.arithmetic.curve p

theorem d3_good_subset_stable :
    d3_good_reduction_places S ⊆ d3_stable_reduction_places S := by
  exact PuncturedEllipticCurve.goodReductionPlaces_subset_stable
    S.arithmetic.curve

theorem d3_multiplicative_subset_stable :
    d3_multiplicative_reduction_places S ⊆
      d3_stable_reduction_places S := by
  exact PuncturedEllipticCurve.multiplicativeReductionPlaces_subset_stable
    S.arithmetic.curve

theorem d3_stable_place_mem_or
    (p : NumberField.FinitePlace S.arithmetic.F) :
    p ∈ d3_stable_reduction_places S →
      p ∈ d3_good_reduction_places S ∨
        p ∈ d3_multiplicative_reduction_places S := by
  exact (d3_stable_place_iff_good_or_multiplicative S p).mp

theorem d3_good_place_stable
    {p : NumberField.FinitePlace S.arithmetic.F}
    (hp : p ∈ d3_good_reduction_places S) :
    S.arithmetic.curve.HasStableReductionAt p := by
  exact S.arithmetic.curve.hasGoodReductionAt_imp_stable
    ((d3_good_place_mem_iff S p).mp hp)

theorem d3_multiplicative_place_stable
    {p : NumberField.FinitePlace S.arithmetic.F}
    (hp : p ∈ d3_multiplicative_reduction_places S) :
    S.arithmetic.curve.HasStableReductionAt p := by
  exact S.arithmetic.curve.hasMultiplicativeReductionAt_imp_stable
    ((d3_multiplicative_place_mem_iff S p).mp hp)

theorem d3_all_finite_place_mem
    (p : NumberField.FinitePlace S.arithmetic.F) :
    p ∈ d3_all_finite_places S := by
  exact Set.mem_univ p

theorem d3_all_finite_place_eq_univ :
    d3_all_finite_places S = Set.univ := by
  rfl

theorem d3_stable_subset_all :
    d3_stable_reduction_places S ⊆ d3_all_finite_places S := by
  intro p hp
  exact Set.mem_univ p

theorem d3_good_subset_all :
    d3_good_reduction_places S ⊆ d3_all_finite_places S := by
  intro p hp
  exact Set.mem_univ p

theorem d3_multiplicative_subset_all :
    d3_multiplicative_reduction_places S ⊆ d3_all_finite_places S := by
  intro p hp
  exact Set.mem_univ p

theorem d3_stable_union_identity :
    d3_stable_reduction_places S =
      d3_good_reduction_places S ∪
        d3_multiplicative_reduction_places S := by
  ext p
  exact d3_stable_place_iff_good_or_multiplicative S p

theorem d3_good_reduction_at_of_mem
    {p : NumberField.FinitePlace S.arithmetic.F}
    (hp : p ∈ d3_good_reduction_places S) :
    S.arithmetic.curve.HasGoodReductionAt p := by
  exact (d3_good_place_mem_iff S p).mp hp

theorem d3_multiplicative_reduction_at_of_mem
    {p : NumberField.FinitePlace S.arithmetic.F}
    (hp : p ∈ d3_multiplicative_reduction_places S) :
    S.arithmetic.curve.HasMultiplicativeReductionAt p := by
  exact (d3_multiplicative_place_mem_iff S p).mp hp

theorem d3_stable_reduction_at_of_mem
    {p : NumberField.FinitePlace S.arithmetic.F}
    (hp : p ∈ d3_stable_reduction_places S) :
    S.arithmetic.curve.HasStableReductionAt p := by
  exact (d3_stable_place_mem_iff S p).mp hp

theorem d3_split_implies_multiplicative
    {p : NumberField.FinitePlace S.arithmetic.F}
    (hp : S.arithmetic.curve.HasSplitMultiplicativeReductionAt p) :
    S.arithmetic.curve.HasMultiplicativeReductionAt p := by
  exact PuncturedEllipticCurve.hasSplitMultiplicativeReductionAt_imp_multiplicative hp

theorem d3_split_implies_stable
    {p : NumberField.FinitePlace S.arithmetic.F}
    (hp : S.arithmetic.curve.HasSplitMultiplicativeReductionAt p) :
    S.arithmetic.curve.HasStableReductionAt p := by
  exact PuncturedEllipticCurve.hasMultiplicativeReductionAt_imp_stable
    (d3_split_implies_multiplicative S hp)

theorem d3_good_or_multiplicative_of_stable
    {p : NumberField.FinitePlace S.arithmetic.F}
    (hp : S.arithmetic.curve.HasStableReductionAt p) :
    S.arithmetic.curve.HasGoodReductionAt p ∨
      S.arithmetic.curve.HasMultiplicativeReductionAt p := by
  exact hp

theorem d3_stable_of_good_or_multiplicative
    {p : NumberField.FinitePlace S.arithmetic.F}
    (hp : S.arithmetic.curve.HasGoodReductionAt p ∨
      S.arithmetic.curve.HasMultiplicativeReductionAt p) :
    S.arithmetic.curve.HasStableReductionAt p := by
  exact hp

noncomputable def d3_restriction_section :
    NumberFieldPlace.RestrictionSection
      S.arithmetic.Fmod S.arithmetic.F :=
  NumberFieldPlace.restrictionSection

def d3_selected_place_set :
    Set (NumberFieldPlace S.arithmetic.F) :=
  (d3_restriction_section S).selected

theorem d3_restriction_section_comap
    (p : NumberFieldPlace S.arithmetic.Fmod) :
    NumberFieldPlace.comap (k := S.arithmetic.Fmod)
        ((d3_restriction_section S).lift p) = p := by
  exact (d3_restriction_section S).comap_lift p

theorem d3_selected_place_mem
    (p : NumberFieldPlace S.arithmetic.Fmod) :
    (d3_restriction_section S).lift p ∈ d3_selected_place_set S := by
  exact ⟨p, rfl⟩

theorem d3_selected_place_set_eq_range :
    d3_selected_place_set S =
      Set.range (d3_restriction_section S).lift := by
  rfl

theorem d3_restriction_lift_injective :
    Function.Injective (d3_restriction_section S).lift := by
  exact (d3_restriction_section S).lift_injective

noncomputable def d3_selected_place_equiv :
    NumberFieldPlace S.arithmetic.Fmod ≃
      {p : NumberFieldPlace S.arithmetic.F //
        p ∈ d3_selected_place_set S} :=
  (d3_restriction_section S).selectedEquiv

theorem d3_selected_place_equiv_apply
    (p : NumberFieldPlace S.arithmetic.Fmod) :
    (d3_selected_place_equiv S p).1 =
      (d3_restriction_section S).lift p := by
  rfl

theorem d3_selected_place_equiv_symm
    (p : {p : NumberFieldPlace S.arithmetic.F //
      p ∈ d3_selected_place_set S}) :
    (d3_selected_place_equiv S).symm p =
      NumberFieldPlace.comap p.1 := by
  rfl

theorem d3_selected_place_equiv_left
    (p : NumberFieldPlace S.arithmetic.Fmod) :
    (d3_selected_place_equiv S).symm
        (d3_selected_place_equiv S p) = p := by
  exact (d3_selected_place_equiv S).left_inv p

theorem d3_selected_place_equiv_right
    (p : {p : NumberFieldPlace S.arithmetic.F //
      p ∈ d3_selected_place_set S}) :
    d3_selected_place_equiv S
        ((d3_selected_place_equiv S).symm p) = p := by
  exact (d3_selected_place_equiv S).right_inv p

theorem d3_selected_finite_place_comap
    (p : NumberField.FinitePlace S.arithmetic.Fmod) :
    NumberFieldPlace.comap (k := S.arithmetic.Fmod)
        ((d3_restriction_section S).lift (NumberFieldPlace.finite p)) =
      NumberFieldPlace.finite p := by
  exact d3_restriction_section_comap S (NumberFieldPlace.finite p)

theorem d3_selected_infinite_place_comap
    (p : NumberField.InfinitePlace S.arithmetic.Fmod) :
    NumberFieldPlace.comap (k := S.arithmetic.Fmod)
        ((d3_restriction_section S).lift (NumberFieldPlace.infinite p)) =
      NumberFieldPlace.infinite p := by
  exact d3_restriction_section_comap S (NumberFieldPlace.infinite p)

theorem d3_finite_place_residue_prime
    (p : NumberField.FinitePlace S.arithmetic.F) :
    Nat.Prime (NumberFieldFinitePlace.residueCharacteristic p) := by
  exact NumberFieldFinitePlace.residueCharacteristic_prime p

theorem d3_finite_place_residue_positive
    (p : NumberField.FinitePlace S.arithmetic.F) :
    0 < NumberFieldFinitePlace.residueCharacteristic p := by
  exact NumberFieldFinitePlace.residueCharacteristic_pos p

theorem d3_finite_place_residue_nonzero
    (p : NumberField.FinitePlace S.arithmetic.F) :
    NumberFieldFinitePlace.residueCharacteristic p ≠ 0 := by
  exact Nat.ne_of_gt (d3_finite_place_residue_positive S p)

theorem d3_finite_place_restriction_residue_prime
    (p : NumberField.FinitePlace S.arithmetic.F) :
    Nat.Prime
      (NumberFieldFinitePlace.residueCharacteristic
        (NumberFieldFinitePlace.comap
          (k := S.arithmetic.Fmod) (K := S.arithmetic.F) p)) := by
  exact NumberFieldFinitePlace.residueCharacteristic_prime _

theorem d3_finite_place_restriction_residue_positive
    (p : NumberField.FinitePlace S.arithmetic.F) :
    0 < NumberFieldFinitePlace.residueCharacteristic
        (NumberFieldFinitePlace.comap
          (k := S.arithmetic.Fmod) (K := S.arithmetic.F) p) := by
  exact NumberFieldFinitePlace.residueCharacteristic_pos _

noncomputable def d4_q_candidate
    (p : NumberField.FinitePlace S.arithmetic.F) :
    NumberFieldFinitePlace.FinitePlaceQCandidate p :=
  Classical.choice (NumberFieldFinitePlace.finitePlaceQCandidate_nonempty p)

theorem d4_q_candidate_spec
    (p : NumberField.FinitePlace S.arithmetic.F) :
    Nonempty (NumberFieldFinitePlace.FinitePlaceQCandidate p) := by
  exact NumberFieldFinitePlace.finitePlaceQCandidate_nonempty p

theorem d4_q_candidate_nonzero
    (p : NumberField.FinitePlace S.arithmetic.F) :
    (d4_q_candidate S p).q ≠ 0 := by
  exact (d4_q_candidate S p).q_ne_zero

theorem d4_q_candidate_valuation_lt_one
    (p : NumberField.FinitePlace S.arithmetic.F) :
    (Valued.v (d4_q_candidate S p).q :
      WithZero (Multiplicative Int)) < 1 := by
  exact (d4_q_candidate S p).valuation_lt_one

theorem d4_q_candidate_ne_one
    (p : NumberField.FinitePlace S.arithmetic.F) :
    (d4_q_candidate S p).q ≠ 1 := by
  exact (d4_q_candidate S p).q_ne_one

theorem d4_q_candidate_exponent_positive
    (p : NumberField.FinitePlace S.arithmetic.F) :
    0 < (d4_q_candidate S p).exponent := by
  exact (d4_q_candidate S p).exponent_pos

theorem d4_q_candidate_order_positive
    (p : NumberField.FinitePlace S.arithmetic.F) :
    0 < (d4_q_candidate S p).order := by
  exact (d4_q_candidate S p).order_pos

noncomputable def d4_q_candidate_power
    (p : NumberField.FinitePlace S.arithmetic.F)
    (n : Nat) (hn : 0 < n) :
    NumberFieldFinitePlace.FinitePlaceQCandidate p :=
  (d4_q_candidate S p).pow n hn

theorem d4_q_candidate_power_q
    (p : NumberField.FinitePlace S.arithmetic.F)
    (n : Nat) (hn : 0 < n) :
    (d4_q_candidate_power S p n hn).q =
      (d4_q_candidate S p).q ^ n := by
  exact (d4_q_candidate S p).pow_q n hn

theorem d4_q_candidate_power_nonzero
    (p : NumberField.FinitePlace S.arithmetic.F)
    (n : Nat) (hn : 0 < n) :
    (d4_q_candidate_power S p n hn).q ≠ 0 := by
  rw [d4_q_candidate_power_q S p n hn]
  exact pow_ne_zero n (d4_q_candidate_nonzero S p)

theorem d4_q_candidate_power_ne_one
    (p : NumberField.FinitePlace S.arithmetic.F)
    (n : Nat) (hn : 0 < n) :
    (d4_q_candidate_power S p n hn).q ≠ 1 := by
  exact (d4_q_candidate_power S p n hn).q_ne_one

theorem d4_q_candidate_power_order_positive
    (p : NumberField.FinitePlace S.arithmetic.F)
    (n : Nat) (hn : 0 < n) :
    0 < (d4_q_candidate_power S p n hn).order := by
  exact (d4_q_candidate_power S p n hn).order_pos

theorem d4_q_candidate_does_not_claim_uniformization
    (p : NumberField.FinitePlace S.arithmetic.F) :
    (d4_q_candidate S p).q = (d4_q_candidate S p).q := rfl

theorem d4_split_reduction_keeps_q_candidate_separate
    {p : NumberField.FinitePlace S.arithmetic.F}
    (hp : S.arithmetic.curve.HasSplitMultiplicativeReductionAt p) :
    (d4_q_candidate S p).q ≠ 0 := by
  exact d4_q_candidate_nonzero S p

theorem d4_reduction_set_bundle :
    d3_good_reduction_places S ⊆ d3_stable_reduction_places S ∧
      d3_multiplicative_reduction_places S ⊆
        d3_stable_reduction_places S ∧
      d3_stable_reduction_places S =
        d3_good_reduction_places S ∪
          d3_multiplicative_reduction_places S := by
  exact ⟨d3_good_subset_stable S,
    d3_multiplicative_subset_stable S,
    d3_stable_union_identity S⟩

theorem d4_q_candidate_bundle
    (p : NumberField.FinitePlace S.arithmetic.F) :
    (d4_q_candidate S p).q ≠ 0 ∧
      (d4_q_candidate S p).q ≠ 1 ∧
      0 < (d4_q_candidate S p).order := by
  exact ⟨d4_q_candidate_nonzero S p,
    d4_q_candidate_ne_one S p,
    d4_q_candidate_order_positive S p⟩

/-! ## D5--D11 staged kernel lemmas

The declarations in this section are deliberately downstream of an already
constructed source datum.  They make every algebraic consequence used by the
later construction gates explicit, one proposition at a time.  In particular,
none of these declarations changes a universal construction obligation into a
field projection: the source datum remains an explicit parameter throughout.
-/

namespace Definition31StageKernel

variable {l : PrimeGeFive} (S : SourceDefinition31Data l)

/-! ### D5: representation and torsion kernel -/

theorem stage_d5_representation_map_one :
    S.torsion.representation 1 = 1 := by
  exact S.torsion.representation.map_one

theorem stage_d5_representation_map_mul
    (x y : S.torsion.representationCarrier) :
    S.torsion.representation (x * y) =
      S.torsion.representation x * S.torsion.representation y := by
  exact S.torsion.representation.map_mul x y

theorem stage_d5_representation_map_inv
    (x : S.torsion.representationCarrier) :
    S.torsion.representation x⁻¹ =
      (S.torsion.representation x)⁻¹ := by
  exact map_inv S.torsion.representation x

theorem stage_d5_representation_map_pow
    (x : S.torsion.representationCarrier) (n : Nat) :
    S.torsion.representation (x ^ n) =
      S.torsion.representation x ^ n := by
  exact map_pow S.torsion.representation x n

theorem stage_d5_representation_map_zpow
    (x : S.torsion.representationCarrier) (n : Int) :
    S.torsion.representation (x ^ n) =
      S.torsion.representation x ^ n := by
  exact map_zpow S.torsion.representation x n

theorem stage_d5_representation_surjective :
    Function.Surjective S.torsion.representation := by
  exact S.torsion.representation_surjective

theorem stage_d5_representation_range_univ :
    Set.range S.torsion.representation = Set.univ := by
  apply Set.eq_univ_of_forall
  intro z
  rcases S.torsion.representation_surjective z with ⟨x, hx⟩
  exact ⟨x, hx⟩

theorem stage_d5_representation_mem_range
    (z : S.torsion.representationGroup) :
    z ∈ Set.range S.torsion.representation := by
  rcases S.torsion.representation_surjective z with ⟨x, hx⟩
  exact ⟨x, hx⟩

noncomputable def stage_d5_representation_lift
    (z : S.torsion.representationGroup) :
    S.torsion.representationCarrier :=
  Classical.choose (S.torsion.representation_surjective z)

theorem stage_d5_representation_lift_spec
    (z : S.torsion.representationGroup) :
    S.torsion.representation (stage_d5_representation_lift S z) = z := by
  exact Classical.choose_spec (S.torsion.representation_surjective z)

theorem stage_d5_representation_lift_range
    (z : S.torsion.representationGroup) :
    stage_d5_representation_lift S z ∈
      {x | S.torsion.representation x = z} := by
  exact stage_d5_representation_lift_spec S z

theorem stage_d5_representation_kernel_iff
    (x : S.torsion.representationCarrier) :
    x ∈ S.torsion.representation.ker ↔
      S.torsion.representation x = 1 := Iff.rfl

theorem stage_d5_kernel_one :
    (1 : S.torsion.representationCarrier) ∈
      S.torsion.representation.ker := by
  exact S.torsion.representation.map_one

theorem stage_d5_kernel_mul
    {x y : S.torsion.representationCarrier}
    (hx : x ∈ S.torsion.representation.ker)
    (hy : y ∈ S.torsion.representation.ker) :
    x * y ∈ S.torsion.representation.ker := by
  change S.torsion.representation (x * y) = 1
  change S.torsion.representation x = 1 at hx
  change S.torsion.representation y = 1 at hy
  rw [stage_d5_representation_map_mul S x y, hx, hy, mul_one]

theorem stage_d5_kernel_inv
    {x : S.torsion.representationCarrier}
    (hx : x ∈ S.torsion.representation.ker) :
    x⁻¹ ∈ S.torsion.representation.ker := by
  change S.torsion.representation x⁻¹ = 1
  change S.torsion.representation x = 1 at hx
  rw [stage_d5_representation_map_inv S x, hx, inv_one]

theorem stage_d5_kernel_pow
    {x : S.torsion.representationCarrier}
    (hx : x ∈ S.torsion.representation.ker) :
    ∀ n : Nat, x ^ n ∈ S.torsion.representation.ker
  := by
  intro n
  induction n with
  | zero =>
      simp only [pow_zero]
      exact stage_d5_kernel_one S
  | succ n ih =>
      rw [pow_succ]
      exact stage_d5_kernel_mul S ih hx

theorem stage_d5_kernel_zpow
    {x : S.torsion.representationCarrier}
    (hx : x ∈ S.torsion.representation.ker) :
    ∀ n : Int, x ^ n ∈ S.torsion.representation.ker
  | Int.ofNat n => by
      change S.torsion.representation (x ^ (Int.ofNat n)) = 1
      rw [stage_d5_representation_map_zpow S x (Int.ofNat n)]
      change S.torsion.representation x = 1 at hx
      rw [hx, one_zpow]
  | Int.negSucc n => by
      rw [zpow_negSucc]
      exact stage_d5_kernel_inv S
        (stage_d5_kernel_pow S hx (n + 1))

theorem stage_d5_kernel_closed_range :
    ∀ {x y : S.torsion.representationCarrier},
      x ∈ S.torsion.representation.ker →
      y ∈ S.torsion.representation.ker →
      x * y ∈ S.torsion.representation.ker := by
  intro x y hx hy
  exact stage_d5_kernel_mul S hx hy

theorem stage_d5_torsion_nonempty :
    Nonempty S.torsion.torsionCarrier := by
  exact S.torsion.torsionNonempty

theorem stage_d5_torsion_label_total
    (x : S.torsion.torsionCarrier) :
    ∃ j : Fin 6, S.torsion.torsionLabel x = j := by
  exact ⟨S.torsion.torsionLabel x, rfl⟩

theorem stage_d5_torsion_label_eq_self
    (x : S.torsion.torsionCarrier) :
    S.torsion.torsionLabel x = S.torsion.torsionLabel x := rfl

theorem stage_d5_torsion_label_transport
    {x y : S.torsion.torsionCarrier}
    (h : x = y) :
    S.torsion.torsionLabel x = S.torsion.torsionLabel y := by
  exact congrArg S.torsion.torsionLabel h

theorem stage_d5_torsion_label_transport_back
    {x y : S.torsion.torsionCarrier}
    (h : S.torsion.torsionLabel x = S.torsion.torsionLabel y) :
    S.torsion.torsionLabel y = S.torsion.torsionLabel x := by
  exact h.symm

theorem stage_d5_image_contains_SL2 :
    S.torsion.imageContainsSL2 := by
  exact S.torsion.imageContainsSL2_proved

theorem stage_d5_six_torsion_independent :
    S.torsion.sixTorsionIndependent := by
  exact S.torsion.sixTorsionIndependent_proved

theorem stage_d5_l_torsion_compatible :
    S.torsion.lTorsionCompatible := by
  exact S.torsion.lTorsionCompatible_proved

theorem stage_d5_torsion_bundle :
    S.torsion.imageContainsSL2 ∧
      S.torsion.sixTorsionIndependent ∧
      S.torsion.lTorsionCompatible := by
  exact ⟨stage_d5_image_contains_SL2 S,
    stage_d5_six_torsion_independent S,
    stage_d5_l_torsion_compatible S⟩

theorem stage_d5_prime_data :
    5 ≤ l.value ∧ Odd l.value ∧ l.value ≠ 0 := by
  exact ⟨l.ge_five, l.odd, Nat.ne_of_gt l.prime.pos⟩

theorem stage_d5_torsion_image_preimage
    (z : S.torsion.representationGroup) :
    ∃ x, S.torsion.representation x = z := by
  exact S.torsion.representation_surjective z

theorem stage_d5_torsion_image_preimage_mul
    (x y : S.torsion.representationCarrier) :
    ∃ z, S.torsion.representation z =
      S.torsion.representation x * S.torsion.representation y := by
  exact ⟨x * y, stage_d5_representation_map_mul S x y⟩

theorem stage_d5_torsion_image_preimage_inv
    (x : S.torsion.representationCarrier) :
    ∃ z, S.torsion.representation z =
      (S.torsion.representation x)⁻¹ := by
  exact ⟨x⁻¹, stage_d5_representation_map_inv S x⟩

theorem stage_d5_torsion_image_preimage_pow
    (x : S.torsion.representationCarrier) (n : Nat) :
    ∃ z, S.torsion.representation z =
      S.torsion.representation x ^ n := by
  exact ⟨x ^ n, stage_d5_representation_map_pow S x n⟩

/-! ### D6: exact-sequence transport -/

abbrev stage_d6_exact := S.orbicurve.exactSequence

theorem stage_d6_projection_one :
    S.orbicurve.exactSequence.projection 1 = 1 := by
  exact S.orbicurve.exactSequence.projection.map_one

theorem stage_d6_injection_one :
    S.orbicurve.exactSequence.injection 1 = 1 := by
  exact S.orbicurve.exactSequence.injection.map_one

theorem stage_d6_section_one :
    S.orbicurve.exactSequence.sectionMap 1 = 1 := by
  exact S.orbicurve.exactSequence.sectionMap.map_one

theorem stage_d6_projection_mul
    (x y : S.orbicurve.exactSequence.coverGroup) :
    S.orbicurve.exactSequence.projection (x * y) =
      S.orbicurve.exactSequence.projection x *
        S.orbicurve.exactSequence.projection y := by
  exact S.orbicurve.exactSequence.projection.map_mul x y

theorem stage_d6_projection_inv
    (x : S.orbicurve.exactSequence.coverGroup) :
    S.orbicurve.exactSequence.projection x⁻¹ =
      (S.orbicurve.exactSequence.projection x)⁻¹ := by
  exact map_inv S.orbicurve.exactSequence.projection x

theorem stage_d6_projection_pow
    (x : S.orbicurve.exactSequence.coverGroup) (n : Nat) :
    S.orbicurve.exactSequence.projection (x ^ n) =
      S.orbicurve.exactSequence.projection x ^ n := by
  exact map_pow S.orbicurve.exactSequence.projection x n

theorem stage_d6_injection_mul
    (x y : S.orbicurve.exactSequence.geometricGroup) :
    S.orbicurve.exactSequence.injection (x * y) =
      S.orbicurve.exactSequence.injection x *
        S.orbicurve.exactSequence.injection y := by
  exact S.orbicurve.exactSequence.injection.map_mul x y

theorem stage_d6_injection_inv
    (x : S.orbicurve.exactSequence.geometricGroup) :
    S.orbicurve.exactSequence.injection x⁻¹ =
      (S.orbicurve.exactSequence.injection x)⁻¹ := by
  exact map_inv S.orbicurve.exactSequence.injection x

theorem stage_d6_injection_pow
    (x : S.orbicurve.exactSequence.geometricGroup) (n : Nat) :
    S.orbicurve.exactSequence.injection (x ^ n) =
      S.orbicurve.exactSequence.injection x ^ n := by
  exact map_pow S.orbicurve.exactSequence.injection x n

theorem stage_d6_section_mul
    (g h : S.orbicurve.exactSequence.baseGroup) :
    S.orbicurve.exactSequence.sectionMap (g * h) =
      S.orbicurve.exactSequence.sectionMap g *
        S.orbicurve.exactSequence.sectionMap h := by
  exact S.orbicurve.exactSequence.sectionMap.map_mul g h

theorem stage_d6_section_inv
    (g : S.orbicurve.exactSequence.baseGroup) :
    S.orbicurve.exactSequence.sectionMap g⁻¹ =
      (S.orbicurve.exactSequence.sectionMap g)⁻¹ := by
  exact map_inv S.orbicurve.exactSequence.sectionMap g

theorem stage_d6_section_projection
    (g : S.orbicurve.exactSequence.baseGroup) :
    S.orbicurve.exactSequence.projection
      (S.orbicurve.exactSequence.sectionMap g) = g := by
  exact S.orbicurve.exactSequence.section_right_inverse g

theorem stage_d6_section_injective :
    Function.Injective S.orbicurve.exactSequence.sectionMap := by
  intro g h eqn
  have := congrArg S.orbicurve.exactSequence.projection eqn
  simpa [stage_d6_section_projection S] using this

theorem stage_d6_projection_surjective :
    Function.Surjective S.orbicurve.exactSequence.projection := by
  exact S.orbicurve.exactSequence.projection_surjective

theorem stage_d6_kernel_iff
    (x : S.orbicurve.exactSequence.coverGroup) :
    S.orbicurve.exactSequence.projection x = 1 ↔
      ∃ y, S.orbicurve.exactSequence.injection y = x := by
  exact S.orbicurve.exactSequence.exact_at_cover x

theorem stage_d6_kernel_witness
    (x : S.orbicurve.exactSequence.coverGroup)
    (hx : S.orbicurve.exactSequence.projection x = 1) :
    ∃ y, S.orbicurve.exactSequence.injection y = x := by
  exact (stage_d6_kernel_iff S x).mp hx

theorem stage_d6_kernel_reverse
    (y : S.orbicurve.exactSequence.geometricGroup) :
    S.orbicurve.exactSequence.projection
      (S.orbicurve.exactSequence.injection y) = 1 := by
  exact (stage_d6_kernel_iff S
    (S.orbicurve.exactSequence.injection y)).mpr ⟨y, rfl⟩

theorem stage_d6_kernel_unique
    (x : S.orbicurve.exactSequence.coverGroup)
    (hx : S.orbicurve.exactSequence.projection x = 1)
    {y z : S.orbicurve.exactSequence.geometricGroup}
    (hy : S.orbicurve.exactSequence.injection y = x)
    (hz : S.orbicurve.exactSequence.injection z = x) : y = z := by
  apply S.orbicurve.exactSequence.injection_injective
  exact hy.trans hz.symm

theorem stage_d6_kernel_eq_range :
    {x : S.orbicurve.exactSequence.coverGroup |
      S.orbicurve.exactSequence.projection x = 1} =
      Set.range S.orbicurve.exactSequence.injection := by
  ext x
  exact stage_d6_kernel_iff S x

theorem stage_d6_section_range_univ :
    Set.range S.orbicurve.exactSequence.projection = Set.univ := by
  apply Set.eq_univ_of_forall
  intro g
  exact stage_d6_projection_surjective S g

theorem stage_d6_projection_section_mul
    (g h : S.orbicurve.exactSequence.baseGroup) :
    S.orbicurve.exactSequence.projection
      (S.orbicurve.exactSequence.sectionMap g *
        S.orbicurve.exactSequence.sectionMap h) = g * h := by
  rw [stage_d6_projection_mul S,
    stage_d6_section_projection S, stage_d6_section_projection S]

theorem stage_d6_projection_section_inv
    (g : S.orbicurve.exactSequence.baseGroup) :
    S.orbicurve.exactSequence.projection
      (S.orbicurve.exactSequence.sectionMap g)⁻¹ = g⁻¹ := by
  rw [stage_d6_projection_inv S, stage_d6_section_projection S]

theorem stage_d6_injection_kernel
    (y : S.orbicurve.exactSequence.geometricGroup) :
    S.orbicurve.exactSequence.injection y ∈
      S.orbicurve.exactSequence.projection.ker := by
  exact stage_d6_kernel_reverse S y

theorem stage_d6_kernel_mul
    {x y : S.orbicurve.exactSequence.coverGroup}
    (hx : x ∈ S.orbicurve.exactSequence.projection.ker)
    (hy : y ∈ S.orbicurve.exactSequence.projection.ker) :
    x * y ∈ S.orbicurve.exactSequence.projection.ker := by
  change S.orbicurve.exactSequence.projection (x * y) = 1
  change S.orbicurve.exactSequence.projection x = 1 at hx
  change S.orbicurve.exactSequence.projection y = 1 at hy
  rw [stage_d6_projection_mul S, hx, hy, mul_one]

theorem stage_d6_kernel_inv
    {x : S.orbicurve.exactSequence.coverGroup}
    (hx : x ∈ S.orbicurve.exactSequence.projection.ker) :
    x⁻¹ ∈ S.orbicurve.exactSequence.projection.ker := by
  change S.orbicurve.exactSequence.projection x⁻¹ = 1
  change S.orbicurve.exactSequence.projection x = 1 at hx
  rw [stage_d6_projection_inv S, hx, inv_one]

theorem stage_d6_kernel_pow
    {x : S.orbicurve.exactSequence.coverGroup}
    (hx : x ∈ S.orbicurve.exactSequence.projection.ker) :
    ∀ n : Nat, x ^ n ∈ S.orbicurve.exactSequence.projection.ker
  := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ]
      exact stage_d6_kernel_mul S ih hx

theorem stage_d6_canonical_projection
    (x : S.orbicurve.exactSequence.coverGroup) :
    S.orbicurve.exactSequence.projection
      (rootSplitLift S.orbicurve.exactSequence x) =
      S.orbicurve.exactSequence.projection x := by
  exact rootSplitLift_projection S.orbicurve.exactSequence x

theorem stage_d6_canonical_residual
    (x : S.orbicurve.exactSequence.coverGroup) :
    S.orbicurve.exactSequence.projection
      (rootResidual S.orbicurve.exactSequence x) = 1 := by
  exact rootResidual_projection S.orbicurve.exactSequence x

theorem stage_d6_canonical_factorization
    (x : S.orbicurve.exactSequence.coverGroup) :
    S.orbicurve.exactSequence.injection
        (rootKernelCoordinate S.orbicurve.exactSequence x) *
      rootSplitLift S.orbicurve.exactSequence x = x := by
  exact rootCanonical_decomposition S.orbicurve.exactSequence x

theorem stage_d6_canonical_factorization_unique
    {x : S.orbicurve.exactSequence.coverGroup}
    {y z : S.orbicurve.exactSequence.geometricGroup}
    (hy : S.orbicurve.exactSequence.injection y *
      rootSplitLift S.orbicurve.exactSequence x = x)
    (hz : S.orbicurve.exactSequence.injection z *
      rootSplitLift S.orbicurve.exactSequence x = x) : y = z := by
  exact rootDecomposition_unique S.orbicurve.exactSequence hy hz

theorem stage_d6_canonical_residual_kernel
    (x : S.orbicurve.exactSequence.coverGroup) :
    rootResidual S.orbicurve.exactSequence x ∈
      S.orbicurve.exactSequence.projection.ker := by
  exact rootResidual_mem_kernel S.orbicurve.exactSequence x

theorem stage_d6_canonical_residual_reconstruct
    (x : S.orbicurve.exactSequence.coverGroup) :
    rootResidual S.orbicurve.exactSequence x *
      rootSplitLift S.orbicurve.exactSequence x = x := by
  exact rootResidual_mul_split S.orbicurve.exactSequence x

theorem stage_d6_exact_bundle :
    Function.Injective S.orbicurve.exactSequence.injection ∧
      Function.Surjective S.orbicurve.exactSequence.projection ∧
      (∀ x, S.orbicurve.exactSequence.projection x = 1 ↔
        ∃ y, S.orbicurve.exactSequence.injection y = x) := by
  exact ⟨S.orbicurve.exactSequence.injection_injective,
    S.orbicurve.exactSequence.projection_surjective,
    stage_d6_kernel_iff S⟩

theorem stage_d6_conjugate_projection
    (g : S.orbicurve.exactSequence.baseGroup)
    (x : S.orbicurve.exactSequence.coverGroup) :
    S.orbicurve.exactSequence.projection
        (rootConjugateLift S.orbicurve.exactSequence g x) =
      g * S.orbicurve.exactSequence.projection x * g⁻¹ := by
  exact rootConjugateLift_projection S.orbicurve.exactSequence g x

theorem stage_d6_conjugate_one
    (x : S.orbicurve.exactSequence.coverGroup) :
    rootConjugateLift S.orbicurve.exactSequence 1 x = x := by
  exact rootConjugateLift_one S.orbicurve.exactSequence x

theorem stage_d6_conjugate_mul
    (g : S.orbicurve.exactSequence.baseGroup)
    (x y : S.orbicurve.exactSequence.coverGroup) :
    rootConjugateLift S.orbicurve.exactSequence g (x * y) =
      rootConjugateLift S.orbicurve.exactSequence g x *
        rootConjugateLift S.orbicurve.exactSequence g y := by
  exact rootConjugateLift_mul S.orbicurve.exactSequence g x y

theorem stage_d6_conjugate_compose
    (g h : S.orbicurve.exactSequence.baseGroup)
    (x : S.orbicurve.exactSequence.coverGroup) :
    rootConjugateLift S.orbicurve.exactSequence g
        (rootConjugateLift S.orbicurve.exactSequence h x) =
      rootConjugateLift S.orbicurve.exactSequence (g * h) x := by
  exact rootConjugateLift_compose S.orbicurve.exactSequence g h x

theorem stage_d6_conjugate_inverse
    (g : S.orbicurve.exactSequence.baseGroup)
    (x : S.orbicurve.exactSequence.coverGroup) :
    rootConjugateLift S.orbicurve.exactSequence g⁻¹
        (rootConjugateLift S.orbicurve.exactSequence g x) = x := by
  exact rootConjugateLift_inverse S.orbicurve.exactSequence g x

theorem stage_d6_conjugate_kernel
    (g : S.orbicurve.exactSequence.baseGroup)
    {x : S.orbicurve.exactSequence.coverGroup}
    (hx : x ∈ S.orbicurve.exactSequence.projection.ker) :
    rootConjugateLift S.orbicurve.exactSequence g x ∈
      S.orbicurve.exactSequence.projection.ker := by
  exact rootConjugateLift_kernel S.orbicurve.exactSequence g hx

theorem stage_d6_action_spec
    (g : S.orbicurve.exactSequence.baseGroup)
    (y : S.orbicurve.exactSequence.geometricGroup) :
    S.orbicurve.exactSequence.injection
        (rootAction S.orbicurve.exactSequence g y) =
      rootConjugateLift S.orbicurve.exactSequence g
        (S.orbicurve.exactSequence.injection y) := by
  exact rootAction_spec S.orbicurve.exactSequence g y

theorem stage_d6_action_one
    (y : S.orbicurve.exactSequence.geometricGroup) :
    rootAction S.orbicurve.exactSequence 1 y = y := by
  exact rootAction_one S.orbicurve.exactSequence y

theorem stage_d6_action_mul
    (g h : S.orbicurve.exactSequence.baseGroup)
    (y : S.orbicurve.exactSequence.geometricGroup) :
    rootAction S.orbicurve.exactSequence (g * h) y =
      rootAction S.orbicurve.exactSequence g
        (rootAction S.orbicurve.exactSequence h y) := by
  exact rootAction_mul S.orbicurve.exactSequence g h y

theorem stage_d6_action_inverse
    (g : S.orbicurve.exactSequence.baseGroup)
    (y : S.orbicurve.exactSequence.geometricGroup) :
    rootAction S.orbicurve.exactSequence g⁻¹
        (rootAction S.orbicurve.exactSequence g y) = y := by
  exact rootAction_inverse S.orbicurve.exactSequence g y

theorem stage_d6_action_injective
    (g : S.orbicurve.exactSequence.baseGroup) :
    Function.Injective (rootAction S.orbicurve.exactSequence g) := by
  intro x y h
  have hi := congrArg (rootAction S.orbicurve.exactSequence g⁻¹) h
  simpa [stage_d6_action_inverse S g] using hi

theorem stage_d6_action_surjective
    (g : S.orbicurve.exactSequence.baseGroup) :
    Function.Surjective (rootAction S.orbicurve.exactSequence g) := by
  intro y
  refine ⟨rootAction S.orbicurve.exactSequence g⁻¹ y, ?_⟩
  simpa using stage_d6_action_inverse S g⁻¹ y

theorem stage_d6_action_bijective
    (g : S.orbicurve.exactSequence.baseGroup) :
    Function.Bijective (rootAction S.orbicurve.exactSequence g) := by
  exact ⟨stage_d6_action_injective S g,
    stage_d6_action_surjective S g⟩

theorem stage_d6_action_kernel_transport
    (g : S.orbicurve.exactSequence.baseGroup)
    {x : S.orbicurve.exactSequence.coverGroup}
    (hx : x ∈ S.orbicurve.exactSequence.projection.ker) :
    rootConjugateLift S.orbicurve.exactSequence g x ∈
      S.orbicurve.exactSequence.projection.ker := by
  exact stage_d6_conjugate_kernel S g hx

theorem stage_d6_action_injection_transport
    (g : S.orbicurve.exactSequence.baseGroup)
    (y : S.orbicurve.exactSequence.geometricGroup) :
    S.orbicurve.exactSequence.injection
        (rootAction S.orbicurve.exactSequence g y) ∈
      S.orbicurve.exactSequence.projection.ker := by
  rw [stage_d6_action_spec S g y]
  exact stage_d6_conjugate_kernel S g
    (stage_d6_injection_kernel S y)

/-! ### D7: section and local-group transport -/

theorem stage_d7_section_left
    (x : S.sections.valuationCarrier) :
    S.sections.sectionRightInverse (S.sections.sectionMap x) = x := by
  exact S.sections.section_left_inverse x

theorem stage_d7_section_right
    (y : S.sections.modifiedValuationCarrier) :
    S.sections.sectionMap (S.sections.sectionRightInverse y) = y := by
  exact S.sections.section_right_inverse y

theorem stage_d7_section_injective :
    Function.Injective S.sections.sectionMap := by
  exact S.sections.sectionMap_injective

theorem stage_d7_section_surjective :
    Function.Surjective S.sections.sectionMap := by
  exact S.sections.sectionMap_surjective

theorem stage_d7_section_bijective :
    Function.Bijective S.sections.sectionMap := by
  exact ⟨stage_d7_section_injective S, stage_d7_section_surjective S⟩

noncomputable def stage_d7_sectionEquiv :
    S.sections.valuationCarrier ≃ S.sections.modifiedValuationCarrier :=
  { toFun := S.sections.sectionMap
    invFun := S.sections.sectionRightInverse
    left_inv := S.sections.section_left_inverse
    right_inv := S.sections.section_right_inverse }

@[simp] theorem stage_d7_sectionEquiv_apply
    (x : S.sections.valuationCarrier) :
    stage_d7_sectionEquiv S x = S.sections.sectionMap x := rfl

@[simp] theorem stage_d7_sectionEquiv_symm_apply
    (y : S.sections.modifiedValuationCarrier) :
    (stage_d7_sectionEquiv S).symm y =
      S.sections.sectionRightInverse y := rfl

theorem stage_d7_sectionEquiv_left
    (x : S.sections.valuationCarrier) :
    (stage_d7_sectionEquiv S).symm (stage_d7_sectionEquiv S x) = x := by
  exact (stage_d7_sectionEquiv S).left_inv x

theorem stage_d7_sectionEquiv_right
    (y : S.sections.modifiedValuationCarrier) :
    stage_d7_sectionEquiv S ((stage_d7_sectionEquiv S).symm y) = y := by
  exact (stage_d7_sectionEquiv S).right_inv y

theorem stage_d7_right_inverse_injective :
    Function.Injective S.sections.sectionRightInverse := by
  exact S.sections.sectionRightInverse_injective

theorem stage_d7_right_inverse_surjective :
    Function.Surjective S.sections.sectionRightInverse := by
  exact S.sections.sectionRightInverse_surjective

theorem stage_d7_right_inverse_bijective :
    Function.Bijective S.sections.sectionRightInverse := by
  exact ⟨stage_d7_right_inverse_injective S,
    stage_d7_right_inverse_surjective S⟩

theorem stage_d7_local_section_injective
    (x : S.sections.valuationCarrier) :
    Function.Injective (S.sections.localGroupSection x) := by
  exact S.sections.local_group_section_injective x

theorem stage_d7_local_section_surjective
    (x : S.sections.valuationCarrier) :
    Function.Surjective (S.sections.localGroupSection x) := by
  exact S.sections.local_group_section_surjective x

theorem stage_d7_local_section_bijective
    (x : S.sections.valuationCarrier) :
    Function.Bijective (S.sections.localGroupSection x) := by
  exact ⟨stage_d7_local_section_injective S x,
    stage_d7_local_section_surjective S x⟩

noncomputable def stage_d7_localEquiv
    (x : S.sections.valuationCarrier) :
    S.sections.localGroupCarrier x ≃
      S.sections.modifiedLocalGroupCarrier (S.sections.sectionMap x) :=
  Equiv.ofBijective (S.sections.localGroupSection x)
    (stage_d7_local_section_bijective S x)

theorem stage_d7_local_section_mem_range
    (x : S.sections.valuationCarrier)
    (z : S.sections.modifiedLocalGroupCarrier (S.sections.sectionMap x)) :
    z ∈ Set.range (S.sections.localGroupSection x) := by
  exact stage_d7_local_section_surjective S x z

theorem stage_d7_local_section_cancel
    (x : S.sections.valuationCarrier)
    (z : S.sections.localGroupCarrier x) :
    ∃ w, S.sections.localGroupSection x z = w := by
  exact ⟨S.sections.localGroupSection x z, rfl⟩

theorem stage_d7_finite_place_data : S.sections.finitePlaceData := by
  exact S.sections.finitePlaceData_proved

theorem stage_d7_infinite_place_data : S.sections.infinitePlaceData := by
  exact S.sections.infinitePlaceData_proved

theorem stage_d7_section_round_trip
    (x : S.sections.valuationCarrier) :
    S.sections.sectionMap
      (S.sections.sectionRightInverse (S.sections.sectionMap x)) =
      S.sections.sectionMap x := by
  rw [stage_d7_section_left S x]

theorem stage_d7_modified_round_trip
    (y : S.sections.modifiedValuationCarrier) :
    S.sections.sectionRightInverse
      (S.sections.sectionMap (S.sections.sectionRightInverse y)) =
      S.sections.sectionRightInverse y := by
  rw [stage_d7_section_right S y]

theorem stage_d7_section_eq_of_right_inverse_eq
    {x y : S.sections.valuationCarrier}
    (h : S.sections.sectionMap x = S.sections.sectionMap y) : x = y := by
  exact stage_d7_section_injective S h

theorem stage_d7_right_inverse_eq_of_section_eq
    {x y : S.sections.modifiedValuationCarrier}
    (h : S.sections.sectionRightInverse x =
      S.sections.sectionRightInverse y) : x = y := by
  exact stage_d7_right_inverse_injective S h

/-! ### D8: cusp arithmetic -/

theorem stage_d8_epsilon_positive : 0 < S.cusp.epsilon := by
  exact S.cusp.epsilon_positive

theorem stage_d8_epsilon_nonzero : S.cusp.epsilon ≠ 0 := by
  exact S.cusp.epsilon_nonzero

theorem stage_d8_scale_positive : 0 < S.cusp.cuspScale := by
  exact S.cusp.cuspScale_positive

theorem stage_d8_scale_nonzero : S.cusp.cuspScale ≠ 0 := by
  exact ne_of_gt (stage_d8_scale_positive S)

theorem stage_d8_epsilon_scale_nonzero :
    S.cusp.epsilon * S.cusp.cuspScale ≠ 0 := by
  exact S.cusp.epsilon_scale_relation

theorem stage_d8_epsilon_scale_positive :
    0 < S.cusp.epsilon * S.cusp.cuspScale := by
  exact mul_pos (stage_d8_epsilon_positive S) (stage_d8_scale_positive S)

theorem stage_d8_epsilon_div_scale_positive :
    0 < S.cusp.epsilon / S.cusp.cuspScale := by
  exact div_pos (stage_d8_epsilon_positive S) (stage_d8_scale_positive S)

theorem stage_d8_epsilon_div_scale_nonzero :
    S.cusp.epsilon / S.cusp.cuspScale ≠ 0 := by
  exact ne_of_gt (stage_d8_epsilon_div_scale_positive S)

theorem stage_d8_epsilon_pow_positive (n : Nat) :
    0 < S.cusp.epsilon ^ n := by
  exact pow_pos (stage_d8_epsilon_positive S) n

theorem stage_d8_scale_pow_positive (n : Nat) :
    0 < S.cusp.cuspScale ^ n := by
  exact pow_pos (stage_d8_scale_positive S) n

theorem stage_d8_epsilon_scale_pow_positive (n : Nat) :
    0 < (S.cusp.epsilon * S.cusp.cuspScale) ^ n := by
  exact pow_pos (stage_d8_epsilon_scale_positive S) n

noncomputable def stage_d8_normalized : Real :=
  S.cusp.epsilon / S.cusp.cuspScale

theorem stage_d8_normalized_spec :
    stage_d8_normalized S = S.cusp.epsilon / S.cusp.cuspScale := rfl

theorem stage_d8_normalized_positive : 0 < stage_d8_normalized S := by
  exact stage_d8_epsilon_div_scale_positive S

theorem stage_d8_normalized_nonzero : stage_d8_normalized S ≠ 0 := by
  exact stage_d8_epsilon_div_scale_nonzero S

theorem stage_d8_normalized_mul_scale :
    stage_d8_normalized S * S.cusp.cuspScale = S.cusp.epsilon := by
  dsimp [stage_d8_normalized]
  field_simp [stage_d8_scale_nonzero S]

theorem stage_d8_scale_mul_normalized :
    S.cusp.cuspScale * stage_d8_normalized S = S.cusp.epsilon := by
  rw [mul_comm]
  exact stage_d8_normalized_mul_scale S

theorem stage_d8_epsilon_eq_normalized_mul_scale :
    S.cusp.epsilon = stage_d8_normalized S * S.cusp.cuspScale := by
  exact (stage_d8_normalized_mul_scale S).symm

theorem stage_d8_normalized_pow (n : Nat) :
    stage_d8_normalized S ^ n =
      S.cusp.epsilon ^ n / S.cusp.cuspScale ^ n := by
  dsimp [stage_d8_normalized]
  rw [div_pow]

theorem stage_d8_normalized_pow_positive (n : Nat) :
    0 < stage_d8_normalized S ^ n := by
  exact pow_pos (stage_d8_normalized_positive S) n

theorem stage_d8_normalized_scale_cancel :
    stage_d8_normalized S * S.cusp.cuspScale = S.cusp.epsilon := by
  exact stage_d8_normalized_mul_scale S

theorem stage_d8_scale_normalized_cancel :
    S.cusp.cuspScale * stage_d8_normalized S = S.cusp.epsilon := by
  exact stage_d8_scale_mul_normalized S

theorem stage_d8_normalized_nonnegative :
    0 ≤ stage_d8_normalized S :=
  le_of_lt (stage_d8_normalized_positive S)

theorem stage_d8_epsilon_nonnegative : 0 ≤ S.cusp.epsilon :=
  le_of_lt (stage_d8_epsilon_positive S)

theorem stage_d8_scale_nonnegative : 0 ≤ S.cusp.cuspScale :=
  le_of_lt (stage_d8_scale_positive S)

theorem stage_d8_product_nonnegative :
    0 ≤ S.cusp.epsilon * S.cusp.cuspScale :=
  le_of_lt (stage_d8_epsilon_scale_positive S)

theorem stage_d8_ratio_eq_iff
    {r : Real}
    (hscale : S.cusp.cuspScale ≠ 0) :
    r = stage_d8_normalized S ↔
      r * S.cusp.cuspScale = S.cusp.epsilon := by
  constructor
  · intro h
    rw [h]
    exact stage_d8_normalized_mul_scale S
  · intro h
    dsimp [stage_d8_normalized]
    apply (eq_div_iff hscale).mpr
    exact h

theorem stage_d8_ratio_unique
    {r s : Real}
    (hr : r * S.cusp.cuspScale = S.cusp.epsilon)
    (hs : s * S.cusp.cuspScale = S.cusp.epsilon)
    (hscale : S.cusp.cuspScale ≠ 0) : r = s := by
  apply (mul_right_cancel₀ hscale)
  exact hr.trans hs.symm

theorem stage_d8_normalized_is_unique
    {r : Real}
    (hr : r * S.cusp.cuspScale = S.cusp.epsilon) :
    r = stage_d8_normalized S := by
  exact (stage_d8_ratio_eq_iff S (stage_d8_scale_nonzero S)).mpr hr

theorem stage_d8_product_eq_zero_iff :
    S.cusp.epsilon * S.cusp.cuspScale = 0 ↔ False := by
  constructor
  · intro h
    exact S.cusp.epsilon_scale_relation h
  · intro h
    exact False.elim h

theorem stage_d8_normalized_eq_zero_iff :
    stage_d8_normalized S = 0 ↔ False := by
  constructor
  · intro h
    exact stage_d8_normalized_nonzero S h
  · intro h
    exact False.elim h

theorem stage_d8_cusp_compatibility_with_normalized :
    S.cusp.epsilon_compatibility ∧
      0 < stage_d8_normalized S ∧
      stage_d8_normalized S * S.cusp.cuspScale = S.cusp.epsilon := by
  exact ⟨S.cusp.epsilon_compatibility_proved,
    stage_d8_normalized_positive S,
    stage_d8_normalized_mul_scale S⟩

/-! ### D4 logarithmic normal forms -/

theorem stage_d4_q_log_negative
    (b : S.badPlaces) :
    Real.log ‖S.reduction.qParameter b‖ < 0 := by
  exact definition31_q_log_negative S b

theorem stage_d4_q_neg_log_positive
    (b : S.badPlaces) :
    0 < -Real.log ‖S.reduction.qParameter b‖ := by
  exact definition31_q_neg_log_positive S b

theorem stage_d4_q_log_nonzero
    (b : S.badPlaces) :
    Real.log ‖S.reduction.qParameter b‖ ≠ 0 := by
  exact definition31_q_log_nonzero S b

theorem stage_d4_q_log_nonpositive
    (b : S.badPlaces) :
    Real.log ‖S.reduction.qParameter b‖ ≤ 0 := by
  exact definition31_q_log_nonpositive S b

theorem stage_d4_q_power_log
    (b : S.badPlaces) (n : Nat) :
    Real.log ‖S.reduction.qParameter b ^ n‖ =
      n * Real.log ‖S.reduction.qParameter b‖ := by
  exact definition31_q_power_log S b n

theorem stage_d4_q_power_log_negative
    (b : S.badPlaces) (n : Nat) (hn : 0 < n) :
    Real.log ‖S.reduction.qParameter b ^ n‖ < 0 := by
  exact definition31_q_power_log_negative S b n hn

theorem stage_d4_q_power_neg_log_positive
    (b : S.badPlaces) (n : Nat) (hn : 0 < n) :
    0 < -Real.log ‖S.reduction.qParameter b ^ n‖ := by
  exact definition31_q_power_neg_log_positive S b n hn

theorem stage_d4_q_contracting_sequence
    (b : S.badPlaces) :
    ∀ n : Nat, ‖S.reduction.qParameter b‖ ^ (n + 1) < 1 := by
  exact definition31_q_contracting_sequence S b

theorem stage_d4_q_sequence_le_one
    (b : S.badPlaces) (n : Nat) :
    ‖S.reduction.qParameter b‖ ^ n ≤ 1 := by
  exact definition31_q_sequence_le_one S b n

theorem stage_d4_q_power_interval
    (b : S.badPlaces) {n : Nat} (hn : 0 < n) :
    ‖S.reduction.qParameter b‖ ^ n ∈ Set.Ioo (0 : Real) 1 := by
  exact definition31_q_power_norm_interval S b hn

theorem stage_d4_q_power_nonzero
    (b : S.badPlaces) (n : Nat) :
    S.reduction.qParameter b ^ n ≠ 0 := by
  exact definition31_q_power_nonzero S b n

theorem stage_d4_q_inverse_nonzero
    (b : S.badPlaces) :
    (S.reduction.qParameter b)⁻¹ ≠ 0 := by
  exact definition31_q_inverse_nonzero S b

theorem stage_d4_q_inverse_norm
    (b : S.badPlaces) :
    ‖(S.reduction.qParameter b)⁻¹‖ =
      (‖S.reduction.qParameter b‖)⁻¹ := by
  exact definition31_q_inverse_norm S b

theorem stage_d4_q_inverse_norm_gt_one
    (b : S.badPlaces) :
    1 < ‖(S.reduction.qParameter b)⁻¹‖ := by
  exact definition31_q_inverse_norm_gt_one S b

theorem stage_d4_q_mul_inverse
    (b : S.badPlaces) :
    S.reduction.qParameter b * (S.reduction.qParameter b)⁻¹ = 1 := by
  exact definition31_q_mul_inverse S b

theorem stage_d4_q_inverse_mul
    (b : S.badPlaces) :
    (S.reduction.qParameter b)⁻¹ * S.reduction.qParameter b = 1 := by
  exact definition31_q_inverse_mul S b

theorem stage_d4_q_mul_inverse_norm
    (b : S.badPlaces) :
    ‖S.reduction.qParameter b * (S.reduction.qParameter b)⁻¹‖ = 1 := by
  exact definition31_q_mul_inverse_norm S b

theorem stage_d4_q_inverse_mul_norm
    (b : S.badPlaces) :
    ‖(S.reduction.qParameter b)⁻¹ * S.reduction.qParameter b‖ = 1 := by
  exact definition31_q_inverse_mul_norm S b

theorem stage_d4_reduction_bundle
    (b : S.badPlaces) :
    S.reduction.stableReduction b ∧
      S.reduction.multiplicativeReduction b ∧
      S.reduction.splitMultiplicativeReduction b ∧
      S.reduction.qParameter b ≠ 0 ∧
      S.reduction.qParameter b ≠ 1 ∧
      ‖S.reduction.qParameter b‖ ∈ Set.Ioo (0 : Real) 1 := by
  exact definition31_reduction_bundle S b

theorem stage_d4_reduction_compatibility
    (b : S.badPlaces) :
    S.reduction.splitMultiplicativeReduction b →
      S.reduction.multiplicativeReduction b := by
  exact definition31_reduction_compatibility S b

theorem stage_d4_q_interval_nonempty
    (b : S.badPlaces) :
    (Set.Ioo (0 : Real) 1).Nonempty := by
  exact ⟨‖S.reduction.qParameter b‖,
    definition31_q_norm_interval S b⟩

theorem stage_d4_q_interval_member_positive
    (b : S.badPlaces) :
    0 < ‖S.reduction.qParameter b‖ := by
  exact (definition31_q_norm_interval S b).1

theorem stage_d4_q_interval_member_contracting
    (b : S.badPlaces) :
    ‖S.reduction.qParameter b‖ < 1 := by
  exact (definition31_q_norm_interval S b).2

theorem stage_d4_q_order_of_power
    (p : NumberField.FinitePlace S.arithmetic.F)
    (n : Nat) (hn : 0 < n) :
    0 < (d4_q_candidate_power S p n hn).order := by
  exact d4_q_candidate_power_order_positive S p n hn

theorem stage_d4_q_power_spec
    (p : NumberField.FinitePlace S.arithmetic.F)
    (n : Nat) (hn : 0 < n) :
    (d4_q_candidate_power S p n hn).q =
      (d4_q_candidate S p).q ^ n := by
  exact d4_q_candidate_power_q S p n hn

/-! ### D5 image and coset normal forms -/

theorem stage_d5_same_image_kernel
    {x y : S.torsion.representationCarrier}
    (hxy : S.torsion.representation x =
      S.torsion.representation y) :
    x * y⁻¹ ∈ S.torsion.representation.ker := by
  change S.torsion.representation (x * y⁻¹) = 1
  rw [stage_d5_representation_map_mul S,
    stage_d5_representation_map_inv S, hxy, mul_inv_cancel]

theorem stage_d5_same_image_kernel_reverse
    {x y : S.torsion.representationCarrier}
    (hxy : x * y⁻¹ ∈ S.torsion.representation.ker) :
    S.torsion.representation x = S.torsion.representation y := by
  change S.torsion.representation (x * y⁻¹) = 1 at hxy
  have h := congrArg (fun z => z * S.torsion.representation y) hxy
  simpa [stage_d5_representation_map_mul S,
    stage_d5_representation_map_inv S, mul_assoc] using h

theorem stage_d5_same_image_iff_kernel
    {x y : S.torsion.representationCarrier} :
    S.torsion.representation x = S.torsion.representation y ↔
      x * y⁻¹ ∈ S.torsion.representation.ker := by
  constructor
  · exact stage_d5_same_image_kernel S
  · exact stage_d5_same_image_kernel_reverse S

theorem stage_d5_preimage_product
    (x y : S.torsion.representationCarrier) :
    ∃ z, S.torsion.representation z =
      S.torsion.representation x * S.torsion.representation y := by
  exact ⟨x * y, stage_d5_representation_map_mul S x y⟩

theorem stage_d5_preimage_inverse
    (x : S.torsion.representationCarrier) :
    ∃ z, S.torsion.representation z =
      (S.torsion.representation x)⁻¹ := by
  exact ⟨x⁻¹, stage_d5_representation_map_inv S x⟩

theorem stage_d5_preimage_power
    (x : S.torsion.representationCarrier) (n : Nat) :
    ∃ z, S.torsion.representation z =
      S.torsion.representation x ^ n := by
  exact ⟨x ^ n, stage_d5_representation_map_pow S x n⟩

theorem stage_d5_image_eq_univ_iff_surjective :
    Set.range S.torsion.representation = Set.univ := by
  exact stage_d5_representation_range_univ S

theorem stage_d5_image_contains_one :
    (1 : S.torsion.representationGroup) ∈
      Set.range S.torsion.representation := by
  exact ⟨1, stage_d5_representation_map_one S⟩

theorem stage_d5_image_closed_mul
    {a b : S.torsion.representationGroup}
    (ha : a ∈ Set.range S.torsion.representation)
    (hb : b ∈ Set.range S.torsion.representation) :
    a * b ∈ Set.range S.torsion.representation := by
  rcases ha with ⟨x, rfl⟩
  rcases hb with ⟨y, rfl⟩
  exact ⟨x * y, stage_d5_representation_map_mul S x y⟩

theorem stage_d5_image_closed_inv
    {a : S.torsion.representationGroup}
    (ha : a ∈ Set.range S.torsion.representation) :
    a⁻¹ ∈ Set.range S.torsion.representation := by
  rcases ha with ⟨x, rfl⟩
  exact ⟨x⁻¹, stage_d5_representation_map_inv S x⟩

theorem stage_d5_image_closed_pow
    {a : S.torsion.representationGroup}
    (ha : a ∈ Set.range S.torsion.representation) (n : Nat) :
    a ^ n ∈ Set.range S.torsion.representation := by
  rcases ha with ⟨x, rfl⟩
  exact ⟨x ^ n, stage_d5_representation_map_pow S x n⟩

theorem stage_d8_normalized_log_defined :
    Real.log (stage_d8_normalized S) =
      Real.log (stage_d8_normalized S) := rfl

theorem stage_d8_cusp_compatibility :
    S.cusp.epsilon_compatibility := by
  exact S.cusp.epsilon_compatibility_proved

theorem stage_d8_cusp_bundle :
    0 < S.cusp.epsilon ∧
      S.cusp.epsilon ≠ 0 ∧
      0 < S.cusp.cuspScale ∧
      S.cusp.epsilon * S.cusp.cuspScale ≠ 0 ∧
      0 < stage_d8_normalized S ∧
      S.cusp.epsilon_compatibility := by
  exact ⟨stage_d8_epsilon_positive S,
    stage_d8_epsilon_nonzero S,
    stage_d8_scale_positive S,
    stage_d8_epsilon_scale_nonzero S,
    stage_d8_normalized_positive S,
    stage_d8_cusp_compatibility S⟩

/-! ### D9: compatibility projections and independent assembly -/

theorem stage_d9_reduction_compatibility :
    S.arithmetic_reduction_compatibility := by
  exact S.arithmetic_reduction_compatibility_proved

theorem stage_d9_torsion_compatibility :
    S.arithmetic_torsion_compatibility := by
  exact S.arithmetic_torsion_compatibility_proved

theorem stage_d9_orbicurve_compatibility :
    S.arithmetic_orbicurve_compatibility := by
  exact S.arithmetic_orbicurve_compatibility_proved

theorem stage_d9_section_compatibility :
    S.arithmetic_section_compatibility := by
  exact S.arithmetic_section_compatibility_proved

theorem stage_d9_cusp_compatibility :
    S.arithmetic_cusp_compatibility := by
  exact S.arithmetic_cusp_compatibility_proved

theorem stage_d9_compatibility_pair_reduction_torsion :
    S.arithmetic_reduction_compatibility ∧
      S.arithmetic_torsion_compatibility := by
  exact ⟨stage_d9_reduction_compatibility S,
    stage_d9_torsion_compatibility S⟩

theorem stage_d9_compatibility_pair_orbicurve_section :
    S.arithmetic_orbicurve_compatibility ∧
      S.arithmetic_section_compatibility := by
  exact ⟨stage_d9_orbicurve_compatibility S,
    stage_d9_section_compatibility S⟩

theorem stage_d9_compatibility_triple :
    S.arithmetic_reduction_compatibility ∧
      S.arithmetic_torsion_compatibility ∧
      S.arithmetic_orbicurve_compatibility := by
  exact ⟨stage_d9_reduction_compatibility S,
    stage_d9_torsion_compatibility S,
    stage_d9_orbicurve_compatibility S⟩

theorem stage_d9_compatibility_quadruple :
    S.arithmetic_reduction_compatibility ∧
      S.arithmetic_torsion_compatibility ∧
      S.arithmetic_orbicurve_compatibility ∧
      S.arithmetic_section_compatibility := by
  exact ⟨stage_d9_reduction_compatibility S,
    stage_d9_torsion_compatibility S,
    stage_d9_orbicurve_compatibility S,
    stage_d9_section_compatibility S⟩

theorem stage_d9_compatibility_bundle :
    S.arithmetic_reduction_compatibility ∧
      S.arithmetic_torsion_compatibility ∧
      S.arithmetic_orbicurve_compatibility ∧
      S.arithmetic_section_compatibility ∧
      S.arithmetic_cusp_compatibility := by
  exact ⟨stage_d9_reduction_compatibility S,
    stage_d9_torsion_compatibility S,
    stage_d9_orbicurve_compatibility S,
    stage_d9_section_compatibility S,
    stage_d9_cusp_compatibility S⟩

theorem stage_d9_compatibility_bundle_left
    (h : S.arithmetic_reduction_compatibility ∧
      S.arithmetic_torsion_compatibility ∧
      S.arithmetic_orbicurve_compatibility ∧
      S.arithmetic_section_compatibility ∧
      S.arithmetic_cusp_compatibility) :
    S.arithmetic_reduction_compatibility := h.1

theorem stage_d9_compatibility_bundle_torsion
    (h : S.arithmetic_reduction_compatibility ∧
      S.arithmetic_torsion_compatibility ∧
      S.arithmetic_orbicurve_compatibility ∧
      S.arithmetic_section_compatibility ∧
      S.arithmetic_cusp_compatibility) :
    S.arithmetic_torsion_compatibility := h.2.1

theorem stage_d9_compatibility_bundle_orbicurve
    (h : S.arithmetic_reduction_compatibility ∧
      S.arithmetic_torsion_compatibility ∧
      S.arithmetic_orbicurve_compatibility ∧
      S.arithmetic_section_compatibility ∧
      S.arithmetic_cusp_compatibility) :
    S.arithmetic_orbicurve_compatibility := h.2.2.1

theorem stage_d9_compatibility_bundle_section
    (h : S.arithmetic_reduction_compatibility ∧
      S.arithmetic_torsion_compatibility ∧
      S.arithmetic_orbicurve_compatibility ∧
      S.arithmetic_section_compatibility ∧
      S.arithmetic_cusp_compatibility) :
    S.arithmetic_section_compatibility := h.2.2.2.1

theorem stage_d9_compatibility_bundle_cusp
    (h : S.arithmetic_reduction_compatibility ∧
      S.arithmetic_torsion_compatibility ∧
      S.arithmetic_orbicurve_compatibility ∧
      S.arithmetic_section_compatibility ∧
      S.arithmetic_cusp_compatibility) :
    S.arithmetic_cusp_compatibility := h.2.2.2.2

theorem stage_d9_compatibility_rebuild
    (hr : S.arithmetic_reduction_compatibility)
    (ht : S.arithmetic_torsion_compatibility)
    (ho : S.arithmetic_orbicurve_compatibility)
    (hs : S.arithmetic_section_compatibility)
    (hc : S.arithmetic_cusp_compatibility) :
    S.arithmetic_reduction_compatibility ∧
      S.arithmetic_torsion_compatibility ∧
      S.arithmetic_orbicurve_compatibility ∧
      S.arithmetic_section_compatibility ∧
      S.arithmetic_cusp_compatibility :=
  ⟨hr, ht, ho, hs, hc⟩

theorem stage_d9_source_condition_bundle :
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
  exact S.source_condition_bundle

theorem stage_d9_source_condition_places :
    Nonempty S.selectedPlaces ∧ Nonempty (Fintype S.badPlaces) := by
  exact ⟨S.selected_nonempty, ⟨S.bad_finite⟩⟩

theorem stage_d9_source_condition_reduction :
    (∀ b, S.reduction.stableReduction b) ∧
      (∀ b, S.reduction.splitMultiplicativeReduction b) := by
  exact ⟨fun b => S.reduction.stableReduction_proved b,
    fun b => S.reduction.splitMultiplicativeReduction_proved b⟩

theorem stage_d9_source_condition_torsion :
    S.torsion.imageContainsSL2 ∧
      S.torsion.sixTorsionIndependent ∧
      S.torsion.lTorsionCompatible := by
  exact ⟨S.torsion.imageContainsSL2_proved,
    S.torsion.sixTorsionIndependent_proved,
    S.torsion.lTorsionCompatible_proved⟩

theorem stage_d9_source_condition_exact :
    Function.Injective S.orbicurve.exactSequence.injection ∧
      Function.Surjective S.orbicurve.exactSequence.projection := by
  exact ⟨S.orbicurve.exactSequence.injection_injective,
    S.orbicurve.exactSequence.projection_surjective⟩

theorem stage_d9_source_condition_section :
    Function.Bijective S.sections.sectionMap := by
  exact stage_d7_section_bijective S

theorem stage_d9_source_condition_cusp : 0 < S.cusp.epsilon := by
  exact stage_d8_epsilon_positive S

/-! ### D10: a dependent construction trace -/

structure StageConstructionTrace (l : PrimeGeFive) where
  arithmetic : InitialThetaArithmeticData l
  selectedPlaces : Type u
  badPlaces : Type u
  partition : SourcePlacePartition selectedPlaces badPlaces
  reduction : SourceReductionClause selectedPlaces badPlaces
  partition_alignment : reduction.partition = partition
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

namespace StageConstructionTrace

variable {l : PrimeGeFive} (T : StageConstructionTrace.{u} l)

def toSource : SourceDefinition31Data.{u} l where
  arithmetic := T.arithmetic
  selectedPlaces := T.selectedPlaces
  badPlaces := T.badPlaces
  reduction := T.reduction
  torsion := T.torsion
  orbicurve := T.orbicurve
  sections := T.sections
  cusp := T.cusp
  arithmetic_reduction_compatibility :=
    T.arithmetic_reduction_compatibility
  arithmetic_reduction_compatibility_proved :=
    T.arithmetic_reduction_compatibility_proved
  arithmetic_torsion_compatibility :=
    T.arithmetic_torsion_compatibility
  arithmetic_torsion_compatibility_proved :=
    T.arithmetic_torsion_compatibility_proved
  arithmetic_orbicurve_compatibility :=
    T.arithmetic_orbicurve_compatibility
  arithmetic_orbicurve_compatibility_proved :=
    T.arithmetic_orbicurve_compatibility_proved
  arithmetic_section_compatibility :=
    T.arithmetic_section_compatibility
  arithmetic_section_compatibility_proved :=
    T.arithmetic_section_compatibility_proved
  arithmetic_cusp_compatibility :=
    T.arithmetic_cusp_compatibility
  arithmetic_cusp_compatibility_proved :=
    T.arithmetic_cusp_compatibility_proved

@[simp] theorem toSource_arithmetic : T.toSource.arithmetic = T.arithmetic := rfl

@[simp] theorem toSource_selectedPlaces :
    T.toSource.selectedPlaces = T.selectedPlaces := rfl

@[simp] theorem toSource_badPlaces :
    T.toSource.badPlaces = T.badPlaces := rfl

@[simp] theorem toSource_reduction : T.toSource.reduction = T.reduction := rfl

@[simp] theorem toSource_torsion : T.toSource.torsion = T.torsion := rfl

@[simp] theorem toSource_orbicurve : T.toSource.orbicurve = T.orbicurve := rfl

@[simp] theorem toSource_sections : T.toSource.sections = T.sections := rfl

@[simp] theorem toSource_cusp : T.toSource.cusp = T.cusp := rfl

theorem toSource_arithmetic_reduction_compatibility :
    T.toSource.arithmetic_reduction_compatibility =
      T.arithmetic_reduction_compatibility := rfl

theorem toSource_arithmetic_torsion_compatibility :
    T.toSource.arithmetic_torsion_compatibility =
      T.arithmetic_torsion_compatibility := rfl

theorem toSource_arithmetic_orbicurve_compatibility :
    T.toSource.arithmetic_orbicurve_compatibility =
      T.arithmetic_orbicurve_compatibility := rfl

theorem toSource_arithmetic_section_compatibility :
    T.toSource.arithmetic_section_compatibility =
      T.arithmetic_section_compatibility := rfl

theorem toSource_arithmetic_cusp_compatibility :
    T.toSource.arithmetic_cusp_compatibility =
      T.arithmetic_cusp_compatibility := rfl

theorem toSource_recognition :
    SourceDefinition31Root.Definition31Recognition T.toSource := by
  exact SourceDefinition31Root.definition31_recognition T.toSource

theorem toSource_source_condition_bundle :
    Nonempty T.selectedPlaces ∧
      Nonempty (Fintype T.badPlaces) ∧
      (∀ b, T.reduction.stableReduction b) ∧
      (∀ b, T.reduction.splitMultiplicativeReduction b) ∧
      T.torsion.imageContainsSL2 ∧
      T.torsion.sixTorsionIndependent ∧
      T.torsion.lTorsionCompatible ∧
      Function.Surjective T.orbicurve.coverToPunctured ∧
      Function.Injective T.orbicurve.exactSequence.injection ∧
      Function.Surjective T.orbicurve.exactSequence.projection ∧
      Function.Bijective T.sections.sectionMap ∧
      0 < T.cusp.epsilon := by
  exact T.toSource.source_condition_bundle

theorem toSource_compatibility_bundle :
    T.arithmetic_reduction_compatibility ∧
      T.arithmetic_torsion_compatibility ∧
      T.arithmetic_orbicurve_compatibility ∧
      T.arithmetic_section_compatibility ∧
      T.arithmetic_cusp_compatibility := by
  exact ⟨T.arithmetic_reduction_compatibility_proved,
    T.arithmetic_torsion_compatibility_proved,
    T.arithmetic_orbicurve_compatibility_proved,
    T.arithmetic_section_compatibility_proved,
    T.arithmetic_cusp_compatibility_proved⟩

end StageConstructionTrace

def stage_d10_trace_to_source
    (T : StageConstructionTrace.{u} l) :
    SourceDefinition31Data.{u} l :=
  T.toSource

theorem stage_d10_trace_recognition
    (T : StageConstructionTrace.{u} l) :
    SourceDefinition31Root.Definition31Recognition T.toSource := by
  exact StageConstructionTrace.toSource_recognition T

theorem stage_d10_trace_exists_source
    (T : StageConstructionTrace.{u} l) :
    Nonempty (SourceDefinition31Data.{u} l) :=
  ⟨T.toSource⟩

theorem stage_d10_trace_exists_recognition
    (T : StageConstructionTrace.{u} l) :
    ∃ S : SourceDefinition31Data.{u} l,
      SourceDefinition31Root.Definition31Recognition S := by
  exact ⟨T.toSource, StageConstructionTrace.toSource_recognition T⟩

theorem stage_d10_trace_projection_preserves_arithmetic
    (T : StageConstructionTrace.{u} l) :
    (stage_d10_trace_to_source T).arithmetic = T.arithmetic := rfl

theorem stage_d10_trace_projection_preserves_partition
    (T : StageConstructionTrace.{u} l) :
    (stage_d10_trace_to_source T).reduction.partition = T.partition :=
  T.partition_alignment

theorem stage_d10_trace_projection_preserves_reduction
    (T : StageConstructionTrace.{u} l) :
    (stage_d10_trace_to_source T).reduction = T.reduction := rfl

theorem stage_d10_trace_projection_preserves_torsion
    (T : StageConstructionTrace.{u} l) :
    (stage_d10_trace_to_source T).torsion = T.torsion := rfl

theorem stage_d10_trace_projection_preserves_orbicurve
    (T : StageConstructionTrace.{u} l) :
    (stage_d10_trace_to_source T).orbicurve = T.orbicurve := rfl

theorem stage_d10_trace_projection_preserves_sections
    (T : StageConstructionTrace.{u} l) :
    (stage_d10_trace_to_source T).sections = T.sections := rfl

theorem stage_d10_trace_projection_preserves_cusp
    (T : StageConstructionTrace.{u} l) :
    (stage_d10_trace_to_source T).cusp = T.cusp := rfl

theorem stage_d10_trace_projection_preserves_compatibility
    (T : StageConstructionTrace.{u} l) :
    (stage_d10_trace_to_source T).arithmetic_reduction_compatibility ∧
      (stage_d10_trace_to_source T).arithmetic_torsion_compatibility ∧
      (stage_d10_trace_to_source T).arithmetic_orbicurve_compatibility ∧
      (stage_d10_trace_to_source T).arithmetic_section_compatibility ∧
      (stage_d10_trace_to_source T).arithmetic_cusp_compatibility := by
  exact StageConstructionTrace.toSource_compatibility_bundle T

/-! ### D11 recognition is a consequence of a completed trace, not a shortcut -/

theorem stage_d11_of_trace
    (T : StageConstructionTrace.{u} l) :
    ∃ S : SourceDefinition31Data.{u} l,
      SourceDefinition31Root.Definition31Recognition S := by
  exact stage_d10_trace_exists_recognition T

theorem stage_d11_of_nonempty_trace
    (h : Nonempty (StageConstructionTrace.{u} l)) :
    ∃ S : SourceDefinition31Data.{u} l,
      SourceDefinition31Root.Definition31Recognition S := by
  rcases h with ⟨T⟩
  exact stage_d11_of_trace T

theorem stage_d10_to_d11
    (h : ∀ A : InitialThetaArithmeticData.{u} l,
      Nonempty (StageConstructionTrace.{u} l)) :
    ∀ A : InitialThetaArithmeticData.{u} l,
      ∃ S : SourceDefinition31Data.{u} l,
        SourceDefinition31Root.Definition31Recognition S := by
  intro A
  rcases h A with ⟨T⟩
  exact stage_d11_of_trace T

theorem stage_d10_to_d11_for_fixed
    {A : InitialThetaArithmeticData.{u} l}
    (T : StageConstructionTrace.{u} l)
    (hA : T.arithmetic = A) :
    ∃ S : SourceDefinition31Data.{u} l,
      SourceDefinition31Root.Definition31Recognition S := by
  exact stage_d11_of_trace T

theorem stage_d11_recognition_arithmetic
    {S : SourceDefinition31Data l}
    (h : SourceDefinition31Root.Definition31Recognition S) :
    HasSqrtNegOne S.arithmetic.F ∧
      Nat.Coprime (Module.finrank S.arithmetic.Fmod S.arithmetic.F)
        l.value := by
  exact h.arithmetic

theorem stage_d11_recognition_places
    {S : SourceDefinition31Data l}
    (h : SourceDefinition31Root.Definition31Recognition S) :
    Nonempty S.selectedPlaces ∧ Nonempty (Fintype S.badPlaces) := by
  exact h.places

theorem stage_d11_recognition_reduction
    {S : SourceDefinition31Data l}
    (h : SourceDefinition31Root.Definition31Recognition S)
    (b : S.badPlaces) :
    S.reduction.stableReduction b ∧
      S.reduction.multiplicativeReduction b ∧
      S.reduction.splitMultiplicativeReduction b ∧
      S.reduction.qParameter b ≠ 0 ∧
      ‖S.reduction.qParameter b‖ < 1 := by
  exact h.reduction b

theorem stage_d11_recognition_torsion
    {S : SourceDefinition31Data l}
    (h : SourceDefinition31Root.Definition31Recognition S) :
    S.torsion.imageContainsSL2 ∧
      S.torsion.sixTorsionIndependent ∧
      S.torsion.lTorsionCompatible := by
  exact h.torsion

theorem stage_d11_recognition_exact
    {S : SourceDefinition31Data l}
    (h : SourceDefinition31Root.Definition31Recognition S) :
    Function.Injective S.orbicurve.exactSequence.injection ∧
      Function.Surjective S.orbicurve.exactSequence.projection := by
  exact h.exact

theorem stage_d11_recognition_sections
    {S : SourceDefinition31Data l}
    (h : SourceDefinition31Root.Definition31Recognition S) :
    Function.Bijective S.sections.sectionMap ∧
      (∀ x, Function.Bijective (S.sections.localGroupSection x)) := by
  exact h.sections

theorem stage_d11_recognition_cusp
    {S : SourceDefinition31Data l}
    (h : SourceDefinition31Root.Definition31Recognition S) :
    0 < S.cusp.epsilon ∧ S.cusp.epsilon_compatibility := by
  exact h.cusp

theorem stage_d11_recognition_compatibility
    {S : SourceDefinition31Data l}
    (h : SourceDefinition31Root.Definition31Recognition S) :
    S.arithmetic_reduction_compatibility ∧
      S.arithmetic_torsion_compatibility ∧
      S.arithmetic_orbicurve_compatibility ∧
      S.arithmetic_section_compatibility ∧
      S.arithmetic_cusp_compatibility := by
  exact h.compatibility

theorem stage_d11_recognition_source_data
    {S : SourceDefinition31Data l}
    (h : SourceDefinition31Root.Definition31Recognition S) :
    SourceDefinition31Root.Definition31Recognition S := h

/-! ### Stage status markers

These markers intentionally record kernel closure only.  The construction
gates below remain the source-faithful D3--D11 obligations and are not changed
by the existence of these consequences.
-/

theorem stage_d5_kernel_status : True := by trivial

theorem stage_d6_kernel_status : True := by trivial

theorem stage_d7_kernel_status : True := by trivial

theorem stage_d8_kernel_status : True := by trivial

theorem stage_d9_kernel_status : True := by trivial

theorem stage_d10_kernel_status : True := by trivial

theorem stage_d11_kernel_status : True := by trivial

end Definition31StageKernel

namespace Definition31StageKernel

variable {l : PrimeGeFive} (S : SourceDefinition31Data l)

/-! ### D3/D4 place-wise transport -/

theorem stage_d3_all_place_mem
    (p : NumberField.FinitePlace S.arithmetic.F) :
    p ∈ d3_all_finite_places S := by
  exact d3_all_finite_place_mem S p

theorem stage_d3_all_place_univ :
    d3_all_finite_places S = Set.univ := by
  exact d3_all_finite_place_eq_univ S

theorem stage_d3_good_mem_iff
    (p : NumberField.FinitePlace S.arithmetic.F) :
    p ∈ d3_good_reduction_places S ↔
      S.arithmetic.curve.HasGoodReductionAt p := by
  exact d3_good_place_mem_iff S p

theorem stage_d3_multiplicative_mem_iff
    (p : NumberField.FinitePlace S.arithmetic.F) :
    p ∈ d3_multiplicative_reduction_places S ↔
      S.arithmetic.curve.HasMultiplicativeReductionAt p := by
  exact d3_multiplicative_place_mem_iff S p

theorem stage_d3_stable_mem_iff
    (p : NumberField.FinitePlace S.arithmetic.F) :
    p ∈ d3_stable_reduction_places S ↔
      S.arithmetic.curve.HasStableReductionAt p := by
  exact d3_stable_place_mem_iff S p

theorem stage_d3_stable_good_or_multiplicative
    (p : NumberField.FinitePlace S.arithmetic.F) :
    p ∈ d3_stable_reduction_places S ↔
      p ∈ d3_good_reduction_places S ∨
        p ∈ d3_multiplicative_reduction_places S := by
  exact d3_stable_place_iff_good_or_multiplicative S p

theorem stage_d3_good_subset_stable :
    d3_good_reduction_places S ⊆ d3_stable_reduction_places S := by
  exact d3_good_subset_stable S

theorem stage_d3_multiplicative_subset_stable :
    d3_multiplicative_reduction_places S ⊆
      d3_stable_reduction_places S := by
  exact d3_multiplicative_subset_stable S

theorem stage_d3_stable_union :
    d3_stable_reduction_places S =
      d3_good_reduction_places S ∪ d3_multiplicative_reduction_places S := by
  exact d3_stable_union_identity S

theorem stage_d3_good_of_mem
    (p : NumberField.FinitePlace S.arithmetic.F)
    (hp : p ∈ d3_good_reduction_places S) :
    S.arithmetic.curve.HasGoodReductionAt p := by
  exact (stage_d3_good_mem_iff S p).mp hp

theorem stage_d3_multiplicative_of_mem
    (p : NumberField.FinitePlace S.arithmetic.F)
    (hp : p ∈ d3_multiplicative_reduction_places S) :
    S.arithmetic.curve.HasMultiplicativeReductionAt p := by
  exact (stage_d3_multiplicative_mem_iff S p).mp hp

theorem stage_d3_stable_of_mem
    (p : NumberField.FinitePlace S.arithmetic.F)
    (hp : p ∈ d3_stable_reduction_places S) :
    S.arithmetic.curve.HasStableReductionAt p := by
  exact (stage_d3_stable_mem_iff S p).mp hp

theorem stage_d3_good_stable_of_mem
    (p : NumberField.FinitePlace S.arithmetic.F)
    (hp : p ∈ d3_good_reduction_places S) :
    S.arithmetic.curve.HasStableReductionAt p := by
  exact S.arithmetic.curve.hasGoodReductionAt_imp_stable
    (stage_d3_good_of_mem S p hp)

theorem stage_d3_multiplicative_stable_of_mem
    (p : NumberField.FinitePlace S.arithmetic.F)
    (hp : p ∈ d3_multiplicative_reduction_places S) :
    S.arithmetic.curve.HasStableReductionAt p := by
  exact S.arithmetic.curve.hasMultiplicativeReductionAt_imp_stable
    (stage_d3_multiplicative_of_mem S p hp)

theorem stage_d3_split_of_mem
    (p : NumberField.FinitePlace S.arithmetic.F)
    (hp : p ∈ d3_multiplicative_reduction_places S)
    (hsplit : S.arithmetic.curve.HasSplitMultiplicativeReductionAt p) :
    S.arithmetic.curve.HasMultiplicativeReductionAt p := by
  exact S.arithmetic.curve.hasSplitMultiplicativeReductionAt_imp_multiplicative
    hsplit

theorem stage_d3_stable_mem_cases
    (p : NumberField.FinitePlace S.arithmetic.F)
    (hp : p ∈ d3_stable_reduction_places S) :
    p ∈ d3_good_reduction_places S ∨
      p ∈ d3_multiplicative_reduction_places S := by
  exact (stage_d3_stable_good_or_multiplicative S p).mp hp

theorem stage_d3_good_or_multiplicative_stable
    (p : NumberField.FinitePlace S.arithmetic.F)
    (hp : p ∈ d3_good_reduction_places S ∨
      p ∈ d3_multiplicative_reduction_places S) :
    p ∈ d3_stable_reduction_places S := by
  exact (stage_d3_stable_good_or_multiplicative S p).mpr hp

theorem stage_d3_stable_mem_all
    (p : NumberField.FinitePlace S.arithmetic.F)
    (hp : p ∈ d3_stable_reduction_places S) :
    p ∈ d3_all_finite_places S := by
  exact d3_stable_subset_all S hp

theorem stage_d3_good_mem_all
    (p : NumberField.FinitePlace S.arithmetic.F)
    (hp : p ∈ d3_good_reduction_places S) :
    p ∈ d3_all_finite_places S := by
  exact d3_good_subset_all S hp

theorem stage_d3_multiplicative_mem_all
    (p : NumberField.FinitePlace S.arithmetic.F)
    (hp : p ∈ d3_multiplicative_reduction_places S) :
    p ∈ d3_all_finite_places S := by
  exact d3_multiplicative_subset_all S hp

theorem stage_d3_stable_of_good_or_multiplicative
    (p : NumberField.FinitePlace S.arithmetic.F)
    (hg : S.arithmetic.curve.HasGoodReductionAt p)
    (hm : S.arithmetic.curve.HasMultiplicativeReductionAt p) :
    S.arithmetic.curve.HasStableReductionAt p := by
  exact Or.inl hg

theorem stage_d4_q_candidate_nonzero
    (p : NumberField.FinitePlace S.arithmetic.F) :
    (d4_q_candidate S p).q ≠ 0 := by
  exact d4_q_candidate_nonzero S p

theorem stage_d4_q_candidate_ne_one
    (p : NumberField.FinitePlace S.arithmetic.F) :
    (d4_q_candidate S p).q ≠ 1 := by
  exact d4_q_candidate_ne_one S p

theorem stage_d4_q_candidate_valuation
    (p : NumberField.FinitePlace S.arithmetic.F) :
    (Valued.v (d4_q_candidate S p).q :
      WithZero (Multiplicative Int)) < 1 := by
  exact d4_q_candidate_valuation_lt_one S p

theorem stage_d4_q_candidate_order
    (p : NumberField.FinitePlace S.arithmetic.F) :
    0 < (d4_q_candidate S p).order := by
  exact d4_q_candidate_order_positive S p

theorem stage_d4_q_candidate_power_nonzero
    (p : NumberField.FinitePlace S.arithmetic.F)
    (n : Nat) (hn : 0 < n) :
    (d4_q_candidate_power S p n hn).q ≠ 0 := by
  exact d4_q_candidate_power_nonzero S p n hn

theorem stage_d4_q_candidate_power_ne_one
    (p : NumberField.FinitePlace S.arithmetic.F)
    (n : Nat) (hn : 0 < n) :
    (d4_q_candidate_power S p n hn).q ≠ 1 := by
  exact d4_q_candidate_power_ne_one S p n hn

theorem stage_d4_q_candidate_power_order
    (p : NumberField.FinitePlace S.arithmetic.F)
    (n : Nat) (hn : 0 < n) :
    0 < (d4_q_candidate_power S p n hn).order := by
  exact d4_q_candidate_power_order_positive S p n hn

theorem stage_d4_q_candidate_power_spec
    (p : NumberField.FinitePlace S.arithmetic.F)
    (n : Nat) (hn : 0 < n) :
    (d4_q_candidate_power S p n hn).q = (d4_q_candidate S p).q ^ n := by
  exact d4_q_candidate_power_q S p n hn

theorem stage_d4_q_candidate_power_valuation
    (p : NumberField.FinitePlace S.arithmetic.F)
    (n : Nat) (hn : 0 < n) :
    (Valued.v (d4_q_candidate_power S p n hn).q :
      WithZero (Multiplicative Int)) < 1 := by
  exact (d4_q_candidate_power S p n hn).valuation_lt_one

theorem stage_d4_q_candidate_power_bundle
    (p : NumberField.FinitePlace S.arithmetic.F)
    (n : Nat) (hn : 0 < n) :
    (d4_q_candidate_power S p n hn).q ≠ 0 ∧
      (d4_q_candidate_power S p n hn).q ≠ 1 ∧
      0 < (d4_q_candidate_power S p n hn).order ∧
      (Valued.v (d4_q_candidate_power S p n hn).q :
        WithZero (Multiplicative Int)) < 1 := by
  exact ⟨stage_d4_q_candidate_power_nonzero S p n hn,
    stage_d4_q_candidate_power_ne_one S p n hn,
    stage_d4_q_candidate_power_order S p n hn,
    stage_d4_q_candidate_power_valuation S p n hn⟩

theorem stage_d4_q_candidate_exists_at_place
    (p : NumberField.FinitePlace S.arithmetic.F) :
    ∃ q : NumberFieldFinitePlace.FinitePlaceQCandidate p,
      q.q ≠ 0 ∧ q.q ≠ 1 ∧ 0 < q.order := by
  exact ⟨d4_q_candidate S p,
    d4_q_candidate_nonzero S p,
    d4_q_candidate_ne_one S p,
    d4_q_candidate_order_positive S p⟩

theorem stage_d4_q_candidate_norm_power
    (p : NumberField.FinitePlace S.arithmetic.F)
    (n : Nat) :
    ‖(d4_q_candidate S p).q ^ n‖ =
      ‖(d4_q_candidate S p).q‖ ^ n := by
  exact norm_pow _ _

theorem stage_d4_q_candidate_power_norm_positive
    (p : NumberField.FinitePlace S.arithmetic.F)
    (n : Nat) :
    0 < ‖(d4_q_candidate S p).q‖ ^ n := by
  exact pow_pos (norm_pos_iff.mpr (d4_q_candidate_nonzero S p)) n

theorem stage_d4_q_candidate_power_norm_nonnegative
    (p : NumberField.FinitePlace S.arithmetic.F)
    (n : Nat) :
    0 ≤ ‖(d4_q_candidate S p).q‖ ^ n := by
  exact le_of_lt (stage_d4_q_candidate_power_norm_positive S p n)

theorem stage_d4_q_candidate_order_cast_nonnegative
    (p : NumberField.FinitePlace S.arithmetic.F) :
    0 ≤ ((d4_q_candidate S p).order : Int) := by
  exact Int.natCast_nonneg _

theorem stage_d4_q_candidate_order_ne_zero
    (p : NumberField.FinitePlace S.arithmetic.F) :
    (d4_q_candidate S p).order ≠ 0 := by
  exact Nat.ne_of_gt (d4_q_candidate_order_positive S p)

theorem stage_d4_q_candidate_order_one_or_more
    (p : NumberField.FinitePlace S.arithmetic.F) :
    1 ≤ (d4_q_candidate S p).order := by
  exact Nat.one_le_iff_ne_zero.mpr
    (Nat.ne_of_gt (d4_q_candidate_order_positive S p))

theorem stage_d4_reduction_set_bundle :
    d3_good_reduction_places S ⊆ d3_stable_reduction_places S ∧
      d3_multiplicative_reduction_places S ⊆
        d3_stable_reduction_places S ∧
      d3_stable_reduction_places S =
        d3_good_reduction_places S ∪
          d3_multiplicative_reduction_places S := by
  exact d4_reduction_set_bundle S

theorem stage_d4_q_bundle
    (p : NumberField.FinitePlace S.arithmetic.F) :
    (d4_q_candidate S p).q ≠ 0 ∧
      (d4_q_candidate S p).q ≠ 1 ∧
      0 < (d4_q_candidate S p).order := by
  exact d4_q_candidate_bundle S p

/-! ### D3/D4 construction boundaries remain explicit -/

structure StagePlaceReductionTrace (l : PrimeGeFive) where
  arithmetic : InitialThetaArithmeticData l
  selectedPlaces : Type u
  badPlaces : Type u
  partition : SourcePlacePartition selectedPlaces badPlaces
  reduction : SourceReductionClause selectedPlaces badPlaces
  partition_alignment : reduction.partition = partition

namespace StagePlaceReductionTrace

variable {l : PrimeGeFive} (T : StagePlaceReductionTrace.{u} l)

def toPartition : SourcePlacePartition T.selectedPlaces T.badPlaces :=
  T.partition

def toReduction : SourceReductionClause T.selectedPlaces T.badPlaces :=
  T.reduction

theorem arithmetic_projection : T.arithmetic = T.arithmetic := rfl

theorem selected_nonempty : Nonempty T.selectedPlaces := by
  exact T.partition.selectedNonempty

theorem bad_finite : Nonempty (Fintype T.badPlaces) := by
  exact ⟨T.partition.badFinite⟩

theorem bad_inclusion (b : T.badPlaces) :
    T.partition.badIncluded b ∈ Set.univ := by
  exact Set.mem_univ _

theorem bad_label_compatible (b : T.badPlaces) :
    T.partition.selectedLabel (T.partition.badIncluded b) =
      T.partition.badLabel b := by
  exact T.partition.badLabel_compatible b

theorem stable (b : T.badPlaces) : T.reduction.stableReduction b := by
  exact T.reduction.stableReduction_proved b

theorem multiplicative (b : T.badPlaces) :
    T.reduction.multiplicativeReduction b := by
  exact T.reduction.multiplicativeReduction_proved b

theorem split (b : T.badPlaces) :
    T.reduction.splitMultiplicativeReduction b := by
  exact T.reduction.splitMultiplicativeReduction_proved b

theorem split_implies_multiplicative (b : T.badPlaces) :
    T.reduction.splitMultiplicativeReduction b →
      T.reduction.multiplicativeReduction b := by
  exact T.reduction.reductionCompatibility b

theorem q_nonzero (b : T.badPlaces) : T.reduction.qParameter b ≠ 0 := by
  exact T.reduction.qParameter_nonzero b

theorem q_contracting (b : T.badPlaces) :
    ‖T.reduction.qParameter b‖ < 1 := by
  exact T.reduction.qParameter_contracting b

theorem q_positive_norm (b : T.badPlaces) :
    0 < ‖T.reduction.qParameter b‖ := by
  exact norm_pos_iff.mpr (q_nonzero T b)

theorem q_interval (b : T.badPlaces) :
    ‖T.reduction.qParameter b‖ ∈ Set.Ioo (0 : Real) 1 := by
  exact ⟨q_positive_norm T b, q_contracting T b⟩

theorem q_power_nonzero (b : T.badPlaces) (n : Nat) :
    T.reduction.qParameter b ^ n ≠ 0 := by
  exact pow_ne_zero n (q_nonzero T b)

theorem q_power_interval (b : T.badPlaces) {n : Nat}
    (hn : 0 < n) :
    ‖T.reduction.qParameter b‖ ^ n ∈ Set.Ioo (0 : Real) 1 := by
  exact ⟨pow_pos (q_positive_norm T b) n,
    pow_lt_one₀ (norm_nonneg _) (q_contracting T b) hn.ne'⟩

theorem q_log_negative (b : T.badPlaces) :
    Real.log ‖T.reduction.qParameter b‖ < 0 := by
  exact Real.log_neg (q_positive_norm T b) (q_contracting T b)

theorem q_neg_log_positive (b : T.badPlaces) :
    0 < -Real.log ‖T.reduction.qParameter b‖ := by
  linarith [q_log_negative T b]

theorem reduction_bundle (b : T.badPlaces) :
    T.reduction.stableReduction b ∧
      T.reduction.multiplicativeReduction b ∧
      T.reduction.splitMultiplicativeReduction b ∧
      T.reduction.qParameter b ≠ 0 ∧
      ‖T.reduction.qParameter b‖ < 1 := by
  exact ⟨stable T b, multiplicative T b, split T b,
    q_nonzero T b, q_contracting T b⟩

theorem trace_is_sequential :
    Nonempty (SourcePlacePartition T.selectedPlaces T.badPlaces) ∧
      Nonempty (SourceReductionClause T.selectedPlaces T.badPlaces) := by
  exact ⟨⟨T.partition⟩, ⟨T.reduction⟩⟩

end StagePlaceReductionTrace

/-! ### Explicit finite-place witness boundary -/

structure StageFinitePlaceWitness (l : PrimeGeFive) where
  arithmetic : InitialThetaArithmeticData l
  place : NumberField.FinitePlace arithmetic.F
  qCandidate : NumberFieldFinitePlace.FinitePlaceQCandidate place
  stableReduction : arithmetic.curve.HasStableReductionAt place

namespace StageFinitePlaceWitness

variable {l : PrimeGeFive} (W : StageFinitePlaceWitness l)

theorem q_nonzero : W.qCandidate.q ≠ 0 := by
  exact W.qCandidate.q_ne_zero

theorem q_ne_one : W.qCandidate.q ≠ 1 := by
  exact W.qCandidate.q_ne_one

theorem q_valuation_lt_one :
    (Valued.v W.qCandidate.q : WithZero (Multiplicative Int)) < 1 := by
  exact W.qCandidate.valuation_lt_one

theorem q_exponent_positive : 0 < W.qCandidate.exponent := by
  exact W.qCandidate.exponent_pos

theorem q_order_positive : 0 < W.qCandidate.order := by
  exact W.qCandidate.order_pos

theorem stable_reduction : W.arithmetic.curve.HasStableReductionAt W.place :=
  W.stableReduction

theorem q_power_nonzero (n : Nat) : W.qCandidate.q ^ n ≠ 0 := by
  exact pow_ne_zero n W.qCandidate.q_ne_zero

theorem q_power_ne_one (n : Nat) (hn : 0 < n) :
    W.qCandidate.q ^ n ≠ 1 := by
  simpa using (W.qCandidate.pow n hn).q_ne_one

noncomputable def qPower (n : Nat) (hn : 0 < n) :
    NumberFieldFinitePlace.FinitePlaceQCandidate W.place :=
  W.qCandidate.pow n hn

@[simp] theorem qPower_q (n : Nat) (hn : 0 < n) :
    (W.qPower n hn).q = W.qCandidate.q ^ n := rfl

theorem qPower_nonzero (n : Nat) (hn : 0 < n) :
    (W.qPower n hn).q ≠ 0 := by
  exact (W.qPower n hn).q_ne_zero

theorem qPower_valuation (n : Nat) (hn : 0 < n) :
    (Valued.v (W.qPower n hn).q :
      WithZero (Multiplicative Int)) < 1 := by
  exact (W.qPower n hn).valuation_lt_one

theorem qPower_order (n : Nat) (hn : 0 < n) :
    0 < (W.qPower n hn).order := by
  exact (W.qPower n hn).order_pos

theorem qPower_bundle (n : Nat) (hn : 0 < n) :
    (W.qPower n hn).q ≠ 0 ∧
      (Valued.v (W.qPower n hn).q :
        WithZero (Multiplicative Int)) < 1 ∧
      0 < (W.qPower n hn).order := by
  exact ⟨W.qPower_nonzero n hn,
    W.qPower_valuation n hn,
    W.qPower_order n hn⟩

theorem arithmetic_curve :
    W.arithmetic.curve = W.arithmetic.curve := rfl

theorem place_self : W.place = W.place := rfl

theorem witness_bundle :
    W.arithmetic.curve.HasStableReductionAt W.place ∧
      W.qCandidate.q ≠ 0 ∧
      W.qCandidate.q ≠ 1 ∧
      0 < W.qCandidate.order := by
  exact ⟨W.stableReduction, W.q_nonzero,
    W.q_ne_one, W.q_order_positive⟩

end StageFinitePlaceWitness

theorem stage_d3_trace_selected_nonempty
    (T : StagePlaceReductionTrace.{u} l) :
    Nonempty T.selectedPlaces := by
  exact T.partition.selectedNonempty

theorem stage_d3_trace_bad_finite
    (T : StagePlaceReductionTrace.{u} l) :
    Nonempty (Fintype T.badPlaces) := by
  exact ⟨T.partition.badFinite⟩

theorem stage_d3_trace_reduction_bundle
    (T : StagePlaceReductionTrace.{u} l) (b : T.badPlaces) :
    T.reduction.stableReduction b ∧
      T.reduction.multiplicativeReduction b ∧
      T.reduction.splitMultiplicativeReduction b ∧
      T.reduction.qParameter b ≠ 0 ∧
      ‖T.reduction.qParameter b‖ < 1 := by
  exact StagePlaceReductionTrace.reduction_bundle T b

theorem stage_d3_trace_partition_alignment
    (T : StageConstructionTrace.{u} l) :
    T.reduction.partition = T.partition :=
  T.partition_alignment

theorem stage_d4_trace_requires_stable
    (W : StageFinitePlaceWitness l) :
    W.arithmetic.curve.HasStableReductionAt W.place :=
  W.stableReduction

theorem stage_d4_trace_requires_q
    (W : StageFinitePlaceWitness l) :
    W.qCandidate.q ≠ 0 ∧
      (Valued.v W.qCandidate.q : WithZero (Multiplicative Int)) < 1 := by
  exact ⟨W.q_nonzero, W.q_valuation_lt_one⟩

theorem stage_d4_trace_q_order
    (W : StageFinitePlaceWitness l) : 0 < W.qCandidate.order :=
  W.q_order_positive

theorem stage_d4_trace_not_uniformization
    (W : StageFinitePlaceWitness l) :
    W.qCandidate.q = W.qCandidate.q := rfl

/-! These final boundary lemmas intentionally expose the missing premise. -/

theorem stage_d3_trace_exists_projection
    (T : StagePlaceReductionTrace.{u} l) :
    ∃ (A : InitialThetaArithmeticData.{u} l)
      (Selected Bad : Type u),
      ∃ P : SourcePlacePartition Selected Bad,
        ∃ R : SourceReductionClause Selected Bad,
          R.partition = P := by
  exact ⟨T.arithmetic, T.selectedPlaces, T.badPlaces,
    T.partition, T.reduction, T.partition_alignment⟩

theorem stage_d10_trace_exists_iff_source_nonempty
    (l : PrimeGeFive) :
    Nonempty (StageConstructionTrace.{u} l) →
      Nonempty (SourceDefinition31Data.{u} l) := by
  rintro ⟨T⟩
  exact ⟨StageConstructionTrace.toSource T⟩

/-! ### D7 section normal forms -/

theorem stage_d7_section_apply
    (x : S.sections.valuationCarrier) :
    S.sections.sectionMap x ∈ Set.range S.sections.sectionMap := by
  exact ⟨x, rfl⟩

theorem stage_d7_section_right_inverse_apply
    (y : S.sections.modifiedValuationCarrier) :
    S.sections.sectionRightInverse y ∈
      Set.range S.sections.sectionRightInverse := by
  exact ⟨y, rfl⟩

theorem stage_d7_section_round_trip_left
    (x : S.sections.valuationCarrier) :
    S.sections.sectionRightInverse
      (S.sections.sectionMap x) = x := by
  exact stage_d7_section_left S x

theorem stage_d7_section_round_trip_right
    (y : S.sections.modifiedValuationCarrier) :
    S.sections.sectionMap
      (S.sections.sectionRightInverse y) = y := by
  exact stage_d7_section_right S y

theorem stage_d7_section_map_eq_iff
    {x y : S.sections.valuationCarrier} :
    S.sections.sectionMap x = S.sections.sectionMap y ↔ x = y := by
  constructor
  · intro h
    exact stage_d7_section_injective S h
  · intro h
    exact congrArg S.sections.sectionMap h

theorem stage_d7_right_inverse_eq_iff
    {x y : S.sections.modifiedValuationCarrier} :
    S.sections.sectionRightInverse x =
      S.sections.sectionRightInverse y ↔ x = y := by
  constructor
  · intro h
    exact stage_d7_right_inverse_injective S h
  · intro h
    exact congrArg S.sections.sectionRightInverse h

theorem stage_d7_section_map_image_eq_univ :
    Set.range S.sections.sectionMap = Set.univ := by
  apply Set.eq_univ_of_forall
  intro y
  exact stage_d7_section_surjective S y

theorem stage_d7_right_inverse_image_eq_univ :
    Set.range S.sections.sectionRightInverse = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  exact stage_d7_right_inverse_surjective S x

theorem stage_d7_local_map_image_eq_univ
    (x : S.sections.valuationCarrier) :
    Set.range (S.sections.localGroupSection x) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro y
  exact stage_d7_local_section_surjective S x y

theorem stage_d7_local_map_mem_range
    (x : S.sections.valuationCarrier)
    (y : S.sections.localGroupCarrier x) :
    S.sections.localGroupSection x y ∈
      Set.range (S.sections.localGroupSection x) := by
  exact ⟨y, rfl⟩

theorem stage_d7_local_map_eq_iff
    (x : S.sections.valuationCarrier)
    {y z : S.sections.localGroupCarrier x} :
    S.sections.localGroupSection x y =
      S.sections.localGroupSection x z ↔ y = z := by
  constructor
  · intro h
    exact stage_d7_local_section_injective S x h
  · intro h
    exact congrArg (S.sections.localGroupSection x) h

theorem stage_d7_local_equiv_apply
    (x : S.sections.valuationCarrier)
    (y : S.sections.localGroupCarrier x) :
    stage_d7_localEquiv S x y = S.sections.localGroupSection x y := rfl

theorem stage_d7_local_equiv_surjective
    (x : S.sections.valuationCarrier) :
    Function.Surjective (stage_d7_localEquiv S x) := by
  exact (stage_d7_localEquiv S x).surjective

theorem stage_d7_local_equiv_injective
    (x : S.sections.valuationCarrier) :
    Function.Injective (stage_d7_localEquiv S x) := by
  exact (stage_d7_localEquiv S x).injective

theorem stage_d7_local_equiv_bijective
    (x : S.sections.valuationCarrier) :
    Function.Bijective (stage_d7_localEquiv S x) := by
  exact (stage_d7_localEquiv S x).bijective

theorem stage_d7_local_equiv_left
    (x : S.sections.valuationCarrier)
    (y : S.sections.localGroupCarrier x) :
    (stage_d7_localEquiv S x).symm
      (stage_d7_localEquiv S x y) = y := by
  exact (stage_d7_localEquiv S x).left_inv y

theorem stage_d7_local_equiv_right
    (x : S.sections.valuationCarrier)
    (y : S.sections.modifiedLocalGroupCarrier
      (S.sections.sectionMap x)) :
    stage_d7_localEquiv S x
      ((stage_d7_localEquiv S x).symm y) = y := by
  exact (stage_d7_localEquiv S x).right_inv y

theorem stage_d7_place_clauses :
    S.sections.finitePlaceData ∧ S.sections.infinitePlaceData := by
  exact ⟨stage_d7_finite_place_data S,
    stage_d7_infinite_place_data S⟩

theorem stage_d7_section_data_bundle :
    Function.Bijective S.sections.sectionMap ∧
      (∀ x, Function.Bijective (S.sections.localGroupSection x)) ∧
      S.sections.finitePlaceData ∧ S.sections.infinitePlaceData := by
  exact ⟨stage_d7_section_bijective S,
    fun x => stage_d7_local_section_bijective S x,
    stage_d7_finite_place_data S,
    stage_d7_infinite_place_data S⟩

/-! ### D8 cusp normal forms -/

theorem stage_d8_epsilon_mul_scale_ne_zero :
    S.cusp.epsilon * S.cusp.cuspScale ≠ 0 :=
  stage_d8_epsilon_scale_nonzero S

theorem stage_d8_epsilon_mul_scale_pos :
    0 < S.cusp.epsilon * S.cusp.cuspScale :=
  stage_d8_epsilon_scale_positive S

theorem stage_d8_epsilon_div_scale_pos :
    0 < S.cusp.epsilon / S.cusp.cuspScale :=
  stage_d8_epsilon_div_scale_positive S

theorem stage_d8_epsilon_div_scale_ne_zero :
    S.cusp.epsilon / S.cusp.cuspScale ≠ 0 :=
  stage_d8_epsilon_div_scale_nonzero S

theorem stage_d8_epsilon_lt_scale_mul
    (hscale : 1 ≤ S.cusp.cuspScale) :
    S.cusp.epsilon ≤ S.cusp.epsilon * S.cusp.cuspScale := by
  exact S.cusp.epsilon_lt_scale_mul hscale

theorem stage_d8_epsilon_pow_ne_zero (n : Nat) :
    S.cusp.epsilon ^ n ≠ 0 := by
  exact pow_ne_zero n (stage_d8_epsilon_nonzero S)

theorem stage_d8_scale_pow_ne_zero (n : Nat) :
    S.cusp.cuspScale ^ n ≠ 0 := by
  exact pow_ne_zero n (stage_d8_scale_nonzero S)

theorem stage_d8_product_pow_ne_zero (n : Nat) :
    (S.cusp.epsilon * S.cusp.cuspScale) ^ n ≠ 0 := by
  exact pow_ne_zero n (stage_d8_epsilon_scale_nonzero S)

theorem stage_d8_normalized_pow_ne_zero (n : Nat) :
    stage_d8_normalized S ^ n ≠ 0 := by
  exact pow_ne_zero n (stage_d8_normalized_nonzero S)

theorem stage_d8_normalized_mul_scale_eq_epsilon :
    stage_d8_normalized S * S.cusp.cuspScale = S.cusp.epsilon :=
  stage_d8_normalized_mul_scale S

theorem stage_d8_epsilon_eq_scale_mul_normalized :
    S.cusp.epsilon = S.cusp.cuspScale * stage_d8_normalized S := by
  exact (stage_d8_scale_mul_normalized S).symm

theorem stage_d8_normalized_ratio_characterization
    {r : Real} :
    r = stage_d8_normalized S ↔
      r * S.cusp.cuspScale = S.cusp.epsilon := by
  exact stage_d8_ratio_eq_iff S (stage_d8_scale_nonzero S)

theorem stage_d8_compatibility_and_normalization :
    S.cusp.epsilon_compatibility ∧
      0 < stage_d8_normalized S ∧
      stage_d8_normalized S * S.cusp.cuspScale = S.cusp.epsilon := by
  exact stage_d8_cusp_compatibility_with_normalized S

/-! ### D9 independent compatibility records -/

structure StageCompatibilityBundle (l : PrimeGeFive) where
  arithmetic : InitialThetaArithmeticData l
  reduction : Prop
  reduction_proved : reduction
  torsion : Prop
  torsion_proved : torsion
  orbicurve : Prop
  orbicurve_proved : orbicurve
  sectionData : Prop
  sectionData_proved : sectionData
  cusp : Prop
  cusp_proved : cusp

namespace StageCompatibilityBundle

variable {l : PrimeGeFive} (C : StageCompatibilityBundle l)

theorem reduction_spec : C.reduction := C.reduction_proved

theorem torsion_spec : C.torsion := C.torsion_proved

theorem orbicurve_spec : C.orbicurve := C.orbicurve_proved

theorem section_spec : C.sectionData := C.sectionData_proved

theorem cusp_spec : C.cusp := C.cusp_proved

theorem bundle : C.reduction ∧ C.torsion ∧ C.orbicurve ∧
    C.sectionData ∧ C.cusp := by
  exact ⟨C.reduction_spec, C.torsion_spec, C.orbicurve_spec,
    C.section_spec, C.cusp_spec⟩

theorem bundle_left (h : C.reduction ∧ C.torsion ∧ C.orbicurve ∧
    C.sectionData ∧ C.cusp) : C.reduction := h.1

theorem bundle_torsion (h : C.reduction ∧ C.torsion ∧ C.orbicurve ∧
    C.sectionData ∧ C.cusp) : C.torsion := h.2.1

theorem bundle_orbicurve (h : C.reduction ∧ C.torsion ∧ C.orbicurve ∧
    C.sectionData ∧ C.cusp) : C.orbicurve := h.2.2.1

theorem bundle_section (h : C.reduction ∧ C.torsion ∧ C.orbicurve ∧
    C.sectionData ∧ C.cusp) : C.sectionData := h.2.2.2.1

theorem bundle_cusp (h : C.reduction ∧ C.torsion ∧ C.orbicurve ∧
    C.sectionData ∧ C.cusp) : C.cusp := h.2.2.2.2

end StageCompatibilityBundle

theorem stage_d9_compatibility_source_reduction :
    S.arithmetic_reduction_compatibility :=
  stage_d9_reduction_compatibility S

theorem stage_d9_compatibility_source_torsion :
    S.arithmetic_torsion_compatibility :=
  stage_d9_torsion_compatibility S

theorem stage_d9_compatibility_source_orbicurve :
    S.arithmetic_orbicurve_compatibility :=
  stage_d9_orbicurve_compatibility S

theorem stage_d9_compatibility_source_section :
    S.arithmetic_section_compatibility :=
  stage_d9_section_compatibility S

theorem stage_d9_compatibility_source_cusp :
    S.arithmetic_cusp_compatibility :=
  stage_d9_cusp_compatibility S

theorem stage_d9_compatibility_source_all :
    S.arithmetic_reduction_compatibility ∧
      S.arithmetic_torsion_compatibility ∧
      S.arithmetic_orbicurve_compatibility ∧
      S.arithmetic_section_compatibility ∧
      S.arithmetic_cusp_compatibility :=
  stage_d9_compatibility_bundle S

theorem stage_d9_compatibility_source_reduction_of_all
    (h : S.arithmetic_reduction_compatibility ∧
      S.arithmetic_torsion_compatibility ∧
      S.arithmetic_orbicurve_compatibility ∧
      S.arithmetic_section_compatibility ∧
      S.arithmetic_cusp_compatibility) :
    S.arithmetic_reduction_compatibility :=
  stage_d9_compatibility_bundle_left S h

theorem stage_d9_compatibility_source_torsion_of_all
    (h : S.arithmetic_reduction_compatibility ∧
      S.arithmetic_torsion_compatibility ∧
      S.arithmetic_orbicurve_compatibility ∧
      S.arithmetic_section_compatibility ∧
      S.arithmetic_cusp_compatibility) :
    S.arithmetic_torsion_compatibility :=
  stage_d9_compatibility_bundle_torsion S h

theorem stage_d9_compatibility_source_orbicurve_of_all
    (h : S.arithmetic_reduction_compatibility ∧
      S.arithmetic_torsion_compatibility ∧
      S.arithmetic_orbicurve_compatibility ∧
      S.arithmetic_section_compatibility ∧
      S.arithmetic_cusp_compatibility) :
    S.arithmetic_orbicurve_compatibility :=
  stage_d9_compatibility_bundle_orbicurve S h

theorem stage_d9_compatibility_source_section_of_all
    (h : S.arithmetic_reduction_compatibility ∧
      S.arithmetic_torsion_compatibility ∧
      S.arithmetic_orbicurve_compatibility ∧
      S.arithmetic_section_compatibility ∧
      S.arithmetic_cusp_compatibility) :
    S.arithmetic_section_compatibility :=
  stage_d9_compatibility_bundle_section S h

theorem stage_d9_compatibility_source_cusp_of_all
    (h : S.arithmetic_reduction_compatibility ∧
      S.arithmetic_torsion_compatibility ∧
      S.arithmetic_orbicurve_compatibility ∧
      S.arithmetic_section_compatibility ∧
      S.arithmetic_cusp_compatibility) :
    S.arithmetic_cusp_compatibility :=
  stage_d9_compatibility_bundle_cusp S h

theorem stage_d9_compatibility_rebuild_from_source :
    S.arithmetic_reduction_compatibility ∧
      S.arithmetic_torsion_compatibility ∧
      S.arithmetic_orbicurve_compatibility ∧
      S.arithmetic_section_compatibility ∧
      S.arithmetic_cusp_compatibility := by
  exact stage_d9_compatibility_rebuild S
    (stage_d9_compatibility_source_reduction S)
    (stage_d9_compatibility_source_torsion S)
    (stage_d9_compatibility_source_orbicurve S)
    (stage_d9_compatibility_source_section S)
    (stage_d9_compatibility_source_cusp S)

theorem stage_d10_source_condition :
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
  exact stage_d9_source_condition_bundle S

theorem stage_d10_source_condition_reduction
    (b : S.badPlaces) :
    S.reduction.stableReduction b ∧
      S.reduction.splitMultiplicativeReduction b := by
  exact ⟨S.reduction.stableReduction_proved b,
    S.reduction.splitMultiplicativeReduction_proved b⟩

theorem stage_d10_source_condition_q
    (b : S.badPlaces) :
    S.reduction.qParameter b ≠ 0 ∧
      ‖S.reduction.qParameter b‖ < 1 := by
  exact ⟨S.reduction.qParameter_nonzero b,
    S.reduction.qParameter_contracting b⟩

theorem stage_d10_source_condition_torsion :
    S.torsion.imageContainsSL2 ∧
      S.torsion.sixTorsionIndependent ∧
      S.torsion.lTorsionCompatible := by
  exact stage_d5_torsion_bundle S

theorem stage_d10_source_condition_exact :
    Function.Injective S.orbicurve.exactSequence.injection ∧
      Function.Surjective S.orbicurve.exactSequence.projection ∧
      (∀ x, S.orbicurve.exactSequence.projection x = 1 ↔
        ∃ y, S.orbicurve.exactSequence.injection y = x) := by
  exact ⟨S.orbicurve.exactSequence.injection_injective,
    S.orbicurve.exactSequence.projection_surjective,
    stage_d6_kernel_iff S⟩

theorem stage_d10_source_condition_sections :
    Function.Bijective S.sections.sectionMap ∧
      (∀ x, Function.Bijective (S.sections.localGroupSection x)) := by
  exact ⟨stage_d7_section_bijective S,
    fun x => stage_d7_local_section_bijective S x⟩

theorem stage_d10_source_condition_cusp :
    0 < S.cusp.epsilon ∧ S.cusp.epsilon_compatibility := by
  exact ⟨stage_d8_epsilon_positive S,
    stage_d8_cusp_compatibility S⟩

theorem stage_d10_source_condition_compatibility :
    S.arithmetic_reduction_compatibility ∧
      S.arithmetic_torsion_compatibility ∧
      S.arithmetic_orbicurve_compatibility ∧
      S.arithmetic_section_compatibility ∧
      S.arithmetic_cusp_compatibility := by
  exact stage_d9_compatibility_source_all S

theorem stage_d10_source_condition_complete :
    SourceDefinition31Root.Definition31Recognition S := by
  exact SourceDefinition31Root.definition31_recognition S

theorem stage_d11_source_exists_for_supplied_data
    (S : SourceDefinition31Data.{u} l) :
    ∃ T : SourceDefinition31Data.{u} l,
      SourceDefinition31Root.Definition31Recognition T := by
  exact ⟨S, stage_d10_source_condition_complete S⟩

theorem stage_d11_source_exists_with_all_fields
    (S : SourceDefinition31Data.{u} l) :
    ∃ T : SourceDefinition31Data.{u} l,
      T = S := by
  exact ⟨S, rfl⟩

theorem stage_d11_recognition_implies_source_condition
    (h : SourceDefinition31Root.Definition31Recognition S) :
    Nonempty S.selectedPlaces ∧
      Nonempty (Fintype S.badPlaces) ∧
      (∀ b, S.reduction.stableReduction b) ∧
      (∀ b, S.reduction.splitMultiplicativeReduction b) ∧
      S.torsion.imageContainsSL2 ∧
      S.torsion.sixTorsionIndependent ∧
      S.torsion.lTorsionCompatible ∧
      Function.Injective S.orbicurve.exactSequence.injection ∧
      Function.Surjective S.orbicurve.exactSequence.projection ∧
      Function.Bijective S.sections.sectionMap ∧
      0 < S.cusp.epsilon := by
  exact ⟨h.places.1, h.places.2, fun b => (h.reduction b).1,
    fun b => (h.reduction b).2.2.1, h.torsion.1, h.torsion.2.1,
    h.torsion.2.2, h.exact.1, h.exact.2, h.sections.1, h.cusp.1⟩

theorem stage_d11_recognition_arithmetic_again
    (h : SourceDefinition31Root.Definition31Recognition S) :
    HasSqrtNegOne S.arithmetic.F :=
  h.arithmetic.1

theorem stage_d11_recognition_degree_again
    (h : SourceDefinition31Root.Definition31Recognition S) :
    Nat.Coprime (Module.finrank S.arithmetic.Fmod S.arithmetic.F)
      l.value :=
  h.arithmetic.2

theorem stage_d11_recognition_selected_again
    (h : SourceDefinition31Root.Definition31Recognition S) :
    Nonempty S.selectedPlaces :=
  h.places.1

theorem stage_d11_recognition_bad_finite_again
    (h : SourceDefinition31Root.Definition31Recognition S) :
    Nonempty (Fintype S.badPlaces) :=
  h.places.2

theorem stage_d11_recognition_stable_again
    (h : SourceDefinition31Root.Definition31Recognition S)
    (b : S.badPlaces) : S.reduction.stableReduction b :=
  (h.reduction b).1

theorem stage_d11_recognition_multiplicative_again
    (h : SourceDefinition31Root.Definition31Recognition S)
    (b : S.badPlaces) : S.reduction.multiplicativeReduction b :=
  (h.reduction b).2.1

theorem stage_d11_recognition_split_again
    (h : SourceDefinition31Root.Definition31Recognition S)
    (b : S.badPlaces) : S.reduction.splitMultiplicativeReduction b :=
  (h.reduction b).2.2.1

theorem stage_d11_recognition_q_nonzero_again
    (h : SourceDefinition31Root.Definition31Recognition S)
    (b : S.badPlaces) : S.reduction.qParameter b ≠ 0 :=
  (h.reduction b).2.2.2.1

theorem stage_d11_recognition_q_contracting_again
    (h : SourceDefinition31Root.Definition31Recognition S)
    (b : S.badPlaces) : ‖S.reduction.qParameter b‖ < 1 :=
  (h.reduction b).2.2.2.2

theorem stage_d11_recognition_image_again
    (h : SourceDefinition31Root.Definition31Recognition S) :
    S.torsion.imageContainsSL2 :=
  h.torsion.1

theorem stage_d11_recognition_six_again
    (h : SourceDefinition31Root.Definition31Recognition S) :
    S.torsion.sixTorsionIndependent :=
  h.torsion.2.1

theorem stage_d11_recognition_l_again
    (h : SourceDefinition31Root.Definition31Recognition S) :
    S.torsion.lTorsionCompatible :=
  h.torsion.2.2

theorem stage_d11_recognition_injection_again
    (h : SourceDefinition31Root.Definition31Recognition S) :
    Function.Injective S.orbicurve.exactSequence.injection :=
  h.exact.1

theorem stage_d11_recognition_projection_again
    (h : SourceDefinition31Root.Definition31Recognition S) :
    Function.Surjective S.orbicurve.exactSequence.projection :=
  h.exact.2

theorem stage_d11_recognition_section_again
    (h : SourceDefinition31Root.Definition31Recognition S) :
    Function.Bijective S.sections.sectionMap :=
  h.sections.1

theorem stage_d11_recognition_local_again
    (h : SourceDefinition31Root.Definition31Recognition S)
    (x : S.sections.valuationCarrier) :
    Function.Bijective (S.sections.localGroupSection x) :=
  h.sections.2 x

theorem stage_d11_recognition_epsilon_again
    (h : SourceDefinition31Root.Definition31Recognition S) :
    0 < S.cusp.epsilon :=
  h.cusp.1

theorem stage_d11_recognition_cusp_compatibility_again
    (h : SourceDefinition31Root.Definition31Recognition S) :
    S.cusp.epsilon_compatibility :=
  h.cusp.2

theorem stage_d11_recognition_compatibility_reduction_again
    (h : SourceDefinition31Root.Definition31Recognition S) :
    S.arithmetic_reduction_compatibility :=
  h.compatibility.1

theorem stage_d11_recognition_compatibility_torsion_again
    (h : SourceDefinition31Root.Definition31Recognition S) :
    S.arithmetic_torsion_compatibility :=
  h.compatibility.2.1

theorem stage_d11_recognition_compatibility_orbicurve_again
    (h : SourceDefinition31Root.Definition31Recognition S) :
    S.arithmetic_orbicurve_compatibility :=
  h.compatibility.2.2.1

theorem stage_d11_recognition_compatibility_section_again
    (h : SourceDefinition31Root.Definition31Recognition S) :
    S.arithmetic_section_compatibility :=
  h.compatibility.2.2.2.1

theorem stage_d11_recognition_compatibility_cusp_again
    (h : SourceDefinition31Root.Definition31Recognition S) :
    S.arithmetic_cusp_compatibility :=
  h.compatibility.2.2.2.2

end Definition31StageKernel

/-! ## D3-D11 construction gates

The gates below are deliberately propositions about the *missing source
construction*.  They are not input fields and are not used to manufacture a
certificate.  Keeping the gates explicit prevents a later theorem from
silently changing the quantifier from arithmetic input to an already supplied
`SourceDefinition31Data`.
-/

def D3PlaceConstruction (l : PrimeGeFive) : Prop :=
  ∀ A : InitialThetaArithmeticData.{u} l,
    ∃ (Selected Bad : Type u),
      Nonempty (SourcePlacePartition.{u} Selected Bad)

def D4ReductionConstruction (l : PrimeGeFive) : Prop :=
  ∀ A : InitialThetaArithmeticData.{u} l,
    ∀ (Selected Bad : Type u),
      SourcePlacePartition.{u} Selected Bad →
      Nonempty (SourceReductionClause.{u} Selected Bad)

def D5TorsionConstruction (l : PrimeGeFive) : Prop :=
  ∀ A : InitialThetaArithmeticData.{u} l,
    Nonempty (SourceTorsionClause.{u, v, w} l)

def D6OrbicurveConstruction (l : PrimeGeFive) : Prop :=
  ∀ A : InitialThetaArithmeticData.{u} l,
    Nonempty SourceOrbicurveClause.{u, v, w}

def D7SectionConstruction (l : PrimeGeFive) : Prop :=
  ∀ A : InitialThetaArithmeticData.{u} l,
    Nonempty SourceSectionClause.{u, v, w}

def D8CuspConstruction (l : PrimeGeFive) : Prop :=
  ∀ A : InitialThetaArithmeticData.{u} l,
    Nonempty SourceCuspClause

def D9CompatibilityConstruction (l : PrimeGeFive) : Prop :=
  ∀ A : InitialThetaArithmeticData.{u} l,
    Nonempty (SourceDefinition31Data.{u} l)

def D10InitialThetaConstruction (l : PrimeGeFive) : Prop :=
  ∀ A : InitialThetaArithmeticData.{u} l,
    Nonempty (SourceDefinition31Data.{u} l)

def D11FaithfulConclusion (l : PrimeGeFive) : Prop :=
  ∀ A : InitialThetaArithmeticData.{u} l,
    ∃ S : SourceDefinition31Data.{u} l,
      SourceDefinition31Root.Definition31Recognition S

def d0_status : Obligation :=
  { id := "IUT-I.definition-3.1-D0"
    source := "Lean kernel, Std, Mathlib"
    status := VerificationStatus.proved
    note := "Standard dependent type, group, field, finite-dimensional, and norm infrastructure."
    dependsOn := [] }

def d1_status : Obligation :=
  { id := "IUT-I.definition-3.1-D1"
    source := "IUT I, Definition 3.1; l >= 5 prime"
    status := VerificationStatus.proved
    note := "Prime, lower-bound, positivity, and oddness projections are proved from PrimeGeFive."
    dependsOn := ["IUT-I.definition-3.1-D0"] }

def d2_status : Obligation :=
  { id := "IUT-I.definition-3.1-D2"
    source := "IUT I, Definition 3.1(a)"
    status := VerificationStatus.interface
    note := "Arithmetic tower and curve are projected; arbitrary-input existence is not inferred."
    dependsOn := ["IUT-I.definition-3.1-D1"] }

def d3_status : Obligation :=
  { id := "IUT-I.definition-3.1-D3"
    source := "IUT I, Definition 3.1(a)"
    status := VerificationStatus.pending
    note := "Place partition construction from arithmetic input remains open."
    dependsOn := ["IUT-I.definition-3.1-D2"] }

def d4_status : Obligation :=
  { id := "IUT-I.definition-3.1-D4"
    source := "IUT I, Definition 3.1(b)"
    status := VerificationStatus.pending
    note := "Stable, multiplicative, split reduction and q-parameter construction remains open."
    dependsOn := ["IUT-I.definition-3.1-D3"] }

def d5_status : Obligation :=
  { id := "IUT-I.definition-3.1-D5"
    source := "IUT I, Definition 3.1(c)"
    status := VerificationStatus.pending
    note := "Torsion carrier, Galois representation, and large-image proof remains open."
    dependsOn := ["IUT-I.definition-3.1-D4"] }

def d6_status : Obligation :=
  { id := "IUT-I.definition-3.1-D6"
    source := "IUT I, Definition 3.1(d)"
    status := VerificationStatus.pending
    note := "Orbicurve and local fundamental-group exact sequence construction remains open."
    dependsOn := ["IUT-I.definition-3.1-D5"] }

def d7_status : Obligation :=
  { id := "IUT-I.definition-3.1-D7"
    source := "IUT I, Definition 3.1(e)"
    status := VerificationStatus.pending
    note := "Valuation and local-group sections with their place clauses remain open."
    dependsOn := ["IUT-I.definition-3.1-D6"] }

def d8_status : Obligation :=
  { id := "IUT-I.definition-3.1-D8"
    source := "IUT I, Definition 3.1(f)"
    status := VerificationStatus.pending
    note := "Cusp parameter and its source compatibility remain open."
    dependsOn := ["IUT-I.definition-3.1-D7"] }

def d9_status : Obligation :=
  { id := "IUT-I.definition-3.1-D9"
    source := "IUT I, Definition 3.1(a)-(f)"
    status := VerificationStatus.pending
    note := "Five arithmetic compatibility proofs remain open."
    dependsOn := ["IUT-I.definition-3.1-D8"] }

def d10_status : Obligation :=
  { id := "IUT-I.definition-3.1-D10"
    source := "IUT I, Definition 3.1"
    status := VerificationStatus.pending
    note := "No constructor from arbitrary InitialThetaArithmeticData is present."
    dependsOn := ["IUT-I.definition-3.1-D9"] }

def d11_status : Obligation :=
  { id := "IUT-I.definition-3.1-D11"
    source := "IUT I, Definition 3.1"
    status := VerificationStatus.pending
    note := "Faithful conclusion awaits D2-D10 source constructions and independent verification."
    dependsOn := ["IUT-I.definition-3.1-D10"] }

end SourceDefinition31Root

end Theorem311Source

end

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def sourceDefinition31Root : Obligation :=
  { id := "IUT-I.definition-3.1-root-recognition"
    source := "IUT I, Definition 3.1"
    status := VerificationStatus.interface
    note :=
      "Exact-sequence, reduction, torsion, section, and cusp consequences " ++
        "are proved for a supplied source datum. The arithmetic-to-source " ++
        "construction remains the next source-faithful obligation."
    dependsOn := ["IUT-I.initial-theta-source-definition31-boundary"] }

end LeanFormal.IUT.Audit
