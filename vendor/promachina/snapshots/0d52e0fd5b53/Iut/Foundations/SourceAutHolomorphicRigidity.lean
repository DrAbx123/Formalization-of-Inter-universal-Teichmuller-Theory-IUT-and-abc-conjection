/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceArchimedeanSemiGerm
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Topology.Algebra.IsOpenUnits

/-!
# Rigidity of the archimedean Aut-holomorphic group germ

IUT I, Remark 3.4.2 uses the elementary rigidity statement that a holomorphic
automorphism of the complex Lie group `ℂˣ` which preserves the norm-at-most-one
submonoid is the identity.  IUT III, Remark 1.1.1(ii) applies the same statement
to the Aut-holomorphic semi-germ along `S¹`, with the inner component selected.

This module defines the automorphism as an actual continuous multiplicative
equivalence with holomorphic forward and inverse maps.  The proof below derives
its exponent from the exponential covering and then uses the selected side to
rule out inversion.
-/

open Set

namespace Iut

noncomputable section

namespace SourceAutHolomorphicRigidity

open SourceAutHolomorphic

/-- The connected complex open `ℂˣ = ℂ \ {0}`. -/
def puncturedPlane : ConnectedOpen where
  carrier := ({0} : Set ℂ)ᶜ
  isOpen_carrier := isOpen_compl_singleton
  isConnected_carrier :=
    isConnected_compl_singleton_of_one_lt_rank (E := ℂ) (by
      rw [Complex.rank_real_complex]
      norm_num) 0

@[simp]
theorem mem_puncturedPlane_iff (value : ℂ) :
    value ∈ puncturedPlane.carrier ↔ value ≠ 0 := by
  simp [puncturedPlane]

/-- The standard homeomorphism from complex units to the punctured plane. -/
def unitsHomeomorph : ℂˣ ≃ₜ puncturedPlane.carrier := by
  simpa only [puncturedPlane, Set.mem_compl_iff, Set.mem_singleton_iff] using
    (unitsHomeomorphNeZero : ℂˣ ≃ₜ {value : ℂ // value ≠ 0})

@[simp]
theorem unitsHomeomorph_coe (unit : ℂˣ) :
    (unitsHomeomorph unit : ℂ) = unit := by
  rfl

@[simp]
theorem unitsHomeomorph_symm_coe (value : puncturedPlane.carrier) :
    ((unitsHomeomorph.symm value : ℂˣ) : ℂ) = value := by
  simpa only [unitsHomeomorph_coe] using congrArg Subtype.val
    (unitsHomeomorph.apply_symm_apply value)

@[simp]
theorem unitsHomeomorph_symm_eq_mk0 (value : puncturedPlane.carrier) :
    unitsHomeomorph.symm value =
      Units.mk0 (value : ℂ) ((mem_puncturedPlane_iff value).mp value.2) := by
  ext
  exact unitsHomeomorph_symm_coe value

@[simp]
theorem unitsHomeomorph_mk0 (value : ℂ) (hvalue : value ≠ 0) :
    unitsHomeomorph (Units.mk0 value hvalue) =
      (⟨value, (mem_puncturedPlane_iff value).mpr hvalue⟩ :
        puncturedPlane.carrier) := by
  apply Subtype.ext
  rfl

/--
An actual holomorphic automorphism of the complex Lie group `ℂˣ`.  The
continuous multiplicative equivalence supplies the group automorphism; the two
lift fields say that both directions are holomorphic on the punctured plane.
-/
structure Automorphism where
  toContinuousMulEquiv : ℂˣ ≃ₜ* ℂˣ
  holomorphic :
    HasAmbientHolomorphicLift puncturedPlane puncturedPlane
      (fun value ↦ unitsHomeomorph
        (toContinuousMulEquiv (unitsHomeomorph.symm value)))
  holomorphic_symm :
    HasAmbientHolomorphicLift puncturedPlane puncturedPlane
      (fun value ↦ unitsHomeomorph
        (toContinuousMulEquiv.symm (unitsHomeomorph.symm value)))

namespace Automorphism

/-- The induced self-map of the punctured complex plane. -/
def puncturedMap (automorphism : Automorphism) :
    puncturedPlane.carrier → puncturedPlane.carrier :=
  fun value ↦ unitsHomeomorph
    (automorphism.toContinuousMulEquiv (unitsHomeomorph.symm value))

/-- The inverse self-map of the punctured complex plane. -/
def puncturedMapInv (automorphism : Automorphism) :
    puncturedPlane.carrier → puncturedPlane.carrier :=
  fun value ↦ unitsHomeomorph
    (automorphism.toContinuousMulEquiv.symm (unitsHomeomorph.symm value))

@[simp]
theorem puncturedMapInv_apply_puncturedMap
    (automorphism : Automorphism) (value : puncturedPlane.carrier) :
    automorphism.puncturedMapInv (automorphism.puncturedMap value) = value := by
  simp [puncturedMap, puncturedMapInv]

@[simp]
theorem puncturedMap_apply_puncturedMapInv
    (automorphism : Automorphism) (value : puncturedPlane.carrier) :
    automorphism.puncturedMap (automorphism.puncturedMapInv value) = value := by
  simp [puncturedMap, puncturedMapInv]

/-- The group automorphism as an element of the derived assignment
`Aut_hol(ℂˣ)`. -/
def toAutHolomorphic (automorphism : Automorphism) :
    AutHolomorphic puncturedPlane := by
  let homeomorphism :
      puncturedPlane.carrier ≃ₜ puncturedPlane.carrier :=
    unitsHomeomorph.symm.trans
      (automorphism.toContinuousMulEquiv.toHomeomorph.trans unitsHomeomorph)
  refine ⟨homeomorphism, ?_⟩
  change HasAmbientHolomorphicLift puncturedPlane puncturedPlane homeomorphism ∧
    HasAmbientHolomorphicLift puncturedPlane puncturedPlane homeomorphism.symm
  constructor
  · simpa only [homeomorphism, Homeomorph.trans_apply] using automorphism.holomorphic
  · simpa only [homeomorphism, Homeomorph.symm_trans_apply] using
      automorphism.holomorphic_symm

/-- A chosen ambient representative of the forward holomorphic map. -/
def ambient (automorphism : Automorphism) : ℂ → ℂ :=
  Classical.choose automorphism.holomorphic

theorem ambient_differentiableOn (automorphism : Automorphism) :
    DifferentiableOn ℂ automorphism.ambient puncturedPlane.carrier :=
  (Classical.choose_spec automorphism.holomorphic).1

theorem ambient_eq
    (automorphism : Automorphism) (value : puncturedPlane.carrier) :
    automorphism.ambient value = automorphism.puncturedMap value :=
  (Classical.choose_spec automorphism.holomorphic).2 value

theorem ambient_ne_zero
    (automorphism : Automorphism) {value : ℂ} (hvalue : value ≠ 0) :
    automorphism.ambient value ≠ 0 := by
  rw [automorphism.ambient_eq ⟨value, by simpa [mem_puncturedPlane_iff]⟩]
  exact (automorphism.puncturedMap
    ⟨value, by simpa [mem_puncturedPlane_iff]⟩).2

theorem ambient_one (automorphism : Automorphism) :
    automorphism.ambient 1 = 1 := by
  rw [automorphism.ambient_eq ⟨1, by simp [mem_puncturedPlane_iff]⟩]
  simp only [puncturedMap, unitsHomeomorph_coe,
    unitsHomeomorph_symm_eq_mk0]
  rw [show Units.mk0 (1 : ℂ) (by simp) = (1 : ℂˣ) by ext; rfl]
  rw [map_one]
  rfl

theorem ambient_mul
    (automorphism : Automorphism)
    {first second : ℂ} (hfirst : first ≠ 0) (hsecond : second ≠ 0) :
    automorphism.ambient (first * second) =
      automorphism.ambient first * automorphism.ambient second := by
  rw [automorphism.ambient_eq
      ⟨first * second, mul_ne_zero hfirst hsecond⟩,
    automorphism.ambient_eq ⟨first, hfirst⟩,
    automorphism.ambient_eq ⟨second, hsecond⟩]
  simp only [puncturedMap, unitsHomeomorph_coe,
    unitsHomeomorph_symm_eq_mk0]
  change
    ((automorphism.toContinuousMulEquiv
      (Units.mk0 (first * second) (mul_ne_zero hfirst hsecond)) : ℂˣ) : ℂ) =
      ((automorphism.toContinuousMulEquiv (Units.mk0 first hfirst) : ℂˣ) : ℂ) *
        ((automorphism.toContinuousMulEquiv (Units.mk0 second hsecond) : ℂˣ) : ℂ)
  rw [show Units.mk0 (first * second) (mul_ne_zero hfirst hsecond) =
      Units.mk0 first hfirst * Units.mk0 second hsecond by ext; rfl,
    map_mul]
  rfl

/-- Pullback of the automorphism along the exponential covering. -/
def exponentialLift (automorphism : Automorphism) (value : ℂ) : ℂ :=
  automorphism.ambient (Complex.exp value)

theorem exponentialLift_differentiable (automorphism : Automorphism) :
    Differentiable ℂ automorphism.exponentialLift := by
  intro value
  have hexpMem : Complex.exp value ∈ puncturedPlane.carrier := by
    simp [mem_puncturedPlane_iff]
  have hambient : DifferentiableAt ℂ automorphism.ambient (Complex.exp value) :=
    automorphism.ambient_differentiableOn.differentiableAt
      (puncturedPlane.isOpen_carrier.mem_nhds hexpMem)
  change DifferentiableAt ℂ (automorphism.ambient ∘ Complex.exp) value
  exact hambient.comp value (Complex.hasDerivAt_exp value).differentiableAt

@[simp]
theorem exponentialLift_zero (automorphism : Automorphism) :
    automorphism.exponentialLift 0 = 1 := by
  simp [exponentialLift, automorphism.ambient_one]

theorem exponentialLift_add
    (automorphism : Automorphism) (first second : ℂ) :
    automorphism.exponentialLift (first + second) =
      automorphism.exponentialLift first * automorphism.exponentialLift second := by
  rw [exponentialLift, Complex.exp_add,
    automorphism.ambient_mul (Complex.exp_ne_zero first)
      (Complex.exp_ne_zero second)]
  rfl

/-- The infinitesimal exponent of the pulled-back multiplicative map. -/
def exponentCoefficient (automorphism : Automorphism) : ℂ :=
  deriv automorphism.exponentialLift 0

theorem deriv_exponentialLift (automorphism : Automorphism) (value : ℂ) :
    deriv automorphism.exponentialLift value =
      automorphism.exponentialLift value * automorphism.exponentCoefficient := by
  let shifted : ℂ → ℂ := fun increment ↦
    automorphism.exponentialLift (value + increment)
  let multiplied : ℂ → ℂ := fun increment ↦
    automorphism.exponentialLift value * automorphism.exponentialLift increment
  have hfunctions : shifted = multiplied := by
    funext increment
    exact automorphism.exponentialLift_add value increment
  calc
    deriv automorphism.exponentialLift value = deriv shifted 0 := by
      simpa only [shifted, add_zero] using
        (deriv_comp_const_add automorphism.exponentialLift value 0).symm
    _ = deriv multiplied 0 := by rw [hfunctions]
    _ = automorphism.exponentialLift value *
        deriv automorphism.exponentialLift 0 := by
      exact deriv_const_mul _
        (automorphism.exponentialLift_differentiable 0)
    _ = automorphism.exponentialLift value *
        automorphism.exponentCoefficient := rfl

/-- The exponential lift after cancelling its infinitesimal exponential. -/
def normalizedLift (automorphism : Automorphism) (value : ℂ) : ℂ :=
  automorphism.exponentialLift value *
    Complex.exp (-(automorphism.exponentCoefficient * value))

theorem normalizedLift_differentiable (automorphism : Automorphism) :
    Differentiable ℂ automorphism.normalizedLift := by
  intro value
  have hlinear : HasDerivAt
      (fun input : ℂ ↦ -(automorphism.exponentCoefficient * input))
      (-automorphism.exponentCoefficient) value := by
    simpa only [neg_mul] using
      (hasDerivAt_const_mul automorphism.exponentCoefficient).neg
  exact (automorphism.exponentialLift_differentiable value).mul
    ((Complex.hasDerivAt_exp _).comp value hlinear).differentiableAt

theorem deriv_normalizedLift_eq_zero
    (automorphism : Automorphism) (value : ℂ) :
    deriv automorphism.normalizedLift value = 0 := by
  have hlinear : HasDerivAt
      (fun input : ℂ ↦ -(automorphism.exponentCoefficient * input))
      (-automorphism.exponentCoefficient) value := by
    simpa only [neg_mul] using
      (hasDerivAt_const_mul automorphism.exponentCoefficient).neg
  have hexponential : HasDerivAt
      (fun input : ℂ ↦
        Complex.exp (-(automorphism.exponentCoefficient * input)))
      (Complex.exp (-(automorphism.exponentCoefficient * value)) *
        (-automorphism.exponentCoefficient)) value :=
    (Complex.hasDerivAt_exp _).comp value hlinear
  have hproduct :=
    (automorphism.exponentialLift_differentiable value).hasDerivAt.mul
      hexponential
  have hproduct' : HasDerivAt
      (fun input ↦ automorphism.exponentialLift input *
        Complex.exp (-(automorphism.exponentCoefficient * input)))
      (deriv automorphism.exponentialLift value *
          Complex.exp (-(automorphism.exponentCoefficient * value)) +
        automorphism.exponentialLift value *
          (Complex.exp (-(automorphism.exponentCoefficient * value)) *
            (-automorphism.exponentCoefficient))) value := by
    simpa only [Pi.mul_apply] using hproduct
  change deriv
    (fun input ↦ automorphism.exponentialLift input *
      Complex.exp (-(automorphism.exponentCoefficient * input))) value = 0
  rw [hproduct'.deriv, automorphism.deriv_exponentialLift value]
  ring

theorem exponentialLift_eq_exp_exponentCoefficient
    (automorphism : Automorphism) (value : ℂ) :
    automorphism.exponentialLift value =
      Complex.exp (automorphism.exponentCoefficient * value) := by
  have hconstant := is_const_of_deriv_eq_zero
    automorphism.normalizedLift_differentiable
    automorphism.deriv_normalizedLift_eq_zero value 0
  have hnormalized :
      automorphism.exponentialLift value *
        Complex.exp (-(automorphism.exponentCoefficient * value)) = 1 := by
    simpa only [normalizedLift, exponentialLift_zero, mul_zero, neg_zero,
      Complex.exp_zero, mul_one] using hconstant
  apply mul_right_cancel₀
    (Complex.exp_ne_zero (-(automorphism.exponentCoefficient * value)))
  rw [hnormalized]
  rw [← Complex.exp_add]
  ring_nf
  simp

theorem exists_integer_exponent (automorphism : Automorphism) :
    ∃ exponent : ℤ, automorphism.exponentCoefficient = (exponent : ℂ) := by
  have hperiod :
      Complex.exp
        (automorphism.exponentCoefficient * (2 * Real.pi * Complex.I)) = 1 := by
    rw [← automorphism.exponentialLift_eq_exp_exponentCoefficient]
    simp [exponentialLift, Complex.exp_two_pi_mul_I,
      automorphism.ambient_one]
  obtain ⟨exponent, hexponent⟩ :=
    Complex.exp_eq_one_iff.mp hperiod
  refine ⟨exponent, ?_⟩
  apply mul_right_cancel₀ Complex.two_pi_I_ne_zero
  exact hexponent

theorem ambient_eq_zpow
    (automorphism : Automorphism) (exponent : ℤ)
    (hexponent : automorphism.exponentCoefficient = (exponent : ℂ))
    {value : ℂ} (hvalue : value ≠ 0) :
    automorphism.ambient value = value ^ exponent := by
  calc
    automorphism.ambient value =
        automorphism.exponentialLift (Complex.log value) := by
      rw [exponentialLift, Complex.exp_log hvalue]
    _ = Complex.exp
        (automorphism.exponentCoefficient * Complex.log value) :=
      automorphism.exponentialLift_eq_exp_exponentCoefficient _
    _ = Complex.exp ((exponent : ℂ) * Complex.log value) := by rw [hexponent]
    _ = Complex.exp (Complex.log value) ^ exponent :=
      Complex.exp_int_mul _ _
    _ = value ^ exponent := by rw [Complex.exp_log hvalue]

/-- The inverse holomorphic group automorphism. -/
def symm (automorphism : Automorphism) : Automorphism where
  toContinuousMulEquiv := automorphism.toContinuousMulEquiv.symm
  holomorphic := automorphism.holomorphic_symm
  holomorphic_symm := by
    simpa using automorphism.holomorphic

@[simp]
theorem symm_puncturedMap
    (automorphism : Automorphism) (value : puncturedPlane.carrier) :
    automorphism.symm.puncturedMap value = automorphism.puncturedMapInv value :=
  rfl

theorem symm_ambient_apply_ambient
    (automorphism : Automorphism) {value : ℂ} (hvalue : value ≠ 0) :
    automorphism.symm.ambient (automorphism.ambient value) = value := by
  rw [automorphism.symm.ambient_eq
      ⟨automorphism.ambient value, automorphism.ambient_ne_zero hvalue⟩]
  have hforward :
      (⟨automorphism.ambient value,
          automorphism.ambient_ne_zero hvalue⟩ : puncturedPlane.carrier) =
        automorphism.puncturedMap ⟨value, hvalue⟩ := by
    apply Subtype.ext
    exact automorphism.ambient_eq ⟨value, hvalue⟩
  rw [hforward]
  exact congrArg Subtype.val <| by
    simpa only [symm_puncturedMap] using
      automorphism.puncturedMapInv_apply_puncturedMap ⟨value, hvalue⟩

/-- Bijectivity restricts the integer exponent of a holomorphic group
automorphism to `1` or `-1`. -/
theorem exponent_eq_one_or_neg_one
    (automorphism : Automorphism) (exponent : ℤ)
    (hexponent : automorphism.exponentCoefficient = (exponent : ℂ)) :
    exponent = 1 ∨ exponent = -1 := by
  obtain ⟨inverseExponent, hinverseExponent⟩ :=
    automorphism.symm.exists_integer_exponent
  have hcompose := automorphism.symm_ambient_apply_ambient
    (by norm_num : (2 : ℂ) ≠ 0)
  rw [automorphism.ambient_eq_zpow exponent hexponent (by norm_num),
    automorphism.symm.ambient_eq_zpow inverseExponent hinverseExponent
      (zpow_ne_zero _ (by norm_num : (2 : ℂ) ≠ 0))] at hcompose
  have hpower :
      (2 : ℂ) ^ (exponent * inverseExponent) = (2 : ℂ) := by
    rw [zpow_mul]
    exact hcompose
  have hnorm :
      (2 : ℝ) ^ (exponent * inverseExponent) = (2 : ℝ) ^ (1 : ℤ) := by
    have := congrArg norm hpower
    simpa only [norm_zpow, Complex.norm_ofNat, zpow_one] using this
  have hproduct : exponent * inverseExponent = 1 :=
    (zpow_right_injective₀ (a := (2 : ℝ)) (by norm_num) (by norm_num)) hnorm
  exact Int.eq_one_or_neg_one_of_mul_eq_one hproduct

/-- Preservation of the norm-at-most-one submonoid from IUT I,
Remark 3.4.2. -/
def PreservesClosedUnitSubmonoid (automorphism : Automorphism) : Prop :=
  ∀ (value : ℂ) (_hvalue : value ≠ 0),
    ‖value‖ ≤ 1 ↔ ‖automorphism.ambient value‖ ≤ 1

/-- Preservation of the selected component `0 < ‖z‖ < 1` used by the
semi-germ formulation in IUT III, Remark 1.1.1(ii). -/
def PreservesSelectedInnerSide (automorphism : Automorphism) : Prop :=
  ∀ (value : ℂ) (_hvalue : value ≠ 0),
    ‖value‖ < 1 ↔ ‖automorphism.ambient value‖ < 1

theorem exponent_eq_one_of_preservesClosedUnitSubmonoid
    (automorphism : Automorphism)
    (hpreserves : PreservesClosedUnitSubmonoid automorphism)
    (exponent : ℤ)
    (hexponent : automorphism.exponentCoefficient = (exponent : ℂ)) :
    exponent = 1 := by
  rcases automorphism.exponent_eq_one_or_neg_one exponent hexponent with
    hone | hneg
  · exact hone
  · subst exponent
    have hhalf := (hpreserves (1 / 2 : ℂ) (by norm_num)).mp (by norm_num)
    rw [automorphism.ambient_eq_zpow (-1) hexponent (by norm_num)] at hhalf
    norm_num at hhalf

theorem exponent_eq_one_of_preservesSelectedInnerSide
    (automorphism : Automorphism)
    (hpreserves : PreservesSelectedInnerSide automorphism)
    (exponent : ℤ)
    (hexponent : automorphism.exponentCoefficient = (exponent : ℂ)) :
    exponent = 1 := by
  rcases automorphism.exponent_eq_one_or_neg_one exponent hexponent with
    hone | hneg
  · exact hone
  · subst exponent
    have hhalf := (hpreserves (1 / 2 : ℂ) (by norm_num)).mp (by norm_num)
    rw [automorphism.ambient_eq_zpow (-1) hexponent (by norm_num)] at hhalf
    norm_num at hhalf

theorem ambient_eq_id_of_preservesSelectedInnerSide
    (automorphism : Automorphism)
    (hpreserves : PreservesSelectedInnerSide automorphism)
    {value : ℂ} (hvalue : value ≠ 0) :
    automorphism.ambient value = value := by
  obtain ⟨exponent, hexponent⟩ := automorphism.exists_integer_exponent
  have hone := automorphism.exponent_eq_one_of_preservesSelectedInnerSide
    hpreserves exponent hexponent
  simpa only [hone, zpow_one] using
    automorphism.ambient_eq_zpow exponent hexponent hvalue

theorem ambient_eq_id_of_preservesClosedUnitSubmonoid
    (automorphism : Automorphism)
    (hpreserves : PreservesClosedUnitSubmonoid automorphism)
    {value : ℂ} (hvalue : value ≠ 0) :
    automorphism.ambient value = value := by
  obtain ⟨exponent, hexponent⟩ := automorphism.exists_integer_exponent
  have hone := automorphism.exponent_eq_one_of_preservesClosedUnitSubmonoid
    hpreserves exponent hexponent
  simpa only [hone, zpow_one] using
    automorphism.ambient_eq_zpow exponent hexponent hvalue

/-- Source rigidity: the selected-side-preserving element of
`Aut_hol(ℂˣ)` is the identity. -/
theorem toAutHolomorphic_eq_identity
    (automorphism : Automorphism)
    (hpreserves : PreservesSelectedInnerSide automorphism) :
    automorphism.toAutHolomorphic =
      SourceAutHolomorphic.AutHolomorphic.identity puncturedPlane := by
  apply Subtype.ext
  apply Homeomorph.ext
  intro value
  apply Subtype.ext
  have hambient := automorphism.ambient_eq_id_of_preservesSelectedInnerSide
    hpreserves ((mem_puncturedPlane_iff value).mp value.2)
  rw [automorphism.ambient_eq value] at hambient
  exact hambient

/-- IUT I, Remark 3.4.2 in its norm-at-most-one formulation. -/
theorem toAutHolomorphic_eq_identity_of_preservesClosedUnitSubmonoid
    (automorphism : Automorphism)
    (hpreserves : PreservesClosedUnitSubmonoid automorphism) :
    automorphism.toAutHolomorphic =
      SourceAutHolomorphic.AutHolomorphic.identity puncturedPlane := by
  apply Subtype.ext
  apply Homeomorph.ext
  intro value
  apply Subtype.ext
  have hambient := automorphism.ambient_eq_id_of_preservesClosedUnitSubmonoid
    hpreserves ((mem_puncturedPlane_iff value).mp value.2)
  rw [automorphism.ambient_eq value] at hambient
  exact hambient

/-- The forward holomorphic map as a germ along the unit circle. -/
def ambientGerm (automorphism : Automorphism) :
    Filter.Germ
      SourceAutHolomorphicSemiGerm.unitNeighborhoodFilter ℂ :=
  automorphism.ambient

theorem ambient_eventuallyEq_id
    (automorphism : Automorphism)
    (hpreserves : PreservesSelectedInnerSide automorphism) :
    automorphism.ambient =ᶠ[
      SourceAutHolomorphicSemiGerm.unitNeighborhoodFilter] id := by
  filter_upwards [
    SourceAutHolomorphicSemiGerm.neighborhood_mem_unitNeighborhoodFilter 0]
      with value hvalue
  exact automorphism.ambient_eq_id_of_preservesSelectedInnerSide hpreserves
    (fun hzero ↦
      SourceAutHolomorphicSemiGerm.zero_not_mem_neighborhood 0
        (hzero ▸ hvalue))

/-- The selected-side-preserving automorphism induces the identity germ. -/
theorem ambientGerm_eq_identity
    (automorphism : Automorphism)
    (hpreserves : PreservesSelectedInnerSide automorphism) :
    automorphism.ambientGerm =
      ((id : ℂ → ℂ) : Filter.Germ
        SourceAutHolomorphicSemiGerm.unitNeighborhoodFilter ℂ) :=
  Filter.Germ.coe_eq.mpr (automorphism.ambient_eventuallyEq_id hpreserves)

/-- Consequently the representative preserves the unit-circle neighborhood
filter, so it is an actual endomorphism of the semi-germ. -/
theorem ambient_tendsto_unitNeighborhoodFilter
    (automorphism : Automorphism)
    (hpreserves : PreservesSelectedInnerSide automorphism) :
    Filter.Tendsto automorphism.ambient
      SourceAutHolomorphicSemiGerm.unitNeighborhoodFilter
      SourceAutHolomorphicSemiGerm.unitNeighborhoodFilter :=
  Filter.Tendsto.congr'
    (automorphism.ambient_eventuallyEq_id hpreserves).symm
    Filter.tendsto_id

end Automorphism

end SourceAutHolomorphicRigidity

end

end Iut
