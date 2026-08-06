import LeanFormal.IUT.Foundations.Geometry.TateUniformizationContract

namespace LeanFormal.IUT

universe u

noncomputable section

namespace NumberFieldFinitePlace

def unitsAlgEquiv
    {K : Type u} [Field K] [NumberField K]
    (place : NumberField.FinitePlace K)
    (sigma : AlgebraicClosure (Completion place) ≃ₐ[Completion place]
      AlgebraicClosure (Completion place)) :
    (AlgebraicClosure (Completion place))ˣ ≃* (AlgebraicClosure (Completion place))ˣ where
  toFun := Units.map sigma.toRingEquiv.toMonoidHom
  invFun := Units.map sigma.symm.toRingEquiv.toMonoidHom
  left_inv := by
    intro x
    apply Units.ext
    simp
  right_inv := by
    intro x
    apply Units.ext
    simp
  map_mul' := by
    intro x y
    simp

theorem unitsAlgEquiv_tateParameterUnit
    {K : Type u} [Field K] [NumberField K]
    (place : NumberField.FinitePlace K)
    (q : Completion place) (q_ne_zero : q ≠ 0)
    (sigma : AlgebraicClosure (Completion place) ≃ₐ[Completion place]
      AlgebraicClosure (Completion place)) :
    unitsAlgEquiv place sigma (tateParameterUnit place q q_ne_zero) =
      tateParameterUnit place q q_ne_zero := by
  exact tateParameterUnit_algEquiv_map place q q_ne_zero sigma

theorem unitsAlgEquiv_refl
    {K : Type u} [Field K] [NumberField K]
    (place : NumberField.FinitePlace K) :
    unitsAlgEquiv place
        (AlgEquiv.refl : AlgebraicClosure (Completion place) ≃ₐ[Completion place]
          AlgebraicClosure (Completion place)) =
      MulEquiv.refl _ := by
  apply MulEquiv.ext
  intro x
  apply Units.ext
  rfl

theorem unitsAlgEquiv_trans
    {K : Type u} [Field K] [NumberField K]
    (place : NumberField.FinitePlace K)
    (sigma tau : AlgebraicClosure (Completion place) ≃ₐ[Completion place]
      AlgebraicClosure (Completion place)) :
    unitsAlgEquiv place (sigma.trans tau) =
      (unitsAlgEquiv place sigma).trans (unitsAlgEquiv place tau) := by
  apply MulEquiv.ext
  intro x
  apply Units.ext
  rfl

def tateDeckQuotientEquiv
    {K : Type u} [Field K] [NumberField K]
    (place : NumberField.FinitePlace K)
    (q : Completion place) (q_ne_zero : q ≠ 0)
    (sigma : AlgebraicClosure (Completion place) ≃ₐ[Completion place]
      AlgebraicClosure (Completion place)) :
    (AlgebraicClosure (Completion place))ˣ ⧸
        Subgroup.zpowers (tateParameterUnit place q q_ne_zero) ≃*
      (AlgebraicClosure (Completion place))ˣ ⧸
        Subgroup.zpowers (tateParameterUnit place q q_ne_zero) := by
  apply QuotientGroup.congr
    (Subgroup.zpowers (tateParameterUnit place q q_ne_zero))
    (Subgroup.zpowers (tateParameterUnit place q q_ne_zero))
    (unitsAlgEquiv place sigma)
  simpa [unitsAlgEquiv] using
    (tateParameterDeckSubgroup_algEquiv_map place q q_ne_zero sigma)

@[simp] theorem tateDeckQuotientEquiv_mk
    {K : Type u} [Field K] [NumberField K]
    (place : NumberField.FinitePlace K)
    (q : Completion place) (q_ne_zero : q ≠ 0)
    (sigma : AlgebraicClosure (Completion place) ≃ₐ[Completion place]
      AlgebraicClosure (Completion place))
    (x : (AlgebraicClosure (Completion place))ˣ) :
    tateDeckQuotientEquiv place q q_ne_zero sigma (QuotientGroup.mk x) =
      QuotientGroup.mk (unitsAlgEquiv place sigma x) := by
  apply QuotientGroup.congr_mk

end NumberFieldFinitePlace

end

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def tateDeckGaloisAction : Obligation :=
  { id := "Foundations.Geometry.tate-deck-galois-action"
    source := "IUT I, Definition 3.1(c); Galois action on the Tate deck quotient"
    status := VerificationStatus.proved
    note :=
      "A base-field algebra equivalence acts on algebraic-closure units, fixes " ++
        "the q-parameter unit, preserves its q^Z subgroup, and therefore " ++
        "descends to an actual multiplicative quotient equivalence. This is " ++
        "the algebraic equivariance carrier only; Tate uniformization and its " ++
        "identification with curve points remain explicit obligations."
    dependsOn :=
      [ "Foundations.Geometry.curve-indexed-tate-uniformization" ] }

end LeanFormal.IUT.Audit
