/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/

import LeanFormal.IUT.IUTI.InitialTheta.ArithmeticData
import LeanFormal.IUT.Foundations.Geometry.EllipticTorsion
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
  # Source-faithful transport of the `l`-torsion carrier

  The source contract uses the `F`-side Galois representation in clause (c)
  and the `K`-side boundary quotient in clause (f).  These are points on two
  different chosen algebraic closures in the current foundations.  This file
  constructs the comparison from the finite algebraic extension `K/F`; it does
  not identify the carriers by notation or by an arbitrary equivalence.

  The construction has three layers:

  * a genuine `F`-algebra equivalence between the two algebraic closures;
  * the induced additive equivalence on the actual nonsingular Weierstrass
    point groups, with the base-change curve equality made explicit;
  * the induced `ZMod l`-linear equivalence on the actual torsion subgroups.

  No descent of the torsion points to `K` is claimed here.  The result only
  compares the two algebraic-closure carriers used by the source records.
-/

namespace LeanFormal.IUT

universe u

noncomputable section

namespace InitialThetaSource

/-! ## Algebraic-closure comparison -/

variable {l : PrimeGeFive}

theorem initialTheta_finite_extension_is_algebraic
    (A : InitialThetaArithmeticData l) :
    Algebra.IsAlgebraic A.F A.K :=
  Algebra.IsAlgebraic.of_finite A.F A.K

/-!
  `AlgebraicClosure A.K` is algebraic and algebraically closed over `A.F`
  because `A.K/A.F` is finite.  The equivalence is the standard Mathlib
  algebraic-closure equivalence, with no choice of a point or a carrier.
-/
noncomputable def initialThetaClosureAlgEquiv
    (A : InitialThetaArithmeticData l) :
    AlgebraicClosure A.K ≃ₐ[A.F] AlgebraicClosure A.F := by
  exact IsAlgClosure.equivOfAlgebraic
    A.F A.K (AlgebraicClosure A.K) (AlgebraicClosure A.F)

theorem initialThetaClosureAlgEquiv_commutes
    (A : InitialThetaArithmeticData l) (x : A.F) :
    initialThetaClosureAlgEquiv A (algebraMap A.F (AlgebraicClosure A.K) x) =
      algebraMap A.F (AlgebraicClosure A.F) x :=
  (initialThetaClosureAlgEquiv A).commutes x

theorem initialThetaClosureAlgEquiv_injective
    (A : InitialThetaArithmeticData l) :
    Function.Injective (initialThetaClosureAlgEquiv A) :=
  (initialThetaClosureAlgEquiv A).injective

theorem initialThetaClosureAlgEquiv_surjective
    (A : InitialThetaArithmeticData l) :
    Function.Surjective (initialThetaClosureAlgEquiv A) :=
  (initialThetaClosureAlgEquiv A).surjective

theorem initialThetaClosureAlgEquiv_inverse_commutes
    (A : InitialThetaArithmeticData l) (x : A.F) :
    (initialThetaClosureAlgEquiv A).symm
        (algebraMap A.F (AlgebraicClosure A.F) x) =
      algebraMap A.F (AlgebraicClosure A.K) x :=
  (initialThetaClosureAlgEquiv A).symm.commutes x

/-! ## Iterated base-change equality for projective curves -/

namespace PuncturedEllipticCurve

variable {F K : Type u} [Field F] [Field K]
variable [Algebra F K]

/-!
  The left-hand curve is the curve obtained by first extending the
  coefficients to `K` and then to an algebraic closure of `K`.  The right-hand
  curve extends directly from `F`.  The equality is the tower equality of the
  two algebra maps, expressed through the projective Weierstrass API.
-/
theorem baseChange_algebraicClosure_projective_curve_eq
    (X : PuncturedEllipticCurve F)
    (L : Type u) [Field L] [Algebra K L] [Algebra F L]
    [IsScalarTower F K L] :
    ((X.baseChange K).curve.toProjective.baseChange L) =
      X.curve.toProjective.baseChange L := by
  change
    (X.curve.toProjective.baseChange K).map (algebraMap K L) =
      X.curve.toProjective.baseChange L
  let extensionMap : K →ₐ[F] L := IsScalarTower.toAlgHom F K L
  have hmap :=
    WeierstrassCurve.Projective.map_baseChange
      (W' := X.curve.toProjective) extensionMap
  simpa [extensionMap] using hmap

/-! ## Additive point transport -/

variable {M N : Type u} [Field M] [Field N]
variable [Algebra F M] [Algebra F N]

/-!
  Map nonsingular projective points after changing the coefficient field.  The
  affine map is an actual group homomorphism from Mathlib; the projective
  affine equivalences transfer that group structure without introducing a
  second point carrier.
-/
noncomputable def algebraicClosurePointAddHom
    (X : PuncturedEllipticCurve F) (f : M →ₐ[F] N) :
    (X.curve.toProjective.baseChange M).Point →+
      (X.curve.toProjective.baseChange N).Point := by
  classical
  exact
    (WeierstrassCurve.Projective.Point.toAffineAddEquiv
      (X.curve.toProjective.baseChange N)).symm.toAddMonoidHom.comp
      ((WeierstrassCurve.Affine.Point.map
          (W' := X.curve.toAffine) f).comp
        (WeierstrassCurve.Projective.Point.toAffineAddEquiv
          (X.curve.toProjective.baseChange M)).toAddMonoidHom)

@[simp]
theorem algebraicClosurePointAddHom_zero
    (X : PuncturedEllipticCurve F) (f : M →ₐ[F] N) :
    algebraicClosurePointAddHom X f 0 = 0 :=
  map_zero _

theorem algebraicClosurePointAddHom_add
    (X : PuncturedEllipticCurve F) (f : M →ₐ[F] N)
    (P Q : (X.curve.toProjective.baseChange M).Point) :
    algebraicClosurePointAddHom X f (P + Q) =
      algebraicClosurePointAddHom X f P +
        algebraicClosurePointAddHom X f Q :=
  map_add _ P Q

/-!
  The map for an algebra equivalence is invertible.  Keeping this as an
  `AddEquiv` makes the later torsion restriction independent of any chosen
  coordinates or basis.
-/
noncomputable def algebraicClosurePointAddEquiv
    (X : PuncturedEllipticCurve F) (e : M ≃ₐ[F] N) :
    (X.curve.toProjective.baseChange M).Point ≃+
      (X.curve.toProjective.baseChange N).Point := by
  classical
  let forward := algebraicClosurePointAddHom X e.toAlgHom
  let backward := algebraicClosurePointAddHom X e.symm.toAlgHom
  refine
    { toFun := forward
      invFun := backward
      left_inv := ?_
      right_inv := ?_
      map_add' := ?_ }
  · intro P
    dsimp [forward, backward, algebraicClosurePointAddHom]
    have hmap
        (Q : (X.curve.toProjective.baseChange M).toAffine.Point) :
        WeierstrassCurve.Affine.Point.map e.symm.toAlgHom
            (WeierstrassCurve.Affine.Point.map e.toAlgHom Q) = Q := by
      rw [WeierstrassCurve.Affine.Point.map_map]
      cases Q with
      | zero => exact WeierstrassCurve.Affine.Point.zero_def
      | some x y h => simp [WeierstrassCurve.Affine.Point.map]
    apply (WeierstrassCurve.Projective.Point.toAffineAddEquiv
      (X.curve.toProjective.baseChange M)).injective
    simp only [AddEquiv.apply_symm_apply]
    exact hmap _
  · intro P
    dsimp [forward, backward, algebraicClosurePointAddHom]
    have hmap
        (Q : (X.curve.toProjective.baseChange N).toAffine.Point) :
        WeierstrassCurve.Affine.Point.map e.toAlgHom
            (WeierstrassCurve.Affine.Point.map e.symm.toAlgHom Q) = Q := by
      rw [WeierstrassCurve.Affine.Point.map_map]
      cases Q with
      | zero => exact WeierstrassCurve.Affine.Point.zero_def
      | some x y h => simp [WeierstrassCurve.Affine.Point.map]
    apply (WeierstrassCurve.Projective.Point.toAffineAddEquiv
      (X.curve.toProjective.baseChange N)).injective
    simp only [AddEquiv.apply_symm_apply]
    exact hmap _
  · intro P Q
    exact algebraicClosurePointAddHom_add X e.toAlgHom P Q

theorem algebraicClosurePointAddEquiv_apply
    (X : PuncturedEllipticCurve F) (e : M ≃ₐ[F] N)
    (P : (X.curve.toProjective.baseChange M).Point) :
    algebraicClosurePointAddEquiv X e P =
      algebraicClosurePointAddHom X e.toAlgHom P :=
  rfl

theorem algebraicClosurePointAddEquiv_zero
    (X : PuncturedEllipticCurve F) (e : M ≃ₐ[F] N) :
    algebraicClosurePointAddEquiv X e 0 = 0 :=
  map_zero _

theorem algebraicClosurePointAddEquiv_add
    (X : PuncturedEllipticCurve F) (e : M ≃ₐ[F] N)
    (P Q : (X.curve.toProjective.baseChange M).Point) :
    algebraicClosurePointAddEquiv X e (P + Q) =
      algebraicClosurePointAddEquiv X e P +
        algebraicClosurePointAddEquiv X e Q :=
  map_add _ P Q

theorem algebraicClosurePointAddEquiv_nsmul
    (X : PuncturedEllipticCurve F) (e : M ≃ₐ[F] N)
    (n : Nat) (P : (X.curve.toProjective.baseChange M).Point) :
    algebraicClosurePointAddEquiv X e (n • P) =
      n • algebraicClosurePointAddEquiv X e P :=
  map_nsmul (algebraicClosurePointAddEquiv X e) n P

theorem algebraicClosurePointAddEquiv_zsmul
    (X : PuncturedEllipticCurve F) (e : M ≃ₐ[F] N)
    (n : Int) (P : (X.curve.toProjective.baseChange M).Point) :
    algebraicClosurePointAddEquiv X e (n • P) =
      n • algebraicClosurePointAddEquiv X e P :=
  map_zsmul (algebraicClosurePointAddEquiv X e) n P

theorem algebraicClosurePointAddEquiv_neg
    (X : PuncturedEllipticCurve F) (e : M ≃ₐ[F] N)
    (P : (X.curve.toProjective.baseChange M).Point) :
    algebraicClosurePointAddEquiv X e (-P) =
      -algebraicClosurePointAddEquiv X e P :=
  map_neg (algebraicClosurePointAddEquiv X e) P

theorem algebraicClosurePointAddEquiv_symm_apply
    (X : PuncturedEllipticCurve F) (e : M ≃ₐ[F] N)
    (P : (X.curve.toProjective.baseChange N).Point) :
    (algebraicClosurePointAddEquiv X e).symm P =
      algebraicClosurePointAddEquiv X e.symm P := by
  apply (algebraicClosurePointAddEquiv X e).injective
  rw [(algebraicClosurePointAddEquiv X e).apply_symm_apply]
  exact (algebraicClosurePointAddEquiv X e.symm).left_inv P |>.symm

theorem algebraicClosurePointAddEquiv_inverse_left
    (X : PuncturedEllipticCurve F) (e : M ≃ₐ[F] N)
    (P : (X.curve.toProjective.baseChange M).Point) :
    algebraicClosurePointAddEquiv X e.symm
        (algebraicClosurePointAddEquiv X e P) = P := by
  exact (algebraicClosurePointAddEquiv X e).left_inv P

theorem algebraicClosurePointAddEquiv_inverse_right
    (X : PuncturedEllipticCurve F) (e : M ≃ₐ[F] N)
    (P : (X.curve.toProjective.baseChange N).Point) :
    algebraicClosurePointAddEquiv X e
        (algebraicClosurePointAddEquiv X e.symm P) = P := by
  exact (algebraicClosurePointAddEquiv X e).right_inv P

/-! ## Torsion restriction and linear upgrade -/

instance torsionByZModModule
    {G : Type u} [AddCommGroup G] (n : Nat) [NeZero n] :
    Module (ZMod n) (AddSubgroup.torsionBy G n) :=
  AddSubgroup.torsionBy.zmodModule

noncomputable def mapAddEquivTorsionBy
    {G H : Type u} [AddCommGroup G] [AddCommGroup H]
    (e : G ≃+ H) (n : Nat) :
    AddSubgroup.torsionBy G n ≃+
      AddSubgroup.torsionBy H n := by
  refine
    { toFun := (e.toAddMonoidHom.comp
          (AddSubgroup.torsionBy G n).subtype).codRestrict
        (AddSubgroup.torsionBy H n) ?_
      invFun := (e.symm.toAddMonoidHom.comp
          (AddSubgroup.torsionBy H n).subtype).codRestrict
        (AddSubgroup.torsionBy G n) ?_
      left_inv := ?_
      right_inv := ?_
      map_add' := ?_ }
  · intro P
    rw [AddSubgroup.torsionBy.nsmul_iff]
    rw [← map_nsmul, AddSubgroup.torsionBy.nsmul P, map_zero]
  · intro P
    rw [AddSubgroup.torsionBy.nsmul_iff]
    rw [← map_nsmul, AddSubgroup.torsionBy.nsmul P, map_zero]
  · intro P
    apply Subtype.ext
    exact e.symm_apply_apply P
  · intro P
    apply Subtype.ext
    exact e.apply_symm_apply P
  · intro P Q
    apply Subtype.ext
    exact e.map_add (P : G) (Q : G)

theorem mapAddEquivTorsionBy_apply
    {G H : Type u} [AddCommGroup G] [AddCommGroup H]
    (e : G ≃+ H) (n : Nat) (P : AddSubgroup.torsionBy G n) :
    mapAddEquivTorsionBy e n P = e P :=
  rfl

theorem mapAddEquivTorsionBy_symm_apply
    {G H : Type u} [AddCommGroup G] [AddCommGroup H]
    (e : G ≃+ H) (n : Nat) (P : AddSubgroup.torsionBy H n) :
    (mapAddEquivTorsionBy e n).symm P = e.symm P :=
  rfl

theorem mapAddEquivTorsionBy_nsmul
    {G H : Type u} [AddCommGroup G] [AddCommGroup H]
    (e : G ≃+ H) (n m : Nat) (P : AddSubgroup.torsionBy G n) :
    mapAddEquivTorsionBy e n (m • P) =
      m • mapAddEquivTorsionBy e n P :=
  map_nsmul (mapAddEquivTorsionBy e n) m P

theorem mapAddEquivTorsionBy_mem_target
    {G H : Type u} [AddCommGroup G] [AddCommGroup H]
    (e : G ≃+ H) (n : Nat) (P : G)
    (hP : P ∈ AddSubgroup.torsionBy G n) :
    e P ∈ AddSubgroup.torsionBy H n := by
  rw [AddSubgroup.torsionBy.nsmul_iff] at hP ⊢
  rw [← map_nsmul]
  simpa using congrArg e hP

theorem mapAddEquivTorsionBy_preimage_mem
    {G H : Type u} [AddCommGroup G] [AddCommGroup H]
    (e : G ≃+ H) (n : Nat) (P : H)
    (hP : P ∈ AddSubgroup.torsionBy H n) :
    e.symm P ∈ AddSubgroup.torsionBy G n := by
  rw [AddSubgroup.torsionBy.nsmul_iff] at hP ⊢
  rw [← map_nsmul]
  simpa using congrArg e.symm hP

noncomputable def mapAddEquivTorsionByLinear
    {G H : Type u} [AddCommGroup G] [AddCommGroup H]
    (e : G ≃+ H) (l : PrimeGeFive) :
    AddSubgroup.torsionBy G l.value ≃ₗ[ZMod l.value]
      AddSubgroup.torsionBy H l.value :=
  LinearEquiv.ofLinear
    (AddMonoidHom.toZModLinearMap l.value
      (mapAddEquivTorsionBy e l.value).toAddMonoidHom)
    (AddMonoidHom.toZModLinearMap l.value
      (mapAddEquivTorsionBy e l.value).symm.toAddMonoidHom)
    (by
      apply LinearMap.ext
      intro P
      apply Subtype.ext
      simpa only [LinearMap.comp_apply, LinearMap.id_apply,
        AddMonoidHom.coe_toZModLinearMap, AddEquiv.coe_toAddMonoidHom] using
        congrArg (fun Q : AddSubgroup.torsionBy H l.value => (Q : H))
          ((mapAddEquivTorsionBy e l.value).apply_symm_apply P))
    (by
      apply LinearMap.ext
      intro P
      apply Subtype.ext
      simpa only [LinearMap.comp_apply, LinearMap.id_apply,
        AddMonoidHom.coe_toZModLinearMap, AddEquiv.coe_toAddMonoidHom] using
        congrArg (fun Q : AddSubgroup.torsionBy G l.value => (Q : G))
          ((mapAddEquivTorsionBy e l.value).symm_apply_apply P))

theorem mapAddEquivTorsionByLinear_apply
    {G H : Type u} [AddCommGroup G] [AddCommGroup H]
    (e : G ≃+ H) (l : PrimeGeFive)
    (P : AddSubgroup.torsionBy G l.value) :
    mapAddEquivTorsionByLinear e l P = mapAddEquivTorsionBy e l.value P := by
  rfl

theorem mapAddEquivTorsionByLinear_zero
    {G H : Type u} [AddCommGroup G] [AddCommGroup H]
    (e : G ≃+ H) (l : PrimeGeFive) :
    mapAddEquivTorsionByLinear e l 0 = 0 :=
  map_zero _

theorem mapAddEquivTorsionByLinear_add
    {G H : Type u} [AddCommGroup G] [AddCommGroup H]
    (e : G ≃+ H) (l : PrimeGeFive)
    (P Q : AddSubgroup.torsionBy G l.value) :
    mapAddEquivTorsionByLinear e l (P + Q) =
      mapAddEquivTorsionByLinear e l P +
        mapAddEquivTorsionByLinear e l Q :=
  map_add _ P Q

theorem mapAddEquivTorsionByLinear_smul
    {G H : Type u} [AddCommGroup G] [AddCommGroup H]
    (e : G ≃+ H) (l : PrimeGeFive)
    (a : ZMod l.value) (P : AddSubgroup.torsionBy G l.value) :
    mapAddEquivTorsionByLinear e l (a • P) =
      a • mapAddEquivTorsionByLinear e l P := by
  exact (mapAddEquivTorsionByLinear e l).map_smul a P

theorem mapAddEquivTorsionByLinear_bijective
    {G H : Type u} [AddCommGroup G] [AddCommGroup H]
    (e : G ≃+ H) (l : PrimeGeFive) :
    Function.Bijective (mapAddEquivTorsionByLinear e l) :=
  (mapAddEquivTorsionByLinear e l).bijective

/-! ## The K/F torsion transport used by the source clauses -/

noncomputable def initialThetaKClosurePointAddEquiv
    (A : InitialThetaArithmeticData l) :
    (A.curve.baseChange A.K).AlgebraicClosurePoint ≃+
      A.curve.AlgebraicClosurePoint := by
  let hcurve :=
    baseChange_algebraicClosure_projective_curve_eq
      (X := A.curve) (K := A.K) (L := AlgebraicClosure A.K)
  let castSource :
      (A.curve.baseChange A.K).AlgebraicClosurePoint ≃+
        (A.curve.curve.toProjective.baseChange (AlgebraicClosure A.K)).Point :=
    AddEquiv.cast hcurve
  exact castSource.trans
    (algebraicClosurePointAddEquiv A.curve
      (initialThetaClosureAlgEquiv A))

theorem initialThetaKClosurePointAddEquiv_apply
    (A : InitialThetaArithmeticData l)
    (P : (A.curve.baseChange A.K).AlgebraicClosurePoint) :
    initialThetaKClosurePointAddEquiv A P =
      (algebraicClosurePointAddEquiv A.curve
        (initialThetaClosureAlgEquiv A))
        ((AddEquiv.cast
          (baseChange_algebraicClosure_projective_curve_eq
            (X := A.curve) (K := A.K) (L := AlgebraicClosure A.K))) P) :=
  rfl

noncomputable def initialThetaKToFTorsionAddEquiv
    (A : InitialThetaArithmeticData l) :
    (A.curve.baseChange A.K).LTorsion l ≃+
      A.curve.LTorsion l := by
  exact mapAddEquivTorsionBy (initialThetaKClosurePointAddEquiv A) l.value

noncomputable def initialThetaKToFTorsionTransport
    (A : InitialThetaArithmeticData l) :
    (A.curve.baseChange A.K).LTorsion l ≃ₗ[ZMod l.value]
      A.curve.LTorsion l :=
  mapAddEquivTorsionByLinear (initialThetaKClosurePointAddEquiv A) l

theorem initialThetaKToFTorsionTransport_bijective
    (A : InitialThetaArithmeticData l) :
    Function.Bijective (initialThetaKToFTorsionTransport A) :=
  (initialThetaKToFTorsionTransport A).bijective

end PuncturedEllipticCurve

end InitialThetaSource

end

end LeanFormal.IUT
