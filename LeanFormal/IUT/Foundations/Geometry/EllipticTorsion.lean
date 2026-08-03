import LeanFormal.IUT.Audit.Status
import LeanFormal.IUT.Foundations.Arithmetic.PrimeLabels
import LeanFormal.IUT.Foundations.Geometry.PuncturedEllipticCurve
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Instances.ZMod

/-!
  Elliptic torsion and its absolute-Galois action.

  This file builds the ordinary algebraic-geometry objects required before
  the mod-l representation of IUT I, Definition 3.1(c): the actual torsion
  subgroup over an algebraic closure and the semilinear action induced by
  automorphisms of that closure.  It does not assert the source's rational
  2*3-torsion or large-image hypotheses.

  Source comparison: IUT I, Definition 3.1(b),(c); compare the torsion block
  of `promachina/iut-lean/Iut/Foundations/InitialThetaData.lean`.
-/

namespace LeanFormal.IUT

universe u

noncomputable section

namespace PuncturedEllipticCurve

/--
Every n-torsion point over an algebraic closure comes from an affine point
over the base field. This is a source hypothesis, not an automatic theorem.
-/
def AllNTorsionRational
    {F : Type u} [Field F]
    (X : PuncturedEllipticCurve F) (n : Nat) : Prop := by
  classical
  exact
    forall P :
        (X.curve.toAffine.baseChange (AlgebraicClosure F)).Point,
      n • P = 0 ->
        exists Q : X.curve.toAffine.Point,
          WeierstrassCurve.Affine.Point.baseChange
            (W' := X.curve.toAffine) F (AlgebraicClosure F) Q = P

/-- Rationality of the 2*3-torsion required in IUT I, Definition 3.1(b). -/
def Torsion23Rational
    {F : Type u} [Field F] (X : PuncturedEllipticCurve F) : Prop :=
  X.AllNTorsionRational 6

/-- Nonsingular projective points over an algebraic closure. -/
abbrev AlgebraicClosurePoint
    {F : Type u} [Field F] (X : PuncturedEllipticCurve F) :=
  (X.curve.toProjective.baseChange (AlgebraicClosure F)).Point

/-- The actual l-torsion subgroup of the elliptic curve over the closure. -/
abbrev LTorsion
    {F : Type u} [Field F] (X : PuncturedEllipticCurve F)
    (l : PrimeGeFive) :=
  AddSubgroup.torsionBy X.AlgebraicClosurePoint l.value

instance lTorsionModule
    {F : Type u} [Field F] (X : PuncturedEllipticCurve F)
    (l : PrimeGeFive) :
    Module (ZMod l.value) (X.LTorsion l) :=
  AddSubgroup.torsionBy.zmodModule

/-- The action of an absolute-Galois element on closure-valued points. -/
def galoisActionOnPoint
    {F : Type u} [Field F] (X : PuncturedEllipticCurve F)
    (sigma : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F) :
    X.AlgebraicClosurePoint →+ X.AlgebraicClosurePoint := by
  classical
  let Wbar := X.curve.toProjective.baseChange (AlgebraicClosure F)
  let toAffine := WeierstrassCurve.Projective.Point.toAffineAddEquiv Wbar
  let affineAction :=
    WeierstrassCurve.Affine.Point.map
      (W' := X.curve.toAffine) sigma.toAlgHom
  exact toAffine.symm.toAddMonoidHom.comp
    (affineAction.comp toAffine.toAddMonoidHom)

@[simp]
theorem galoisActionOnPoint_one
    {F : Type u} [Field F] (X : PuncturedEllipticCurve F) :
    X.galoisActionOnPoint
        (1 : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F) =
      AddMonoidHom.id X.AlgebraicClosurePoint := by
  classical
  apply AddMonoidHom.ext
  intro P
  let e :=
    WeierstrassCurve.Projective.Point.toAffineAddEquiv
      (X.curve.toProjective.baseChange (AlgebraicClosure F))
  apply e.injective
  change
    e (e.symm
      (WeierstrassCurve.Affine.Point.map
        (W' := X.curve.toAffine)
        (1 : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F).toAlgHom
        (e P))) = e P
  rw [e.apply_symm_apply]
  cases e P <;> rfl

@[simp]
theorem galoisActionOnPoint_mul
    {F : Type u} [Field F] (X : PuncturedEllipticCurve F)
    (sigma tau : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F) :
    X.galoisActionOnPoint (sigma * tau) =
      (X.galoisActionOnPoint sigma).comp
        (X.galoisActionOnPoint tau) := by
  classical
  apply AddMonoidHom.ext
  intro P
  let e :=
    WeierstrassCurve.Projective.Point.toAffineAddEquiv
      (X.curve.toProjective.baseChange (AlgebraicClosure F))
  apply e.injective
  change
    e (e.symm
      (WeierstrassCurve.Affine.Point.map
        (W' := X.curve.toAffine) (sigma * tau).toAlgHom (e P))) =
      e (e.symm
        (WeierstrassCurve.Affine.Point.map
          (W' := X.curve.toAffine) sigma.toAlgHom
          (e (e.symm
            (WeierstrassCurve.Affine.Point.map
              (W' := X.curve.toAffine) tau.toAlgHom (e P))))))
  rw [e.apply_symm_apply, e.apply_symm_apply,
    e.apply_symm_apply,
    WeierstrassCurve.Affine.Point.map_map]
  congr 1

/-- The stabilizer of a closure-valued point is Krull-open. -/
theorem galoisActionOnPoint_stabilizer_isOpen
    {F : Type u} [Field F] (X : PuncturedEllipticCurve F)
    (P : X.AlgebraicClosurePoint) :
    IsOpen {sigma : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F |
      X.galoisActionOnPoint sigma P = P} := by
  classical
  let e :=
    WeierstrassCurve.Projective.Point.toAffineAddEquiv
      (X.curve.toProjective.baseChange (AlgebraicClosure F))
  cases hP : e P with
  | zero =>
      have hset :
          {sigma : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F |
              X.galoisActionOnPoint sigma P = P} = Set.univ := by
        ext sigma
        simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
        apply e.injective
        change
          e (e.symm
            (WeierstrassCurve.Affine.Point.map
              (W' := X.curve.toAffine) sigma.toAlgHom (e P))) = e P
        rw [e.apply_symm_apply, hP]
        rfl
      rw [hset]
      exact isOpen_univ
  | some x y h =>
      have hset :
          {sigma : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F |
              X.galoisActionOnPoint sigma P = P} =
            (MulAction.stabilizer
                (AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F) x :
                  Set (AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F)) ∩
              (MulAction.stabilizer
                (AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F) y :
                  Set (AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F)) := by
        ext sigma
        simp only [Set.mem_setOf_eq, Set.mem_inter_iff, SetLike.mem_coe]
        rw [← e.apply_eq_iff_eq]
        change
          e (e.symm
            (WeierstrassCurve.Affine.Point.map
              (W' := X.curve.toAffine) sigma.toAlgHom (e P))) = e P ↔ _
        rw [e.apply_symm_apply, hP]
        change
          WeierstrassCurve.Affine.Point.some (sigma x) (sigma y) _ =
              WeierstrassCurve.Affine.Point.some x y h ↔
            sigma x = x ∧ sigma y = y
        simp
      rw [hset]
      exact (stabilizer_isOpen_of_isIntegral x).inter
        (stabilizer_isOpen_of_isIntegral y)

/-- The actual Galois action restricted to the l-torsion subgroup. -/
def galoisActionOnLTorsion
    {F : Type u} [Field F] (X : PuncturedEllipticCurve F)
    (l : PrimeGeFive)
    (sigma : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F) :
    X.LTorsion l →+ X.LTorsion l :=
  ((X.galoisActionOnPoint sigma).comp
      (X.LTorsion l).subtype).codRestrict
    (X.LTorsion l)
    (fun P => by
      rw [AddSubgroup.torsionBy.nsmul_iff]
      rw [← map_nsmul,
        AddSubgroup.torsionBy.nsmul P, map_zero])

@[simp]
theorem galoisActionOnLTorsion_coe
    {F : Type u} [Field F] (X : PuncturedEllipticCurve F)
    (l : PrimeGeFive)
    (sigma : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F)
    (P : X.LTorsion l) :
    ((X.galoisActionOnLTorsion l sigma P : X.LTorsion l) :
        X.AlgebraicClosurePoint) =
      X.galoisActionOnPoint sigma P :=
  rfl

/-- The Galois action on E[l] as a ZMod-l linear equivalence. -/
def galoisActionOnLTorsionLinearEquiv
    {F : Type u} [Field F] (X : PuncturedEllipticCurve F)
    (l : PrimeGeFive)
    (sigma : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F) :
    X.LTorsion l ≃ₗ[ZMod l.value] X.LTorsion l :=
  LinearEquiv.ofLinear
    (AddMonoidHom.toZModLinearMap l.value
      (X.galoisActionOnLTorsion l sigma))
    (AddMonoidHom.toZModLinearMap l.value
      (X.galoisActionOnLTorsion l sigma⁻¹))
    (by
      apply LinearMap.ext
      intro P
      apply Subtype.ext
      simp only [LinearMap.comp_apply,
        AddMonoidHom.coe_toZModLinearMap,
        galoisActionOnLTorsion_coe,
        LinearMap.id_apply]
      rw [← AddMonoidHom.comp_apply,
        ← X.galoisActionOnPoint_mul]
      simp)
    (by
      apply LinearMap.ext
      intro P
      apply Subtype.ext
      simp only [LinearMap.comp_apply,
        AddMonoidHom.coe_toZModLinearMap,
        galoisActionOnLTorsion_coe,
        LinearMap.id_apply]
      rw [← AddMonoidHom.comp_apply,
        ← X.galoisActionOnPoint_mul]
      simp)

@[simp]
theorem galoisActionOnLTorsionLinearEquiv_apply
    {F : Type u} [Field F] (X : PuncturedEllipticCurve F)
    (l : PrimeGeFive)
    (sigma : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F)
    (P : X.LTorsion l) :
    X.galoisActionOnLTorsionLinearEquiv l sigma P =
      X.galoisActionOnLTorsion l sigma P :=
  rfl

@[simp]
theorem galoisActionOnLTorsionLinearEquiv_one
    {F : Type u} [Field F] (X : PuncturedEllipticCurve F)
    (l : PrimeGeFive) :
    X.galoisActionOnLTorsionLinearEquiv l
        (1 : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F) =
      LinearEquiv.refl (ZMod l.value) (X.LTorsion l) := by
  apply LinearEquiv.ext
  intro P
  apply Subtype.ext
  simp [galoisActionOnLTorsionLinearEquiv_apply,
    galoisActionOnLTorsion_coe]

@[simp]
theorem galoisActionOnLTorsionLinearEquiv_mul
    {F : Type u} [Field F] (X : PuncturedEllipticCurve F)
    (l : PrimeGeFive)
    (sigma tau : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F) :
    X.galoisActionOnLTorsionLinearEquiv l (sigma * tau) =
      X.galoisActionOnLTorsionLinearEquiv l sigma *
        X.galoisActionOnLTorsionLinearEquiv l tau := by
  apply LinearEquiv.ext
  intro P
  apply Subtype.ext
  change
    X.galoisActionOnPoint (sigma * tau) P =
      X.galoisActionOnPoint sigma
        (X.galoisActionOnPoint tau P)
  rw [X.galoisActionOnPoint_mul]
  rfl

/-- The source-defined Galois representation on the actual module E[l]. -/
def galoisActionOnLTorsionLinearEquivHom
    {F : Type u} [Field F] (X : PuncturedEllipticCurve F)
    (l : PrimeGeFive) :
    (AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F) →*
      (X.LTorsion l ≃ₗ[ZMod l.value] X.LTorsion l) where
  toFun := X.galoisActionOnLTorsionLinearEquiv l
  map_one' := X.galoisActionOnLTorsionLinearEquiv_one l
  map_mul' := X.galoisActionOnLTorsionLinearEquiv_mul l

/-- The same representation in the module general linear group. -/
def galoisActionOnLTorsionGeneralLinearRepresentation
    {F : Type u} [Field F] (X : PuncturedEllipticCurve F)
    (l : PrimeGeFive) :
    (AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F) →*
      LinearMap.GeneralLinearGroup (ZMod l.value) (X.LTorsion l) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv
      (ZMod l.value) (X.LTorsion l)).symm.toMonoidHom.comp
    (X.galoisActionOnLTorsionLinearEquivHom l)

/-- The matrix representation associated to a chosen two-dimensional basis. -/
def galoisLTorsionMatrixRepresentation
    (l : PrimeGeFive) {F : Type u} [Field F]
    (X : PuncturedEllipticCurve F)
    (basis :
      (Fin 2 -> ZMod l.value) ≃ₗ[ZMod l.value] X.LTorsion l) :
    (AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F) →*
      Matrix.GeneralLinearGroup (Fin 2) (ZMod l.value) :=
  Matrix.GeneralLinearGroup.toLin.symm.toMonoidHom.comp
    ((LinearMap.GeneralLinearGroup.congrLinearEquiv basis).symm.toMonoidHom.comp
      (X.galoisActionOnLTorsionGeneralLinearRepresentation l))

/-- The basis-transported representation acts by the pointwise Galois action. -/
theorem galoisLTorsionMatrixRepresentation_acts
    (l : PrimeGeFive) {F : Type u} [Field F]
    (X : PuncturedEllipticCurve F)
    (basis :
      (Fin 2 -> ZMod l.value) ≃ₗ[ZMod l.value] X.LTorsion l)
    (sigma : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F)
    (coordinates : Fin 2 -> ZMod l.value) :
    ((basis
        ((Matrix.GeneralLinearGroup.toLin
          (X.galoisLTorsionMatrixRepresentation l basis sigma)).toLinearEquiv
            coordinates) : X.LTorsion l) : X.AlgebraicClosurePoint) =
      X.galoisActionOnPoint sigma (basis coordinates) := by
  simp [galoisLTorsionMatrixRepresentation,
    galoisActionOnLTorsionGeneralLinearRepresentation,
    galoisActionOnLTorsionLinearEquivHom,
    LinearMap.GeneralLinearGroup.generalLinearEquiv,
    LinearMap.GeneralLinearGroup.congrLinearEquiv_apply,
    galoisActionOnLTorsionLinearEquiv_apply,
    galoisActionOnLTorsion_coe]

/-- The kernel is a finite intersection of open point stabilizers. -/
theorem galoisLTorsionMatrixRepresentation_ker_isOpen
    (l : PrimeGeFive) {F : Type u} [Field F]
    (X : PuncturedEllipticCurve F)
    (basis :
      (Fin 2 -> ZMod l.value) ≃ₗ[ZMod l.value] X.LTorsion l) :
    IsOpen
      ((X.galoisLTorsionMatrixRepresentation l basis).ker :
        Set (AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F)) := by
  classical
  let fixedPoint :
      (Fin 2 -> ZMod l.value) ->
        Set (AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F) :=
    fun coordinates =>
      {sigma | X.galoisActionOnPoint sigma (basis coordinates) = basis coordinates}
  have hopen : forall coordinates, IsOpen (fixedPoint coordinates) :=
    fun coordinates => X.galoisActionOnPoint_stabilizer_isOpen (basis coordinates)
  have hinter : IsOpen (⋂ coordinates, fixedPoint coordinates) :=
    isOpen_iInter_of_finite hopen
  have hker :
      ((X.galoisLTorsionMatrixRepresentation l basis).ker :
          Set (AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F)) =
        ⋂ coordinates, fixedPoint coordinates := by
    ext sigma
    simp only [Set.mem_iInter]
    constructor
    · intro hsigma coordinates
      have hacts :=
        X.galoisLTorsionMatrixRepresentation_acts
          l basis sigma coordinates
      rw [hsigma] at hacts
      change
        X.galoisActionOnPoint sigma (basis coordinates) =
          basis coordinates
      simpa using hacts.symm
    · intro hsigma
      apply Matrix.GeneralLinearGroup.toLin.injective
      apply Units.ext
      apply LinearMap.ext
      intro coordinates
      apply basis.injective
      have hacts :=
        X.galoisLTorsionMatrixRepresentation_acts
          l basis sigma coordinates
      simpa using hacts.trans (hsigma coordinates)
  rw [hker]
  exact hinter

/-- The matrix representation is continuous for the Krull topology. -/
theorem galoisLTorsionMatrixRepresentation_continuous
    (l : PrimeGeFive) {F : Type u} [Field F]
    (X : PuncturedEllipticCurve F)
    (basis :
      (Fin 2 -> ZMod l.value) ≃ₗ[ZMod l.value] X.LTorsion l) :
    Continuous (X.galoisLTorsionMatrixRepresentation l basis) := by
  apply continuous_of_tendsto_nhds_one
  rw [show
    nhds (1 : Matrix.GeneralLinearGroup (Fin 2) (ZMod l.value)) = pure 1 from
      congrFun
        (nhds_discrete
          (Matrix.GeneralLinearGroup (Fin 2) (ZMod l.value))) 1]
  rw [Filter.tendsto_pure]
  exact
    (X.galoisLTorsionMatrixRepresentation_ker_isOpen l basis).mem_nhds
      (Subgroup.one_mem _)

/-- The kernel subgroup defining the source field K. -/
def galoisLTorsionKernelSubgroup
    (l : PrimeGeFive) {F : Type u} [Field F]
    (X : PuncturedEllipticCurve F)
    (basis :
      (Fin 2 -> ZMod l.value) ≃ₗ[ZMod l.value] X.LTorsion l) :
    Subgroup (AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F) :=
  (X.galoisLTorsionMatrixRepresentation l basis).ker

/-- The representation kernel bundled with its proved closedness. -/
def galoisLTorsionKernelClosedSubgroup
    (l : PrimeGeFive) {F : Type u} [Field F]
    (X : PuncturedEllipticCurve F)
    (basis :
      (Fin 2 -> ZMod l.value) ≃ₗ[ZMod l.value] X.LTorsion l) :
    ClosedSubgroup (AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F) :=
  ⟨X.galoisLTorsionKernelSubgroup l basis,
    OpenSubgroup.isClosed
      ⟨X.galoisLTorsionKernelSubgroup l basis,
        X.galoisLTorsionMatrixRepresentation_ker_isOpen l basis⟩⟩

/-- The field K constructed as the fixed field of the representation kernel. -/
def galoisLTorsionKernelField
    (l : PrimeGeFive) {F : Type u} [Field F]
    (X : PuncturedEllipticCurve F)
    (basis :
      (Fin 2 -> ZMod l.value) ≃ₗ[ZMod l.value] X.LTorsion l) :
    IntermediateField F (AlgebraicClosure F) :=
  IntermediateField.fixedField
    (X.galoisLTorsionKernelSubgroup l basis)

/-- The fixing subgroup of the kernel field is exactly the representation kernel. -/
theorem galoisLTorsionKernelField_fixingSubgroup
    (l : PrimeGeFive) {F : Type u} [Field F] [CharZero F]
    (X : PuncturedEllipticCurve F)
    (basis :
      (Fin 2 -> ZMod l.value) ≃ₗ[ZMod l.value] X.LTorsion l) :
    (X.galoisLTorsionKernelField l basis).fixingSubgroup =
      X.galoisLTorsionKernelSubgroup l basis := by
  simpa [galoisLTorsionKernelField,
    galoisLTorsionKernelClosedSubgroup] using
    InfiniteGalois.fixingSubgroup_fixedField
      (X.galoisLTorsionKernelClosedSubgroup l basis)

/-- Krull openness makes the kernel field finite over F. -/
instance galoisLTorsionKernelField_finiteDimensional
    (l : PrimeGeFive) {F : Type u} [Field F] [CharZero F]
    (X : PuncturedEllipticCurve F)
    (basis :
      (Fin 2 -> ZMod l.value) ≃ₗ[ZMod l.value] X.LTorsion l) :
    FiniteDimensional F (X.galoisLTorsionKernelField l basis) := by
  apply
    (InfiniteGalois.isOpen_iff_finite
      (X.galoisLTorsionKernelField l basis)).mp
  rw [X.galoisLTorsionKernelField_fixingSubgroup l basis]
  exact X.galoisLTorsionMatrixRepresentation_ker_isOpen l basis

/-- Normality of the kernel makes the kernel field Galois over F. -/
instance galoisLTorsionKernelField_isGalois
    (l : PrimeGeFive) {F : Type u} [Field F] [CharZero F]
    (X : PuncturedEllipticCurve F)
    (basis :
      (Fin 2 -> ZMod l.value) ≃ₗ[ZMod l.value] X.LTorsion l) :
    IsGalois F (X.galoisLTorsionKernelField l basis) := by
  apply
    (InfiniteGalois.normal_iff_isGalois
      (X.galoisLTorsionKernelField l basis)).mp
  rw [X.galoisLTorsionKernelField_fixingSubgroup l basis]
  exact MonoidHom.normal_ker
    (X.galoisLTorsionMatrixRepresentation l basis)

/-- Over a number field, the finite kernel field is again a number field. -/
instance galoisLTorsionKernelField_numberField
    (l : PrimeGeFive) {F : Type u} [Field F] [NumberField F]
    (X : PuncturedEllipticCurve F)
    (basis :
      (Fin 2 -> ZMod l.value) ≃ₗ[ZMod l.value] X.LTorsion l) :
    NumberField (X.galoisLTorsionKernelField l basis) :=
  NumberField.of_module_finite F
    (X.galoisLTorsionKernelField l basis)

end PuncturedEllipticCurve

end


end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def ellipticTorsionGaloisKernel : Obligation :=
  { id := "Foundations.Geometry.elliptic-torsion-galois"
    source := "Elliptic l-torsion and IUT I, Definition 3.1(c) prerequisite"
    status := VerificationStatus.proved
    note :=
      "The actual l-torsion subgroup over Mathlib's algebraic closure, the " ++
        "absolute-Galois point action, its open point stabilizers, its " ++
        "restriction to torsion, and the resulting ZMod-linear and general " ++
        "linear representations are constructed. Given an actual rank-two " ++
        "basis, the matrix representation is proved continuous and its fixed " ++
        "kernel field is proved finite Galois (and a number field over a " ++
        "number-field base). Basis existence and the large-image claim are " ++
        "not asserted."
    dependsOn :=
      [ "Foundations.Arithmetic.prime-label-ge-five",
        "Foundations.Geometry.punctured-elliptic-curve" ] }

def ellipticTorsion23Rationality : Obligation :=
  { id := "IUT-I.elliptic-2-3-torsion-rational"
    source := "IUT I, Definition 3.1(b)"
    status := VerificationStatus.interface
    note :=
      "Rationality of all six-torsion points is expressed using the actual " ++
        "base-change homomorphism on affine elliptic points. It is a source " ++
        "hypothesis and is not proved for arbitrary input curves."
    dependsOn := ["Foundations.Geometry.elliptic-torsion-galois"] }

def ellipticLTorsionRankTwoBasis : Obligation :=
  { id := "Foundations.Geometry.elliptic-l-torsion-rank-two"
    source := "Standard prime-to-characteristic elliptic torsion; IUT I, Definition 3.1(c)"
    status := VerificationStatus.pending
    note :=
      "The matrix and kernel-field constructions accept a genuine linear " ++
        "equivalence (ZMod l)^2 ~= E[l]. This file does not prove existence " ++
        "of that basis from the elliptic-curve hypotheses."
    dependsOn := ["Foundations.Geometry.elliptic-torsion-galois"] }

def ellipticLTorsionLargeImage : Obligation :=
  { id := "IUT-I.elliptic-l-torsion-large-image"
    source := "IUT I, Definition 3.1(c)"
    status := VerificationStatus.pending
    note :=
      "No theorem proves that the image of the constructed matrix " ++
        "representation contains SL(2, ZMod l); this remains a source " ++
        "hypothesis on the chosen initial Theta datum."
    dependsOn := ["Foundations.Geometry.elliptic-l-torsion-rank-two"] }

end LeanFormal.IUT.Audit
