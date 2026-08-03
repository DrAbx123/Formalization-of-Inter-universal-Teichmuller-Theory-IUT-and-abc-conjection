import LeanFormal.IUT.Audit.Status
import Mathlib.AlgebraicGeometry.EllipticCurve.ModelsWithJ
import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Point

/-!
  The standard punctured elliptic-curve carrier.

  The puncture is an explicit projective point.  This records the ordinary
  geometric input shape used by IUT, without asserting a particular number
  field, reduction type, or anabelian reconstruction.
-/

namespace LeanFormal.IUT

universe u

structure PuncturedEllipticCurve (F : Type u) [Field F] where
  curve : WeierstrassCurve F
  isElliptic : curve.IsElliptic
  puncture : curve.toProjective.Point

namespace PuncturedEllipticCurve

universe v

variable {F : Type u} [Field F] (E : PuncturedEllipticCurve F)

instance : E.curve.IsElliptic := E.isElliptic

noncomputable def jInvariant : F := by
  letI := E.isElliptic
  exact E.curve.j

theorem jInvariant_spec : E.jInvariant = E.curve.j := by
  rfl

/-- A field homomorphism maps projective coordinate classes. The quotient
proof sends a scalar unit to its image unit, so no representative is chosen. -/
def projectivePointClassMap
    {K : Type v} [Field K] (f : F →+* K) :
    WeierstrassCurve.Projective.PointClass F →
      WeierstrassCurve.Projective.PointClass K :=
  Quotient.map (fun P => f ∘ P) (by
    intro P Q h
    rcases h with ⟨a, rfl⟩
    refine ⟨Units.map f.toMonoidHom a, ?_⟩
    change f (a : F) • (f ∘ Q) = f ∘ ((a : F) • Q)
    exact (WeierstrassCurve.Projective.comp_smul f Q a).symm)

@[simp]
theorem projectivePointClassMap_mk
    {K : Type v} [Field K] (f : F →+* K) (P : Fin 3 → F) :
    projectivePointClassMap f ⟦P⟧ = ⟦f ∘ P⟧ :=
  rfl

/-- Nonsingularity of a projective point is preserved by a field
homomorphism. -/
theorem projectiveNonsingularLift_map
    {K : Type v} [Field K] (f : F →+* K)
    {W : WeierstrassCurve F}
    {P : WeierstrassCurve.Projective.PointClass F}
    (hP : W.toProjective.NonsingularLift P) :
    (W.map f).toProjective.NonsingularLift
      (projectivePointClassMap f P) := by
  induction P using Quotient.inductionOn with
  | _ P =>
    change (W.map f).toProjective.Nonsingular (f ∘ P)
    exact (WeierstrassCurve.Projective.map_nonsingular
      (W' := W.toProjective) (f := f) f.injective P).mpr hP

/-- The induced map on nonsingular projective points. -/
def projectivePointMap
    {K : Type v} [Field K] (f : F →+* K) (W : WeierstrassCurve F) :
    W.toProjective.Point → (W.map f).toProjective.Point :=
  fun P =>
    { point := projectivePointClassMap f P.point
      nonsingular := projectiveNonsingularLift_map f P.nonsingular }

@[simp]
theorem projectivePointMap_point
    {K : Type v} [Field K] (f : F →+* K) (W : WeierstrassCurve F)
    (P : W.toProjective.Point) :
    (projectivePointMap f W P).point =
      projectivePointClassMap f P.point :=
  rfl

/-- Map a punctured elliptic curve, including its actual projective puncture,
along a field homomorphism. -/
def map {K : Type v} [Field K]
    (X : PuncturedEllipticCurve F) (f : F →+* K) :
    PuncturedEllipticCurve K := by
  letI : X.curve.IsElliptic := X.isElliptic
  exact
    { curve := X.curve.map f
      isElliptic := inferInstance
      puncture := projectivePointMap f X.curve X.puncture }

@[simp]
theorem map_curve {K : Type v} [Field K]
    (X : PuncturedEllipticCurve F) (f : F →+* K) :
    (X.map f).curve = X.curve.map f :=
  rfl

@[simp]
theorem map_puncture {K : Type v} [Field K]
    (X : PuncturedEllipticCurve F) (f : F →+* K) :
    (X.map f).puncture = projectivePointMap f X.curve X.puncture :=
  rfl

/-- Base change of a punctured elliptic curve. -/
def baseChange (X : PuncturedEllipticCurve F) (K : Type v)
    [Field K] [Algebra F K] : PuncturedEllipticCurve K :=
  X.map (algebraMap F K)

@[simp]
theorem baseChange_curve (X : PuncturedEllipticCurve F) (K : Type v)
    [Field K] [Algebra F K] :
    (X.baseChange K).curve = X.curve.baseChange K :=
  rfl

end PuncturedEllipticCurve

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def puncturedEllipticCarrier : Obligation :=
  { id := "Foundations.Geometry.punctured-elliptic-curve"
    source := "Standard Weierstrass elliptic curve with a puncture"
    status := VerificationStatus.proved
    note :=
      "The curve, ellipticity proof, projective puncture, and j-invariant " ++
        "projection are explicit Mathlib-backed data. Field homomorphisms map " ++
        "projective quotient classes without choosing representatives, " ++
        "preserve nonsingularity, and give a genuine base change of the " ++
        "curve together with its puncture. IUT initial-data conditions remain " ++
        "separate."
    dependsOn := [] }

end LeanFormal.IUT.Audit
