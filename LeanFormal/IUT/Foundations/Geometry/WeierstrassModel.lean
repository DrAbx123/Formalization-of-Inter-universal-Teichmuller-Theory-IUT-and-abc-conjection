import LeanFormal.IUT.Audit.Status
import Mathlib.AlgebraicGeometry.EllipticCurve.ModelsWithJ

/-!
  A concrete elliptic-curve model over an arbitrary field.

  Mathlib's `WeierstrassCurve.ofJ` gives an elliptic curve with prescribed
  j-invariant, including the characteristic 2/3 branches.  This is a genuine
  lower-layer construction; it is not the IUT initial-data theorem and carries
  none of the reduction or anabelian hypotheses.
-/

namespace LeanFormal.IUT

noncomputable def ellipticModelWithJ {F : Type*} [Field F] [DecidableEq F]
    (j : F) : {W : WeierstrassCurve F // W.IsElliptic} :=
  ⟨WeierstrassCurve.ofJ j, inferInstance⟩

theorem ellipticModelWithJ_j {F : Type*} [Field F] [DecidableEq F]
    (j : F) :
    ∀ h : (ellipticModelWithJ j).1.IsElliptic,
      @WeierstrassCurve.j F _ (ellipticModelWithJ j).1 h = j := by
  intro h
  change (WeierstrassCurve.ofJ j).j = j
  exact WeierstrassCurve.ofJ_j j

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def weierstrassModelArithmetic : Obligation :=
  { id := "Foundations.Geometry.weierstrass-model-with-j"
    source := "Standard elliptic-curve Weierstrass model theory"
    status := VerificationStatus.proved
    note :=
      "Mathlib's explicit ofJ model constructs an elliptic Weierstrass curve " ++
        "with any prescribed j-invariant; IUT reduction and anabelian input " ++
        "conditions remain outside this layer."
    dependsOn := [] }

end LeanFormal.IUT.Audit
