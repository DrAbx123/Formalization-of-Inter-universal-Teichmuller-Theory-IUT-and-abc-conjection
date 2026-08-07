import LeanFormal.IUT.Foundations.Geometry.ReductionBaseChange
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.Tactic

namespace LeanFormal.IUT

noncomputable section

def concreteSplitCurve : WeierstrassCurve ℚ :=
  WeierstrassCurve.mk 1 0 0 0 5

theorem concreteSplitCurve_a₁ : (concreteSplitCurve).a₁ = (1 : ℚ) := by
  rfl

theorem concreteSplitCurve_a₂ : (concreteSplitCurve).a₂ = (0 : ℚ) := by
  rfl

theorem concreteSplitCurve_a₃ : (concreteSplitCurve).a₃ = (0 : ℚ) := by
  rfl

theorem concreteSplitCurve_a₄ : (concreteSplitCurve).a₄ = (0 : ℚ) := by
  rfl

theorem concreteSplitCurve_a₆ : (concreteSplitCurve).a₆ = (5 : ℚ) := by
  rfl

theorem concreteSplitCurve_b₂ : (concreteSplitCurve).b₂ = (1 : ℚ) := by
  norm_num [concreteSplitCurve, WeierstrassCurve.b₂]

theorem concreteSplitCurve_b₄ : (concreteSplitCurve).b₄ = (0 : ℚ) := by
  norm_num [concreteSplitCurve, WeierstrassCurve.b₄]

theorem concreteSplitCurve_b₆ : (concreteSplitCurve).b₆ = (20 : ℚ) := by
  norm_num [concreteSplitCurve, WeierstrassCurve.b₆]

theorem concreteSplitCurve_b₈ : (concreteSplitCurve).b₈ = (5 : ℚ) := by
  norm_num [concreteSplitCurve, WeierstrassCurve.b₈]

theorem concreteSplitCurve_c₄ : (concreteSplitCurve).c₄ = (1 : ℚ) := by
  norm_num [concreteSplitCurve, WeierstrassCurve.c₄,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄]

theorem concreteSplitCurve_c₆ : (concreteSplitCurve).c₆ = (-4321 : ℚ) := by
  norm_num [concreteSplitCurve, WeierstrassCurve.c₆,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆]

theorem concreteSplitCurve_delta : (concreteSplitCurve).Δ = (-10805 : ℚ) := by
  norm_num [concreteSplitCurve, WeierstrassCurve.Δ,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]

theorem concreteSplitCurve_delta_ne_zero : (concreteSplitCurve).Δ ≠ 0 := by
  rw [concreteSplitCurve_delta]
  norm_num

instance concreteSplitCurve_isElliptic : (concreteSplitCurve).IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff]
  rw [concreteSplitCurve_delta]
  norm_num

def concreteSplitPuncturedCurve : PuncturedEllipticCurve ℚ :=
  { curve := concreteSplitCurve
    isElliptic := inferInstance
    puncture := ⟨WeierstrassCurve.Projective.nonsingularLift_zero⟩ }

end

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def concreteSplitMultiplicativeCurve : Obligation :=
  { id := "Foundations.Geometry.concrete-split-multiplicative-curve"
    source := "Standard Weierstrass arithmetic; IUT I, Definition 3.1(b)"
    status := VerificationStatus.proved
    note :=
      "The explicit curve y^2 + xy = x^3 + 5 over Q has nonzero " ++
        "discriminant, c4 = 1, and a fully checked projective puncture. " ++
        "The local split-reduction transport is recorded in dependent modules."
    dependsOn := ["Foundations.Geometry.punctured-elliptic-curve"] }

end LeanFormal.IUT.Audit
