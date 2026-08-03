import LeanFormal.IUT.Audit.Status
import LeanFormal.IUT.Foundations.Volumes.WeightedVolume
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Fintype.Prod
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
  A finite, source-oriented arithmetic kernel for the Step-(xi) bookkeeping.

  The paper's holomorphic hull and determinant/tensor normalization are not
  constructed here.  Instead, this file isolates the finite positive-packet
  identities that any such construction must satisfy.  The packet carries its
  positivity proof explicitly, so the logarithm and determinant calculations
  cannot silently cross zero.  This is a proved model layer, not an IUT
  existence theorem.
-/

namespace LeanFormal.IUT

open scoped BigOperators

structure PositivePacket (label : Type*) [Fintype label] where
  scale : label → Real
  positive : ∀ i, 0 < scale i

noncomputable def packetDet {label : Type*} [Fintype label]
    (packet : PositivePacket label) : Real := by
  classical
  exact Matrix.det (Matrix.diagonal packet.scale)

noncomputable def packetLogVolume {label : Type*} [Fintype label]
    (packet : PositivePacket label) : Real := by
  classical
  exact ∑ i, Real.log (packet.scale i)

theorem packetDet_eq_prod {label : Type*} [Fintype label]
    (packet : PositivePacket label) :
    packetDet packet = ∏ i, packet.scale i := by
  classical
  unfold packetDet
  exact Matrix.det_diagonal

theorem packetLogVolume_eq_log_det {label : Type*} [Fintype label]
    (packet : PositivePacket label) :
    packetLogVolume packet = Real.log (packetDet packet) := by
  rw [packetDet_eq_prod]
  symm
  exact Real.log_prod (fun i hi => (ne_of_gt (packet.positive i)))

def tensorPacket {α β : Type*} [Fintype α] [Fintype β]
    (p : PositivePacket α) (q : PositivePacket β) : PositivePacket (α × β) where
  scale ij := p.scale ij.1 * q.scale ij.2
  positive ij := mul_pos (p.positive ij.1) (q.positive ij.2)

theorem packetDet_tensor {α β : Type*} [Fintype α] [Fintype β]
    (p : PositivePacket α) (q : PositivePacket β) :
    packetDet (tensorPacket p q) =
      packetDet p ^ Fintype.card β * packetDet q ^ Fintype.card α := by
  classical
  rw [packetDet_eq_prod, packetDet_eq_prod, packetDet_eq_prod]
  change (∏ i : α × β, p.scale i.1 * q.scale i.2) = _
  rw [← Finset.univ_product_univ,
    Finset.prod_product' (Finset.univ : Finset α) (Finset.univ : Finset β)
      (fun i j => p.scale i * q.scale j)]
  calc
    (∏ x : α, ∏ y : β, p.scale x * q.scale y) =
        ∏ x : α, (p.scale x) ^ Fintype.card β * ∏ y : β, q.scale y := by
      apply Finset.prod_congr rfl
      intro x hx
      rw [← Finset.pow_card_mul_prod]
      simp only [Finset.card_univ]
    _ = (∏ x : α, (p.scale x) ^ Fintype.card β) *
        ∏ x : α, (∏ y : β, q.scale y) := by
      rw [Finset.prod_mul_distrib]
    _ = (∏ x : α, p.scale x) ^ Fintype.card β *
        (∏ y : β, q.scale y) ^ Fintype.card α := by
      rw [Finset.prod_pow, Finset.prod_const]
      simp

theorem packetLogVolume_tensor {α β : Type*} [Fintype α] [Fintype β]
    (p : PositivePacket α) (q : PositivePacket β) :
    packetLogVolume (tensorPacket p q) =
      (Fintype.card β : Real) * packetLogVolume p +
        (Fintype.card α : Real) * packetLogVolume q := by
  classical
  unfold packetLogVolume tensorPacket
  change (∑ i : α × β, Real.log (p.scale i.1 * q.scale i.2)) = _
  rw [← Finset.univ_product_univ,
    Finset.sum_product' (Finset.univ : Finset α) (Finset.univ : Finset β)
      (fun i j => Real.log (p.scale i * q.scale j))]
  have hlog : ∀ i : α, ∀ j : β,
      Real.log (p.scale i * q.scale j) =
        Real.log (p.scale i) + Real.log (q.scale j) := by
    intro i j
    exact Real.log_mul (ne_of_gt (p.positive i)) (ne_of_gt (q.positive j))
  simp_rw [hlog]
  calc
    (∑ x : α, (∑ y : β, (Real.log (p.scale x) + Real.log (q.scale y)))) =
        ∑ x : α, ((Fintype.card β : Real) * Real.log (p.scale x) +
          (∑ y : β, Real.log (q.scale y))) := by
      apply Finset.sum_congr rfl
      intro x hx
      simp [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ]
    _ = (Fintype.card β : Real) * packetLogVolume p +
        (Fintype.card α : Real) * packetLogVolume q := by
      rw [Finset.sum_add_distrib]
      simp [Finset.mul_sum, Finset.sum_const, Finset.card_univ, packetLogVolume]

def rescalePacket {label : Type*} [Fintype label]
    (c : Real) (hc : 0 < c) (packet : PositivePacket label) :
    PositivePacket label where
  scale i := c * packet.scale i
  positive i := mul_pos hc (packet.positive i)

theorem packetDet_rescale {label : Type*} [Fintype label]
    (c : Real) (hc : 0 < c) (packet : PositivePacket label) :
    packetDet (rescalePacket c hc packet) =
      c ^ Fintype.card label * packetDet packet := by
  rw [packetDet_eq_prod, packetDet_eq_prod]
  simp [rescalePacket, Finset.prod_mul_distrib, Finset.prod_const, mul_comm]

theorem packetLogVolume_rescale {label : Type*} [Fintype label]
    (c : Real) (hc : 0 < c) (packet : PositivePacket label) :
    packetLogVolume (rescalePacket c hc packet) =
      (Fintype.card label : Real) * Real.log c + packetLogVolume packet := by
  classical
  unfold packetLogVolume rescalePacket
  have hlog : ∀ i : label,
      Real.log (c * packet.scale i) = Real.log c + Real.log (packet.scale i) := by
    intro i
    exact Real.log_mul (ne_of_gt hc) (ne_of_gt (packet.positive i))
  simp_rw [hlog]
  rw [Finset.sum_add_distrib]
  simp [Finset.sum_const, Finset.card_univ]

structure FiniteHull (label : Type*) [Fintype label] where
  volume : label → Real
  hullVolume : Real
  contains : ∀ i, volume i ≤ hullVolume

theorem FiniteHull.average_le {label : Type*} [Fintype label]
    (hull : FiniteHull label) (data : WeightedValues label)
    (hvalue : ∀ i, data.value i = hull.volume i)
    (hw : ∀ i, 0 ≤ data.weight i) :
    data.average ≤ hull.hullVolume := by
  apply WeightedValues.average_le_of_pointwise data hw
  intro i
  rw [hvalue]
  exact hull.contains i

structure StepXIFiniteCertificate (label : Type*) [Fintype label] where
  hull : FiniteHull label
  weighted : WeightedValues label
  weighted_matches_hull : ∀ i, weighted.value i = hull.volume i
  weights_nonnegative : ∀ i, 0 ≤ weighted.weight i
  qSigned : Real
  thetaSigned : Real
  q_le_hull : qSigned ≤ hull.hullVolume
  hull_le_theta : hull.hullVolume ≤ thetaSigned
  q_negative : qSigned < 0

theorem StepXIFiniteCertificate.q_le_theta
    {label : Type*} [Fintype label]
    (certificate : StepXIFiniteCertificate label) :
    certificate.qSigned ≤ certificate.thetaSigned := by
  exact le_trans certificate.q_le_hull certificate.hull_le_theta

theorem StepXIFiniteCertificate.q_positive
    {label : Type*} [Fintype label]
    (certificate : StepXIFiniteCertificate label) :
    0 < -certificate.qSigned := by
  exact neg_pos.mpr certificate.q_negative

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def hullDeterminantLogVolume : Obligation :=
  { id := "IUT-III.holomorphic-hull-determinant-log-volume"
    source := "IUT III, Corollary 3.12 proof, Steps (xi-d)-(xi-g)"
    status := VerificationStatus.interface
    note :=
      "Finite positive-packet determinant, tensor, rescaling, and hull-average " ++
        "identities are proved; the paper's holomorphic hull and source-facing " ++
        "log-volume construction remain pending." }

end LeanFormal.IUT.Audit
