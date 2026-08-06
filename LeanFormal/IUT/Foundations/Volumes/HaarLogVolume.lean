import LeanFormal.IUT.Audit.Status
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

namespace LeanFormal.IUT

open MeasureTheory Set Metric

noncomputable section

def logClosedBallVolume
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) (x : E) (r : ℝ) : ℝ :=
  Real.log (μ.real (closedBall x r))

theorem addHaar_closedBall_unit_pos
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    [FiniteDimensional ℝ E] :
    0 < (Measure.addHaar : Measure E).real (closedBall (0 : E) 1) := by
  apply ENNReal.toReal_pos
  · exact (Measure.measure_pos_of_nonempty_interior
      (μ := (Measure.addHaar : Measure E))
      (show (interior (closedBall (0 : E) 1)).Nonempty from
        ⟨0, ball_subset_interior_closedBall (mem_ball_self (by positivity))⟩)).ne'
  · exact ne_top_of_lt (isCompact_closedBall _ _).measure_lt_top

theorem logClosedBallVolume_smul
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    [FiniteDimensional ℝ E]
    (μ : Measure E) [Measure.IsAddHaarMeasure μ]
    (x : E) {r : ℝ} (hr : 0 < r)
    (hbase_pos : 0 < μ.real (closedBall (0 : E) 1)) :
    logClosedBallVolume μ x r =
      (Module.finrank ℝ E : ℝ) * Real.log r +
        logClosedBallVolume μ (0 : E) 1 := by
  have hscale := Measure.addHaar_real_closedBall' μ x hr.le
  have hrpow : 0 < r ^ Module.finrank ℝ E := by positivity
  rw [logClosedBallVolume, logClosedBallVolume, hscale]
  rw [Real.log_mul (ne_of_gt hrpow) (ne_of_gt hbase_pos)]
  rw [Real.log_pow]

theorem addHaar_logClosedBallVolume_smul
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    [FiniteDimensional ℝ E]
    (x : E) {r : ℝ} (hr : 0 < r) :
    logClosedBallVolume (Measure.addHaar : Measure E) x r =
      (Module.finrank ℝ E : ℝ) * Real.log r +
        logClosedBallVolume (Measure.addHaar : Measure E) (0 : E) 1 := by
  exact logClosedBallVolume_smul (Measure.addHaar : Measure E) x hr
    addHaar_closedBall_unit_pos

end
end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def haarLogVolume : Obligation :=
  { id := "Foundations.Volumes.haar-log-volume"
    source := "Standard finite-dimensional Haar measure and log-volume arithmetic"
    status := VerificationStatus.proved
    note :=
      "Mathlib's additive Haar measure gives finite positive closed-ball volume " ++
        "in a finite-dimensional real normed space. Its exact scaling law and " ++
        "the corresponding logarithmic volume identity are proved. No IUT " ++
        "holomorphic-hull, local-field, or Frobenioid identification is assumed." }

end LeanFormal.IUT.Audit
