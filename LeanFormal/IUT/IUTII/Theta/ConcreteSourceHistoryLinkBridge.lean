import LeanFormal.IUT.IUTII.Theta.ConcreteSourceEtaleThetaBridge
import LeanFormal.IUT.IUTI.HodgeTheater.History
import LeanFormal.IUT.IUTI.HodgeTheater.LinkVolumeTransport
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.Volume
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.WeightedNormalization

/-!
  A source-facing finite history bridge for the concrete C-stage carrier.

  This module composes already proved pieces instead of introducing a new
  geometric existence claim.  The history is a dependent history of the
  actual finite Hodge-theater object; its endpoint, composite link, theta
  transport, determinant packet, tensor product, rescaling, and denominator
  normalization are all proved in their concrete types.  The construction
  remains algebraic: it does not identify this finite history with the
  source's anabelian distinct-history or with an etale fundamental group.
-/

namespace LeanFormal.IUT

open scoped BigOperators

noncomputable section

local instance gaussianPolynomialIrreducibleFactHistoryBridge :
    Fact (Irreducible
      (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

local instance fivePrimeFactHistoryBridge : Fact (Nat.Prime 5) :=
  ⟨Nat.prime_five⟩

local instance primeFactForHistoryBridge (l : PrimeGeFive) :
    Fact (Nat.Prime l.value) :=
  l.factPrime

namespace ConcreteSourceHistoryLinkBridge

open ConcreteSourceEtaleThetaBridge

abbrev sourceTheater (l : PrimeGeFive) := theater l

abbrev sourceCarrier (l : PrimeGeFive) := cStage l

abbrev sourceFiniteLabel (l : PrimeGeFive) := SignedLabel l.value

def sourceHistory (l : PrimeGeFive) :
    HodgeTheaterHistory l (FinitePrimePlace 2 7) (sourceTheater l) :=
  .cons (HodgeTheaterLink.refl (sourceTheater l))
    (.cons (HodgeTheaterLink.refl (sourceTheater l))
      (.singleton (sourceTheater l)))

theorem sourceHistory_terminal (l : PrimeGeFive) :
    (sourceHistory l).terminal = sourceTheater l := by
  rfl

theorem sourceHistory_length (l : PrimeGeFive) :
    (sourceHistory l).length = 3 := by
  rfl

theorem sourceHistory_length_pos (l : PrimeGeFive) :
    0 < (sourceHistory l).length := by
  exact HodgeTheaterHistory.length_pos (sourceHistory l)

theorem sourceHistory_composite_refl (l : PrimeGeFive) :
    (sourceHistory l).composite =
      HodgeTheaterLink.refl (sourceTheater l) := by
  rfl

theorem sourceHistory_composite_q (l : PrimeGeFive) :
    (sourceTheater l).thetaPacket.q =
      (sourceHistory l).terminal.thetaPacket.q := by
  exact HodgeTheaterHistory.composite_q (sourceHistory l)

theorem sourceHistory_q_self (l : PrimeGeFive) :
    (sourceHistory l).terminal.thetaPacket.q =
      (sourceTheater l).thetaPacket.q := by
  rfl

theorem sourceHistory_composite_scale (l : PrimeGeFive)
    (j : sourceFiniteLabel l) :
    (sourceTheater l).thetaPacket.scale j =
      (sourceHistory l).terminal.thetaPacket.scale j := by
  exact HodgeTheaterHistory.composite_scale (sourceHistory l) j

theorem sourceHistory_scale_self (l : PrimeGeFive)
    (j : sourceFiniteLabel l) :
    (sourceHistory l).terminal.thetaPacket.scale j =
      (sourceTheater l).thetaPacket.scale j := by
  rfl

theorem sourceHistory_composite_log_scale (l : PrimeGeFive)
    (j : sourceFiniteLabel l) :
    Real.log ((sourceTheater l).thetaPacket.scale j) =
      Real.log ((sourceHistory l).terminal.thetaPacket.scale j) := by
  exact (sourceHistory l).composite.log_scale_eq j

theorem sourceHistory_composite_log_volume (l : PrimeGeFive) :
    (sourceTheater l).thetaPacket.logVolume =
      (sourceHistory l).terminal.thetaPacket.logVolume := by
  exact (sourceHistory l).composite.log_volume_eq

theorem sourceHistory_scale_product (l : PrimeGeFive) :
    (∏ j : sourceFiniteLabel l, (sourceTheater l).thetaPacket.scale j) =
      ∏ j : sourceFiniteLabel l,
        (sourceHistory l).terminal.thetaPacket.scale j := by
  exact (sourceHistory l).composite.scale_product_eq

theorem sourceHistory_source_q_positive (l : PrimeGeFive) :
    0 < (sourceTheater l).thetaPacket.q := by
  exact (sourceTheater l).thetaPacket.q_pos

theorem sourceHistory_terminal_q_positive (l : PrimeGeFive) :
    0 < (sourceHistory l).terminal.thetaPacket.q := by
  exact (sourceHistory l).terminal.thetaPacket.q_pos

theorem sourceHistory_source_scale_positive (l : PrimeGeFive)
    (j : sourceFiniteLabel l) :
    0 < (sourceTheater l).thetaPacket.scale j := by
  exact (sourceTheater l).thetaPacket.scale_pos j

theorem sourceHistory_terminal_scale_positive (l : PrimeGeFive)
    (j : sourceFiniteLabel l) :
    0 < (sourceHistory l).terminal.thetaPacket.scale j := by
  exact (sourceHistory l).terminal.thetaPacket.scale_pos j

theorem sourceHistory_source_scale_nonzero (l : PrimeGeFive)
    (j : sourceFiniteLabel l) :
    (sourceTheater l).thetaPacket.scale j ≠ 0 := by
  exact (sourceTheater l).thetaPacket.scale_ne_zero j

theorem sourceHistory_terminal_scale_nonzero (l : PrimeGeFive)
    (j : sourceFiniteLabel l) :
    (sourceHistory l).terminal.thetaPacket.scale j ≠ 0 := by
  exact (sourceHistory l).terminal.thetaPacket.scale_ne_zero j

theorem sourceHistory_source_scale_neg (l : PrimeGeFive)
    (j : sourceFiniteLabel l) :
    (sourceTheater l).thetaPacket.scale (SignedLabel.neg j) =
      (sourceTheater l).thetaPacket.scale j := by
  exact (sourceTheater l).thetaPacket.scale_neg j

theorem sourceHistory_terminal_scale_neg (l : PrimeGeFive)
    (j : sourceFiniteLabel l) :
    (sourceHistory l).terminal.thetaPacket.scale (SignedLabel.neg j) =
      (sourceHistory l).terminal.thetaPacket.scale j := by
  exact (sourceHistory l).terminal.thetaPacket.scale_neg j

theorem sourceHistory_source_log_volume_sum (l : PrimeGeFive) :
    (sourceTheater l).thetaPacket.logVolume =
      ∑ j : sourceFiniteLabel l,
        Real.log ((sourceTheater l).thetaPacket.scale j) := by
  exact (sourceTheater l).thetaPacket.logVolume_eq_sum

theorem sourceHistory_terminal_log_volume_sum (l : PrimeGeFive) :
    (sourceHistory l).terminal.thetaPacket.logVolume =
      ∑ j : sourceFiniteLabel l,
        Real.log ((sourceHistory l).terminal.thetaPacket.scale j) := by
  exact (sourceHistory l).terminal.thetaPacket.logVolume_eq_sum

theorem sourceHistory_source_product_positive (l : PrimeGeFive) :
    0 < ∏ j : sourceFiniteLabel l,
      (sourceTheater l).thetaPacket.scale j := by
  apply Finset.prod_pos
  intro j hj
  exact sourceHistory_source_scale_positive l j

theorem sourceHistory_terminal_product_positive (l : PrimeGeFive) :
    0 < ∏ j : sourceFiniteLabel l,
      (sourceHistory l).terminal.thetaPacket.scale j := by
  apply Finset.prod_pos
  intro j hj
  exact sourceHistory_terminal_scale_positive l j

theorem sourceHistory_source_product_nonzero (l : PrimeGeFive) :
    (∏ j : sourceFiniteLabel l,
      (sourceTheater l).thetaPacket.scale j) ≠ 0 := by
  exact ne_of_gt (sourceHistory_source_product_positive l)

theorem sourceHistory_terminal_product_nonzero (l : PrimeGeFive) :
    (∏ j : sourceFiniteLabel l,
      (sourceHistory l).terminal.thetaPacket.scale j) ≠ 0 := by
  exact ne_of_gt (sourceHistory_terminal_product_positive l)

theorem sourceHistory_source_log_product (l : PrimeGeFive) :
    Real.log (∏ j : sourceFiniteLabel l,
      (sourceTheater l).thetaPacket.scale j) =
      (sourceTheater l).thetaPacket.logVolume := by
  rw [Real.log_prod (fun j _ => (sourceTheater l).thetaPacket.scale_ne_zero j)]
  exact (sourceHistory_source_log_volume_sum l).symm

theorem sourceHistory_terminal_log_product (l : PrimeGeFive) :
    Real.log (∏ j : sourceFiniteLabel l,
      (sourceHistory l).terminal.thetaPacket.scale j) =
      (sourceHistory l).terminal.thetaPacket.logVolume := by
  rw [Real.log_prod
    (fun j _ => (sourceHistory l).terminal.thetaPacket.scale_ne_zero j)]
  exact (sourceHistory_terminal_log_volume_sum l).symm

theorem sourceHistory_source_to_terminal_q (l : PrimeGeFive) :
    (sourceTheater l).thetaPacket.q =
      (sourceHistory l).terminal.thetaPacket.q := by
  exact (sourceHistory l).composite.theta_q_eq

theorem sourceHistory_source_to_terminal_scale (l : PrimeGeFive)
    (j : sourceFiniteLabel l) :
    (sourceTheater l).thetaPacket.scale j =
      (sourceHistory l).terminal.thetaPacket.scale j := by
  exact (sourceHistory l).composite.theta_scale_eq j

theorem sourceHistory_source_to_terminal_log_scale (l : PrimeGeFive)
    (j : sourceFiniteLabel l) :
    Real.log ((sourceTheater l).thetaPacket.scale j) =
      Real.log ((sourceHistory l).terminal.thetaPacket.scale j) := by
  exact (sourceHistory l).composite.log_scale_eq j

theorem sourceHistory_source_to_terminal_log_volume (l : PrimeGeFive) :
    (sourceTheater l).thetaPacket.logVolume =
      (sourceHistory l).terminal.thetaPacket.logVolume := by
  exact (sourceHistory l).composite.log_volume_eq

theorem sourceHistory_source_to_terminal_product (l : PrimeGeFive) :
    (∏ j : sourceFiniteLabel l,
      (sourceTheater l).thetaPacket.scale j) =
      ∏ j : sourceFiniteLabel l,
        (sourceHistory l).terminal.thetaPacket.scale j := by
  exact (sourceHistory l).composite.scale_product_eq

structure ConcreteSourceHistoryLinkOutput (l : PrimeGeFive) where
  cStage : ConcreteInitialThetaCStage l
  level : AlgebraicFiniteThetaLevel l
  history : HodgeTheaterHistory l (FinitePrimePlace 2 7) (sourceTheater l)
  history_eq_sourceHistory : history = sourceHistory l
  sourceModel : Iut.FrobenioidPresentation
  sourceModel_eq : sourceModel = ConcreteSourceEtaleThetaBridge.sourceModel
  terminal : HodgeTheater l (FinitePrimePlace 2 7)
  terminal_eq : terminal = history.terminal
  packet_volume : terminal.thetaPacket.logVolume = thetaLogVolume l

noncomputable def concreteSourceHistoryLinkOutput (l : PrimeGeFive) :
    ConcreteSourceHistoryLinkOutput l where
  cStage := cStage l
  level := algebraicFiniteThetaLevel l
  history := sourceHistory l
  history_eq_sourceHistory := rfl
  sourceModel := ConcreteSourceEtaleThetaBridge.sourceModel
  sourceModel_eq := rfl
  terminal := sourceTheater l
  terminal_eq := rfl
  packet_volume := rfl

@[simp] theorem history_output_cStage (l : PrimeGeFive) :
    (concreteSourceHistoryLinkOutput l).cStage = cStage l :=
  rfl

@[simp] theorem history_output_level (l : PrimeGeFive) :
    (concreteSourceHistoryLinkOutput l).level = algebraicFiniteThetaLevel l :=
  rfl

@[simp] theorem history_output_history (l : PrimeGeFive) :
    (concreteSourceHistoryLinkOutput l).history = sourceHistory l :=
  rfl

@[simp] theorem history_output_model (l : PrimeGeFive) :
    (concreteSourceHistoryLinkOutput l).sourceModel =
      ConcreteSourceEtaleThetaBridge.sourceModel :=
  rfl

@[simp] theorem history_output_terminal (l : PrimeGeFive) :
    (concreteSourceHistoryLinkOutput l).terminal = sourceTheater l :=
  rfl

theorem history_output_terminal_eq_history (l : PrimeGeFive) :
    (concreteSourceHistoryLinkOutput l).terminal =
      (concreteSourceHistoryLinkOutput l).history.terminal :=
  (concreteSourceHistoryLinkOutput l).terminal_eq

theorem history_output_packet_volume (l : PrimeGeFive) :
    (concreteSourceHistoryLinkOutput l).terminal.thetaPacket.logVolume =
      thetaLogVolume l :=
  (concreteSourceHistoryLinkOutput l).packet_volume

theorem history_output_model_connection (l : PrimeGeFive) :
    (concreteSourceHistoryLinkOutput l).sourceModel = sourceModel :=
  (concreteSourceHistoryLinkOutput l).sourceModel_eq

theorem history_output_generator_order (l : PrimeGeFive) :
    addOrderOf (generator l) = l.value :=
  generator_order l

theorem history_output_kernel (l : PrimeGeFive) :
    (reduction l).ker = AddSubgroup.zmultiples (l.value : ℤ) :=
  reduction_kernel l

def sourcePositivePacket (l : PrimeGeFive) :
    PositivePacket (sourceFiniteLabel l) where
  scale j := thetaScale l j
  positive j := theta_scale_pos l j

@[simp] theorem sourcePositivePacket_scale (l : PrimeGeFive)
    (j : sourceFiniteLabel l) :
    (sourcePositivePacket l).scale j = thetaScale l j :=
  rfl

theorem sourcePositivePacket_positive (l : PrimeGeFive)
    (j : sourceFiniteLabel l) :
    0 < (sourcePositivePacket l).scale j :=
  (sourcePositivePacket l).positive j

theorem sourcePositivePacket_nonzero (l : PrimeGeFive)
    (j : sourceFiniteLabel l) :
    (sourcePositivePacket l).scale j ≠ 0 :=
  ne_of_gt (sourcePositivePacket_positive l j)

theorem sourcePositivePacket_det_eq_product (l : PrimeGeFive) :
    packetDet (sourcePositivePacket l) =
      ∏ j : sourceFiniteLabel l, thetaScale l j := by
  rw [packetDet_eq_prod]
  rfl

theorem sourcePositivePacket_log_volume_eq_sum (l : PrimeGeFive) :
    packetLogVolume (sourcePositivePacket l) =
      ∑ j : sourceFiniteLabel l, thetaLogScale l j := by
  rfl

theorem sourcePositivePacket_log_volume_eq_theta (l : PrimeGeFive) :
    packetLogVolume (sourcePositivePacket l) = thetaLogVolume l := by
  rw [sourcePositivePacket_log_volume_eq_sum, theta_log_volume_eq_sum]

theorem sourcePositivePacket_log_det (l : PrimeGeFive) :
    packetLogVolume (sourcePositivePacket l) =
      Real.log (packetDet (sourcePositivePacket l)) := by
  exact packetLogVolume_eq_log_det (sourcePositivePacket l)

theorem sourcePositivePacket_log_det_eq_theta (l : PrimeGeFive) :
    Real.log (packetDet (sourcePositivePacket l)) = thetaLogVolume l := by
  rw [← sourcePositivePacket_log_det l,
    sourcePositivePacket_log_volume_eq_theta]

theorem sourcePositivePacket_det_positive (l : PrimeGeFive) :
    0 < packetDet (sourcePositivePacket l) := by
  rw [sourcePositivePacket_det_eq_product]
  apply Finset.prod_pos
  intro j hj
  exact theta_scale_pos l j

theorem sourcePositivePacket_det_nonzero (l : PrimeGeFive) :
    packetDet (sourcePositivePacket l) ≠ 0 := by
  exact ne_of_gt (sourcePositivePacket_det_positive l)

theorem sourcePositivePacket_det_exp_log (l : PrimeGeFive) :
    Real.exp (thetaLogVolume l) = packetDet (sourcePositivePacket l) := by
  rw [← sourcePositivePacket_log_det_eq_theta l]
  exact Real.exp_log (sourcePositivePacket_det_positive l)

def sourceTensorPacket (l : PrimeGeFive) :
    PositivePacket (sourceFiniteLabel l × sourceFiniteLabel l) :=
  tensorPacket (sourcePositivePacket l) (sourcePositivePacket l)

theorem sourceTensorPacket_scale (l : PrimeGeFive)
    (i j : sourceFiniteLabel l) :
    (sourceTensorPacket l).scale (i, j) = thetaScale l i * thetaScale l j :=
  rfl

theorem sourceTensorPacket_positive (l : PrimeGeFive)
    (ij : sourceFiniteLabel l × sourceFiniteLabel l) :
    0 < (sourceTensorPacket l).scale ij :=
  (sourceTensorPacket l).positive ij

theorem sourceTensorPacket_det (l : PrimeGeFive) :
    packetDet (sourceTensorPacket l) =
      packetDet (sourcePositivePacket l) ^ Fintype.card (sourceFiniteLabel l) *
        packetDet (sourcePositivePacket l) ^ Fintype.card (sourceFiniteLabel l) := by
  exact packetDet_tensor (sourcePositivePacket l) (sourcePositivePacket l)

theorem sourceTensorPacket_det_pow (l : PrimeGeFive) :
    packetDet (sourceTensorPacket l) =
      packetDet (sourcePositivePacket l) ^
        (2 * Fintype.card (sourceFiniteLabel l)) := by
  rw [sourceTensorPacket_det]
  rw [← pow_add]
  congr 1
  omega

theorem sourceTensorPacket_log_volume (l : PrimeGeFive) :
    packetLogVolume (sourceTensorPacket l) =
      (2 * (Fintype.card (sourceFiniteLabel l) : Real)) *
          packetLogVolume (sourcePositivePacket l) := by
  change packetLogVolume
    (tensorPacket (sourcePositivePacket l) (sourcePositivePacket l)) = _
  rw [packetLogVolume_tensor]
  ring

theorem sourceTensorPacket_log_volume_eq_theta (l : PrimeGeFive) :
    packetLogVolume (sourceTensorPacket l) =
      (2 * (Fintype.card (sourceFiniteLabel l) : Real)) * thetaLogVolume l := by
  rw [sourceTensorPacket_log_volume,
    sourcePositivePacket_log_volume_eq_theta]

def sourceRescaledPacket (l : PrimeGeFive) (c : Real) (hc : 0 < c) :
    PositivePacket (sourceFiniteLabel l) :=
  rescalePacket c hc (sourcePositivePacket l)

theorem sourceRescaledPacket_scale (l : PrimeGeFive) (c : Real) (hc : 0 < c)
    (j : sourceFiniteLabel l) :
    (sourceRescaledPacket l c hc).scale j = c * thetaScale l j :=
  rfl

theorem sourceRescaledPacket_positive (l : PrimeGeFive) (c : Real) (hc : 0 < c)
    (j : sourceFiniteLabel l) :
    0 < (sourceRescaledPacket l c hc).scale j :=
  (sourceRescaledPacket l c hc).positive j

theorem sourceRescaledPacket_det (l : PrimeGeFive) (c : Real) (hc : 0 < c) :
    packetDet (sourceRescaledPacket l c hc) =
      c ^ Fintype.card (sourceFiniteLabel l) *
        packetDet (sourcePositivePacket l) := by
  exact packetDet_rescale c hc (sourcePositivePacket l)

theorem sourceRescaledPacket_log_volume (l : PrimeGeFive) (c : Real) (hc : 0 < c) :
    packetLogVolume (sourceRescaledPacket l c hc) =
      (Fintype.card (sourceFiniteLabel l) : Real) * Real.log c +
        thetaLogVolume l := by
  change packetLogVolume
    (rescalePacket c hc (sourcePositivePacket l)) = _
  rw [packetLogVolume_rescale,
    sourcePositivePacket_log_volume_eq_theta]

theorem sourceRescaledPacket_log_det (l : PrimeGeFive) (c : Real) (hc : 0 < c) :
    packetLogVolume (sourceRescaledPacket l c hc) =
      Real.log (packetDet (sourceRescaledPacket l c hc)) := by
  exact packetLogVolume_eq_log_det (sourceRescaledPacket l c hc)

def sourceNormalizationPacket : WeightedDeterminantPacket (Fin 2) where
  hullLogDegree := fun _ => 0
  structureSheafLogDegree := 0
  denominator := fun i => if i = 0 then 2 else 4

theorem sourceNormalizationPacket_denominator_zero :
    sourceNormalizationPacket.denominator 0 = 2 := by
  rfl

theorem sourceNormalizationPacket_denominator_one :
    sourceNormalizationPacket.denominator 1 = 4 := by
  rfl

theorem sourceNormalizationPacket_common_degree :
    sourceNormalizationPacket.commonTensorDegree = 8 := by
  exact WeightedDeterminantPacket.denominator_two_four_commonTensorDegree
    sourceNormalizationPacket sourceNormalizationPacket_denominator_zero
      sourceNormalizationPacket_denominator_one

theorem sourceNormalizationPacket_weighted_identity :
    sourceNormalizationPacket.weightedLogVolume =
      (sourceNormalizationPacket.commonTensorDegree : Real) *
        sourceNormalizationPacket.normalizedLogVolume := by
  exact sourceNormalizationPacket.weightedLogVolume_eq_commonTensorDegree_mul_normalizedLogVolume

theorem sourceNormalizationPacket_degree_positive :
    0 < sourceNormalizationPacket.commonTensorDegree := by
  exact sourceNormalizationPacket.commonTensorDegree_pos

def sourceHistoryDeterminant (l : PrimeGeFive) : Real :=
  packetDet (sourcePositivePacket l)

theorem sourceHistoryDeterminant_eq_product (l : PrimeGeFive) :
    sourceHistoryDeterminant l =
      ∏ j : sourceFiniteLabel l, thetaScale l j := by
  exact sourcePositivePacket_det_eq_product l

theorem sourceHistoryDeterminant_positive (l : PrimeGeFive) :
    0 < sourceHistoryDeterminant l := by
  exact sourcePositivePacket_det_positive l

theorem sourceHistoryDeterminant_nonzero (l : PrimeGeFive) :
    sourceHistoryDeterminant l ≠ 0 := by
  exact sourcePositivePacket_det_nonzero l

theorem sourceHistoryDeterminant_log (l : PrimeGeFive) :
    Real.log (sourceHistoryDeterminant l) = thetaLogVolume l := by
  exact sourcePositivePacket_log_det_eq_theta l

theorem sourceHistoryDeterminant_exp (l : PrimeGeFive) :
    Real.exp (thetaLogVolume l) = sourceHistoryDeterminant l := by
  exact sourcePositivePacket_det_exp_log l

theorem sourceHistoryDeterminant_tensor (l : PrimeGeFive) :
    packetDet (sourceTensorPacket l) =
      sourceHistoryDeterminant l ^ Fintype.card (sourceFiniteLabel l) *
        sourceHistoryDeterminant l ^ Fintype.card (sourceFiniteLabel l) := by
  exact sourceTensorPacket_det l

theorem sourceHistoryDeterminant_tensor_log (l : PrimeGeFive) :
    Real.log (packetDet (sourceTensorPacket l)) =
      (2 * (Fintype.card (sourceFiniteLabel l) : Real)) * thetaLogVolume l := by
  rw [← sourceTensorPacket_log_volume_eq_theta,
    (packetLogVolume_eq_log_det (sourceTensorPacket l)).symm]

theorem source_history_model_and_packet (l : PrimeGeFive) :
    (concreteSourceHistoryLinkOutput l).sourceModel = sourceModel ∧
      packetLogVolume (sourcePositivePacket l) = thetaLogVolume l := by
  exact ⟨history_output_model_connection l,
    sourcePositivePacket_log_volume_eq_theta l⟩

theorem source_history_level_kernel (l : PrimeGeFive) :
    Function.Injective (concreteSourceHistoryLinkOutput l).level.quotientEquiv := by
  exact (concreteSourceHistoryLinkOutput l).level.quotientEquiv_injective

theorem source_history_level_surjective (l : PrimeGeFive) :
    Function.Surjective (concreteSourceHistoryLinkOutput l).level.quotientEquiv := by
  exact (concreteSourceHistoryLinkOutput l).level.quotientEquiv_surjective

theorem source_history_level_generator (l : PrimeGeFive) :
    (concreteSourceHistoryLinkOutput l).level.generator = reduction l 1 := by
  exact (concreteSourceHistoryLinkOutput l).level.generator_eq_reduction_one

theorem source_history_level_roots (l : PrimeGeFive) (n : ℤ) :
    (packet l).integerRoot n = (roots l).roots (n : ℚ) := by
  exact integer_root_compatible l n

theorem source_history_q_deck_fixes_generator
    (l : PrimeGeFive) (sigma : ConcreteTateParameter.LocalAbsoluteGalois l) :
    qDeckAction l sigma (QuotientGroup.mk (parameter l).qUnit) =
      QuotientGroup.mk (parameter l).qUnit := by
  exact q_deck_action_fixes_generator l sigma

theorem source_history_q_deck_preserves_power
    (l : PrimeGeFive) (sigma : ConcreteTateParameter.LocalAbsoluteGalois l)
    (x : (AlgebraicClosure ℚ_[l.value])ˣ) (n : ℤ) :
    qDeckAction l sigma (QuotientGroup.mk (x ^ n)) =
      QuotientGroup.mk ((parameter l).unitsGaloisEquiv sigma x ^ n) := by
  exact q_deck_action_preserves_power l sigma x n

theorem source_history_reduction_additive (l : PrimeGeFive) (m n : ℤ) :
    reduction l (m + n) = reduction l m + reduction l n := by
  exact map_add (reduction l) m n

theorem source_history_reduction_kernel_exact (l : PrimeGeFive) :
    (reduction l).ker = AddSubgroup.zmultiples (l.value : ℤ) :=
  reduction_kernel l

theorem source_history_quotient_zero_iff (l : PrimeGeFive) (n : ℤ) :
    (QuotientAddGroup.mk n : quotient l) = 0 ↔
      n ∈ AddSubgroup.zmultiples (l.value : ℤ) := by
  exact quotient_zero_iff_multiple l n

theorem source_history_quotient_add_multiple (l : PrimeGeFive) (n k : ℤ) :
    (QuotientAddGroup.mk (n + (l.value : ℤ) * k) : quotient l) =
      QuotientAddGroup.mk n := by
  exact quotient_mk_add_multiple l n k

theorem source_history_quotient_sub_multiple (l : PrimeGeFive) (n k : ℤ) :
    (QuotientAddGroup.mk (n - (l.value : ℤ) * k) : quotient l) =
      QuotientAddGroup.mk n := by
  exact quotient_mk_sub_multiple l n k

theorem source_history_scale_neg_invariant (l : PrimeGeFive)
    (j : sourceFiniteLabel l) :
    (sourcePositivePacket l).scale (SignedLabel.neg j) =
      (sourcePositivePacket l).scale j := by
  exact theta_scale_neg l j

theorem source_history_log_scale_formula (l : PrimeGeFive)
    (j : sourceFiniteLabel l) :
    Real.log ((sourcePositivePacket l).scale j) =
      Real.log gaussianFiveThetaQ * (gaussExponent j.1).toNat := by
  exact theta_log_scale_eq l j

theorem source_history_log_volume_formula (l : PrimeGeFive) :
    packetLogVolume (sourcePositivePacket l) =
      ∑ j : sourceFiniteLabel l,
        Real.log gaussianFiveThetaQ * (gaussExponent j.1).toNat := by
  rw [sourcePositivePacket_log_volume_eq_sum]
  apply Finset.sum_congr rfl
  intro j hj
  exact source_history_log_scale_formula l j

theorem source_history_log_volume_local_degree (l : PrimeGeFive) :
    packetLogVolume (sourcePositivePacket l) =
      ∑ j : sourceFiniteLabel l,
        (gaussExponent j.1).toNat *
          Multiplicative.toAdd (localUnitNormDegreeFor 5 (localQParameterFor 5)) := by
  rw [sourcePositivePacket_log_volume_eq_theta,
    theta_log_volume_eq_local_degree_sum]

theorem source_history_source_terminal_volume_equal (l : PrimeGeFive) :
    (sourceTheater l).thetaPacket.logVolume =
      (sourceHistory l).terminal.thetaPacket.logVolume := by
  exact sourceHistory_source_to_terminal_log_volume l

theorem source_history_source_terminal_product_equal (l : PrimeGeFive) :
    (∏ j : sourceFiniteLabel l,
      (sourceTheater l).thetaPacket.scale j) =
      ∏ j : sourceFiniteLabel l,
        (sourceHistory l).terminal.thetaPacket.scale j := by
  exact sourceHistory_source_to_terminal_product l

end ConcreteSourceHistoryLinkBridge

end

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def concreteSourceHistoryLinkBridge : Obligation :=
  { id := "IUT-I-II.concrete-source-history-link-volume-bridge"
    source := "IUT I-II, Hodge theaters, histories, theta links; IUT III Step XI arithmetic kernel"
    status := VerificationStatus.proved
    note :=
      "The concrete C-stage theater is placed in a dependent finite history. " ++
        "Its endpoint and composite link transport q, every theta scale, the " ++
        "finite scale product, and log-volume. The same packet is connected to " ++
        "the proved determinant/tensor/rescaling identities and to a concrete " ++
        "denominator-clearing normalization certificate. This remains an " ++
        "algebraic finite history: no distinct anabelian history, etale " ++
        "fundamental-group identification, or holomorphic hull is claimed."
    dependsOn :=
      [ "IUT-I-II.concrete-source-algebraic-theta-bridge",
        "IUT-I.hodge-theater-history-composition",
        "IUT-I.hodge-theater-link-log-volume-transport",
        "IUT-III.holomorphic-hull-determinant-log-volume",
        "IUT-III.remark-3-9-5-weighted-determinant-normalization" ] }

end LeanFormal.IUT.Audit
