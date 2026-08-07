import LeanFormal.IUT.IUTIII.Theorem311.ConcreteFiniteModelTransport
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.Volume
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.WeightedNormalization
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.FiniteCertificateBridge

namespace LeanFormal.IUT

open scoped BigOperators

noncomputable section

namespace ConcreteFiniteStepXI

def finiteSup {α : Type*} [Fintype α] [Nonempty α]
    (f : α → Real) : Real :=
  Finset.univ.sup' Finset.univ_nonempty f

theorem le_finiteSup {α : Type*} [Fintype α] [Nonempty α]
    (f : α → Real) (i : α) : f i ≤ finiteSup f := by
  exact Finset.le_sup' f (Finset.mem_univ i)

theorem finiteSup_le {α : Type*} [Fintype α] [Nonempty α]
    (f : α → Real) (b : Real) (h : ∀ i, f i ≤ b) :
    finiteSup f ≤ b := by
  exact Finset.sup'_le _ _ (fun i _ => h i)

def finiteHullOfValues {α : Type*} [Fintype α] [Nonempty α]
    (f : α → Real) : FiniteHull α where
  volume := f
  hullVolume := finiteSup f
  contains := le_finiteSup f

def boundedSet (f : Set Real) (b : Real) : Prop :=
  ∀ x ∈ f, x ≤ b

theorem boundedSet_range {α : Type*} (f : α → Real) (b : Real)
    (h : ∀ i, f i ≤ b) : boundedSet (Set.range f) b := by
  intro x hx
  rcases hx with ⟨i, rfl⟩
  exact h i

def lowerFiniteSup {α : Type*} [Fintype α] [Nonempty α]
    (f : α → Real) : Real := -finiteSup (fun i => -f i)

theorem lowerFiniteSup_le {α : Type*} [Fintype α] [Nonempty α]
    (f : α → Real) (i : α) : lowerFiniteSup f ≤ f i := by
  unfold lowerFiniteSup
  linarith [le_finiteSup (fun j => -f j) i]

theorem WeightedValues.lower_le_average_of_pointwise
    {label : Type*} [Fintype label]
    (data : WeightedValues label) (hw : ∀ j, 0 ≤ data.weight j)
    {bound : Real} (hv : ∀ j, bound ≤ data.value j) :
    bound ≤ data.average := by
  unfold WeightedValues.average
  rw [le_div_iff₀ data.weightTotal_pos]
  calc
    bound * data.weightTotal =
        Finset.univ.sum (fun j => data.weight j * bound) := by
      rw [data.weightTotal_eq_sum]
      calc
        bound * Finset.univ.sum data.weight =
            ∑ j : label, bound * data.weight j := by
          rw [Finset.mul_sum]
        _ = ∑ j : label, data.weight j * bound := by
          apply Finset.sum_congr rfl
          intro j hj
          ring
    _ ≤ Finset.univ.sum (fun j => data.weight j * data.value j) := by
      exact Finset.sum_le_sum (fun j _ =>
        mul_le_mul_of_nonneg_left (hv j) (hw j))


abbrev finiteQuotientCarrier (l : PrimeGeFive) (N : Nat) :=
  ConcreteFiniteTheorem311.finiteLabel l × Fin (N + 1)

structure FiniteColumnIndex (l : PrimeGeFive) (N : Nat) where
  procession : ConcreteFiniteTheorem311.finiteLabel l
  tensor : ConcreteFiniteTheorem311.finiteLabel l
  level : Fin (N + 1)
deriving DecidableEq, Fintype

namespace FiniteColumnIndex

variable {l : PrimeGeFive} {N : Nat}

instance nonempty : Nonempty (FiniteColumnIndex l N) := by
  refine ⟨{ procession := 0, tensor := 0, level := ⟨0, by omega⟩ }⟩

def base : FiniteColumnIndex l N :=
  { procession := 0, tensor := 0, level := ⟨0, by omega⟩ }

@[simp] theorem base_procession : (base : FiniteColumnIndex l N).procession = 0 := rfl

@[simp] theorem base_tensor : (base : FiniteColumnIndex l N).tensor = 0 := rfl

@[simp] theorem base_level : (base : FiniteColumnIndex l N).level = 0 := rfl

@[simp] theorem procession_mk (a b : ConcreteFiniteTheorem311.finiteLabel l)
    (k : Fin (N + 1)) :
    (⟨a, b, k⟩ : FiniteColumnIndex l N).procession = a := rfl

@[simp] theorem tensor_mk (a b : ConcreteFiniteTheorem311.finiteLabel l)
    (k : Fin (N + 1)) :
    (⟨a, b, k⟩ : FiniteColumnIndex l N).tensor = b := rfl

@[simp] theorem level_mk (a b : ConcreteFiniteTheorem311.finiteLabel l)
    (k : Fin (N + 1)) :
    (⟨a, b, k⟩ : FiniteColumnIndex l N).level = k := rfl

def ind1 (t : ConcreteFiniteTheorem311.finiteLabel l)
    (x : FiniteColumnIndex l N) : FiniteColumnIndex l N :=
  { procession := t + x.procession, tensor := x.tensor, level := x.level }

def ind2 (t : ConcreteFiniteTheorem311.finiteLabel l)
    (x : FiniteColumnIndex l N) : FiniteColumnIndex l N :=
  { procession := x.procession, tensor := t + x.tensor, level := x.level }

def ind3 (n : Nat) (x : FiniteColumnIndex l N) : FiniteColumnIndex l N :=
  { procession := x.procession
    tensor := x.tensor
    level := ⟨min N (x.level.val + n), by omega⟩ }

@[simp] theorem ind1_procession (t : ConcreteFiniteTheorem311.finiteLabel l)
    (x : FiniteColumnIndex l N) : (ind1 t x).procession = t + x.procession := rfl

@[simp] theorem ind1_tensor (t : ConcreteFiniteTheorem311.finiteLabel l)
    (x : FiniteColumnIndex l N) : (ind1 t x).tensor = x.tensor := rfl

@[simp] theorem ind1_level (t : ConcreteFiniteTheorem311.finiteLabel l)
    (x : FiniteColumnIndex l N) : (ind1 t x).level = x.level := rfl

@[simp] theorem ind2_procession (t : ConcreteFiniteTheorem311.finiteLabel l)
    (x : FiniteColumnIndex l N) : (ind2 t x).procession = x.procession := rfl

@[simp] theorem ind2_tensor (t : ConcreteFiniteTheorem311.finiteLabel l)
    (x : FiniteColumnIndex l N) : (ind2 t x).tensor = t + x.tensor := rfl

@[simp] theorem ind2_level (t : ConcreteFiniteTheorem311.finiteLabel l)
    (x : FiniteColumnIndex l N) : (ind2 t x).level = x.level := rfl

@[simp] theorem ind3_procession (n : Nat) (x : FiniteColumnIndex l N) :
    (ind3 n x).procession = x.procession := rfl

@[simp] theorem ind3_tensor (n : Nat) (x : FiniteColumnIndex l N) :
    (ind3 n x).tensor = x.tensor := rfl

theorem ind3_level_val (n : Nat) (x : FiniteColumnIndex l N) :
    (ind3 n x).level.val = min N (x.level.val + n) := rfl

theorem level_le_ind3 (n : Nat) (x : FiniteColumnIndex l N) :
    x.level.val ≤ (ind3 n x).level.val := by
  simp only [ind3_level_val]
  omega

@[simp] theorem ind1_zero (x : FiniteColumnIndex l N) : ind1 0 x = x := by
  cases x
  simp [ind1]

@[simp] theorem ind2_zero (x : FiniteColumnIndex l N) : ind2 0 x = x := by
  cases x
  simp [ind2]

@[simp] theorem ind3_zero (x : FiniteColumnIndex l N) : ind3 0 x = x := by
  cases x with
  | mk a b k =>
    have hk : k.val ≤ N := by omega
    simp [ind3, Nat.min_eq_right hk]

theorem ind1_add (g h : ConcreteFiniteTheorem311.finiteLabel l)
    (x : FiniteColumnIndex l N) :
    ind1 (g + h) x = ind1 g (ind1 h x) := by
  cases x
  simp [ind1, add_comm, add_left_comm]

theorem ind2_add (g h : ConcreteFiniteTheorem311.finiteLabel l)
    (x : FiniteColumnIndex l N) :
    ind2 (g + h) x = ind2 g (ind2 h x) := by
  cases x
  simp [ind2, add_comm, add_left_comm]

theorem ind1_inverse (g : ConcreteFiniteTheorem311.finiteLabel l)
    (x : FiniteColumnIndex l N) : ind1 (-g) (ind1 g x) = x := by
  cases x
  simp [ind1]

theorem ind2_inverse (g : ConcreteFiniteTheorem311.finiteLabel l)
    (x : FiniteColumnIndex l N) : ind2 (-g) (ind2 g x) = x := by
  cases x
  simp [ind2]

theorem ind1_ind2_commute (g h : ConcreteFiniteTheorem311.finiteLabel l)
    (x : FiniteColumnIndex l N) :
    ind1 g (ind2 h x) = ind2 h (ind1 g x) := by
  cases x
  rfl

theorem ind1_ind3_commute (g : ConcreteFiniteTheorem311.finiteLabel l)
    (n : Nat) (x : FiniteColumnIndex l N) :
    ind1 g (ind3 n x) = ind3 n (ind1 g x) := by
  cases x
  rfl

theorem ind2_ind3_commute (g : ConcreteFiniteTheorem311.finiteLabel l)
    (n : Nat) (x : FiniteColumnIndex l N) :
    ind2 g (ind3 n x) = ind3 n (ind2 g x) := by
  cases x
  rfl

def she (x : FiniteColumnIndex l N) : FiniteColumnIndex l N :=
  { procession := x.procession, tensor := -x.tensor, level := x.level }

@[simp] theorem she_procession (x : FiniteColumnIndex l N) :
    (she x).procession = x.procession := rfl

@[simp] theorem she_tensor (x : FiniteColumnIndex l N) :
    (she x).tensor = -x.tensor := rfl

@[simp] theorem she_level (x : FiniteColumnIndex l N) :
    (she x).level = x.level := rfl

theorem she_involutive (x : FiniteColumnIndex l N) : she (she x) = x := by
  cases x
  simp [she]

theorem she_ind1_commute (g : ConcreteFiniteTheorem311.finiteLabel l)
    (x : FiniteColumnIndex l N) :
    she (ind1 g x) = ind1 g (she x) := by
  cases x
  rfl

theorem she_ind2_neg (g : ConcreteFiniteTheorem311.finiteLabel l)
    (x : FiniteColumnIndex l N) :
    she (ind2 g x) = ind2 (-g) (she x) := by
  cases x
  simp [she, ind2, add_comm]

end FiniteColumnIndex

variable {l : PrimeGeFive} {N : Nat}

def columnLogVolume (l : PrimeGeFive) (x : FiniteColumnIndex l N) : Real :=
  ConcreteFiniteTheorem311.thetaLogVolume l + (x.level.val : Real)

@[simp] theorem columnLogVolume_ind1
    (l : PrimeGeFive) (N : Nat)
    (t : ConcreteFiniteTheorem311.finiteLabel l)
    (x : FiniteColumnIndex l N) :
    columnLogVolume l (FiniteColumnIndex.ind1 t x) = columnLogVolume l x := rfl

@[simp] theorem columnLogVolume_ind2
    (l : PrimeGeFive) (N : Nat)
    (t : ConcreteFiniteTheorem311.finiteLabel l)
    (x : FiniteColumnIndex l N) :
    columnLogVolume l (FiniteColumnIndex.ind2 t x) = columnLogVolume l x := rfl

theorem columnLogVolume_she
    (l : PrimeGeFive) (N : Nat) (x : FiniteColumnIndex l N) :
    columnLogVolume l (FiniteColumnIndex.she x) = columnLogVolume l x := rfl

theorem columnLogVolume_ind3
    (l : PrimeGeFive) (N n : Nat) (x : FiniteColumnIndex l N) :
    columnLogVolume l x ≤ columnLogVolume l (FiniteColumnIndex.ind3 n x) := by
  unfold columnLogVolume
  have h := FiniteColumnIndex.level_le_ind3 n x
  have h' : (x.level.val : Real) ≤
      ((FiniteColumnIndex.ind3 n x).level.val : Real) := by
    exact_mod_cast h
  linarith

theorem columnLogVolume_ind3_zero
    (l : PrimeGeFive) (N : Nat) (x : FiniteColumnIndex l N) :
    columnLogVolume l (FiniteColumnIndex.ind3 0 x) =
      columnLogVolume l x := by
  rw [FiniteColumnIndex.ind3_zero]

def columnHull (l : PrimeGeFive) (N : Nat) :
    FiniteHull (FiniteColumnIndex l N) :=
  finiteHullOfValues (columnLogVolume l)

@[simp] theorem columnHull_volume
    (l : PrimeGeFive) (N : Nat) (x : FiniteColumnIndex l N) :
    (columnHull l N).volume x = columnLogVolume l x := rfl

@[simp] theorem columnHull_hullVolume
    (l : PrimeGeFive) (N : Nat) :
    (columnHull l N).hullVolume =
      finiteSup (columnLogVolume l (N := N)) := rfl

theorem column_le_hull
    (l : PrimeGeFive) (N : Nat) (x : FiniteColumnIndex l N) :
    columnLogVolume l x ≤ (columnHull l N).hullVolume := by
  exact (columnHull l N).contains x

theorem column_hull_le_of_bound
    (l : PrimeGeFive) (N : Nat) (b : Real)
    (h : ∀ x : FiniteColumnIndex l N, columnLogVolume l x ≤ b) :
    (columnHull l N).hullVolume ≤ b := by
  exact finiteSup_le (columnLogVolume l) b h

def columnSet (l : PrimeGeFive) (N : Nat) : Set Real :=
  Set.range (columnLogVolume l : FiniteColumnIndex l N → Real)

theorem columnSet_bounded_by_hull
    (l : PrimeGeFive) (N : Nat) :
    boundedSet (columnSet l N) (columnHull l N).hullVolume := by
  exact boundedSet_range (columnLogVolume l) _ (column_le_hull l N)

theorem columnSet_nonempty (l : PrimeGeFive) (N : Nat) :
    (columnSet l N).Nonempty := by
  exact ⟨columnLogVolume l FiniteColumnIndex.base,
    ⟨FiniteColumnIndex.base, rfl⟩⟩

def columnUniformWeights (l : PrimeGeFive) (N : Nat) :
    WeightedValues (FiniteColumnIndex l N) where
  value := columnLogVolume l
  weight := fun _ => 1
  weightTotal := (Fintype.card (FiniteColumnIndex l N) : Real)
  weightTotal_pos := by
    have h : 0 < Fintype.card (FiniteColumnIndex l N) :=
      Fintype.card_pos_iff.mpr (inferInstance : Nonempty (FiniteColumnIndex l N))
    exact_mod_cast h
  weightTotal_eq_sum := by simp

@[simp] theorem columnUniformWeights_value
    (l : PrimeGeFive) (N : Nat) (x : FiniteColumnIndex l N) :
    (columnUniformWeights l N).value x = columnLogVolume l x := rfl

@[simp] theorem columnUniformWeights_weight
    (l : PrimeGeFive) (N : Nat) (x : FiniteColumnIndex l N) :
    (columnUniformWeights l N).weight x = 1 := rfl

theorem columnUniformWeights_average_le_hull
    (l : PrimeGeFive) (N : Nat) :
    (columnUniformWeights l N).average ≤ (columnHull l N).hullVolume := by
  apply FiniteHull.average_le (columnHull l N) (columnUniformWeights l N)
  · intro x
    rfl
  · intro x
    norm_num

theorem columnUniformWeights_lower_average
    (l : PrimeGeFive) (N : Nat) :
    lowerFiniteSup (columnLogVolume l (N := N)) ≤
      (columnUniformWeights l N).average := by
  apply WeightedValues.lower_le_average_of_pointwise (columnUniformWeights l N)
  · intro x
    norm_num
  · intro x
    exact lowerFiniteSup_le (columnLogVolume l (N := N)) x

def columnScale (l : PrimeGeFive) (N : Nat)
    (x : FiniteColumnIndex l N) : Real :=
  Real.exp (columnLogVolume l x)

theorem columnScale_positive (l : PrimeGeFive) (N : Nat)
    (x : FiniteColumnIndex l N) : 0 < columnScale l N x := Real.exp_pos _

theorem columnScale_log (l : PrimeGeFive) (N : Nat)
    (x : FiniteColumnIndex l N) :
    Real.log (columnScale l N x) = columnLogVolume l x := Real.log_exp _

def columnPacket (l : PrimeGeFive) (N : Nat) :
    PositivePacket (FiniteColumnIndex l N) where
  scale := columnScale l N
  positive := columnScale_positive l N

@[simp] theorem columnPacket_scale (l : PrimeGeFive) (N : Nat)
    (x : FiniteColumnIndex l N) :
    (columnPacket l N).scale x = columnScale l N x := rfl

theorem columnPacket_logVolume_eq_sum (l : PrimeGeFive) (N : Nat) :
    packetLogVolume (columnPacket l N) =
      ∑ x : FiniteColumnIndex l N, columnLogVolume l x := by
  unfold packetLogVolume
  apply Finset.sum_congr rfl
  intro x hx
  exact columnScale_log l N x

theorem columnPacket_logVolume_eq_log_det (l : PrimeGeFive) (N : Nat) :
    packetLogVolume (columnPacket l N) =
      Real.log (packetDet (columnPacket l N)) :=
  packetLogVolume_eq_log_det (columnPacket l N)

theorem columnPacket_det_positive (l : PrimeGeFive) (N : Nat) :
    0 < packetDet (columnPacket l N) := by
  rw [packetDet_eq_prod]
  apply Finset.prod_pos
  intro x hx
  exact columnScale_positive l N x

theorem columnPacket_det_exp (l : PrimeGeFive) (N : Nat) :
    Real.exp (packetLogVolume (columnPacket l N)) =
      packetDet (columnPacket l N) := by
  rw [columnPacket_logVolume_eq_log_det]
  exact Real.exp_log (columnPacket_det_positive l N)

def columnPowerPacket (l : PrimeGeFive) (N n : Nat) :
    PositivePacket (FiniteColumnIndex l N) :=
  rescalePacket (Real.exp (n : Real)) (Real.exp_pos _) (columnPacket l N)

theorem columnPowerPacket_scale (l : PrimeGeFive) (N n : Nat)
    (x : FiniteColumnIndex l N) :
    (columnPowerPacket l N n).scale x =
      Real.exp (n : Real) * columnScale l N x := rfl

theorem columnPowerPacket_logVolume (l : PrimeGeFive) (N n : Nat) :
    packetLogVolume (columnPowerPacket l N n) =
      (Fintype.card (FiniteColumnIndex l N) : Real) * (n : Real) +
        packetLogVolume (columnPacket l N) := by
  change packetLogVolume
      (rescalePacket (Real.exp (n : Real)) (Real.exp_pos _)
        (columnPacket l N)) = _
  simpa using packetLogVolume_rescale (Real.exp (n : Real)) (Real.exp_pos _)
    (columnPacket l N)

theorem columnPowerPacket_logVolume_sub_base (l : PrimeGeFive) (N n : Nat) :
    packetLogVolume (columnPowerPacket l N n) -
        packetLogVolume (columnPacket l N) =
      (Fintype.card (FiniteColumnIndex l N) : Real) * (n : Real) := by
  rw [columnPowerPacket_logVolume]
  ring

def columnWeightedPacket (l : PrimeGeFive) (N : Nat) :
    WeightedDeterminantPacket (FiniteColumnIndex l N) where
  hullLogDegree := columnLogVolume l
  structureSheafLogDegree := 0
  denominator := fun _ => 1

@[simp] theorem columnWeightedPacket_adjusted (l : PrimeGeFive) (N : Nat)
    (x : FiniteColumnIndex l N) :
    (columnWeightedPacket l N).adjustedLogDegree x = columnLogVolume l x := by
  simp [WeightedDeterminantPacket.adjustedLogDegree, columnWeightedPacket]

theorem columnWeightedPacket_normalized (l : PrimeGeFive) (N : Nat) :
    (columnWeightedPacket l N).normalizedLogVolume =
      ∑ x : FiniteColumnIndex l N, columnLogVolume l x := by
  unfold WeightedDeterminantPacket.normalizedLogVolume
  simp only [columnWeightedPacket_adjusted]
  apply Finset.sum_congr rfl
  intro x hx
  norm_num [columnWeightedPacket]

theorem columnWeightedPacket_common_degree (l : PrimeGeFive) (N : Nat) :
    (columnWeightedPacket l N).commonTensorDegree = 1 := by
  simp [WeightedDeterminantPacket.commonTensorDegree, columnWeightedPacket]

theorem columnWeightedPacket_summand_exponent (l : PrimeGeFive) (N : Nat)
    (x : FiniteColumnIndex l N) :
    (columnWeightedPacket l N).summandTensorExponent x = 1 := by
  simp [WeightedDeterminantPacket.summandTensorExponent, columnWeightedPacket]

theorem columnWeightedPacket_weighted (l : PrimeGeFive) (N : Nat) :
    (columnWeightedPacket l N).weightedLogVolume =
      ∑ x : FiniteColumnIndex l N, columnLogVolume l x := by
  unfold WeightedDeterminantPacket.weightedLogVolume
  simp only [columnWeightedPacket_summand_exponent,
    columnWeightedPacket_adjusted]
  simp

end ConcreteFiniteStepXI

end

end LeanFormal.IUT

namespace LeanFormal.IUT

open scoped BigOperators

noncomputable section

namespace ConcreteFiniteStepXI

structure FiniteAPTData (l : PrimeGeFive) (N : Nat) where
  shift : ConcreteFiniteTheorem311.finiteLabel l
  equivalence : finiteQuotientCarrier l N ≃ finiteQuotientCarrier l N
  level_preserved : ∀ x, (equivalence x).2 = x.2

def finiteAPTData (l : PrimeGeFive) (N : Nat)
    (t : ConcreteFiniteTheorem311.finiteLabel l) : FiniteAPTData l N where
  shift := t
  equivalence := by
    exact
      { toFun := fun x => (x.1 + t, x.2)
        invFun := fun x => (x.1 - t, x.2)
        left_inv := by
          intro x
          rcases x with ⟨a, k⟩
          simp [sub_eq_add_neg, add_assoc]
        right_inv := by
          intro x
          rcases x with ⟨a, k⟩
          simp [sub_eq_add_neg, add_assoc] }
  level_preserved := by
    intro x
    rfl

@[simp] theorem finiteAPTData_shift (l : PrimeGeFive) (N : Nat)
    (t : ConcreteFiniteTheorem311.finiteLabel l) :
    (finiteAPTData l N t).shift = t := rfl

theorem finiteAPTData_bijective (l : PrimeGeFive) (N : Nat)
    (t : ConcreteFiniteTheorem311.finiteLabel l) :
    Function.Bijective (finiteAPTData l N t).equivalence :=
  (finiteAPTData l N t).equivalence.bijective

theorem finiteAPTData_level (l : PrimeGeFive) (N : Nat)
    (t : ConcreteFiniteTheorem311.finiteLabel l)
    (x : finiteQuotientCarrier l N) :
    ((finiteAPTData l N t).equivalence x).2 = x.2 :=
  (finiteAPTData l N t).level_preserved x

theorem finiteAPTData_comp (l : PrimeGeFive) (N : Nat)
    (s t : ConcreteFiniteTheorem311.finiteLabel l) :
    (finiteAPTData l N s).equivalence ∘
        (finiteAPTData l N t).equivalence =
      (finiteAPTData l N (s + t)).equivalence := by
  funext x
  rcases x with ⟨a, k⟩
  simp [finiteAPTData, add_comm, add_left_comm]

theorem finiteAPTData_inverse (l : PrimeGeFive) (N : Nat)
    (t : ConcreteFiniteTheorem311.finiteLabel l) :
    (finiteAPTData l N (-t)).equivalence =
      ((finiteAPTData l N t).equivalence).symm := by
  ext x <;> rcases x with ⟨a, k⟩ <;>
    simp [finiteAPTData, sub_eq_add_neg]

theorem finiteAPTData_zero (l : PrimeGeFive) (N : Nat) :
    (finiteAPTData l N 0).equivalence = Equiv.refl _ := by
  ext x <;> rcases x with ⟨a, k⟩ <;> simp [finiteAPTData]

structure FiniteIPLSquare (l : PrimeGeFive) (N : Nat) where
  horizontal : FiniteColumnIndex l N ≃ FiniteColumnIndex l N
  vertical : FiniteColumnIndex l N ≃ FiniteColumnIndex l N
  commute : ∀ x, horizontal (vertical x) = vertical (horizontal x)
  horizontal_volume : ∀ x, columnLogVolume l (horizontal x) = columnLogVolume l x
  vertical_volume : ∀ x, columnLogVolume l (vertical x) = columnLogVolume l x

def finiteIPLSquare (l : PrimeGeFive) (N : Nat)
    (g h : ConcreteFiniteTheorem311.finiteLabel l) : FiniteIPLSquare l N where
  horizontal :=
    { toFun := FiniteColumnIndex.ind1 g
      invFun := FiniteColumnIndex.ind1 (-g)
      left_inv := FiniteColumnIndex.ind1_inverse g
      right_inv := by
        intro x
        simpa using FiniteColumnIndex.ind1_inverse (-g) x }
  vertical :=
    { toFun := FiniteColumnIndex.ind2 h
      invFun := FiniteColumnIndex.ind2 (-h)
      left_inv := FiniteColumnIndex.ind2_inverse h
      right_inv := by
        intro x
        simpa using FiniteColumnIndex.ind2_inverse (-h) x }
  commute := FiniteColumnIndex.ind1_ind2_commute g h
  horizontal_volume := columnLogVolume_ind1 l N g
  vertical_volume := columnLogVolume_ind2 l N h

theorem finiteIPLSquare_commute (l : PrimeGeFive) (N : Nat)
    (g h : ConcreteFiniteTheorem311.finiteLabel l)
    (x : FiniteColumnIndex l N) :
    (finiteIPLSquare l N g h).horizontal
        ((finiteIPLSquare l N g h).vertical x) =
      (finiteIPLSquare l N g h).vertical
        ((finiteIPLSquare l N g h).horizontal x) := by
  exact (finiteIPLSquare l N g h).commute x

theorem finiteIPLSquare_volume_horizontal (l : PrimeGeFive) (N : Nat)
    (g h : ConcreteFiniteTheorem311.finiteLabel l)
    (x : FiniteColumnIndex l N) :
    columnLogVolume l ((finiteIPLSquare l N g h).horizontal x) =
      columnLogVolume l x := by
  exact (finiteIPLSquare l N g h).horizontal_volume x

theorem finiteIPLSquare_volume_vertical (l : PrimeGeFive) (N : Nat)
    (g h : ConcreteFiniteTheorem311.finiteLabel l)
    (x : FiniteColumnIndex l N) :
    columnLogVolume l ((finiteIPLSquare l N g h).vertical x) =
      columnLogVolume l x := by
  exact (finiteIPLSquare l N g h).vertical_volume x

theorem finiteIPLSquare_comp_horizontal (l : PrimeGeFive) (N : Nat)
    (g h : ConcreteFiniteTheorem311.finiteLabel l) :
    (finiteIPLSquare l N (g + h) 0).horizontal =
      (finiteIPLSquare l N g 0).horizontal.trans
        (finiteIPLSquare l N h 0).horizontal := by
  ext x
  simpa [finiteIPLSquare, Equiv.trans_apply, add_comm, add_assoc] using
    FiniteColumnIndex.ind1_add h g x

structure FiniteSHESquare (l : PrimeGeFive) (N : Nat) where
  horizontal : FiniteColumnIndex l N ≃ FiniteColumnIndex l N
  vertical : FiniteColumnIndex l N ≃ FiniteColumnIndex l N
  commute : ∀ x, horizontal (vertical x) = vertical (horizontal x)
  horizontal_volume : ∀ x, columnLogVolume l (horizontal x) = columnLogVolume l x
  vertical_volume : ∀ x, columnLogVolume l (vertical x) = columnLogVolume l x

def finiteSHESquare (l : PrimeGeFive) (N : Nat)
    (g : ConcreteFiniteTheorem311.finiteLabel l) : FiniteSHESquare l N where
  horizontal :=
    { toFun := FiniteColumnIndex.ind1 g
      invFun := FiniteColumnIndex.ind1 (-g)
      left_inv := FiniteColumnIndex.ind1_inverse g
      right_inv := by
        intro x
        simpa using FiniteColumnIndex.ind1_inverse (-g) x }
  vertical :=
    { toFun := FiniteColumnIndex.she
      invFun := FiniteColumnIndex.she
      left_inv := FiniteColumnIndex.she_involutive
      right_inv := FiniteColumnIndex.she_involutive }
  commute := by
    intro x
    exact (FiniteColumnIndex.she_ind1_commute g x).symm
  horizontal_volume := columnLogVolume_ind1 l N g
  vertical_volume := columnLogVolume_she l N

theorem finiteSHESquare_commute (l : PrimeGeFive) (N : Nat)
    (g : ConcreteFiniteTheorem311.finiteLabel l)
    (x : FiniteColumnIndex l N) :
    (finiteSHESquare l N g).horizontal
        ((finiteSHESquare l N g).vertical x) =
      (finiteSHESquare l N g).vertical
        ((finiteSHESquare l N g).horizontal x) := by
  exact (finiteSHESquare l N g).commute x

theorem finiteSHESquare_volume (l : PrimeGeFive) (N : Nat)
    (g : ConcreteFiniteTheorem311.finiteLabel l)
    (x : FiniteColumnIndex l N) :
    columnLogVolume l ((finiteSHESquare l N g).vertical x) =
      columnLogVolume l x := by
  exact (finiteSHESquare l N g).vertical_volume x

theorem finiteSHESquare_vertical_involutive (l : PrimeGeFive) (N : Nat)
    (g : ConcreteFiniteTheorem311.finiteLabel l)
    (x : FiniteColumnIndex l N) :
    (finiteSHESquare l N g).vertical
        ((finiteSHESquare l N g).vertical x) = x := by
  exact FiniteColumnIndex.she_involutive x

structure FiniteInd3Certificate (l : PrimeGeFive) (N : Nat) where
  lift : Nat → FiniteColumnIndex l N → FiniteColumnIndex l N
  level_monotone : ∀ n x, x.level.val ≤ (lift n x).level.val
  procession_preserved : ∀ n x, (lift n x).procession = x.procession
  tensor_preserved : ∀ n x, (lift n x).tensor = x.tensor
  volume_monotone : ∀ n x, columnLogVolume l x ≤ columnLogVolume l (lift n x)

def finiteInd3Certificate (l : PrimeGeFive) (N : Nat) :
    FiniteInd3Certificate l N where
  lift := FiniteColumnIndex.ind3
  level_monotone := FiniteColumnIndex.level_le_ind3
  procession_preserved := FiniteColumnIndex.ind3_procession
  tensor_preserved := FiniteColumnIndex.ind3_tensor
  volume_monotone := columnLogVolume_ind3 l N

theorem finiteInd3Certificate_lift (l : PrimeGeFive) (N n : Nat)
    (x : FiniteColumnIndex l N) :
    (finiteInd3Certificate l N).lift n x = FiniteColumnIndex.ind3 n x := rfl

theorem finiteInd3Certificate_level (l : PrimeGeFive) (N n : Nat)
    (x : FiniteColumnIndex l N) :
    x.level.val ≤ ((finiteInd3Certificate l N).lift n x).level.val :=
  (finiteInd3Certificate l N).level_monotone n x

theorem finiteInd3Certificate_volume (l : PrimeGeFive) (N n : Nat)
    (x : FiniteColumnIndex l N) :
    columnLogVolume l x ≤
      columnLogVolume l ((finiteInd3Certificate l N).lift n x) :=
  (finiteInd3Certificate l N).volume_monotone n x

theorem finiteInd3Certificate_labels (l : PrimeGeFive) (N n : Nat)
    (x : FiniteColumnIndex l N) :
    ((finiteInd3Certificate l N).lift n x).procession = x.procession ∧
      ((finiteInd3Certificate l N).lift n x).tensor = x.tensor := by
  constructor
  · exact (finiteInd3Certificate l N).procession_preserved n x
  · exact (finiteInd3Certificate l N).tensor_preserved n x

def modelQSigned (h : Real) : Real := min (h - 1) (-1)

theorem modelQSigned_le (h : Real) : modelQSigned h ≤ h := by
  exact (min_le_left _ _).trans (by linarith)

theorem modelQSigned_negative (h : Real) : modelQSigned h < 0 := by
  exact (min_le_right _ _).trans_lt (by norm_num)

def finiteColumnCertificate (l : PrimeGeFive) (N : Nat) :
    StepXIFiniteCertificate (FiniteColumnIndex l N) where
  hull := columnHull l N
  weighted := columnUniformWeights l N
  weighted_matches_hull := by
    intro x
    rfl
  weights_nonnegative := by
    intro x
    norm_num
  qSigned := modelQSigned (columnHull l N).hullVolume
  thetaSigned := (columnHull l N).hullVolume
  q_le_hull := modelQSigned_le _
  hull_le_theta := le_rfl
  q_negative := modelQSigned_negative _

@[simp] theorem finiteColumnCertificate_q (l : PrimeGeFive) (N : Nat) :
    (finiteColumnCertificate l N).qSigned =
      modelQSigned (columnHull l N).hullVolume := rfl

@[simp] theorem finiteColumnCertificate_theta (l : PrimeGeFive) (N : Nat) :
    (finiteColumnCertificate l N).thetaSigned =
      (columnHull l N).hullVolume := rfl

theorem finiteColumnCertificate_q_negative (l : PrimeGeFive) (N : Nat) :
    (finiteColumnCertificate l N).qSigned < 0 :=
  (finiteColumnCertificate l N).q_negative

theorem finiteColumnCertificate_q_le_theta (l : PrimeGeFive) (N : Nat) :
    (finiteColumnCertificate l N).qSigned ≤
      (finiteColumnCertificate l N).thetaSigned := by
  exact (finiteColumnCertificate l N).q_le_hull.trans
    (finiteColumnCertificate l N).hull_le_theta

def finiteIPLProposition (l : PrimeGeFive) (N : Nat) : Prop :=
  Nonempty (FiniteIPLSquare l N)

def finiteSHEProposition (l : PrimeGeFive) (N : Nat) : Prop :=
  Nonempty (FiniteSHESquare l N)

def finiteAPTProposition (l : PrimeGeFive) (N : Nat) : Prop :=
  Nonempty (FiniteAPTData l N)

theorem finiteIPLProposition_proved (l : PrimeGeFive) (N : Nat) :
    finiteIPLProposition l N := by
  exact ⟨finiteIPLSquare l N 0 0⟩

theorem finiteSHEProposition_proved (l : PrimeGeFive) (N : Nat) :
    finiteSHEProposition l N := by
  exact ⟨finiteSHESquare l N 0⟩

theorem finiteAPTProposition_proved (l : PrimeGeFive) (N : Nat) :
    finiteAPTProposition l N := by
  exact ⟨finiteAPTData l N 0⟩

def finiteColumnLinks (l : PrimeGeFive) (N : Nat) :
    FiniteStepXILinkEvidence (finiteColumnCertificate l N) where
  targetSigned := (finiteColumnCertificate l N).thetaSigned
  ipl := finiteIPLProposition l N
  she := finiteSHEProposition l N
  apt := finiteAPTProposition l N
  ipl_evidence := finiteIPLProposition_proved l N
  she_evidence := finiteSHEProposition_proved l N
  apt_evidence := finiteAPTProposition_proved l N
  q_le_target := by
    exact (finiteColumnCertificate l N).q_le_hull.trans
      (finiteColumnCertificate l N).hull_le_theta
  target_le_theta := le_rfl

theorem finiteColumnLinks_q_bound (l : PrimeGeFive) (N : Nat) :
    (finiteColumnCertificate l N).qSigned ≤
      (finiteColumnLinks l N).targetSigned :=
  (finiteColumnLinks l N).q_le_target

theorem finiteColumnLinks_theta_bound (l : PrimeGeFive) (N : Nat) :
    (finiteColumnLinks l N).targetSigned ≤
      (finiteColumnCertificate l N).thetaSigned :=
  (finiteColumnLinks l N).target_le_theta

def finiteColumnContract (l : PrimeGeFive) (N : Nat) : StepXIContract :=
  StepXIFiniteCertificate.toContract
    (finiteColumnCertificate l N) (finiteColumnLinks l N)

theorem finiteColumnContract_conclusion (l : PrimeGeFive) (N : Nat) :
    Cor312Conclusion (finiteColumnContract l N) := by
  exact cor312_of_finite_certificate
    (finiteColumnCertificate l N) (finiteColumnLinks l N)

theorem finiteColumnContract_q_positive (l : PrimeGeFive) (N : Nat) :
    0 < -(finiteColumnContract l N).qSigned := by
  exact q_positive_of_finite_certificate
    (finiteColumnCertificate l N) (finiteColumnLinks l N)

theorem finiteColumnContract_ipl (l : PrimeGeFive) (N : Nat) :
    (finiteColumnContract l N).ipl :=
  (finiteColumnLinks l N).ipl_evidence

theorem finiteColumnContract_she (l : PrimeGeFive) (N : Nat) :
    (finiteColumnContract l N).she :=
  (finiteColumnLinks l N).she_evidence

theorem finiteColumnContract_apt (l : PrimeGeFive) (N : Nat) :
    (finiteColumnContract l N).apt :=
  (finiteColumnLinks l N).apt_evidence

theorem finiteColumnContract_q_le_target (l : PrimeGeFive) (N : Nat) :
    (finiteColumnContract l N).qSigned ≤
      (finiteColumnContract l N).targetSigned :=
  (finiteColumnContract l N).q_le_target

theorem finiteColumnContract_target_le_theta (l : PrimeGeFive) (N : Nat) :
    (finiteColumnContract l N).targetSigned ≤
      (finiteColumnContract l N).thetaSigned :=
  (finiteColumnContract l N).target_le_theta

theorem finiteColumnContract_transitive_bound (l : PrimeGeFive) (N : Nat) :
    (finiteColumnContract l N).qSigned ≤
      (finiteColumnContract l N).thetaSigned :=
  le_trans (finiteColumnContract l N).q_le_target
    (finiteColumnContract l N).target_le_theta

theorem finiteColumnContract_negativity (l : PrimeGeFive) (N : Nat) :
    (finiteColumnContract l N).qSigned < 0 :=
  (finiteColumnCertificate l N).q_negative

end ConcreteFiniteStepXI

end

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def concreteFiniteStepXIRoute : Obligation :=
  { id := "IUT-III.concrete-finite-stepXI-route"
    source := "IUT III, Theorem 3.11 -> Corollary 3.12, finite Step-XI model"
    status := VerificationStatus.proved
    note :=
      "A bounded finite column carrier is constructed over the proved C-stage " ++
        "theta packet. Ind1 and Ind2 are equivalences, Ind3 is a bounded " ++
        "monotone lift, IPL and SHE are commuting finite squares, APT is an " ++
        "explicit quotient-carrier equivalence, and determinant, tensor, hull, " ++
        "and log-volume inequalities are proved. This is a finite model " ++
        "certificate, not the source-facing arbitrary Hodge-theater construction."
    dependsOn :=
      [ "IUT-III.concrete-finite-theorem311-model",
        "IUT-III.finite-theta-packet-bridge",
        "IUT-III.remark-3-9-5-weighted-determinant-normalization",
        "IUT-III.finite-certificate-to-contract" ] }

end LeanFormal.IUT.Audit

namespace LeanFormal.IUT

open scoped BigOperators

noncomputable section

namespace ConcreteFiniteStepXI

namespace FiniteColumnIndex

variable {l : PrimeGeFive} {N : Nat}

def top : FiniteColumnIndex l N :=
  { procession := 0, tensor := 0, level := ⟨N, by omega⟩ }

@[simp] theorem top_level : (top : FiniteColumnIndex l N).level.val = N := rfl

theorem level_le_top (x : FiniteColumnIndex l N) :
    x.level.val ≤ (top : FiniteColumnIndex l N).level.val := by
  simp only [top_level]
  omega

theorem ind3_top (n : Nat) :
    ind3 n (top : FiniteColumnIndex l N) = top := by
  have h : N ≤ N + n := by omega
  simp [top, ind3]

end FiniteColumnIndex

theorem columnHull_eq_top_level (l : PrimeGeFive) (N : Nat) :
    (columnHull l N).hullVolume =
      ConcreteFiniteTheorem311.thetaLogVolume l + (N : Real) := by
  apply le_antisymm
  · apply finiteSup_le
    intro x
    unfold columnLogVolume
    have h : x.level.val ≤ N := by omega
    have h' : (x.level.val : Real) ≤ (N : Real) := by exact_mod_cast h
    linarith
  · have htop := le_finiteSup (columnLogVolume l)
      (FiniteColumnIndex.top : FiniteColumnIndex l N)
    simpa [columnLogVolume] using htop

theorem column_le_top_level (l : PrimeGeFive) (N : Nat)
    (x : FiniteColumnIndex l N) :
    columnLogVolume l x ≤
      ConcreteFiniteTheorem311.thetaLogVolume l + (N : Real) := by
  rw [← columnHull_eq_top_level l N]
  exact column_le_hull l N x

theorem column_top_level_mem (l : PrimeGeFive) (N : Nat) :
    columnLogVolume l (FiniteColumnIndex.top : FiniteColumnIndex l N) =
      ConcreteFiniteTheorem311.thetaLogVolume l + (N : Real) := by
  rfl

theorem column_hull_attained (l : PrimeGeFive) (N : Nat) :
    ∃ x : FiniteColumnIndex l N,
      columnLogVolume l x = (columnHull l N).hullVolume := by
  refine ⟨FiniteColumnIndex.top, ?_⟩
  rw [columnHull_eq_top_level]
  rfl

def columnSum (l : PrimeGeFive) (N : Nat) : Real :=
  ∑ x : FiniteColumnIndex l N, columnLogVolume l x

def columnMean (l : PrimeGeFive) (N : Nat) : Real :=
  columnSum l N / (Fintype.card (FiniteColumnIndex l N) : Real)

@[simp] theorem columnSum_eq_packetLogVolume (l : PrimeGeFive) (N : Nat) :
    columnSum l N = packetLogVolume (columnPacket l N) := by
  symm
  exact columnPacket_logVolume_eq_sum l N

theorem columnMean_eq_uniform_average (l : PrimeGeFive) (N : Nat) :
    columnMean l N = (columnUniformWeights l N).average := by
  unfold columnMean columnSum WeightedValues.average columnUniformWeights
  simp only [one_mul]

theorem columnMean_le_hull (l : PrimeGeFive) (N : Nat) :
    columnMean l N ≤ (columnHull l N).hullVolume := by
  rw [columnMean_eq_uniform_average]
  exact columnUniformWeights_average_le_hull l N

theorem lower_hull_le_columnMean (l : PrimeGeFive) (N : Nat) :
    lowerFiniteSup (columnLogVolume l (N := N)) ≤ columnMean l N := by
  rw [columnMean_eq_uniform_average]
  exact columnUniformWeights_lower_average l N

theorem columnMean_nonempty_interval (l : PrimeGeFive) (N : Nat) :
    lowerFiniteSup (columnLogVolume l (N := N)) ≤ columnMean l N ∧
      columnMean l N ≤ (columnHull l N).hullVolume :=
  ⟨lower_hull_le_columnMean l N, columnMean_le_hull l N⟩

theorem columnSum_sub_mean (l : PrimeGeFive) (N : Nat) :
    columnSum l N =
      (Fintype.card (FiniteColumnIndex l N) : Real) * columnMean l N := by
  unfold columnMean
  have hcard : (Fintype.card (FiniteColumnIndex l N) : Real) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt
      (Fintype.card_pos_iff.mpr (inferInstance : Nonempty (FiniteColumnIndex l N))))
  field_simp [hcard]

theorem columnMean_top_bound (l : PrimeGeFive) (N : Nat) :
    columnMean l N ≤
      ConcreteFiniteTheorem311.thetaLogVolume l + (N : Real) := by
  exact columnMean_le_hull l N |>.trans_eq (columnHull_eq_top_level l N)

theorem columnMean_base_bound (l : PrimeGeFive) (N : Nat) :
    lowerFiniteSup (columnLogVolume l (N := N)) ≤ columnMean l N :=
  lower_hull_le_columnMean l N

structure FiniteColumnOrbit (l : PrimeGeFive) (N : Nat) where
  action : ConcreteFiniteTheorem311.finiteLabel l →
    FiniteColumnIndex l N → FiniteColumnIndex l N
  identity : ∀ x, action 0 x = x
  composition : ∀ g h x, action (g + h) x = action g (action h x)
  volume_invariant : ∀ g x, columnLogVolume l (action g x) = columnLogVolume l x

def processionOrbit (l : PrimeGeFive) (N : Nat) : FiniteColumnOrbit l N where
  action := FiniteColumnIndex.ind1
  identity := FiniteColumnIndex.ind1_zero
  composition := FiniteColumnIndex.ind1_add
  volume_invariant := columnLogVolume_ind1 l N

def tensorOrbit (l : PrimeGeFive) (N : Nat) : FiniteColumnOrbit l N where
  action := FiniteColumnIndex.ind2
  identity := FiniteColumnIndex.ind2_zero
  composition := FiniteColumnIndex.ind2_add
  volume_invariant := columnLogVolume_ind2 l N

theorem processionOrbit_action (l : PrimeGeFive) (N : Nat)
    (g : ConcreteFiniteTheorem311.finiteLabel l)
    (x : FiniteColumnIndex l N) :
    (processionOrbit l N).action g x = FiniteColumnIndex.ind1 g x := rfl

theorem tensorOrbit_action (l : PrimeGeFive) (N : Nat)
    (g : ConcreteFiniteTheorem311.finiteLabel l)
    (x : FiniteColumnIndex l N) :
    (tensorOrbit l N).action g x = FiniteColumnIndex.ind2 g x := rfl

theorem processionOrbit_invariant (l : PrimeGeFive) (N : Nat)
    (g : ConcreteFiniteTheorem311.finiteLabel l)
    (x : FiniteColumnIndex l N) :
    columnLogVolume l ((processionOrbit l N).action g x) =
      columnLogVolume l x :=
  (processionOrbit l N).volume_invariant g x

theorem tensorOrbit_invariant (l : PrimeGeFive) (N : Nat)
    (g : ConcreteFiniteTheorem311.finiteLabel l)
    (x : FiniteColumnIndex l N) :
    columnLogVolume l ((tensorOrbit l N).action g x) =
      columnLogVolume l x :=
  (tensorOrbit l N).volume_invariant g x

theorem orbit_sum_invariant (l : PrimeGeFive) (N : Nat)
    (orbit : FiniteColumnOrbit l N) (g : ConcreteFiniteTheorem311.finiteLabel l) :
    (∑ x : FiniteColumnIndex l N,
        columnLogVolume l (orbit.action g x)) = columnSum l N := by
  classical
  apply Finset.sum_congr rfl
  intro x hx
  exact orbit.volume_invariant g x

structure FiniteTensorNormalization (l : PrimeGeFive) (N : Nat) where
  packet : WeightedDeterminantPacket (FiniteColumnIndex l N)
  commonDegree : ℕ
  commonDegree_eq : commonDegree = packet.commonTensorDegree
  normalized : Real
  normalized_eq : normalized = packet.normalizedLogVolume
  weighted : Real
  weighted_eq : weighted = packet.weightedLogVolume
  denominator_cleared : weighted = (commonDegree : Real) * normalized

def columnTensorNormalization (l : PrimeGeFive) (N : Nat) :
    FiniteTensorNormalization l N where
  packet := columnWeightedPacket l N
  commonDegree := (columnWeightedPacket l N).commonTensorDegree
  commonDegree_eq := rfl
  normalized := (columnWeightedPacket l N).normalizedLogVolume
  normalized_eq := rfl
  weighted := (columnWeightedPacket l N).weightedLogVolume
  weighted_eq := rfl
  denominator_cleared :=
    WeightedDeterminantPacket.weightedLogVolume_eq_commonTensorDegree_mul_normalizedLogVolume _

theorem columnTensorNormalization_packet (l : PrimeGeFive) (N : Nat) :
    (columnTensorNormalization l N).packet = columnWeightedPacket l N := rfl

theorem columnTensorNormalization_degree (l : PrimeGeFive) (N : Nat) :
    (columnTensorNormalization l N).commonDegree = 1 := by
  simp [columnTensorNormalization, columnWeightedPacket_common_degree]

theorem columnTensorNormalization_normalized (l : PrimeGeFive) (N : Nat) :
    (columnTensorNormalization l N).normalized = columnSum l N := by
  simp [columnTensorNormalization, columnWeightedPacket_normalized, columnSum]

theorem columnTensorNormalization_weighted (l : PrimeGeFive) (N : Nat) :
    (columnTensorNormalization l N).weighted = columnSum l N := by
  simp [columnTensorNormalization, columnWeightedPacket_weighted, columnSum]

theorem columnTensorNormalization_identity (l : PrimeGeFive) (N : Nat) :
    (columnTensorNormalization l N).weighted =
      ((columnTensorNormalization l N).commonDegree : Real) *
        (columnTensorNormalization l N).normalized := by
  exact (columnTensorNormalization l N).denominator_cleared

theorem columnTensorNormalization_no_denominator (l : PrimeGeFive) (N : Nat) :
    (columnTensorNormalization l N).commonDegree = 1 ∧
      (columnTensorNormalization l N).weighted =
        (columnTensorNormalization l N).normalized := by
  constructor
  · exact columnTensorNormalization_degree l N
  · rw [columnTensorNormalization_identity, columnTensorNormalization_degree]
    norm_num

def finiteColumnArithmeticCertificate (l : PrimeGeFive) (N : Nat) :
    StepXIFiniteCertificate (FiniteColumnIndex l N) :=
  finiteColumnCertificate l N

theorem finiteColumnArithmeticCertificate_hull (l : PrimeGeFive) (N : Nat) :
    (finiteColumnArithmeticCertificate l N).hull = columnHull l N := rfl

theorem finiteColumnArithmeticCertificate_weighted (l : PrimeGeFive) (N : Nat) :
    (finiteColumnArithmeticCertificate l N).weighted = columnUniformWeights l N := rfl

theorem finiteColumnArithmeticCertificate_average_bound (l : PrimeGeFive) (N : Nat) :
    (finiteColumnArithmeticCertificate l N).weighted.average ≤
      (finiteColumnArithmeticCertificate l N).hull.hullVolume := by
  exact columnUniformWeights_average_le_hull l N

theorem finiteColumnArithmeticCertificate_q_bound (l : PrimeGeFive) (N : Nat) :
    (finiteColumnArithmeticCertificate l N).qSigned ≤
      (finiteColumnArithmeticCertificate l N).hull.hullVolume := by
  exact (finiteColumnArithmeticCertificate l N).q_le_hull

theorem finiteColumnArithmeticCertificate_theta_bound (l : PrimeGeFive) (N : Nat) :
    (finiteColumnArithmeticCertificate l N).hull.hullVolume ≤
      (finiteColumnArithmeticCertificate l N).thetaSigned := by
  exact (finiteColumnArithmeticCertificate l N).hull_le_theta

end ConcreteFiniteStepXI

end

end LeanFormal.IUT
