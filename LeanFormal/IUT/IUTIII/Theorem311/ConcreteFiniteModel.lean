/-
  A finite, source-oriented carrier for the three indeterminacy layers.

  The construction follows the useful part of the public Stage-1 model: the
  first two indeterminacies are translations by the finite label group and the
  third one is a directed natural-number lift.  Here the underlying arithmetic
  carrier is our proved Q(i)-at-5 C-stage packet, rather than an unconstrained
  toy proposition.  The finite model is deliberately recorded as a model
  boundary; it is not the source theorem about arbitrary Hodge theaters.
-/

import LeanFormal.IUT.IUTII.Theta.ConcreteSourceHistoryLinkBridge
import LeanFormal.IUT.IUTIII.Theorem311.Indeterminacy.UpperSemi
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.ThetaPacketBridge
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic

namespace LeanFormal.IUT

open scoped BigOperators

noncomputable section

local instance primeFactForConcreteTheorem311 (l : PrimeGeFive) :
    Fact (Nat.Prime l.value) := l.factPrime

local instance fivePrimeFactConcreteTheorem311 : Fact (Nat.Prime 5) :=
  ⟨Nat.prime_five⟩

namespace ConcreteFiniteTheorem311

abbrev finiteLabel (l : PrimeGeFive) := Fl l.value
abbrev algebraicLevel (l : PrimeGeFive) :=
  ConcreteSourceEtaleThetaBridge.AlgebraicFiniteThetaLevel l
abbrev theater (l : PrimeGeFive) :=
  ConcreteSourceEtaleThetaBridge.theater l
abbrev packet (l : PrimeGeFive) :=
  ConcreteSourceEtaleThetaBridge.packet l
abbrev quotient (l : PrimeGeFive) :=
  ConcreteSourceEtaleThetaBridge.quotient l

def reduction (l : PrimeGeFive) : ℤ →+ finiteLabel l :=
  ConcreteSourceEtaleThetaBridge.reduction l

def quotientEquiv (l : PrimeGeFive) : quotient l ≃+ finiteLabel l :=
  ConcreteSourceEtaleThetaBridge.quotientEquiv l

def thetaScale (l : PrimeGeFive) (j : SignedLabel l.value) : Real :=
  ConcreteSourceEtaleThetaBridge.thetaScale l j

def thetaLogVolume (l : PrimeGeFive) : Real :=
  ConcreteSourceEtaleThetaBridge.thetaLogVolume l

theorem reduction_apply (l : PrimeGeFive) (n : ℤ) :
    reduction l n = (packet l).finiteReduction n := by
  rfl

theorem reduction_kernel (l : PrimeGeFive) :
    (reduction l).ker = AddSubgroup.zmultiples (l.value : ℤ) := by
  exact ConcreteSourceEtaleThetaBridge.reduction_kernel l

theorem reduction_surjective (l : PrimeGeFive) :
    Function.Surjective (reduction l) := by
  exact ConcreteSourceEtaleThetaBridge.reduction_surjective l

theorem quotientEquiv_apply_mk (l : PrimeGeFive) (n : ℤ) :
    quotientEquiv l (QuotientAddGroup.mk n) = reduction l n := by
  exact ConcreteSourceEtaleThetaBridge.quotientEquiv_apply_mk l n

theorem quotientEquiv_bijective (l : PrimeGeFive) :
    Function.Bijective (quotientEquiv l) := by
  exact (quotientEquiv l).bijective

theorem quotient_zero_iff_multiple (l : PrimeGeFive) (n : ℤ) :
    (QuotientAddGroup.mk n : quotient l) = 0 ↔
      n ∈ AddSubgroup.zmultiples (l.value : ℤ) := by
  exact ConcreteSourceEtaleThetaBridge.quotient_zero_iff_multiple l n

theorem quotient_eq_iff_multiple (l : PrimeGeFive) (m n : ℤ) :
    (QuotientAddGroup.mk m : quotient l) = QuotientAddGroup.mk n ↔
      m - n ∈ AddSubgroup.zmultiples (l.value : ℤ) := by
  exact ConcreteSourceEtaleThetaBridge.quotient_eq_iff_multiple l m n

theorem quotient_add_multiple (l : PrimeGeFive) (n k : ℤ) :
    (QuotientAddGroup.mk (n + (l.value : ℤ) * k) : quotient l) =
      QuotientAddGroup.mk n := by
  exact ConcreteSourceEtaleThetaBridge.quotient_mk_add_multiple l n k

theorem quotient_sub_multiple (l : PrimeGeFive) (n k : ℤ) :
    (QuotientAddGroup.mk (n - (l.value : ℤ) * k) : quotient l) =
      QuotientAddGroup.mk n := by
  exact ConcreteSourceEtaleThetaBridge.quotient_mk_sub_multiple l n k

/-! The finite procession choice.  The place, curve, Frobenioid, and theta
packet are fixed to the proved C-stage carrier; only the three displayed
indeterminacy coordinates vary. -/

structure ProcessionChoice (l : PrimeGeFive) where
  processionLabel : finiteLabel l
  tensorLabel : finiteLabel l
  upperSemiLevel : Nat

namespace ProcessionChoice

variable {l : PrimeGeFive}

def base : ProcessionChoice l where
  processionLabel := 0
  tensorLabel := 0
  upperSemiLevel := 0

@[simp] theorem base_processionLabel : (base : ProcessionChoice l).processionLabel = 0 :=
  rfl

@[simp] theorem base_tensorLabel : (base : ProcessionChoice l).tensorLabel = 0 :=
  rfl

@[simp] theorem base_upperSemiLevel : (base : ProcessionChoice l).upperSemiLevel = 0 :=
  rfl

def ind1Act (t : finiteLabel l) (choice : ProcessionChoice l) : ProcessionChoice l :=
  { choice with processionLabel := t + choice.processionLabel }

def ind2Act (t : finiteLabel l) (choice : ProcessionChoice l) : ProcessionChoice l :=
  { choice with tensorLabel := t + choice.tensorLabel }

def ind3Lift (n : Nat) (choice : ProcessionChoice l) : ProcessionChoice l :=
  { choice with upperSemiLevel := choice.upperSemiLevel + n }

@[simp] theorem ind1_processionLabel (t : finiteLabel l) (choice : ProcessionChoice l) :
    (ind1Act t choice).processionLabel = t + choice.processionLabel :=
  rfl

@[simp] theorem ind1_tensorLabel (t : finiteLabel l) (choice : ProcessionChoice l) :
    (ind1Act t choice).tensorLabel = choice.tensorLabel :=
  rfl

@[simp] theorem ind1_upperSemiLevel (t : finiteLabel l) (choice : ProcessionChoice l) :
    (ind1Act t choice).upperSemiLevel = choice.upperSemiLevel :=
  rfl

@[simp] theorem ind2_processionLabel (t : finiteLabel l) (choice : ProcessionChoice l) :
    (ind2Act t choice).processionLabel = choice.processionLabel :=
  rfl

@[simp] theorem ind2_tensorLabel (t : finiteLabel l) (choice : ProcessionChoice l) :
    (ind2Act t choice).tensorLabel = t + choice.tensorLabel :=
  rfl

@[simp] theorem ind2_upperSemiLevel (t : finiteLabel l) (choice : ProcessionChoice l) :
    (ind2Act t choice).upperSemiLevel = choice.upperSemiLevel :=
  rfl

@[simp] theorem ind3_processionLabel (n : Nat) (choice : ProcessionChoice l) :
    (ind3Lift n choice).processionLabel = choice.processionLabel :=
  rfl

@[simp] theorem ind3_tensorLabel (n : Nat) (choice : ProcessionChoice l) :
    (ind3Lift n choice).tensorLabel = choice.tensorLabel :=
  rfl

@[simp] theorem ind3_upperSemiLevel (n : Nat) (choice : ProcessionChoice l) :
    (ind3Lift n choice).upperSemiLevel = choice.upperSemiLevel + n :=
  rfl

@[simp] theorem ind1_zero (choice : ProcessionChoice l) :
    ind1Act 0 choice = choice := by
  cases choice
  simp [ind1Act]

@[simp] theorem ind1_add (g h : finiteLabel l) (choice : ProcessionChoice l) :
    ind1Act (g + h) choice = ind1Act g (ind1Act h choice) := by
  cases choice
  simp [ind1Act, add_comm, add_left_comm]

@[simp] theorem ind1_inverse (g : finiteLabel l) (choice : ProcessionChoice l) :
    ind1Act (-g) (ind1Act g choice) = choice := by
  cases choice
  simp [ind1Act]

@[simp] theorem ind1_cancel (g : finiteLabel l) (choice : ProcessionChoice l) :
    ind1Act g (ind1Act (-g) choice) = choice := by
  cases choice
  simp [ind1Act]

@[simp] theorem ind2_zero (choice : ProcessionChoice l) :
    ind2Act 0 choice = choice := by
  cases choice
  simp [ind2Act]

@[simp] theorem ind2_add (g h : finiteLabel l) (choice : ProcessionChoice l) :
    ind2Act (g + h) choice = ind2Act g (ind2Act h choice) := by
  cases choice
  simp [ind2Act, add_comm, add_left_comm]

@[simp] theorem ind2_inverse (g : finiteLabel l) (choice : ProcessionChoice l) :
    ind2Act (-g) (ind2Act g choice) = choice := by
  cases choice
  simp [ind2Act]

@[simp] theorem ind2_cancel (g : finiteLabel l) (choice : ProcessionChoice l) :
    ind2Act g (ind2Act (-g) choice) = choice := by
  cases choice
  simp [ind2Act]

@[simp] theorem ind3_zero (choice : ProcessionChoice l) :
    ind3Lift 0 choice = choice := by
  cases choice
  simp [ind3Lift]

@[simp] theorem ind3_add (m n : Nat) (choice : ProcessionChoice l) :
    ind3Lift (m + n) choice = ind3Lift n (ind3Lift m choice) := by
  cases choice
  simp [ind3Lift, Nat.add_assoc]

theorem ind1_ind2_commute (g h : finiteLabel l) (choice : ProcessionChoice l) :
    ind1Act g (ind2Act h choice) = ind2Act h (ind1Act g choice) := by
  cases choice
  rfl

theorem ind1_ind3_commute (g : finiteLabel l) (n : Nat) (choice : ProcessionChoice l) :
    ind1Act g (ind3Lift n choice) = ind3Lift n (ind1Act g choice) := by
  cases choice
  rfl

theorem ind2_ind3_commute (g : finiteLabel l) (n : Nat) (choice : ProcessionChoice l) :
    ind2Act g (ind3Lift n choice) = ind3Lift n (ind2Act g choice) := by
  cases choice
  rfl

def Ind1Step (a b : ProcessionChoice l) : Prop :=
  ∃ t, ind1Act t a = b

def Ind2Step (a b : ProcessionChoice l) : Prop :=
  ∃ t, ind2Act t a = b

def Ind3Step (a b : ProcessionChoice l) : Prop :=
  ∃ n, ind3Lift n a = b

theorem ind1Step_refl (a : ProcessionChoice l) : Ind1Step a a :=
  ⟨0, ind1_zero a⟩

theorem ind1Step_symm {a b : ProcessionChoice l} (h : Ind1Step a b) : Ind1Step b a := by
  rcases h with ⟨t, rfl⟩
  exact ⟨-t, ind1_inverse t a⟩

theorem ind1Step_trans {a b c : ProcessionChoice l}
    (hab : Ind1Step a b) (hbc : Ind1Step b c) : Ind1Step a c := by
  rcases hab with ⟨g, rfl⟩
  rcases hbc with ⟨h, rfl⟩
  exact ⟨h + g, by rw [ind1_add]⟩

theorem ind2Step_refl (a : ProcessionChoice l) : Ind2Step a a :=
  ⟨0, ind2_zero a⟩

theorem ind2Step_symm {a b : ProcessionChoice l} (h : Ind2Step a b) : Ind2Step b a := by
  rcases h with ⟨t, rfl⟩
  exact ⟨-t, ind2_inverse t a⟩

theorem ind2Step_trans {a b c : ProcessionChoice l}
    (hab : Ind2Step a b) (hbc : Ind2Step b c) : Ind2Step a c := by
  rcases hab with ⟨g, rfl⟩
  rcases hbc with ⟨h, rfl⟩
  exact ⟨h + g, by rw [ind2_add]⟩

theorem ind3Step_refl (a : ProcessionChoice l) : Ind3Step a a :=
  ⟨0, ind3_zero a⟩

theorem ind3Step_trans {a b c : ProcessionChoice l}
    (hab : Ind3Step a b) (hbc : Ind3Step b c) : Ind3Step a c := by
  rcases hab with ⟨m, rfl⟩
  rcases hbc with ⟨n, rfl⟩
  exact ⟨m + n, by rw [ind3_add]⟩

theorem ind1_preserves_tensor (t : finiteLabel l) (a : ProcessionChoice l) :
    (ind1Act t a).tensorLabel = a.tensorLabel :=
  rfl

theorem ind2_preserves_procession (t : finiteLabel l) (a : ProcessionChoice l) :
    (ind2Act t a).processionLabel = a.processionLabel :=
  rfl

theorem ind1_preserves_level (t : finiteLabel l) (a : ProcessionChoice l) :
    (ind1Act t a).upperSemiLevel = a.upperSemiLevel :=
  rfl

theorem ind2_preserves_level (t : finiteLabel l) (a : ProcessionChoice l) :
    (ind2Act t a).upperSemiLevel = a.upperSemiLevel :=
  rfl

theorem ind3_preserves_labels (n : Nat) (a : ProcessionChoice l) :
    (ind3Lift n a).processionLabel = a.processionLabel ∧
      (ind3Lift n a).tensorLabel = a.tensorLabel :=
  ⟨rfl, rfl⟩

end ProcessionChoice

def thetaPacket (l : PrimeGeFive) : PositivePacket (SignedLabel l.value) :=
  (theater l).thetaPacket.toPositivePacket

@[simp] theorem thetaPacket_scale (l : PrimeGeFive) (j : SignedLabel l.value) :
    (thetaPacket l).scale j = thetaScale l j :=
  rfl

theorem thetaPacket_positive (l : PrimeGeFive) (j : SignedLabel l.value) :
    0 < (thetaPacket l).scale j := by
  exact ConcreteSourceEtaleThetaBridge.theta_scale_pos l j

theorem thetaPacket_det_eq_product (l : PrimeGeFive) :
    packetDet (thetaPacket l) = ∏ j : SignedLabel l.value, thetaScale l j := by
  exact FiniteThetaPacket.toPositivePacket_det_eq_prod (theater l).thetaPacket

theorem thetaPacket_logVolume_eq_sum (l : PrimeGeFive) :
    packetLogVolume (thetaPacket l) =
      ∑ j : SignedLabel l.value, Real.log (thetaScale l j) := by
  exact FiniteThetaPacket.toPositivePacket_logVolume_eq_sum (theater l).thetaPacket

theorem thetaPacket_logVolume_eq_theta (l : PrimeGeFive) :
    packetLogVolume (thetaPacket l) = thetaLogVolume l := by
  rw [thetaPacket_logVolume_eq_sum]
  simpa [thetaScale, thetaLogVolume, ConcreteSourceEtaleThetaBridge.thetaLogScale] using
    (ConcreteSourceEtaleThetaBridge.theta_log_volume_eq_sum l).symm

theorem thetaPacket_log_det (l : PrimeGeFive) :
    Real.log (packetDet (thetaPacket l)) = thetaLogVolume l := by
  rw [← thetaPacket_logVolume_eq_theta l]
  exact (packetLogVolume_eq_log_det (thetaPacket l)).symm

def normalizedLogVolume (l : PrimeGeFive)
    (choice : ProcessionChoice l) : Real :=
  thetaLogVolume l + (choice.upperSemiLevel : Real)

theorem normalizedLogVolume_base (l : PrimeGeFive) :
    normalizedLogVolume l ProcessionChoice.base = thetaLogVolume l := by
  simp [normalizedLogVolume]

theorem normalizedLogVolume_ind1 (l : PrimeGeFive)
    (t : finiteLabel l) (choice : ProcessionChoice l) :
    normalizedLogVolume l (ProcessionChoice.ind1Act t choice) =
      normalizedLogVolume l choice := by
  simp [normalizedLogVolume]

theorem normalizedLogVolume_ind2 (l : PrimeGeFive)
    (t : finiteLabel l) (choice : ProcessionChoice l) :
    normalizedLogVolume l (ProcessionChoice.ind2Act t choice) =
      normalizedLogVolume l choice := by
  simp [normalizedLogVolume]

theorem normalizedLogVolume_ind3 (l : PrimeGeFive)
    (n : Nat) (choice : ProcessionChoice l) :
    normalizedLogVolume l choice ≤
      normalizedLogVolume l (ProcessionChoice.ind3Lift n choice) := by
  simp [normalizedLogVolume]

theorem normalizedLogVolume_ind3_eq_iff (l : PrimeGeFive)
    (n : Nat) (choice : ProcessionChoice l) :
    normalizedLogVolume l choice =
      normalizedLogVolume l (ProcessionChoice.ind3Lift n choice) ↔ n = 0 := by
  simp [normalizedLogVolume]

theorem normalizedLogVolume_ind1Step {l : PrimeGeFive}
    {a b : ProcessionChoice l} (h : ProcessionChoice.Ind1Step a b) :
    normalizedLogVolume l a = normalizedLogVolume l b := by
  rcases h with ⟨t, rfl⟩
  exact normalizedLogVolume_ind1 l t a

theorem normalizedLogVolume_ind2Step {l : PrimeGeFive}
    {a b : ProcessionChoice l} (h : ProcessionChoice.Ind2Step a b) :
    normalizedLogVolume l a = normalizedLogVolume l b := by
  rcases h with ⟨t, rfl⟩
  exact normalizedLogVolume_ind2 l t a

theorem normalizedLogVolume_ind3Step {l : PrimeGeFive}
    {a b : ProcessionChoice l} (h : ProcessionChoice.Ind3Step a b) :
    normalizedLogVolume l a ≤ normalizedLogVolume l b := by
  rcases h with ⟨n, rfl⟩
  exact normalizedLogVolume_ind3 l n a

def possibleImage (l : PrimeGeFive) (choice : ProcessionChoice l) : Set Real :=
  {normalizedLogVolume l choice}

theorem possibleImage_nonempty (l : PrimeGeFive) (choice : ProcessionChoice l) :
    (possibleImage l choice).Nonempty := by
  exact ⟨normalizedLogVolume l choice, Set.mem_singleton _⟩

theorem possibleImage_ind1 (l : PrimeGeFive)
    (t : finiteLabel l) (choice : ProcessionChoice l) :
    possibleImage l (ProcessionChoice.ind1Act t choice) = possibleImage l choice := by
  rw [possibleImage, possibleImage, normalizedLogVolume_ind1]

theorem possibleImage_ind2 (l : PrimeGeFive)
    (t : finiteLabel l) (choice : ProcessionChoice l) :
    possibleImage l (ProcessionChoice.ind2Act t choice) = possibleImage l choice := by
  rw [possibleImage, possibleImage, normalizedLogVolume_ind2]

theorem possibleImage_ind3 (l : PrimeGeFive)
    (n : Nat) (choice : ProcessionChoice l) :
    ∀ z, z ∈ possibleImage l choice →
      ∃ w, w ∈ possibleImage l (ProcessionChoice.ind3Lift n choice) ∧ z ≤ w := by
  intro z hz
  rw [possibleImage] at hz
  rcases Set.mem_singleton_iff.mp hz with rfl
  refine ⟨normalizedLogVolume l (ProcessionChoice.ind3Lift n choice),
    Set.mem_singleton _, normalizedLogVolume_ind3 l n choice⟩

def possibleImageUpperSemi (l : PrimeGeFive) : UpperSemiCorrespondence Nat Real where
  image n := {thetaLogVolume l + (n : Real)}
  upper := by
    intro m n hmn z hz
    rcases Set.mem_singleton_iff.mp hz with rfl
    refine ⟨thetaLogVolume l + (n : Real), Set.mem_singleton _, ?_⟩
    have hcast : (m : Real) ≤ (n : Real) := by
      exact_mod_cast hmn
    linarith

theorem possibleImageUpperSemi_image (l : PrimeGeFive) (n : Nat) :
    (possibleImageUpperSemi l).image n =
      {thetaLogVolume l + (n : Real)} :=
  rfl

theorem possibleImageUpperSemi_upper (l : PrimeGeFive)
    {m n : Nat} (hmn : m ≤ n) (z : Real)
    (hz : z ∈ (possibleImageUpperSemi l).image m) :
    ∃ w, w ∈ (possibleImageUpperSemi l).image n ∧ z ≤ w := by
  exact (possibleImageUpperSemi l).upper hmn z hz

structure FiniteOutput (l : PrimeGeFive) where
  algebraicLevel : algebraicLevel l
  sourceTheater : HodgeTheater l (FinitePrimePlace 2 7)
  sourceHistory : ConcreteInitialThetaHistory l
  localCarrier : ConcreteTateLocalCarrier l
  finiteQuotient : quotient l
  quotientEquiv : quotient l ≃+ finiteLabel l
  baseChoice : ProcessionChoice l
  logVolume : ProcessionChoice l → Real
  ind1_invariant : ∀ t c,
    logVolume (ProcessionChoice.ind1Act t c) = logVolume c
  ind2_invariant : ∀ t c,
    logVolume (ProcessionChoice.ind2Act t c) = logVolume c
  ind3_upper : ∀ n c,
    logVolume c ≤ logVolume (ProcessionChoice.ind3Lift n c)
  possibleImage : ProcessionChoice l → Set Real
  possibleImage_nonempty : ∀ c, (possibleImage c).Nonempty
  possibleImage_ind1 : ∀ t c,
    possibleImage (ProcessionChoice.ind1Act t c) = possibleImage c
  possibleImage_ind2 : ∀ t c,
    possibleImage (ProcessionChoice.ind2Act t c) = possibleImage c
  possibleImage_ind3 : ∀ n c z, z ∈ possibleImage c →
    ∃ w, w ∈ possibleImage (ProcessionChoice.ind3Lift n c) ∧ z ≤ w

def finiteOutput (l : PrimeGeFive) : FiniteOutput l where
  algebraicLevel := ConcreteSourceEtaleThetaBridge.algebraicFiniteThetaLevel l
  sourceTheater := theater l
  sourceHistory := concreteInitialThetaHistory l
  localCarrier := ConcreteTateLocalCarrier.canonical l
  finiteQuotient := QuotientAddGroup.mk 0
  quotientEquiv := quotientEquiv l
  baseChoice := (ProcessionChoice.base : ProcessionChoice l)
  logVolume := normalizedLogVolume l
  ind1_invariant := by intro t c; exact normalizedLogVolume_ind1 l t c
  ind2_invariant := by intro t c; exact normalizedLogVolume_ind2 l t c
  ind3_upper := by intro n c; exact normalizedLogVolume_ind3 l n c
  possibleImage := possibleImage l
  possibleImage_nonempty := by intro c; exact possibleImage_nonempty l c
  possibleImage_ind1 := by intro t c; exact possibleImage_ind1 l t c
  possibleImage_ind2 := by intro t c; exact possibleImage_ind2 l t c
  possibleImage_ind3 := by
    intro n c z hz
    exact possibleImage_ind3 l n c z hz

@[simp] theorem finiteOutput_sourceTheater (l : PrimeGeFive) :
    (finiteOutput l).sourceTheater = theater l :=
  rfl

@[simp] theorem finiteOutput_sourceHistory (l : PrimeGeFive) :
    (finiteOutput l).sourceHistory = concreteInitialThetaHistory l :=
  rfl

@[simp] theorem finiteOutput_localCarrier (l : PrimeGeFive) :
    (finiteOutput l).localCarrier = ConcreteTateLocalCarrier.canonical l :=
  rfl

@[simp] theorem finiteOutput_finiteQuotient (l : PrimeGeFive) :
    (finiteOutput l).finiteQuotient = (QuotientAddGroup.mk 0 : quotient l) :=
  rfl

@[simp] theorem finiteOutput_quotientEquiv (l : PrimeGeFive) :
    (finiteOutput l).quotientEquiv = quotientEquiv l :=
  rfl

@[simp] theorem finiteOutput_baseChoice (l : PrimeGeFive) :
    (finiteOutput l).baseChoice = ProcessionChoice.base :=
  rfl

@[simp] theorem finiteOutput_logVolume (l : PrimeGeFive)
    (c : ProcessionChoice l) :
    (finiteOutput l).logVolume c = normalizedLogVolume l c :=
  rfl

theorem finiteOutput_ind1_invariant (l : PrimeGeFive)
    (t : finiteLabel l) (c : ProcessionChoice l) :
    (finiteOutput l).logVolume (ProcessionChoice.ind1Act t c) =
      (finiteOutput l).logVolume c := by
  exact normalizedLogVolume_ind1 l t c

theorem finiteOutput_ind2_invariant (l : PrimeGeFive)
    (t : finiteLabel l) (c : ProcessionChoice l) :
    (finiteOutput l).logVolume (ProcessionChoice.ind2Act t c) =
      (finiteOutput l).logVolume c := by
  exact normalizedLogVolume_ind2 l t c

theorem finiteOutput_ind3_upper (l : PrimeGeFive)
    (n : Nat) (c : ProcessionChoice l) :
    (finiteOutput l).logVolume c ≤
      (finiteOutput l).logVolume (ProcessionChoice.ind3Lift n c) := by
  exact normalizedLogVolume_ind3 l n c

theorem finiteOutput_possibleImage_nonempty (l : PrimeGeFive)
    (c : ProcessionChoice l) :
    ((finiteOutput l).possibleImage c).Nonempty := by
  exact possibleImage_nonempty l c

theorem finiteOutput_possibleImage_ind1 (l : PrimeGeFive)
    (t : finiteLabel l) (c : ProcessionChoice l) :
    (finiteOutput l).possibleImage (ProcessionChoice.ind1Act t c) =
      (finiteOutput l).possibleImage c := by
  exact possibleImage_ind1 l t c

theorem finiteOutput_possibleImage_ind2 (l : PrimeGeFive)
    (t : finiteLabel l) (c : ProcessionChoice l) :
    (finiteOutput l).possibleImage (ProcessionChoice.ind2Act t c) =
      (finiteOutput l).possibleImage c := by
  exact possibleImage_ind2 l t c

theorem finiteOutput_possibleImage_ind3 (l : PrimeGeFive)
    (n : Nat) (c : ProcessionChoice l) (z : Real)
    (hz : z ∈ (finiteOutput l).possibleImage c) :
    ∃ w, w ∈ (finiteOutput l).possibleImage (ProcessionChoice.ind3Lift n c) ∧ z ≤ w := by
  exact possibleImage_ind3 l n c z hz

theorem finiteOutput_reduction_kernel (l : PrimeGeFive) :
    (reduction l).ker = AddSubgroup.zmultiples (l.value : ℤ) :=
  reduction_kernel l

theorem finiteOutput_reduction_surjective (l : PrimeGeFive) :
    Function.Surjective (reduction l) :=
  reduction_surjective l

theorem finiteOutput_root_compatibility (l : PrimeGeFive) (n : ℤ) :
    (packet l).integerRoot n =
      (packet l).compatibleRoots.roots (n : ℚ) := by
  exact ConcreteSourceEtaleThetaBridge.integer_root_compatible l n

theorem finiteOutput_q_deck_refl (l : PrimeGeFive) :
    ConcreteSourceEtaleThetaBridge.qDeckAction l (AlgEquiv.refl) = MulEquiv.refl _ :=
  ConcreteSourceEtaleThetaBridge.q_deck_action_refl l

theorem finiteOutput_q_deck_trans (l : PrimeGeFive)
    (sigma tau : ConcreteTateParameter.LocalAbsoluteGalois l) :
    ConcreteSourceEtaleThetaBridge.qDeckAction l (sigma.trans tau) =
      (ConcreteSourceEtaleThetaBridge.qDeckAction l sigma).trans
        (ConcreteSourceEtaleThetaBridge.qDeckAction l tau) :=
  ConcreteSourceEtaleThetaBridge.q_deck_action_trans l sigma tau

theorem finiteOutput_theta_log_det (l : PrimeGeFive) :
    Real.log (packetDet (thetaPacket l)) = thetaLogVolume l :=
  thetaPacket_log_det l

theorem finiteOutput_theta_det_positive (l : PrimeGeFive) :
    0 < packetDet (thetaPacket l) := by
  rw [thetaPacket_det_eq_product]
  apply Finset.prod_pos
  intro j hj
  exact thetaPacket_positive l j

theorem finiteOutput_theta_det_nonzero (l : PrimeGeFive) :
    packetDet (thetaPacket l) ≠ 0 :=
  ne_of_gt (finiteOutput_theta_det_positive l)

theorem finiteOutput_theta_volume_exp (l : PrimeGeFive) :
    Real.exp (thetaLogVolume l) = packetDet (thetaPacket l) := by
  rw [← finiteOutput_theta_log_det l]
  exact Real.exp_log (finiteOutput_theta_det_positive l)

end ConcreteFiniteTheorem311

end

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def concreteFiniteTheorem311Model : Obligation :=
  { id := "IUT-III.concrete-finite-theorem311-model"
    source := "IUT III, Theorem 3.11, (Ind1)--(Ind3) finite model"
    status := VerificationStatus.interface
    note :=
      "A proved finite model is instantiated from the concrete Q(i)-at-5 " ++
        "C-stage carrier. Ind1 and Ind2 are finite translation actions, " ++
        "Ind3 is a directed Nat lift, and the packet determinant/log-volume " ++
        "identities and q-deck action laws are inherited from proved lower " ++
        "layers. This is a source-audited model boundary, not the paper's " ++
        "arbitrary procession of D-prime-strips or its full multiradial " ++
        "algorithm; it cannot discharge the pending Theorem 3.11 obligation."
    dependsOn :=
      [ "IUT-I-II.concrete-source-algebraic-theta-bridge",
        "IUT-I-II.concrete-source-history-link-volume-bridge",
        "IUT-III.orbit-quotient-transport",
        "IUT-III.Ind3.upper-semi-kernel" ] }

end LeanFormal.IUT.Audit
