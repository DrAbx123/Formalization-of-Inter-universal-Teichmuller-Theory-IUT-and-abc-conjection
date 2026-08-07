import LeanFormal.IUT.Foundations.Theta.SignedLabelEquiv
import LeanFormal.IUT.IUTIII.Theorem311.ConcreteFiniteModel
import Mathlib.Tactic

namespace LeanFormal.IUT

open scoped BigOperators

noncomputable section

local instance primeFactForConcreteTransport (l : PrimeGeFive) :
    Fact (Nat.Prime l.value) := l.factPrime

namespace ConcreteFiniteTheorem311

open ProcessionChoice

def translatedPacket (l : PrimeGeFive) (t : finiteLabel l) :
    PositivePacket (SignedLabel l.value) where
  scale j := thetaScale l (SignedLabel.translate l t j)
  positive j := thetaPacket_positive l (SignedLabel.translate l t j)

@[simp] theorem translatedPacket_scale (l : PrimeGeFive) (t : finiteLabel l)
    (j : SignedLabel l.value) :
    (translatedPacket l t).scale j =
      thetaScale l (SignedLabel.translate l t j) :=
  rfl

theorem translatedPacket_positive (l : PrimeGeFive) (t : finiteLabel l)
    (j : SignedLabel l.value) :
    0 < (translatedPacket l t).scale j :=
  (translatedPacket l t).positive j

theorem translatedPacket_scale_ne_zero (l : PrimeGeFive) (t : finiteLabel l)
    (j : SignedLabel l.value) :
    (translatedPacket l t).scale j ≠ 0 :=
  ne_of_gt (translatedPacket_positive l t j)

theorem translatedPacket_logVolume_eq_theta (l : PrimeGeFive) (t : finiteLabel l) :
    packetLogVolume (translatedPacket l t) = thetaLogVolume l := by
  change (∑ j : SignedLabel l.value,
    Real.log (thetaScale l (SignedLabel.translate l t j))) = _
  have hsum := SignedLabel.sum_translate l t
    (fun j : SignedLabel l.value => Real.log (thetaScale l j))
  rw [hsum]
  exact (thetaPacket_logVolume_eq_sum l).trans
    (thetaPacket_logVolume_eq_theta l)

theorem translatedPacket_logVolume_eq_base (l : PrimeGeFive) (t : finiteLabel l) :
    packetLogVolume (translatedPacket l t) =
      packetLogVolume (thetaPacket l) := by
  rw [translatedPacket_logVolume_eq_theta, thetaPacket_logVolume_eq_theta]

theorem translatedPacket_det_eq_product (l : PrimeGeFive) (t : finiteLabel l) :
    packetDet (translatedPacket l t) =
      ∏ j : SignedLabel l.value,
        thetaScale l (SignedLabel.translate l t j) := by
  rw [packetDet_eq_prod]
  rfl

theorem translatedPacket_det_eq_base (l : PrimeGeFive) (t : finiteLabel l) :
    packetDet (translatedPacket l t) = packetDet (thetaPacket l) := by
  rw [translatedPacket_det_eq_product, thetaPacket_det_eq_product]
  exact SignedLabel.prod_translate l t (thetaScale l)

theorem translatedPacket_det_positive (l : PrimeGeFive) (t : finiteLabel l) :
    0 < packetDet (translatedPacket l t) := by
  rw [translatedPacket_det_eq_base]
  exact finiteOutput_theta_det_positive l

theorem translatedPacket_det_nonzero (l : PrimeGeFive) (t : finiteLabel l) :
    packetDet (translatedPacket l t) ≠ 0 :=
  ne_of_gt (translatedPacket_det_positive l t)

theorem translatedPacket_log_det (l : PrimeGeFive) (t : finiteLabel l) :
    Real.log (packetDet (translatedPacket l t)) = thetaLogVolume l := by
  rw [← translatedPacket_logVolume_eq_theta l t]
  exact (packetLogVolume_eq_log_det (translatedPacket l t)).symm

theorem translatedPacket_exp_log_det (l : PrimeGeFive) (t : finiteLabel l) :
    Real.exp (thetaLogVolume l) = packetDet (translatedPacket l t) := by
  rw [← translatedPacket_log_det l t]
  exact Real.exp_log (translatedPacket_det_positive l t)

theorem translatedPacket_scale_translate (l : PrimeGeFive)
    (s t : finiteLabel l) (j : SignedLabel l.value) :
    (translatedPacket l (s + t)).scale j =
      (translatedPacket l s).scale (SignedLabel.translate l t j) := by
  change thetaScale l (SignedLabel.translate l (s + t) j) =
    thetaScale l (SignedLabel.translate l s (SignedLabel.translate l t j))
  rw [SignedLabel.translate_add]

theorem translatedPacket_scale_translate_zero (l : PrimeGeFive)
    (j : SignedLabel l.value) :
    (translatedPacket l 0).scale j = thetaScale l j := by
  change thetaScale l (SignedLabel.translate l 0 j) = thetaScale l j
  rw [SignedLabel.translate_zero]

def choicePacket (l : PrimeGeFive) (choice : ProcessionChoice l) :
    PositivePacket (SignedLabel l.value) :=
  translatedPacket l choice.processionLabel

@[simp] theorem choicePacket_scale (l : PrimeGeFive)
    (choice : ProcessionChoice l) (j : SignedLabel l.value) :
    (choicePacket l choice).scale j =
      thetaScale l (SignedLabel.translate l choice.processionLabel j) :=
  rfl

theorem choicePacket_positive (l : PrimeGeFive)
    (choice : ProcessionChoice l) (j : SignedLabel l.value) :
    0 < (choicePacket l choice).scale j :=
  translatedPacket_positive l choice.processionLabel j

theorem choicePacket_logVolume (l : PrimeGeFive)
    (choice : ProcessionChoice l) :
    packetLogVolume (choicePacket l choice) = thetaLogVolume l :=
  translatedPacket_logVolume_eq_theta l choice.processionLabel

theorem choicePacket_det (l : PrimeGeFive)
    (choice : ProcessionChoice l) :
    packetDet (choicePacket l choice) = packetDet (thetaPacket l) :=
  translatedPacket_det_eq_base l choice.processionLabel

theorem choicePacket_log_det (l : PrimeGeFive)
    (choice : ProcessionChoice l) :
    Real.log (packetDet (choicePacket l choice)) = thetaLogVolume l :=
  translatedPacket_log_det l choice.processionLabel

theorem choicePacket_ind1_scale (l : PrimeGeFive)
    (t : finiteLabel l) (choice : ProcessionChoice l)
    (j : SignedLabel l.value) :
    (choicePacket l (ind1Act t choice)).scale j =
      (choicePacket l choice).scale (SignedLabel.translate l t j) := by
  change thetaScale l (SignedLabel.translate l
    (t + choice.processionLabel) j) =
    thetaScale l (SignedLabel.translate l choice.processionLabel
      (SignedLabel.translate l t j))
  rw [show t + choice.processionLabel = choice.processionLabel + t by ac_rfl,
    SignedLabel.translate_add]

theorem choicePacket_ind2_eq (l : PrimeGeFive)
    (t : finiteLabel l) (choice : ProcessionChoice l) :
    choicePacket l (ind2Act t choice) = choicePacket l choice := by
  rfl

theorem choicePacket_ind3_eq (l : PrimeGeFive)
    (n : Nat) (choice : ProcessionChoice l) :
    choicePacket l (ind3Lift n choice) = choicePacket l choice := by
  rfl

theorem choicePacket_logVolume_ind1 (l : PrimeGeFive)
    (t : finiteLabel l) (choice : ProcessionChoice l) :
    packetLogVolume (choicePacket l (ind1Act t choice)) =
      packetLogVolume (choicePacket l choice) := by
  rw [choicePacket_logVolume, choicePacket_logVolume]

theorem choicePacket_logVolume_ind2 (l : PrimeGeFive)
    (t : finiteLabel l) (choice : ProcessionChoice l) :
    packetLogVolume (choicePacket l (ind2Act t choice)) =
      packetLogVolume (choicePacket l choice) := by
  rw [choicePacket_ind2_eq]

theorem choicePacket_logVolume_ind3 (l : PrimeGeFive)
    (n : Nat) (choice : ProcessionChoice l) :
    packetLogVolume (choicePacket l (ind3Lift n choice)) =
      packetLogVolume (choicePacket l choice) := by
  rw [choicePacket_ind3_eq]

def translatedTensorPacket (l : PrimeGeFive)
    (s t : finiteLabel l) : PositivePacket (SignedLabel l.value × SignedLabel l.value) :=
  tensorPacket (translatedPacket l s) (translatedPacket l t)

@[simp] theorem translatedTensorPacket_scale (l : PrimeGeFive)
    (s t : finiteLabel l) (i : SignedLabel l.value × SignedLabel l.value) :
    (translatedTensorPacket l s t).scale i =
      thetaScale l (SignedLabel.translate l s i.1) *
        thetaScale l (SignedLabel.translate l t i.2) :=
  rfl

theorem translatedTensorPacket_positive (l : PrimeGeFive)
    (s t : finiteLabel l) (i : SignedLabel l.value × SignedLabel l.value) :
    0 < (translatedTensorPacket l s t).scale i := by
  exact mul_pos (translatedPacket_positive l s i.1)
    (translatedPacket_positive l t i.2)

theorem translatedTensorPacket_det (l : PrimeGeFive)
    (s t : finiteLabel l) :
    packetDet (translatedTensorPacket l s t) =
      packetDet (translatedPacket l s) ^ Fintype.card (SignedLabel l.value) *
        packetDet (translatedPacket l t) ^ Fintype.card (SignedLabel l.value) := by
  exact packetDet_tensor (translatedPacket l s) (translatedPacket l t)

theorem translatedTensorPacket_det_eq_base (l : PrimeGeFive)
    (s t : finiteLabel l) :
    packetDet (translatedTensorPacket l s t) =
      packetDet (thetaPacket l) ^ Fintype.card (SignedLabel l.value) *
        packetDet (thetaPacket l) ^ Fintype.card (SignedLabel l.value) := by
  rw [translatedTensorPacket_det, translatedPacket_det_eq_base,
    translatedPacket_det_eq_base]

theorem translatedTensorPacket_logVolume (l : PrimeGeFive)
    (s t : finiteLabel l) :
    packetLogVolume (translatedTensorPacket l s t) =
      (Fintype.card (SignedLabel l.value) : Real) * thetaLogVolume l +
        (Fintype.card (SignedLabel l.value) : Real) * thetaLogVolume l := by
  unfold translatedTensorPacket
  rw [packetLogVolume_tensor, translatedPacket_logVolume_eq_theta,
    translatedPacket_logVolume_eq_theta]

def choiceTensorPacket (l : PrimeGeFive) (choice : ProcessionChoice l) :
    PositivePacket (SignedLabel l.value × SignedLabel l.value) :=
  translatedTensorPacket l choice.processionLabel choice.tensorLabel

theorem choiceTensorPacket_scale (l : PrimeGeFive)
    (choice : ProcessionChoice l)
    (i : SignedLabel l.value × SignedLabel l.value) :
    (choiceTensorPacket l choice).scale i =
      (choicePacket l choice).scale i.1 *
        (translatedPacket l choice.tensorLabel).scale i.2 :=
  rfl

theorem choiceTensorPacket_positive (l : PrimeGeFive)
    (choice : ProcessionChoice l)
    (i : SignedLabel l.value × SignedLabel l.value) :
    0 < (choiceTensorPacket l choice).scale i := by
  exact translatedTensorPacket_positive l choice.processionLabel choice.tensorLabel i

theorem choiceTensorPacket_logVolume (l : PrimeGeFive)
    (choice : ProcessionChoice l) :
    packetLogVolume (choiceTensorPacket l choice) =
      (2 * (Fintype.card (SignedLabel l.value) : Real)) * thetaLogVolume l := by
  change packetLogVolume
    (translatedTensorPacket l choice.processionLabel choice.tensorLabel) = _
  rw [translatedTensorPacket_logVolume]
  ring

theorem choiceTensorPacket_det (l : PrimeGeFive)
    (choice : ProcessionChoice l) :
    packetDet (choiceTensorPacket l choice) =
      packetDet (thetaPacket l) ^ Fintype.card (SignedLabel l.value) *
        packetDet (thetaPacket l) ^ Fintype.card (SignedLabel l.value) :=
  translatedTensorPacket_det_eq_base l choice.processionLabel choice.tensorLabel

def rescaledChoicePacket (l : PrimeGeFive) (choice : ProcessionChoice l)
    (c : Real) (hc : 0 < c) : PositivePacket (SignedLabel l.value) :=
  rescalePacket c hc (choicePacket l choice)

@[simp] theorem rescaledChoicePacket_scale (l : PrimeGeFive)
    (choice : ProcessionChoice l) (c : Real) (hc : 0 < c)
    (j : SignedLabel l.value) :
    (rescaledChoicePacket l choice c hc).scale j =
      c * (choicePacket l choice).scale j :=
  rfl

theorem rescaledChoicePacket_positive (l : PrimeGeFive)
    (choice : ProcessionChoice l) (c : Real) (hc : 0 < c)
    (j : SignedLabel l.value) :
    0 < (rescaledChoicePacket l choice c hc).scale j :=
  (rescaledChoicePacket l choice c hc).positive j

theorem rescaledChoicePacket_det (l : PrimeGeFive)
    (choice : ProcessionChoice l) (c : Real) (hc : 0 < c) :
    packetDet (rescaledChoicePacket l choice c hc) =
      c ^ Fintype.card (SignedLabel l.value) * packetDet (thetaPacket l) := by
  change packetDet (rescalePacket c hc (choicePacket l choice)) = _
  rw [packetDet_rescale, choicePacket_det]

theorem rescaledChoicePacket_logVolume (l : PrimeGeFive)
    (choice : ProcessionChoice l) (c : Real) (hc : 0 < c) :
    packetLogVolume (rescaledChoicePacket l choice c hc) =
      (Fintype.card (SignedLabel l.value) : Real) * Real.log c +
        thetaLogVolume l := by
  change packetLogVolume (rescalePacket c hc (choicePacket l choice)) = _
  rw [packetLogVolume_rescale, choicePacket_logVolume]

theorem rescaledChoicePacket_log_det (l : PrimeGeFive)
    (choice : ProcessionChoice l) (c : Real) (hc : 0 < c) :
    packetLogVolume (rescaledChoicePacket l choice c hc) =
      Real.log (packetDet (rescaledChoicePacket l choice c hc)) :=
  packetLogVolume_eq_log_det _

def profileLogValue (l : PrimeGeFive) (choice : ProcessionChoice l)
    (j : SignedLabel l.value) : Real :=
  Real.log ((choicePacket l choice).scale j) +
    (choice.upperSemiLevel : Real)

theorem profileLogValue_eq_theta (l : PrimeGeFive)
    (choice : ProcessionChoice l) (j : SignedLabel l.value) :
    profileLogValue l choice j =
      Real.log (thetaScale l (SignedLabel.translate l choice.processionLabel j)) +
        (choice.upperSemiLevel : Real) :=
  rfl

def profileLogImage (l : PrimeGeFive) (choice : ProcessionChoice l) : Set Real :=
  Set.range (profileLogValue l choice)

theorem profileLogImage_nonempty (l : PrimeGeFive)
    (choice : ProcessionChoice l) :
    (profileLogImage l choice).Nonempty := by
  let j : SignedLabel l.value := SignedLabel.representative l 0
  exact ⟨profileLogValue l choice j, ⟨j, rfl⟩⟩

theorem profileLogValue_ind1 (l : PrimeGeFive)
    (t : finiteLabel l) (choice : ProcessionChoice l)
    (j : SignedLabel l.value) :
    profileLogValue l (ind1Act t choice) j =
      profileLogValue l choice (SignedLabel.translate l t j) := by
  unfold profileLogValue
  rw [choicePacket_ind1_scale]
  rfl

theorem profileLogValue_ind2 (l : PrimeGeFive)
    (t : finiteLabel l) (choice : ProcessionChoice l)
    (j : SignedLabel l.value) :
    profileLogValue l (ind2Act t choice) j =
      profileLogValue l choice j := by
  unfold profileLogValue
  rw [choicePacket_ind2_eq]
  rfl

theorem profileLogValue_ind3 (l : PrimeGeFive)
    (n : Nat) (choice : ProcessionChoice l)
    (j : SignedLabel l.value) :
    profileLogValue l choice j ≤
      profileLogValue l (ind3Lift n choice) j := by
  unfold profileLogValue
  rw [choicePacket_ind3_eq]
  norm_num [ind3Lift]

theorem profileLogImage_ind1 (l : PrimeGeFive)
    (t : finiteLabel l) (choice : ProcessionChoice l) :
    profileLogImage l (ind1Act t choice) = profileLogImage l choice := by
  ext z
  constructor
  · rintro ⟨j, rfl⟩
    refine ⟨SignedLabel.translate l t j, ?_⟩
    exact (profileLogValue_ind1 l t choice j).symm
  · rintro ⟨j, rfl⟩
    refine ⟨SignedLabel.translate l (-t) j, ?_⟩
    rw [profileLogValue_ind1]
    rw [SignedLabel.translate_cancel]

theorem profileLogImage_ind2 (l : PrimeGeFive)
    (t : finiteLabel l) (choice : ProcessionChoice l) :
    profileLogImage l (ind2Act t choice) = profileLogImage l choice := by
  ext z
  constructor <;> rintro ⟨j, rfl⟩ <;> refine ⟨j, ?_⟩
  · exact (profileLogValue_ind2 l t choice j).symm
  · exact profileLogValue_ind2 l t choice j

theorem profileLogImage_ind3_upper (l : PrimeGeFive)
    (n : Nat) (choice : ProcessionChoice l) (z : Real)
    (hz : z ∈ profileLogImage l choice) :
    ∃ w, w ∈ profileLogImage l (ind3Lift n choice) ∧ z ≤ w := by
  rcases hz with ⟨j, rfl⟩
  refine ⟨profileLogValue l (ind3Lift n choice) j, ⟨j, rfl⟩,
    profileLogValue_ind3 l n choice j⟩

def profileLogUpperSemi (l : PrimeGeFive) : UpperSemiCorrespondence Nat Real where
  image n := Set.range (fun j : SignedLabel l.value =>
    Real.log (thetaScale l j) + (n : Real))
  upper := by
    intro m n hmn z hz
    rcases hz with ⟨j, rfl⟩
    refine ⟨Real.log (thetaScale l j) + (n : Real), ⟨j, rfl⟩, ?_⟩
    have hcast : (m : Real) ≤ (n : Real) := by exact_mod_cast hmn
    linarith

theorem profileLogUpperSemi_upper (l : PrimeGeFive)
    {m n : Nat} (hmn : m ≤ n) (z : Real)
    (hz : z ∈ (profileLogUpperSemi l).image m) :
    ∃ w, w ∈ (profileLogUpperSemi l).image n ∧ z ≤ w := by
  exact (profileLogUpperSemi l).upper hmn z hz

/- The first two layers generate exactly equality of the directed level. -/

inductive GeneratedEqualityRelation {l : PrimeGeFive} :
    ProcessionChoice l → ProcessionChoice l → Prop
  | refl (a) : GeneratedEqualityRelation a a
  | ind1 {a b} : Ind1Step a b → GeneratedEqualityRelation a b
  | ind2 {a b} : Ind2Step a b → GeneratedEqualityRelation a b
  | symm {a b} : GeneratedEqualityRelation a b → GeneratedEqualityRelation b a
  | trans {a b c} : GeneratedEqualityRelation a b →
      GeneratedEqualityRelation b c → GeneratedEqualityRelation a c

theorem generatedRelation_level_eq
    {l : PrimeGeFive} {a b : ProcessionChoice l}
    (h : GeneratedEqualityRelation a b) :
    a.upperSemiLevel = b.upperSemiLevel := by
  induction h with
  | refl a => rfl
  | ind1 hstep => rcases hstep with ⟨t, rfl⟩; rfl
  | ind2 hstep => rcases hstep with ⟨t, rfl⟩; rfl
  | symm h ih => exact ih.symm
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂

theorem generatedRelation_of_level_eq
    {l : PrimeGeFive} {a b : ProcessionChoice l}
    (h : a.upperSemiLevel = b.upperSemiLevel) :
    GeneratedEqualityRelation a b := by
  rcases a with ⟨pa, ta, na⟩
  rcases b with ⟨pb, tb, nb⟩
  dsimp at h
  subst nb
  have h₁ : GeneratedEqualityRelation
      (⟨pa, ta, na⟩ : ProcessionChoice l) (⟨0, ta, na⟩ : ProcessionChoice l) :=
    .ind1 ⟨-pa, by simp [ind1Act]⟩
  have h₂ : GeneratedEqualityRelation
      (⟨0, ta, na⟩ : ProcessionChoice l) (⟨0, tb, na⟩ : ProcessionChoice l) :=
    .ind2 ⟨tb - ta, by simp [ind2Act]⟩
  have h₃ : GeneratedEqualityRelation
      (⟨0, tb, na⟩ : ProcessionChoice l) (⟨pb, tb, na⟩ : ProcessionChoice l) :=
    .ind1 ⟨pb, by simp [ind1Act]⟩
  exact .trans h₁ (.trans h₂ h₃)

def generatedSetoid (l : PrimeGeFive) : Setoid (ProcessionChoice l) where
  r := GeneratedEqualityRelation
  iseqv :=
    { refl := GeneratedEqualityRelation.refl
      symm := GeneratedEqualityRelation.symm
      trans := GeneratedEqualityRelation.trans }

abbrev generatedQuotient (l : PrimeGeFive) :=
  Quotient (generatedSetoid l)

def generatedQuotientMap (l : PrimeGeFive) :
    ProcessionChoice l → generatedQuotient l :=
  fun a => (Quotient.mk'' a : generatedQuotient l)

theorem generatedQuotientMap_eq_iff
    {l : PrimeGeFive} {a b : ProcessionChoice l} :
    generatedQuotientMap l a = generatedQuotientMap l b ↔
      GeneratedEqualityRelation a b := by
  change (Quotient.mk'' a : Quotient (generatedSetoid l)) = Quotient.mk'' b ↔
    GeneratedEqualityRelation a b
  exact Quotient.eq''

theorem generatedQuotientMap_level_eq
    {l : PrimeGeFive} {a b : ProcessionChoice l}
    (h : generatedQuotientMap l a = generatedQuotientMap l b) :
    a.upperSemiLevel = b.upperSemiLevel := by
  exact generatedRelation_level_eq (generatedQuotientMap_eq_iff.mp h)

theorem generatedQuotient_no_level_collapse
    {l : PrimeGeFive} {a b : ProcessionChoice l}
    (hlevel : a.upperSemiLevel ≠ b.upperSemiLevel) :
    generatedQuotientMap l a ≠ generatedQuotientMap l b := by
  intro h
  exact hlevel (generatedQuotientMap_level_eq h)

theorem generatedQuotient_same_level
    {l : PrimeGeFive} {a b : ProcessionChoice l}
    (hlevel : a.upperSemiLevel = b.upperSemiLevel) :
    generatedQuotientMap l a = generatedQuotientMap l b := by
  exact generatedQuotientMap_eq_iff.mpr (generatedRelation_of_level_eq hlevel)

theorem profileLogImage_eq_of_level_eq
    {l : PrimeGeFive} {a b : ProcessionChoice l}
    (hlevel : a.upperSemiLevel = b.upperSemiLevel) :
    profileLogImage l a = profileLogImage l b := by
  ext z
  constructor
  · rintro ⟨j, rfl⟩
    let k := SignedLabel.translate l (-b.processionLabel)
      (SignedLabel.translate l a.processionLabel j)
    refine ⟨k, ?_⟩
    simp only [profileLogValue_eq_theta]
    rw [SignedLabel.translate_cancel, hlevel]
  · rintro ⟨j, rfl⟩
    let k := SignedLabel.translate l (-a.processionLabel)
      (SignedLabel.translate l b.processionLabel j)
    refine ⟨k, ?_⟩
    simp only [profileLogValue_eq_theta]
    rw [SignedLabel.translate_cancel, hlevel.symm]

theorem profileLogImage_respects_generated
    {l : PrimeGeFive} {a b : ProcessionChoice l}
    (hab : GeneratedEqualityRelation a b) :
    profileLogImage l a = profileLogImage l b := by
  exact profileLogImage_eq_of_level_eq (generatedRelation_level_eq hab)

def quotientPossibleLogImage (l : PrimeGeFive) :
  generatedQuotient l → Set Real :=
  fun q => Quotient.liftOn' q (profileLogImage l) (fun a b h => by
    exact profileLogImage_respects_generated h)

theorem quotientPossibleLogImage_nonempty (l : PrimeGeFive)
    (q : generatedQuotient l) :
    (quotientPossibleLogImage l q).Nonempty := by
  refine Quotient.inductionOn q ?_
  intro c
  exact profileLogImage_nonempty l c

theorem quotientPossibleLogImage_level_ind3
    {l : PrimeGeFive} (a : ProcessionChoice l) (n : Nat)
    (z : Real) (hz : z ∈ quotientPossibleLogImage l (generatedQuotientMap l a)) :
    ∃ w, w ∈ quotientPossibleLogImage l
      (generatedQuotientMap l (ind3Lift n a)) ∧ z ≤ w := by
  change z ∈ profileLogImage l a at hz
  change ∃ w, w ∈ profileLogImage l (ind3Lift n a) ∧ z ≤ w
  exact profileLogImage_ind3_upper l n a z hz

end ConcreteFiniteTheorem311

end

end LeanFormal.IUT
