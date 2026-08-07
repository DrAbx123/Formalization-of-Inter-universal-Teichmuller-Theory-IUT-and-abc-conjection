import LeanFormal.IUT.Foundations.Theta.GaussianKernel
import LeanFormal.IUT.Foundations.Arithmetic.PrimeLabels
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace LeanFormal.IUT

noncomputable section

namespace SignedLabel

def toFiniteLabel (l : PrimeGeFive) : SignedLabel l.value → Fl l.value :=
  fun j => SignedLabel.toFl l.value j

theorem toFiniteLabel_apply (l : PrimeGeFive) (j : SignedLabel l.value) :
    toFiniteLabel l j = (j.1 : Fl l.value) :=
  rfl

theorem toFiniteLabel_neg (l : PrimeGeFive) (j : SignedLabel l.value) :
    toFiniteLabel l (SignedLabel.neg j) = -toFiniteLabel l j := by
  exact SignedLabel.toFl_neg j

theorem abs_sub_lt_label (l : PrimeGeFive)
    (a b : SignedLabel l.value) :
    |b.1 - a.1| < (l.value : ℤ) := by
  rw [abs_lt]
  constructor
  · have ha := a.2.2
    have hb := b.2.1
    have hstar := two_mul_lStar_add_one l.value l.odd
    omega
  · have ha := a.2.1
    have hb := b.2.2
    have hstar := two_mul_lStar_add_one l.value l.odd
    omega

theorem toFiniteLabel_injective (l : PrimeGeFive) :
    Function.Injective (toFiniteLabel l) := by
  intro a b hab
  change (a.1 : Fl l.value) = (b.1 : Fl l.value) at hab
  have hdvd : (l.value : ℤ) ∣ b.1 - a.1 := by
    exact (ZMod.intCast_eq_intCast_iff_dvd_sub a.1 b.1 l.value).mp hab
  have hzero : b.1 - a.1 = 0 :=
    Int.eq_zero_of_abs_lt_dvd hdvd (abs_sub_lt_label l a b)
  apply Subtype.ext
  omega

def representative (l : PrimeGeFive) (x : Fl l.value) : SignedLabel l.value := by
  have hval : (x.val : ℤ) < (l.value : ℤ) := by
    exact_mod_cast x.val_lt
  have hstar : 2 * lStar l.value + 1 = l.value :=
    two_mul_lStar_add_one l.value l.odd
  by_cases h : x.val ≤ lStar l.value
  · exact ⟨x.val, by
      constructor
      · omega
      · omega⟩
  · exact ⟨(x.val : ℤ) - (l.value : ℤ), by
      constructor
      · have hlow : lStar l.value + 1 ≤ x.val := by omega
        omega
      · omega⟩

theorem representative_toFl (l : PrimeGeFive) (x : Fl l.value) :
    toFiniteLabel l (representative l x) = x := by
  have hval : (x.val : ℤ) < (l.value : ℤ) := by
    exact_mod_cast x.val_lt
  by_cases h : x.val ≤ lStar l.value
  · simp only [representative, dif_pos h, toFiniteLabel, SignedLabel.toFl]
    simpa only [Int.cast_natCast] using ZMod.natCast_zmod_val x
  · simp only [representative, dif_neg h, toFiniteLabel, SignedLabel.toFl]
    rw [Int.cast_sub, Int.cast_natCast, ZMod.natCast_zmod_val]
    simp

def equiv (l : PrimeGeFive) : SignedLabel l.value ≃ Fl l.value where
  toFun := toFiniteLabel l
  invFun := representative l
  left_inv := by
    intro j
    apply toFiniteLabel_injective l
    exact representative_toFl l (toFiniteLabel l j)
  right_inv := representative_toFl l

@[simp] theorem equiv_apply (l : PrimeGeFive) (j : SignedLabel l.value) :
    equiv l j = toFiniteLabel l j :=
  rfl

@[simp] theorem equiv_symm_apply (l : PrimeGeFive) (x : Fl l.value) :
    (equiv l).symm x = representative l x :=
  rfl

theorem equiv_injective (l : PrimeGeFive) :
    Function.Injective (equiv l) :=
  (equiv l).injective

theorem equiv_surjective (l : PrimeGeFive) :
    Function.Surjective (equiv l) :=
  (equiv l).surjective

def translate (l : PrimeGeFive) (t : Fl l.value) :
    SignedLabel l.value ≃ SignedLabel l.value :=
  (equiv l).trans ((Equiv.addLeft t).trans (equiv l).symm)

@[simp] theorem translate_apply (l : PrimeGeFive) (t : Fl l.value)
    (j : SignedLabel l.value) :
    translate l t j = (equiv l).symm (t + equiv l j) :=
  by simp [translate]

@[simp] theorem translate_zero (l : PrimeGeFive) (j : SignedLabel l.value) :
    translate l 0 j = j := by
  apply toFiniteLabel_injective l
  simp [translate, representative_toFl]

theorem translate_add (l : PrimeGeFive) (s t : Fl l.value)
    (j : SignedLabel l.value) :
    translate l (s + t) j = translate l s (translate l t j) := by
  apply toFiniteLabel_injective l
  simp [translate, representative_toFl]

theorem translate_inverse (l : PrimeGeFive) (t : Fl l.value)
    (j : SignedLabel l.value) :
    translate l (-t) (translate l t j) = j := by
  apply toFiniteLabel_injective l
  simp [translate, representative_toFl]

theorem translate_cancel (l : PrimeGeFive) (t : Fl l.value)
    (j : SignedLabel l.value) :
    translate l t (translate l (-t) j) = j := by
  apply toFiniteLabel_injective l
  simp [translate, representative_toFl]

theorem translate_neg (l : PrimeGeFive) (t : Fl l.value)
    (j : SignedLabel l.value) :
    equiv l (translate l t j) = t + equiv l j := by
  simp [translate, representative_toFl]

theorem translate_bijective (l : PrimeGeFive) (t : Fl l.value) :
    Function.Bijective (translate l t) :=
  (translate l t).bijective

theorem card_signedLabel (l : PrimeGeFive) :
    Fintype.card (SignedLabel l.value) = l.value := by
  calc
    Fintype.card (SignedLabel l.value) = Fintype.card (Fl l.value) :=
      Fintype.card_congr (equiv l)
    _ = l.value := ZMod.card l.value

theorem card_signedLabel_eq_card_fl (l : PrimeGeFive) :
    Fintype.card (SignedLabel l.value) = Fintype.card (Fl l.value) := by
  exact Fintype.card_congr (equiv l)

theorem sum_translate (l : PrimeGeFive) (t : Fl l.value)
    (f : SignedLabel l.value → Real) :
    ∑ j, f (translate l t j) = ∑ j, f j := by
  exact (translate l t).sum_comp f

theorem prod_translate (l : PrimeGeFive) (t : Fl l.value)
    (f : SignedLabel l.value → Real) :
    ∏ j, f (translate l t j) = ∏ j, f j := by
  exact (translate l t).prod_comp f

theorem sum_translate_eq_sum_of_comp (l : PrimeGeFive) (t : Fl l.value)
    (f : SignedLabel l.value → Real) :
    ∑ j, f ((equiv l).symm (t + equiv l j)) = ∑ j, f j := by
  simpa [translate] using sum_translate l t f

theorem prod_translate_eq_prod_of_comp (l : PrimeGeFive) (t : Fl l.value)
    (f : SignedLabel l.value → Real) :
    ∏ j, f ((equiv l).symm (t + equiv l j)) = ∏ j, f j := by
  simpa [translate] using prod_translate l t f

theorem neg_translate_equiv (l : PrimeGeFive) (t : Fl l.value)
    (j : SignedLabel l.value) :
    SignedLabel.neg (translate l t j) =
      translate l (-t) (SignedLabel.neg j) := by
  apply toFiniteLabel_injective l
  rw [toFiniteLabel_neg]
  simp [translate, representative_toFl, toFiniteLabel_neg]
  abel

end SignedLabel

end

end LeanFormal.IUT
