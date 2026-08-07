/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/

import LeanFormal.IUT.Foundations.Algebra.FiniteCyclicQuotient

/-!
  Transport of a finite reduction quotient through a commuting square.

  This is the finite-level analogue of cyclic deck transport.  The square
  explicitly records both the carrier equivalence and the label equivalence,
  so the induced quotient map cannot silently identify unrelated reductions.
-/

namespace LeanFormal

universe u v

noncomputable section

namespace FiniteCyclicQuotientTransport

variable {A : Type u} [AddCommGroup A]
variable {B : Type v} [AddCommGroup B]

structure Square (n m : ℕ) where
  source : FiniteCyclicQuotient.Certificate (A := A) n
  target : FiniteCyclicQuotient.Certificate (A := B) m
  carrierEquiv : A ≃+ B
  labelEquiv : ZMod n ≃+ ZMod m
  commutes : ∀ a : A,
    labelEquiv (source.reduction a) =
      target.reduction (carrierEquiv a)

namespace Square

variable {n m : ℕ} (S : Square (A := A) (B := B) n m)

abbrev SourceQuotient := S.source.KernelQuotient
abbrev TargetQuotient := S.target.KernelQuotient

noncomputable def quotientEquiv : S.SourceQuotient ≃+ S.TargetQuotient :=
  S.source.quotientEquiv.trans
    (S.labelEquiv.trans S.target.quotientEquiv.symm)

theorem quotientEquiv_zero :
    S.quotientEquiv 0 = 0 :=
  map_zero S.quotientEquiv

theorem quotientEquiv_add (x y : S.SourceQuotient) :
    S.quotientEquiv (x + y) = S.quotientEquiv x + S.quotientEquiv y :=
  map_add S.quotientEquiv x y

theorem quotientEquiv_neg (x : S.SourceQuotient) :
    S.quotientEquiv (-x) = -S.quotientEquiv x :=
  map_neg S.quotientEquiv x

theorem quotientEquiv_zsmul (k : ℤ) (x : S.SourceQuotient) :
    S.quotientEquiv (k • x) = k • S.quotientEquiv x := by
  exact map_zsmul S.quotientEquiv k x

theorem quotientEquiv_apply_mk (a : A) :
    S.quotientEquiv (QuotientAddGroup.mk a) =
      QuotientAddGroup.mk (S.carrierEquiv a) := by
  apply S.target.quotientEquiv.injective
  rw [S.target.quotientEquiv_apply_mk]
  simp [quotientEquiv, S.source.quotientEquiv_apply_mk,
    S.commutes]

theorem quotientEquiv_apply_mk_reduction (a : A) :
    S.target.quotientEquiv
      (S.quotientEquiv (QuotientAddGroup.mk a)) =
      S.target.reduction (S.carrierEquiv a) := by
  rw [S.quotientEquiv_apply_mk,
    S.target.quotientEquiv_apply_mk]

theorem quotientEquiv_surjective :
    Function.Surjective S.quotientEquiv :=
  S.quotientEquiv.surjective

theorem quotientEquiv_injective :
    Function.Injective S.quotientEquiv :=
  S.quotientEquiv.injective

theorem quotientEquiv_preserves_eq
    (x y : S.SourceQuotient)
    (h : x = y) : S.quotientEquiv x = S.quotientEquiv y :=
  congrArg S.quotientEquiv h

theorem quotientEquiv_reflects_eq
    (x y : S.SourceQuotient)
    (h : S.quotientEquiv x = S.quotientEquiv y) : x = y :=
  S.quotientEquiv.injective h

theorem quotientEquiv_reduction_square (a : A) :
    S.labelEquiv (S.source.reduction a) =
      S.target.reduction (S.carrierEquiv a) :=
  S.commutes a

theorem quotientEquiv_source_label (a : A) :
    S.quotientEquiv (QuotientAddGroup.mk a) =
      QuotientAddGroup.mk (S.carrierEquiv a) :=
  S.quotientEquiv_apply_mk a

theorem quotientEquiv_mk_add (a b : A) :
    S.quotientEquiv (QuotientAddGroup.mk (a + b)) =
      QuotientAddGroup.mk (S.carrierEquiv a + S.carrierEquiv b) := by
  rw [S.quotientEquiv_apply_mk, map_add]

theorem quotientEquiv_mk_neg (a : A) :
    S.quotientEquiv (QuotientAddGroup.mk (-a)) =
      QuotientAddGroup.mk (-S.carrierEquiv a) := by
  rw [S.quotientEquiv_apply_mk, map_neg]

theorem quotientEquiv_mk_zsmul (k : ℤ) (a : A) :
    S.quotientEquiv (QuotientAddGroup.mk (k • a)) =
      QuotientAddGroup.mk (k • S.carrierEquiv a) := by
  rw [S.quotientEquiv_apply_mk, map_zsmul]

theorem quotientEquiv_label_compatibility (a : A) :
    S.labelEquiv (S.source.quotientEquiv
      (QuotientAddGroup.mk a)) =
      S.target.quotientEquiv
        (QuotientAddGroup.mk (S.carrierEquiv a)) := by
  rw [S.source.quotientEquiv_apply_mk,
    S.target.quotientEquiv_apply_mk]
  exact S.commutes a

theorem quotientEquiv_kernel_class (a : A)
    (ha : a ∈ S.source.reduction.ker) :
    S.quotientEquiv (QuotientAddGroup.mk a) = 0 := by
  rw [S.quotientEquiv_apply_mk]
  apply (S.target.quotient_mk_zero_iff_mem_kernel
    (S.carrierEquiv a)).mpr
  have hz := S.commutes a
  have ha0 : S.source.reduction a = 0 := ha
  rw [ha0] at hz
  simpa using hz.symm

theorem quotientEquiv_inverse (a : A) :
    (S.quotientEquiv).symm (QuotientAddGroup.mk
      (S.carrierEquiv a)) = QuotientAddGroup.mk a := by
  apply S.quotientEquiv.injective
  rw [S.quotientEquiv.apply_symm_apply, S.quotientEquiv_apply_mk]

end Square

end FiniteCyclicQuotientTransport

end

end LeanFormal
