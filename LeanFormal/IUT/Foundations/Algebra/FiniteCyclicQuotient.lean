/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/

import Mathlib.Data.ZMod.QuotientGroup
import Mathlib.Tactic

/-!
  Polymorphic finite cyclic quotients.

  The source frequently changes the carrier of the integer direction while
  retaining the same finite quotient argument.  The first part is stated for
  an arbitrary additive group.  The second part records the additional
  integer-kernel consequences used by Tate/Kummer packets.
-/

namespace LeanFormal

universe u v

noncomputable section

namespace FiniteCyclicQuotient

variable {A : Type u} [AddCommGroup A]

structure Certificate (n : ℕ) where
  reduction : A →+ ZMod n
  surjective : Function.Surjective reduction

namespace Certificate

variable {n : ℕ} (C : Certificate (A := A) n)

abbrev KernelQuotient := A ⧸ C.reduction.ker

noncomputable def quotientEquiv : KernelQuotient C ≃+ ZMod n :=
  QuotientAddGroup.quotientKerEquivOfSurjective
    C.reduction C.surjective

theorem quotientEquiv_apply_mk (a : A) :
    C.quotientEquiv (QuotientAddGroup.mk a) = C.reduction a := by
  change (QuotientAddGroup.kerLift C.reduction) a = C.reduction a
  exact QuotientAddGroup.kerLift_mk C.reduction a

theorem quotientEquiv_zero :
    C.quotientEquiv (0 : KernelQuotient C) = 0 :=
  map_zero C.quotientEquiv

theorem quotientEquiv_add (x y : KernelQuotient C) :
    C.quotientEquiv (x + y) = C.quotientEquiv x + C.quotientEquiv y :=
  map_add C.quotientEquiv x y

theorem quotientEquiv_neg (x : KernelQuotient C) :
    C.quotientEquiv (-x) = -C.quotientEquiv x :=
  map_neg C.quotientEquiv x

theorem quotientEquiv_sub (x y : KernelQuotient C) :
    C.quotientEquiv (x - y) = C.quotientEquiv x - C.quotientEquiv y := by
  exact map_sub C.quotientEquiv x y

theorem quotientEquiv_zsmul (k : ℤ) (x : KernelQuotient C) :
    C.quotientEquiv (k • x) = k • C.quotientEquiv x := by
  exact map_zsmul C.quotientEquiv k x

theorem quotientEquiv_surjective :
    Function.Surjective C.quotientEquiv :=
  C.quotientEquiv.surjective

theorem quotientEquiv_injective :
    Function.Injective C.quotientEquiv :=
  C.quotientEquiv.injective

theorem quotient_mk_surjective :
    Function.Surjective (fun a : A =>
      (QuotientAddGroup.mk a : KernelQuotient C)) :=
  QuotientAddGroup.mk_surjective

theorem quotient_eq_iff (a b : A) :
    (QuotientAddGroup.mk a : KernelQuotient C) = QuotientAddGroup.mk b ↔
      a - b ∈ C.reduction.ker := by
  exact QuotientAddGroup.eq_iff_sub_mem

theorem quotient_mk_eq_iff_reduction_eq (a b : A) :
    (QuotientAddGroup.mk a : KernelQuotient C) = QuotientAddGroup.mk b ↔
      C.reduction a = C.reduction b := by
  constructor
  · intro h
    simpa [C.quotientEquiv_apply_mk] using
      congrArg C.quotientEquiv h
  · intro h
    apply C.quotientEquiv_injective
    simpa [C.quotientEquiv_apply_mk] using h

theorem quotient_mk_zero_iff_mem_kernel (a : A) :
    (QuotientAddGroup.mk a : KernelQuotient C) = 0 ↔
      a ∈ C.reduction.ker := by
  change (QuotientAddGroup.mk a : KernelQuotient C) =
    QuotientAddGroup.mk (0 : A) ↔ _
  simpa only [sub_zero] using C.quotient_eq_iff a 0

theorem quotient_mk_add_kernel (a k : A)
    (hk : k ∈ C.reduction.ker) :
    (QuotientAddGroup.mk (a + k) : KernelQuotient C) =
      QuotientAddGroup.mk a := by
  apply (C.quotient_eq_iff _ _).mpr
  simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hk

theorem reduction_add_kernel (a k : A)
    (hk : k ∈ C.reduction.ker) :
    C.reduction (a + k) = C.reduction a := by
  rw [map_add]
  change C.reduction k = 0 at hk
  simp [hk]

theorem quotient_mk_sub_kernel (a k : A)
    (hk : k ∈ C.reduction.ker) :
    (QuotientAddGroup.mk (a - k) : KernelQuotient C) =
      QuotientAddGroup.mk a := by
  apply (C.quotient_eq_iff _ _).mpr
  simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hk

theorem reduction_sub_kernel (a k : A)
    (hk : k ∈ C.reduction.ker) :
    C.reduction (a - k) = C.reduction a := by
  rw [map_sub]
  change C.reduction k = 0 at hk
  simp [hk]

theorem quotient_mk_zsmul (k : ℤ) (a : A) :
    (QuotientAddGroup.mk (k • a) : KernelQuotient C) =
      k • QuotientAddGroup.mk a := rfl

theorem reduction_zsmul (k : ℤ) (a : A) :
    C.reduction (k • a) = k • C.reduction a :=
  map_zsmul C.reduction k a

end Certificate

/- An integer packet remembers the exact arithmetic shape of the kernel. -/
structure IntegerCertificate (n : ℕ) where
  reduction : ℤ →+ ZMod n
  surjective : Function.Surjective reduction
  kernel_eq : reduction.ker = AddSubgroup.zmultiples (n : ℤ)

namespace IntegerCertificate

variable {n : ℕ} (C : IntegerCertificate n)

abbrev KernelQuotient := ℤ ⧸ C.reduction.ker

noncomputable def asCertificate :
    FiniteCyclicQuotient.Certificate (A := ℤ) n where
  reduction := C.reduction
  surjective := C.surjective

noncomputable def quotientEquiv : KernelQuotient C ≃+ ZMod n :=
  C.asCertificate.quotientEquiv

theorem quotientEquiv_apply_mk (a : ℤ) :
    C.quotientEquiv (QuotientAddGroup.mk a) = C.reduction a :=
  C.asCertificate.quotientEquiv_apply_mk a

theorem quotientEquiv_surjective :
    Function.Surjective C.quotientEquiv :=
  C.quotientEquiv.surjective

theorem quotientEquiv_injective :
    Function.Injective C.quotientEquiv :=
  C.quotientEquiv.injective

theorem quotient_eq_iff_multiple (a b : ℤ) :
    (QuotientAddGroup.mk a : KernelQuotient C) = QuotientAddGroup.mk b ↔
      a - b ∈ AddSubgroup.zmultiples (n : ℤ) := by
  rw [← C.kernel_eq]
  exact C.asCertificate.quotient_eq_iff a b

theorem quotient_mk_zero_iff_multiple (a : ℤ) :
    (QuotientAddGroup.mk a : KernelQuotient C) = 0 ↔
      a ∈ AddSubgroup.zmultiples (n : ℤ) := by
  simpa using C.quotient_eq_iff_multiple a 0

theorem quotient_mk_add_multiple (a k : ℤ) :
    (QuotientAddGroup.mk (a + (n : ℤ) * k) : KernelQuotient C) =
      QuotientAddGroup.mk a := by
  apply (C.quotient_eq_iff_multiple _ _).mpr
  apply AddSubgroup.mem_zmultiples_iff.mpr
  refine ⟨k, ?_⟩
  ring

theorem quotient_mk_sub_multiple (a k : ℤ) :
    (QuotientAddGroup.mk (a - (n : ℤ) * k) : KernelQuotient C) =
      QuotientAddGroup.mk a := by
  apply (C.quotient_eq_iff_multiple _ _).mpr
  apply AddSubgroup.mem_zmultiples_iff.mpr
  refine ⟨-k, ?_⟩
  ring

theorem reduction_add_multiple (a k : ℤ) :
    C.reduction (a + (n : ℤ) * k) = C.reduction a := by
  have h := (C.asCertificate.quotient_mk_eq_iff_reduction_eq a
    (a + (n : ℤ) * k)).mp (C.quotient_mk_add_multiple a k).symm
  exact h.symm

theorem reduction_sub_multiple (a k : ℤ) :
    C.reduction (a - (n : ℤ) * k) = C.reduction a := by
  have h := (C.asCertificate.quotient_mk_eq_iff_reduction_eq a
    (a - (n : ℤ) * k)).mp (C.quotient_mk_sub_multiple a k).symm
  exact h.symm

theorem reduction_eq_iff_multiple (a b : ℤ) :
    C.reduction a = C.reduction b ↔
      a - b ∈ AddSubgroup.zmultiples (n : ℤ) := by
  constructor
  · intro h
    exact C.quotient_eq_iff_multiple a b |>.mp
      ((C.asCertificate.quotient_mk_eq_iff_reduction_eq a b).mpr h)
  · intro h
    exact (C.asCertificate.quotient_mk_eq_iff_reduction_eq a b).mp
      ((C.quotient_eq_iff_multiple a b).mpr h)

theorem multiple_mem_kernel (k : ℤ) :
    (n : ℤ) * k ∈ C.reduction.ker := by
  rw [C.kernel_eq]
  exact AddSubgroup.mem_zmultiples_iff.mpr ⟨k, by ring⟩

theorem reduction_periodic (a k : ℤ) :
    C.reduction (a + (n : ℤ) * k) = C.reduction a :=
  C.reduction_add_multiple a k

theorem reduction_periodic_sub (a k : ℤ) :
    C.reduction (a - (n : ℤ) * k) = C.reduction a :=
  C.reduction_sub_multiple a k

theorem zero_label_iff (a : ℤ) :
    C.reduction a = 0 ↔ a ∈ AddSubgroup.zmultiples (n : ℤ) := by
  constructor
  · intro h
    have : (QuotientAddGroup.mk a : KernelQuotient C) = 0 := by
      apply C.quotientEquiv_injective
      simpa [C.quotientEquiv_apply_mk] using h
    exact C.quotient_mk_zero_iff_multiple a |>.mp this
  · intro h
    have : (QuotientAddGroup.mk a : KernelQuotient C) = 0 :=
      C.quotient_mk_zero_iff_multiple a |>.mpr h
    have h' := congrArg C.quotientEquiv this
    simpa [C.quotientEquiv_apply_mk] using h'

end IntegerCertificate

end FiniteCyclicQuotient

end

end LeanFormal
