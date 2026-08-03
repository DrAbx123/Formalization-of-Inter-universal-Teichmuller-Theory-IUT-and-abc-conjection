import LeanFormal.IUT.IUTII.Frobenioid.PrimeStripArithmetic
import Mathlib.Algebra.Group.TypeTags.Hom
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic

/-!
  A checked arithmetic kernel for the global degree of a finite prime strip.

  The local value objects are ordinary `CommMonoid`s and the local degree is
  an official Mathlib `MonoidHom` into `Multiplicative ℝ`.  The latter is the
  standard type-tag encoding of an additive real-valued degree: multiplication
  of local values becomes addition after `Multiplicative.toAdd`.

  This is the algebraic part of the IUT-I/II prime-strip degree bookkeeping.
  It does not assert that a supplied strip comes from an etale fundamental
  group, a Frobenioid, or an elliptic curve; those source constructions remain
  separate audited obligations.
-/

namespace LeanFormal.IUT

structure PrimeStripDegree (V : Type*) where
  Mon : V → Type*
  [commMonoidMon : ∀ v, CommMonoid (Mon v)]
  degree : ∀ v, Mon v →* Multiplicative Real

attribute [instance] PrimeStripDegree.commMonoidMon

namespace PrimeStripDegree

variable {V : Type*} (S : PrimeStripDegree V)

def localDegree (v : V) (x : S.Mon v) : Real :=
  Multiplicative.toAdd (S.degree v x)

def totalDegree (s : Finset V) (x : ∀ v, S.Mon v) : Real :=
  ∑ v ∈ s, S.localDegree v (x v)

@[simp] theorem localDegree_one (v : V) :
    S.localDegree v 1 = 0 := by
  simp [localDegree]

theorem localDegree_mul (v : V) (x y : S.Mon v) :
    S.localDegree v (x * y) = S.localDegree v x + S.localDegree v y := by
  change Multiplicative.toAdd (S.degree v (x * y)) = _
  rw [(S.degree v).map_mul]
  rfl

theorem totalDegree_mul (s : Finset V) (x y : ∀ v, S.Mon v) :
    S.totalDegree s (fun v => x v * y v) =
      S.totalDegree s x + S.totalDegree s y := by
  unfold totalDegree
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun v hv => S.localDegree_mul v (x v) (y v))

theorem totalDegree_one (s : Finset V) :
    S.totalDegree s (fun _ => 1) = 0 := by
  simp [totalDegree]

end PrimeStripDegree

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def primeStripDegreeKernel : Obligation :=
  { id := "IUT-I-II.prime-strip-degree-kernel"
    source := "IUT I, Sections 5-6; IUT II, Section 4"
    status := VerificationStatus.proved
    note :=
      "Finite global degree is additive under local value multiplication using " ++
        "CommMonoid and MonoidHom; etale/Frobenioid source realization remains pending."
    dependsOn := ["IUT-I-II.prime-strips-frobenioids"] }

end LeanFormal.IUT.Audit
