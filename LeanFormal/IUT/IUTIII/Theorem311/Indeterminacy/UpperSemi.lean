import LeanFormal.IUT.IUTIII.Theorem311.Indeterminacy.OrbitTransport
import Mathlib.Order.Basic

/-!
  An order-theoretic kernel for the Ind3 upper-semi condition.

  A correspondence is set-valued rather than silently single-valued.  Its
  upper-semi law says that every value over a smaller input is dominated by a
  value over a larger input.  This captures the direction of the paper's
  upper-semi compatibility while leaving the actual log-Kummer images as a
  source-facing obligation.
-/

namespace LeanFormal.IUT

universe u v w

structure UpperSemiCorrespondence (α : Type u) (β : Type v)
    [Preorder α] [Preorder β] where
  image : α → Set β
  upper : ∀ {x y : α}, x ≤ y → ∀ z, z ∈ image x →
    ∃ w, w ∈ image y ∧ z ≤ w

namespace UpperSemiCorrespondence

variable {α : Type u} {β : Type v} {γ : Type w}
  [Preorder α] [Preorder β] [Preorder γ]

def singleton (f : α → β) (hf : Monotone f) :
    UpperSemiCorrespondence α β where
  image x := {f x}
  upper := by
    intro x y hxy z hz
    have hz' : z = f x := by simpa using hz
    subst z
    exact ⟨f y, by simp, hf hxy⟩

def comp (g : UpperSemiCorrespondence β γ)
    (f : UpperSemiCorrespondence α β) :
    UpperSemiCorrespondence α γ where
  image x := ⋃ y ∈ f.image x, g.image y
  upper := by
    intro x x' hxx' z hz
    simp only [Set.mem_iUnion] at hz ⊢
    rcases hz with ⟨y, hyf, hzg⟩
    obtain ⟨y', hyf', hyy'⟩ := f.upper hxx' y hyf
    obtain ⟨z', hzg', hzz'⟩ := g.upper hyy' z hzg
    refine ⟨z', ?_, hzz'⟩
    exact ⟨y', hyf', hzg'⟩

theorem upper_of_comp (g : UpperSemiCorrespondence β γ)
    (f : UpperSemiCorrespondence α β) :
    ∀ {x y : α}, x ≤ y → ∀ z, z ∈ (g.comp f).image x →
      ∃ w, w ∈ (g.comp f).image y ∧ z ≤ w := by
  exact (g.comp f).upper

end UpperSemiCorrespondence

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def upperSemiKernel : Obligation :=
  { id := "IUT-III.Ind3.upper-semi-kernel"
    source := "IUT III, Theorem 3.11 (Ind3)"
    status := VerificationStatus.proved
    note :=
      "Set-valued upper-semi correspondences, singleton monotone maps, and " ++
        "composition are proved; the actual log-Kummer image correspondence remains pending."
    dependsOn := ["IUT-III.orbit-quotient-transport", "IUT-II.vertical-log-kummer"] }

end LeanFormal.IUT.Audit
