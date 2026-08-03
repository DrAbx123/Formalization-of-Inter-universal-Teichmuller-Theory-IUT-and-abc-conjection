import LeanFormal.IUT.IUTIII.Theorem311.Indeterminacy.QuotientTransport
import Mathlib.GroupTheory.GroupAction.Quotient

/-!
  The official group-action quotient kernel for Ind1/Ind2-style links.

  An equivariant map sends orbits to orbits, hence descends through the
  Mathlib orbit quotient.  The construction is deliberately independent of
  any IUT-specific Galois group or Kummer shell; those data are supplied only
  by the pending source obligations.
-/

namespace LeanFormal.IUT

universe u₀ u₁ u₂ u₃

structure OrbitCompatibleMap {G : Type u₀} {H : Type u₁}
    {α : Type u₂} {β : Type u₃}
    [Group G] [Group H] [MulAction G α] [MulAction H β] where
  groupMap : G →* H
  map : α → β
  equivariant : ∀ g x, map (g • x) = groupMap g • map x

namespace OrbitCompatibleMap

variable {G : Type u₀} {H : Type u₁} {α : Type u₂} {β : Type u₃}
  [Group G] [Group H] [MulAction G α] [MulAction H β]
  (f : OrbitCompatibleMap (G := G) (H := H) (α := α) (β := β))

theorem respects_orbit {x y : α}
    (hxy : MulAction.orbitRel G α x y) :
    MulAction.orbitRel H β (f.map x) (f.map y) := by
  change x ∈ MulAction.orbit G y at hxy
  change f.map x ∈ MulAction.orbit H (f.map y)
  rcases MulAction.mem_orbit_iff.mp hxy with ⟨g, hg⟩
  apply MulAction.mem_orbit_iff.mpr
  refine ⟨f.groupMap g, ?_⟩
  rw [← f.equivariant, hg]

def quotientMap :
    Quotient (MulAction.orbitRel G α) →
      Quotient (MulAction.orbitRel H β) :=
   Quotient.map' f.map (fun _x _y hxy => f.respects_orbit hxy)

@[simp] theorem quotientMap_mk (x : α) :
    f.quotientMap (Quotient.mk'' x) =
      (Quotient.mk'' (f.map x) : Quotient (MulAction.orbitRel H β)) := by
  exact Quotient.map'_mk'' f.map (fun a b hab => f.respects_orbit hab) x

end OrbitCompatibleMap

structure ThreeLayerOrbitChain
    {G₀ : Type u₀} {G₁ : Type u₁} {G₂ : Type u₂} {G₃ : Type u₃}
    {α₀ : Type u₀} {α₁ : Type u₁} {α₂ : Type u₂} {α₃ : Type u₃}
    [Group G₀] [Group G₁] [Group G₂] [Group G₃]
    [MulAction G₀ α₀] [MulAction G₁ α₁]
    [MulAction G₂ α₂] [MulAction G₃ α₃] where
  ind1 : OrbitCompatibleMap (G := G₀) (H := G₁) (α := α₀) (β := α₁)
  ind2 : OrbitCompatibleMap (G := G₁) (H := G₂) (α := α₁) (β := α₂)
  ind3 : OrbitCompatibleMap (G := G₂) (H := G₃) (α := α₂) (β := α₃)

namespace ThreeLayerOrbitChain

variable {G₀ : Type u₀} {G₁ : Type u₁} {G₂ : Type u₂} {G₃ : Type u₃}
  {α₀ : Type u₀} {α₁ : Type u₁} {α₂ : Type u₂} {α₃ : Type u₃}
  [Group G₀] [Group G₁] [Group G₂] [Group G₃]
  [MulAction G₀ α₀] [MulAction G₁ α₁]
  [MulAction G₂ α₂] [MulAction G₃ α₃]
  (c : ThreeLayerOrbitChain (G₀ := G₀) (G₁ := G₁) (G₂ := G₂) (G₃ := G₃)
    (α₀ := α₀) (α₁ := α₁) (α₂ := α₂) (α₃ := α₃))

def transport :
    Quotient (MulAction.orbitRel G₀ α₀) →
      Quotient (MulAction.orbitRel G₃ α₃) :=
  OrbitCompatibleMap.quotientMap c.ind3 ∘
    OrbitCompatibleMap.quotientMap c.ind2 ∘
      OrbitCompatibleMap.quotientMap c.ind1

theorem transport_mk (x : α₀) :
    c.transport (Quotient.mk'' x) =
      (Quotient.mk'' (c.ind3.map (c.ind2.map (c.ind1.map x))) :
        Quotient (MulAction.orbitRel G₃ α₃)) := by
  simp [transport, OrbitCompatibleMap.quotientMap]

end ThreeLayerOrbitChain

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def orbitTransportKernel : Obligation :=
  { id := "IUT-III.orbit-quotient-transport"
    source := "IUT III, Theorem 3.11 (Ind1--Ind2 mechanism)"
    status := VerificationStatus.proved
    note :=
      "Equivariant maps descend through official Mathlib orbit quotients; the " ++
        "IUT-specific groups, shells, and links remain pending."
    dependsOn := ["IUT-III.generic-quotient-transport", "IUT-I-II.prime-strip-core"] }

end LeanFormal.IUT.Audit
