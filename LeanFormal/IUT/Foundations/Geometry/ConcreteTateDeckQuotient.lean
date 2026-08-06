/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/

import LeanFormal.IUT.Foundations.Geometry.ConcreteTateParameter
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
  The local algebraic deck quotient for the actual q=p parameter.

  This module supplies the exact group-theoretic object appearing in a Tate
  uniformization statement.  It proves Galois invariance and descent of the
  action, but deliberately does not identify the quotient with points on an
  elliptic curve.
-/

namespace LeanFormal.IUT

noncomputable section

namespace ConcreteTateParameter

variable {l : PrimeGeFive} [Fact (Nat.Prime l.value)]

abbrev LocalAbsoluteGalois (l : PrimeGeFive)
    [Fact (Nat.Prime l.value)] : Type :=
  AlgebraicClosure ℚ_[l.value] ≃ₐ[ℚ_[l.value]]
    AlgebraicClosure ℚ_[l.value]

def unitsGaloisEquiv
    (_P : ConcreteTateParameter l) (sigma : LocalAbsoluteGalois l) :
    (AlgebraicClosure ℚ_[l.value])ˣ ≃*
      (AlgebraicClosure ℚ_[l.value])ˣ where
  toFun := Units.map sigma.toRingEquiv.toMonoidHom
  invFun := Units.map sigma.symm.toRingEquiv.toMonoidHom
  left_inv := by
    intro x
    apply Units.ext
    simp
  right_inv := by
    intro x
    apply Units.ext
    simp
  map_mul' := by
    intro x y
    simp

theorem unitsGaloisEquiv_apply
    (P : ConcreteTateParameter l) (sigma : LocalAbsoluteGalois l)
    (x : (AlgebraicClosure ℚ_[l.value])ˣ) :
    P.unitsGaloisEquiv sigma x =
      Units.map sigma.toRingEquiv.toMonoidHom x :=
  rfl

theorem unitsGaloisEquiv_qUnit
    (P : ConcreteTateParameter l) (sigma : LocalAbsoluteGalois l) :
    P.unitsGaloisEquiv sigma P.qUnit = P.qUnit := by
  apply Units.ext
  simp [unitsGaloisEquiv, qUnit]

theorem unitsGaloisEquiv_refl
    (P : ConcreteTateParameter l) :
    P.unitsGaloisEquiv
        (AlgEquiv.refl : LocalAbsoluteGalois l) = MulEquiv.refl _ := by
  apply MulEquiv.ext
  intro x
  apply Units.ext
  rfl

theorem unitsGaloisEquiv_trans
    (P : ConcreteTateParameter l)
    (sigma tau : LocalAbsoluteGalois l) :
    P.unitsGaloisEquiv (sigma.trans tau) =
      (P.unitsGaloisEquiv sigma).trans (P.unitsGaloisEquiv tau) := by
  apply MulEquiv.ext
  intro x
  apply Units.ext
  rfl

def qDeckSubgroup (P : ConcreteTateParameter l) :
    Subgroup (AlgebraicClosure ℚ_[l.value])ˣ :=
  Subgroup.zpowers P.qUnit

theorem qDeckSubgroup_map
    (P : ConcreteTateParameter l) (sigma : LocalAbsoluteGalois l) :
    Subgroup.map (P.unitsGaloisEquiv sigma).toMonoidHom P.qDeckSubgroup =
      P.qDeckSubgroup := by
  change Subgroup.map (P.unitsGaloisEquiv sigma).toMonoidHom
      (Subgroup.zpowers P.qUnit) = Subgroup.zpowers P.qUnit
  rw [MonoidHom.map_zpowers]
  change Subgroup.zpowers (P.unitsGaloisEquiv sigma P.qUnit) =
    Subgroup.zpowers P.qUnit
  rw [P.unitsGaloisEquiv_qUnit sigma]

def qDeckQuotientEquiv
    (P : ConcreteTateParameter l) (sigma : LocalAbsoluteGalois l) :
    (AlgebraicClosure ℚ_[l.value])ˣ ⧸ P.qDeckSubgroup ≃*
      (AlgebraicClosure ℚ_[l.value])ˣ ⧸ P.qDeckSubgroup := by
  apply QuotientGroup.congr P.qDeckSubgroup P.qDeckSubgroup
    (P.unitsGaloisEquiv sigma)
  exact P.qDeckSubgroup_map sigma

@[simp] theorem qDeckQuotientEquiv_mk
    (P : ConcreteTateParameter l) (sigma : LocalAbsoluteGalois l)
    (x : (AlgebraicClosure ℚ_[l.value])ˣ) :
    P.qDeckQuotientEquiv sigma (QuotientGroup.mk x) =
      QuotientGroup.mk (P.unitsGaloisEquiv sigma x) := by
  apply QuotientGroup.congr_mk

theorem qDeckQuotientEquiv_refl
    (P : ConcreteTateParameter l) :
    P.qDeckQuotientEquiv
        (AlgEquiv.refl : LocalAbsoluteGalois l) =
      MulEquiv.refl _ := by
  apply MulEquiv.ext
  intro x
  induction x using QuotientGroup.induction_on with
  | _ x =>
    simp [qDeckQuotientEquiv, unitsGaloisEquiv_refl]

theorem qDeckQuotientEquiv_trans
    (P : ConcreteTateParameter l)
    (sigma tau : LocalAbsoluteGalois l) :
    P.qDeckQuotientEquiv (sigma.trans tau) =
      (P.qDeckQuotientEquiv sigma).trans
        (P.qDeckQuotientEquiv tau) := by
  apply MulEquiv.ext
  intro x
  induction x using QuotientGroup.induction_on with
  | _ x =>
    simp [qDeckQuotientEquiv, unitsGaloisEquiv_trans]

theorem qDeckQuotientEquiv_preserves_power_class
    (P : ConcreteTateParameter l) (sigma : LocalAbsoluteGalois l)
    (x : (AlgebraicClosure ℚ_[l.value])ˣ) (n : ℤ) :
    P.qDeckQuotientEquiv sigma
        (QuotientGroup.mk (x ^ n)) =
      QuotientGroup.mk ((P.unitsGaloisEquiv sigma x) ^ n) := by
  rw [qDeckQuotientEquiv_mk]
  simp

theorem qDeckQuotientEquiv_qUnit_class
    (P : ConcreteTateParameter l) (sigma : LocalAbsoluteGalois l) :
    P.qDeckQuotientEquiv sigma
        (QuotientGroup.mk P.qUnit) =
      QuotientGroup.mk P.qUnit := by
  rw [qDeckQuotientEquiv_mk, P.unitsGaloisEquiv_qUnit]

theorem qDeckSubgroup_mem_iff
    (P : ConcreteTateParameter l)
    (x : (AlgebraicClosure ℚ_[l.value])ˣ) :
    x ∈ P.qDeckSubgroup ↔
      ∃ n : ℤ, x = P.qUnit ^ n := by
  rw [qDeckSubgroup]
  constructor
  · intro h
    rcases Subgroup.mem_zpowers_iff.mp h with ⟨n, hn⟩
    exact ⟨n, hn.symm⟩
  · rintro ⟨n, rfl⟩
    exact Subgroup.mem_zpowers_iff.mpr ⟨n, rfl⟩

theorem qDeckQuotient_eq_iff
    (P : ConcreteTateParameter l)
    (x y : (AlgebraicClosure ℚ_[l.value])ˣ) :
    (QuotientGroup.mk x :
      (AlgebraicClosure ℚ_[l.value])ˣ ⧸ P.qDeckSubgroup) =
        QuotientGroup.mk y ↔
      x / y ∈ P.qDeckSubgroup := by
  exact QuotientGroup.eq_iff_div_mem

theorem qDeckQuotient_eq_iff_power_ratio
    (P : ConcreteTateParameter l)
    (x y : (AlgebraicClosure ℚ_[l.value])ˣ) :
    (QuotientGroup.mk x :
      (AlgebraicClosure ℚ_[l.value])ˣ ⧸ P.qDeckSubgroup) =
        QuotientGroup.mk y ↔
      ∃ n : ℤ, x / y = P.qUnit ^ n := by
  rw [qDeckQuotient_eq_iff P x y,
    qDeckSubgroup_mem_iff P (x / y)]

theorem qDeckQuotient_mk_mul_qUnit
    (P : ConcreteTateParameter l)
    (x : (AlgebraicClosure ℚ_[l.value])ˣ) (n : ℤ) :
    (QuotientGroup.mk (x * P.qUnit ^ n) :
      (AlgebraicClosure ℚ_[l.value])ˣ ⧸ P.qDeckSubgroup) =
        QuotientGroup.mk x := by
  apply (qDeckQuotient_eq_iff P (x * P.qUnit ^ n) x).mpr
  simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using
    (qDeckSubgroup_mem_iff P (P.qUnit ^ n)).mpr ⟨n, rfl⟩

theorem qDeckQuotient_mk_inv
    (P : ConcreteTateParameter l)
    (x : (AlgebraicClosure ℚ_[l.value])ˣ) :
    (QuotientGroup.mk x⁻¹ :
      (AlgebraicClosure ℚ_[l.value])ˣ ⧸ P.qDeckSubgroup) =
        (QuotientGroup.mk x)⁻¹ := by
  rfl

theorem qDeckQuotient_equiv_preserves_eq
    (P : ConcreteTateParameter l) (sigma : LocalAbsoluteGalois l)
    (x y : (AlgebraicClosure ℚ_[l.value])ˣ)
    (h : (QuotientGroup.mk x :
      (AlgebraicClosure ℚ_[l.value])ˣ ⧸ P.qDeckSubgroup) =
        QuotientGroup.mk y) :
    P.qDeckQuotientEquiv sigma (QuotientGroup.mk x) =
      P.qDeckQuotientEquiv sigma (QuotientGroup.mk y) := by
  exact congrArg (P.qDeckQuotientEquiv sigma) h

end ConcreteTateParameter

end

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def concreteTateDeckQuotient : Obligation :=
  { id := "Foundations.Geometry.concrete-tate-deck-quotient"
    source := "IUT I, Definition 3.1(c); algebraic Tate deck quotient"
    status := VerificationStatus.proved
    note :=
      "For the actual q=p unit in the algebraic closure of Q_l, its q^Z " ++
        "deck subgroup, every local absolute-Galois unit equivalence, the " ++
        "subgroup preservation, and the descended quotient equivalence are " ++
        "constructed. Identity, composition, power classes, and q-unit class " ++
        "laws are proved. Curve-point uniformization is still not claimed."
    dependsOn := [ "Foundations.Geometry.concrete-tate-parameter",
      "Foundations.Geometry.tate-deck-galois-action" ] }

end LeanFormal.IUT.Audit
