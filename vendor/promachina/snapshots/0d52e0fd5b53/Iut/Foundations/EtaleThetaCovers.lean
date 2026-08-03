/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.EtaleThetaQuotient
import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Completion

/-!
# Etale-theta fundamental-group covers

This file formalizes the group-theoretic diagrams immediately preceding
Etale Theta, Definition 2.1, and the inversion splitting of Proposition 2.2.
Unlike the legacy initial-theta records, the theta quotient and the theta-root
subgroup below are derived from group homomorphisms.

Realization by finite etale morphisms of stacks, and the corresponding
cartesian squares, are kept in a separate geometric layer.
-/

open Function
open CategoryTheory

namespace Iut.EtaleTheta

universe u

/-- The multiplicative copy of the infinite cyclic Tate direction. -/
abbrev IntegerTateGroup :=
  Multiplicative ℤ

/-- Universe lift of the integral Tate direction. -/
abbrev LiftedIntegerTateGroup :=
  ULift.{u} IntegerTateGroup

/-- The profinite completion `Z-hat` of the Tate direction. -/
noncomputable def profiniteTateGroup : ProfiniteGrp.{u} :=
  ProfiniteGrp.ProfiniteCompletion.completion
    (GrpCat.of (LiftedIntegerTateGroup.{u}))

/-- Reduction of the integral Tate direction modulo `l`, with the target universe lifted. -/
def integerTateReduction (l : ℕ) :
    LiftedIntegerTateGroup.{u} →*
      LiftedLTorsionLabel.{u} l where
  toFun n :=
    ULift.up
      (Multiplicative.ofAdd
        ((Int.castAddHom (ZMod l)) n.down.toAdd))
  map_one' := by
    apply ULift.ext
    simp
  map_mul' x y := by
    apply ULift.ext
    simp

/-- The continuous reduction `Z-hat -> Z/lZ`. -/
noncomputable def profiniteTateReduction
    (l : ℕ) [NeZero l] :
    profiniteTateGroup.{u} ⟶
      lTorsionProfiniteGroup.{u} l :=
  ProfiniteGrp.ProfiniteCompletion.lift
    (GrpCat.ofHom (integerTateReduction l))

/-- The nonzero class of `1 mod l` in the Tate quotient. -/
def canonicalTateGenerator
    (l : ℕ) [NeZero l] (one_lt : 1 < l) :
    NonzeroLabel (LTorsionLabel l) := by
  letI : Fact (1 < l) := ⟨one_lt⟩
  refine
    ⟨Multiplicative.ofAdd (1 : ZMod l), ?_⟩
  intro h
  have :
      (1 : ZMod l) = 0 :=
    congrArg Multiplicative.toAdd h
  exact one_ne_zero this

/-- The canonical generator up to the sign action. -/
def canonicalTateSignLabel
    (l : ℕ) [NeZero l] (one_lt : 1 < l) :
    SignLabel (LTorsionLabel l) :=
  toSignLabel (canonicalTateGenerator l one_lt)

/--
Etale Theta, Definition 2.5(i)'s factorization of the Lagrangian quotient
through the Tate `Z-hat` direction.
-/
structure TateFactorizedLagrangian
    (l : ℕ) [NeZero l]
    (Pi : ProfiniteGrp.{u})
    (lagrangian : ProfiniteLagrangianQuotient l Pi) where
  tateProjection :
    Pi ⟶ profiniteTateGroup.{u}
  factorization :
    tateProjection ≫ profiniteTateReduction l =
      lagrangian.quotient

/-- An exact sequence `1 -> kernel -> middle -> quotient -> 1` of groups. -/
structure GroupExactSequence
    (kernel middle quotient : Type u)
    [Group kernel] [Group middle] [Group quotient] where
  inclusion : kernel →* middle
  projection : middle →* quotient
  inclusion_injective : Injective inclusion
  projection_surjective : Surjective projection
  exact : inclusion.range = projection.ker

namespace GroupExactSequence

variable
    {kernel middle quotient : Type u}
    [Group kernel] [Group middle] [Group quotient]
    (sequence : GroupExactSequence kernel middle quotient)

theorem projection_comp_inclusion :
    sequence.projection.comp sequence.inclusion = 1 := by
  ext x
  have hx : sequence.inclusion x ∈ sequence.inclusion.range :=
    ⟨x, rfl⟩
  rw [sequence.exact] at hx
  exact hx

theorem kernel_eq_range :
    sequence.projection.ker = sequence.inclusion.range :=
  sequence.exact.symm

end GroupExactSequence

/--
The arithmetic quotient `Pi_X -> Pi_X^Theta` induced by the geometric
lower-central, exponent-`l` quotient.

The group `geometricTheta` is not an input: it is definitionally
`ModLThetaQuotient Delta l`.
-/
structure ArithmeticThetaQuotientData
    (l : ℕ)
    (Delta Pi GK PiTheta : Type u)
    [Group Delta] [Group Pi] [Group GK] [Group PiTheta] where
  originalExact : GroupExactSequence Delta Pi GK
  quotientExact :
    GroupExactSequence
      (ModLThetaQuotient Delta l) PiTheta GK
  arithmeticQuotient : Pi →* PiTheta
  arithmeticQuotient_surjective :
    Surjective arithmeticQuotient
  geometric_square :
    quotientExact.inclusion.comp (modLThetaProjection Delta l) =
      arithmeticQuotient.comp originalExact.inclusion
  galois_square :
    quotientExact.projection.comp arithmeticQuotient =
      originalExact.projection
  arithmetic_kernel :
    arithmeticQuotient.ker =
      (modLThetaProjection Delta l).ker.map originalExact.inclusion

namespace ArithmeticThetaQuotientData

variable
    {l : ℕ}
    {Delta Pi GK PiTheta : Type u}
    [Group Delta] [Group Pi] [Group GK] [Group PiTheta]
    (data : ArithmeticThetaQuotientData l Delta Pi GK PiTheta)

theorem geometric_quotient_is_derived :
    Surjective (modLThetaProjection Delta l) :=
  modLThetaProjection_surjective Delta l

theorem arithmetic_kernel_is_geometric :
    data.arithmeticQuotient.ker ≤ data.originalExact.projection.ker := by
  rw [data.arithmetic_kernel, ← data.originalExact.exact]
  exact (modLThetaProjection Delta l).ker.map_le_range
    data.originalExact.inclusion

theorem quotient_projection_surjective :
    Surjective data.quotientExact.projection :=
  data.quotientExact.projection_surjective

end ArithmeticThetaQuotientData

/--
The arithmetic elliptic quotient
`Pi_X^Theta -> Pi_X^ell = Pi_X^Theta / Delta^Theta` used in Etale Theta,
Section 2 and Proposition 2.2.

Its geometric kernel is the actual rank-two mod-`l` elliptic quotient. The
kernel equation records that this quotient kills precisely the embedded theta
center.
-/
structure ArithmeticEllipticQuotientData
    {l : ℕ}
    {Delta Pi GK PiTheta : Type u}
    [Group Delta] [Group Pi] [Group GK] [Group PiTheta]
    (arithmetic :
      ArithmeticThetaQuotientData l Delta Pi GK PiTheta)
    (PiEll : Type u) [Group PiEll] where
  exact :
    GroupExactSequence
      (ModLEllipticAbelianization Delta l) PiEll GK
  quotient : PiTheta →* PiEll
  quotient_surjective :
    Surjective quotient
  geometric_square :
    exact.inclusion.comp (modLThetaToElliptic Delta l) =
      quotient.comp arithmetic.quotientExact.inclusion
  galois_square :
    exact.projection.comp quotient =
      arithmetic.quotientExact.projection
  thetaCenter_kernel :
    quotient.ker =
      (ModLThetaCenter Delta l).map
        arithmetic.quotientExact.inclusion

/--
The conjugation action of the arithmetic elliptic quotient on its geometric
rank-two mod-`l` module. The comparison equation pins the action to actual
conjugation through the fundamental exact sequence.
-/
structure ArithmeticEllipticConjugationAction
    {l : ℕ}
    {Delta Pi GK PiTheta PiEll : Type u}
    [Group Delta] [Group Pi] [Group GK]
    [Group PiTheta] [Group PiEll]
    {arithmetic :
      ArithmeticThetaQuotientData l Delta Pi GK PiTheta}
    (elliptic :
      ArithmeticEllipticQuotientData arithmetic PiEll) where
  action :
    PiEll →* MulAut (ModLEllipticAbelianization Delta l)
  action_is_conjugation :
    ∀ p x,
      elliptic.exact.inclusion (action p x) =
        p * elliptic.exact.inclusion x * p⁻¹

/--
The cuspidal exact sequence
`1 -> Delta^Theta -> D_x -> G_K -> 1`
inside the arithmetic theta quotient.
-/
structure CuspidalThetaSequence
    {l : ℕ}
    {Delta Pi GK PiTheta : Type u}
    [Group Delta] [Group Pi] [Group GK]
    [Group PiTheta]
    (arithmetic :
      ArithmeticThetaQuotientData l Delta Pi GK PiTheta)
    (CuspTheta : Type u) [Group CuspTheta] where
  exact :
    GroupExactSequence
      (ModLThetaCenter Delta l) CuspTheta GK
  intoArithmetic :
    CuspTheta →* PiTheta
  intoArithmetic_injective :
    Injective intoArithmetic
  thetaCenter_square :
    arithmetic.quotientExact.inclusion.comp
        (ModLThetaCenter Delta l).subtype =
      intoArithmetic.comp exact.inclusion
  galois_square :
    arithmetic.quotientExact.projection.comp intoArithmetic =
      exact.projection

namespace CuspidalThetaSequence

variable
    {l : ℕ}
    {Delta Pi GK PiTheta CuspTheta : Type u}
    [Group Delta] [Group Pi] [Group GK]
    [Group PiTheta] [Group CuspTheta]
    {arithmetic :
      ArithmeticThetaQuotientData l Delta Pi GK PiTheta}
    (cusp : CuspidalThetaSequence arithmetic CuspTheta)

def decompositionGroup :
    Subgroup PiTheta :=
  cusp.intoArithmetic.range

theorem decompositionGroup_equiv_cusp :
    Nonempty (CuspTheta ≃* cusp.decompositionGroup) :=
  ⟨MulEquiv.ofBijective cusp.intoArithmetic.rangeRestrict
    ⟨fun _ _ h => cusp.intoArithmetic_injective
      (congrArg Subtype.val h),
     cusp.intoArithmetic.rangeRestrict_surjective⟩⟩

end CuspidalThetaSequence

/--
The full Lagrangian quotient used to construct a type-`(1,l-tors)` cover.
Its geometric subgroup and cusp decomposition group are tied to the two exact
sequences above, rather than supplied as unrelated subgroups.
-/
structure TypeOneLTorsionQuotient
    {l : ℕ}
    {Delta Pi GK PiTheta PiEll CuspTheta : Type u}
    [Group Delta] [Group Pi] [Group GK]
    [Group PiTheta] [Group PiEll] [Group CuspTheta]
    (arithmetic :
      ArithmeticThetaQuotientData l Delta Pi GK PiTheta)
    (elliptic :
      ArithmeticEllipticQuotientData arithmetic PiEll)
    (cusp : CuspidalThetaSequence arithmetic CuspTheta) where
  quotient :
    LagrangianQuotient l PiEll
  geometricSubgroup_eq :
    quotient.geometricSubgroup =
      elliptic.exact.inclusion.range
  cuspDecompositionGroup_eq :
    quotient.cuspDecompositionGroup =
      (elliptic.quotient.comp cusp.intoArithmetic).range

namespace TypeOneLTorsionQuotient

variable
    {l : ℕ}
    {Delta Pi GK PiTheta PiEll CuspTheta : Type u}
    [Group Delta] [Group Pi] [Group GK]
    [Group PiTheta] [Group PiEll] [Group CuspTheta]
    {arithmetic :
      ArithmeticThetaQuotientData l Delta Pi GK PiTheta}
    {elliptic :
      ArithmeticEllipticQuotientData arithmetic PiEll}
    {cusp : CuspidalThetaSequence arithmetic CuspTheta}
    (cover : TypeOneLTorsionQuotient arithmetic elliptic cusp)

def coverSubgroup :
    Subgroup PiEll :=
  cover.quotient.coverSubgroup

theorem geometric_restriction_surjective :
    Surjective
      (cover.quotient.quotient.comp
        elliptic.exact.inclusion) := by
  intro q
  obtain ⟨x, hx⟩ :=
    cover.quotient.geometricRestriction_surjective q
  have hxrange :
      (x : PiEll) ∈
        elliptic.exact.inclusion.range := by
    rw [← cover.geometricSubgroup_eq]
    exact x.2
  obtain ⟨y, hy⟩ := hxrange
  refine ⟨y, ?_⟩
  change cover.quotient.quotient
      (elliptic.exact.inclusion y) = q
  rw [hy]
  simpa using hx

theorem cusp_is_trivial :
    cover.quotient.quotient.comp
        (elliptic.quotient.comp cusp.intoArithmetic) = 1 := by
  ext x
  have hx :
      elliptic.quotient (cusp.intoArithmetic x) ∈
        cover.quotient.cuspDecompositionGroup := by
    rw [cover.cuspDecompositionGroup_eq]
    exact ⟨x, rfl⟩
  exact cover.quotient.cusp_trivial hx

theorem cusp_decompositionGroup_le_coverSubgroup :
    (elliptic.quotient.comp cusp.intoArithmetic).range ≤
      cover.coverSubgroup := by
  rw [← cover.cuspDecompositionGroup_eq]
  exact cover.quotient.cuspDecompositionGroup_le_coverSubgroup

end TypeOneLTorsionQuotient

/--
Etale Theta, Proposition 2.2(i): inversion splits the rank-two mod-`l`
elliptic module into the Lagrangian `(-1)`-eigendirection and the theta
`(1)`-eigendirection. The decomposition is equivariant for the actual
arithmetic conjugation action.
-/
structure InversionEigenspaceSplitting
    {l : ℕ}
    {Delta Pi GK PiTheta PiEll CuspTheta : Type u}
    [Group Delta] [Group Pi] [Group GK]
    [Group PiTheta] [Group PiEll] [Group CuspTheta]
    (arithmetic :
      ArithmeticThetaQuotientData l Delta Pi GK PiTheta)
    (elliptic :
      ArithmeticEllipticQuotientData arithmetic PiEll)
    (cusp : CuspidalThetaSequence arithmetic CuspTheta)
    (cover :
      TypeOneLTorsionQuotient arithmetic elliptic cusp) where
  conjugation :
    ArithmeticEllipticConjugationAction elliptic
  inversion :
    ModLEllipticAbelianization Delta l ≃*
      ModLEllipticAbelianization Delta l
  productDecomposition :
    ModLEllipticAbelianization Delta l ≃*
      LTorsionLabel l × ModLThetaCenter Delta l
  productDecomposition_fst :
    ∀ x,
      (productDecomposition x).1 =
        cover.quotient.quotient
          (elliptic.exact.inclusion x)
  inversion_coordinates :
    ∀ x,
      productDecomposition (inversion x) =
        ((productDecomposition x).1⁻¹,
          (productDecomposition x).2)
  inversion_conjugation_compatible :
    ∀ p x,
      inversion (conjugation.action p x) =
        conjugation.action p (inversion x)

namespace InversionEigenspaceSplitting

variable
    {l : ℕ}
    {Delta Pi GK PiTheta PiEll CuspTheta : Type u}
    [Group Delta] [Group Pi] [Group GK]
    [Group PiTheta] [Group PiEll] [Group CuspTheta]
    {arithmetic :
      ArithmeticThetaQuotientData l Delta Pi GK PiTheta}
    {elliptic :
      ArithmeticEllipticQuotientData arithmetic PiEll}
    {cusp : CuspidalThetaSequence arithmetic CuspTheta}
    {cover :
      TypeOneLTorsionQuotient arithmetic elliptic cusp}
    (splitting :
      InversionEigenspaceSplitting
        arithmetic elliptic cusp cover)

/-- The `(-1)`-eigenspace splitting `s_iota` of Proposition 2.2(i). -/
def negativeSection :
    LTorsionLabel l →*
      ModLEllipticAbelianization Delta l where
  toFun q :=
    splitting.productDecomposition.symm (q, 1)
  map_one' := by simp
  map_mul' x y := by
    calc
      splitting.productDecomposition.symm (x * y, 1) =
          splitting.productDecomposition.symm
            ((x, 1) * (y, 1)) := by
        congr 1
        ext <;> simp
      _ = splitting.productDecomposition.symm (x, 1) *
          splitting.productDecomposition.symm (y, 1) :=
        splitting.productDecomposition.symm.map_mul
          (x, 1) (y, 1)

/-- The fixed theta eigendirection in the rank-two elliptic module. -/
def fixedSection :
    ModLThetaCenter Delta l →*
      ModLEllipticAbelianization Delta l where
  toFun z :=
    splitting.productDecomposition.symm (1, z)
  map_one' := by simp
  map_mul' x y := by
    calc
      splitting.productDecomposition.symm (1, x * y) =
          splitting.productDecomposition.symm
            ((1, x) * (1, y)) := by
        congr 1
        ext <;> simp
      _ = splitting.productDecomposition.symm (1, x) *
          splitting.productDecomposition.symm (1, y) :=
        splitting.productDecomposition.symm.map_mul
          (1, x) (1, y)

theorem inversion_apply_apply
    (g : ModLEllipticAbelianization Delta l) :
    splitting.inversion (splitting.inversion g) = g := by
  apply splitting.productDecomposition.injective
  rw [splitting.inversion_coordinates]
  rw [splitting.inversion_coordinates]
  simp

theorem negativeSection_rightInverse :
    RightInverse splitting.negativeSection
      (cover.quotient.quotient.comp
        elliptic.exact.inclusion) := by
  intro q
  change
    cover.quotient.quotient
      (elliptic.exact.inclusion
        (splitting.negativeSection q)) = q
  calc
    _ = (splitting.productDecomposition
          (splitting.negativeSection q)).1 :=
      (splitting.productDecomposition_fst _).symm
    _ = q := by simp [negativeSection]

theorem negativeSection_injective :
    Injective splitting.negativeSection :=
  splitting.negativeSection_rightInverse.injective

theorem negativeSection_negated
    (q : LTorsionLabel l) :
    splitting.inversion (splitting.negativeSection q) =
      splitting.negativeSection q⁻¹ := by
  apply splitting.productDecomposition.injective
  rw [splitting.inversion_coordinates]
  simp only [negativeSection, MonoidHom.coe_mk,
    OneHom.coe_mk, MulEquiv.apply_symm_apply]

theorem fixedSection_fixed
    (z : ModLThetaCenter Delta l) :
    splitting.inversion (splitting.fixedSection z) =
      splitting.fixedSection z := by
  apply splitting.productDecomposition.injective
  rw [splitting.inversion_coordinates]
  simp only [fixedSection, MonoidHom.coe_mk,
    OneHom.coe_mk, MulEquiv.apply_symm_apply, inv_one]

end InversionEigenspaceSplitting

/--
The quotient and Galois splitting in Etale Theta, Proposition 2.2(ii).

The kernel is exactly `Im(s_iota)` in the arithmetic elliptic quotient.
The theta-root subgroup is defined below from this quotient and the selected
Galois splitting; neither subgroup is an independent field.
-/
structure ThetaRootSplittingData
    {l : ℕ}
    {Delta Pi GK PiTheta PiEll CuspTheta : Type u}
    [Group Delta] [Group Pi] [Group GK]
    [Group PiTheta] [Group PiEll] [Group CuspTheta]
    (arithmetic :
      ArithmeticThetaQuotientData l Delta Pi GK PiTheta)
    (elliptic :
      ArithmeticEllipticQuotientData arithmetic PiEll)
    (cusp : CuspidalThetaSequence arithmetic CuspTheta)
    (cover :
      TypeOneLTorsionQuotient arithmetic elliptic cusp)
    (inversion :
      InversionEigenspaceSplitting
        arithmetic elliptic cusp cover) where
  cuspQuotient :
    PiEll →* CuspTheta
  cuspQuotient_surjective :
    Surjective cuspQuotient
  cuspQuotient_kernel :
    cuspQuotient.ker =
      inversion.negativeSection.range.map
        elliptic.exact.inclusion
  overGalois :
    cusp.exact.projection.comp cuspQuotient =
      elliptic.exact.projection
  galoisSection :
    GK →* CuspTheta
  galoisSection_rightInverse :
    RightInverse galoisSection cusp.exact.projection

namespace ThetaRootSplittingData

variable
    {l : ℕ}
    {Delta Pi GK PiTheta PiEll CuspTheta : Type u}
    [Group Delta] [Group Pi] [Group GK]
    [Group PiTheta] [Group PiEll] [Group CuspTheta]
    {arithmetic :
      ArithmeticThetaQuotientData l Delta Pi GK PiTheta}
    {elliptic :
      ArithmeticEllipticQuotientData arithmetic PiEll}
    {cusp : CuspidalThetaSequence arithmetic CuspTheta}
    {cover :
      TypeOneLTorsionQuotient arithmetic elliptic cusp}
    {inversion :
      InversionEigenspaceSplitting
        arithmetic elliptic cusp cover}
    (root :
      ThetaRootSplittingData
        arithmetic elliptic cusp cover inversion)

/-- The image `Im(s_iota)` of the negative eigenspace splitting. -/
def negativeEigenspaceImage :
    Subgroup PiEll :=
  root.cuspQuotient.ker

instance negativeEigenspaceImage_instNormal :
    root.negativeEigenspaceImage.Normal := by
  change root.cuspQuotient.ker.Normal
  infer_instance

theorem negativeEigenspaceImage_eq_sectionImage :
    root.negativeEigenspaceImage =
      inversion.negativeSection.range.map
        elliptic.exact.inclusion :=
  root.cuspQuotient_kernel

/--
The theta-root open-subgroup candidate: the inverse image of the selected
Galois splitting under `Pi_X^ell -> D_x`.
-/
def thetaRootSubgroup
    (root :
      ThetaRootSplittingData
        arithmetic elliptic cusp cover inversion) :
    Subgroup PiEll :=
  Subgroup.comap root.cuspQuotient root.galoisSection.range

theorem negativeEigenspaceImage_le_thetaRootSubgroup :
    root.negativeEigenspaceImage ≤ root.thetaRootSubgroup := by
  intro x hx
  change root.cuspQuotient x ∈ root.galoisSection.range
  rw [MonoidHom.mem_ker.mp hx]
  exact ⟨1, by simp⟩

theorem thetaRoot_projects_to_section
    {x : PiEll}
    (hx : x ∈ root.thetaRootSubgroup) :
    ∃ g : GK, root.cuspQuotient x = root.galoisSection g :=
  by
    change root.cuspQuotient x ∈ root.galoisSection.range at hx
    obtain ⟨g, hg⟩ := hx
    exact ⟨g, hg.symm⟩

theorem galoisSection_is_section (g : GK) :
    cusp.exact.projection (root.galoisSection g) = g :=
  root.galoisSection_rightInverse g

/-- Proposition 2.2(ii)'s quotient by `Im(s_iota)`. -/
noncomputable def quotientByNegativeEigenspaceEquivCusp :
    PiEll ⧸ root.negativeEigenspaceImage ≃*
      CuspTheta :=
  QuotientGroup.quotientKerEquivOfSurjective
    root.cuspQuotient root.cuspQuotient_surjective

end ThetaRootSplittingData

/--
The cuspidal `{plusminus 1}`-structure used in Etale Theta,
Theorem 1.10(iii) and Definition 2.5(i).

The involution acts trivially on both the theta-center inertia and the Galois
quotient, exactly as used in Proposition 2.2(iii).
-/
structure CuspidalSignStructure
    {l : ℕ}
    {Delta Pi GK PiTheta CuspTheta : Type u}
    [Group Delta] [Group Pi] [Group GK]
    [Group PiTheta] [Group CuspTheta]
    {arithmetic :
      ArithmeticThetaQuotientData l Delta Pi GK PiTheta}
    (cusp : CuspidalThetaSequence arithmetic CuspTheta) where
  inversion : CuspTheta ≃* CuspTheta
  involutive :
    inversion.trans inversion =
      MulEquiv.refl CuspTheta
  fixesThetaCenter :
    ∀ z : ModLThetaCenter Delta l,
      inversion (cusp.exact.inclusion z) =
        cusp.exact.inclusion z
  overGalois :
    cusp.exact.projection.comp inversion.toMonoidHom =
      cusp.exact.projection

/--
Compatibility of the selected splitting of `D_x -> G_K` with the cuspidal
`{plusminus 1}`-structure, as required in Etale Theta, Definition 2.5(i).
-/
structure SignCompatibleThetaRootSplitting
    {l : ℕ}
    {Delta Pi GK PiTheta PiEll CuspTheta : Type u}
    [Group Delta] [Group Pi] [Group GK]
    [Group PiTheta] [Group PiEll] [Group CuspTheta]
    {arithmetic :
      ArithmeticThetaQuotientData l Delta Pi GK PiTheta}
    {elliptic :
      ArithmeticEllipticQuotientData arithmetic PiEll}
    {cusp : CuspidalThetaSequence arithmetic CuspTheta}
    {cover :
      TypeOneLTorsionQuotient arithmetic elliptic cusp}
    {inversion :
      InversionEigenspaceSplitting
        arithmetic elliptic cusp cover}
    (root :
      ThetaRootSplittingData
        arithmetic elliptic cusp cover inversion)
    (sign : CuspidalSignStructure cusp) where
  section_fixed :
    sign.inversion.toMonoidHom.comp root.galoisSection =
      root.galoisSection

end Iut.EtaleTheta
