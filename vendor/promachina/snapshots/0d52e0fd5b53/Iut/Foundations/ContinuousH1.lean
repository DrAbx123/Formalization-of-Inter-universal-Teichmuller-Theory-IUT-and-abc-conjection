/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceMonoThetaEnvironment
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Algebra.OpenSubgroup

/-!
# Continuous nonabelian first cohomology

IUT II, Corollary 2.8 evaluates theta sections in direct limits of continuous
`H^1`.  Mathlib's homological group-cohomology API is algebraic and abelian,
so this file supplies the required degree-one topological definition directly:
continuous crossed homomorphisms modulo continuous coboundary conjugacy.

The construction is nonabelian.  Restriction is defined along an actual
continuous group homomorphism and proved compatible with the coboundary
relation.
-/

namespace Iut

universe u

/-- A jointly continuous action of one topological group on another by automorphisms. -/
structure ContinuousGroupAction
    (G A : Type u)
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group A] [TopologicalSpace A] [IsTopologicalGroup A] where
  automorphism : G →* MulAut A
  continuous_action :
    Continuous fun p : G × A =>
      automorphism p.1 p.2

namespace ContinuousGroupAction

variable
  {G H A : Type u}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [Group A] [TopologicalSpace A] [IsTopologicalGroup A]

/-- Evaluation of the action. -/
def act (action : ContinuousGroupAction G A) (g : G) (a : A) : A :=
  action.automorphism g a

@[simp]
theorem act_one_group
    (action : ContinuousGroupAction G A) (a : A) :
    action.act 1 a = a := by
  change action.automorphism 1 a = a
  rw [map_one]
  rfl

@[simp]
theorem act_one
    (action : ContinuousGroupAction G A) (g : G) :
    action.act g 1 = 1 :=
  map_one (action.automorphism g)

@[simp]
theorem act_mul_group
    (action : ContinuousGroupAction G A)
    (g h : G) (a : A) :
    action.act (g * h) a =
      action.act g (action.act h a) := by
  change action.automorphism (g * h) a =
    action.automorphism g (action.automorphism h a)
  rw [map_mul]
  rfl

@[simp]
theorem act_mul
    (action : ContinuousGroupAction G A)
    (g : G) (a b : A) :
    action.act g (a * b) =
      action.act g a * action.act g b :=
  map_mul (action.automorphism g) a b

@[simp]
theorem act_inv
    (action : ContinuousGroupAction G A)
    (g : G) (a : A) :
    action.act g a⁻¹ = (action.act g a)⁻¹ :=
  map_inv (action.automorphism g) a

theorem continuous_act
    (action : ContinuousGroupAction G A) (g : G) :
    Continuous (action.act g) :=
  action.continuous_action.comp
    (continuous_const.prodMk continuous_id)

/-- Pull an action back along a continuous group homomorphism. -/
def comap
    (action : ContinuousGroupAction G A)
    (f : H →ₜ* G) :
    ContinuousGroupAction H A where
  automorphism := action.automorphism.comp f.toMonoidHom
  continuous_action :=
    action.continuous_action.comp
      ((f.continuous_toFun.comp continuous_fst).prodMk
        continuous_snd)

@[simp]
theorem comap_act
    (action : ContinuousGroupAction G A)
    (f : H →ₜ* G) (h : H) (a : A) :
    (action.comap f).act h a =
      action.act (f h) a :=
  rfl

end ContinuousGroupAction

/-- A continuous crossed homomorphism for a continuous group action. -/
structure ContinuousOneCocycle
    {G A : Type u}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group A] [TopologicalSpace A] [IsTopologicalGroup A]
    (action : ContinuousGroupAction G A) where
  toFun : G → A
  continuous_toFun : Continuous toFun
  map_mul' :
    ∀ g h,
      toFun (g * h) =
        toFun g * action.act g (toFun h)

namespace ContinuousOneCocycle

variable
  {G H A : Type u}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [Group A] [TopologicalSpace A] [IsTopologicalGroup A]
  {action : ContinuousGroupAction G A}

instance :
    CoeFun (ContinuousOneCocycle action) (fun _ => G → A) :=
  ⟨ContinuousOneCocycle.toFun⟩

@[ext]
theorem ext
    {z w : ContinuousOneCocycle action}
    (h : ∀ g, z g = w g) :
    z = w := by
  cases z
  cases w
  simp only at h
  congr
  funext g
  exact h g

/-- Change a cocycle by the coboundary associated to `a`. -/
def twist
    (z : ContinuousOneCocycle action) (a : A) :
    ContinuousOneCocycle action where
  toFun g :=
    a⁻¹ * z g * action.act g a
  continuous_toFun :=
    (continuous_const.mul z.continuous_toFun).mul
      (action.continuous_action.comp
        (continuous_id.prodMk continuous_const))
  map_mul' g h := by
    rw [z.map_mul', action.act_mul_group,
      action.act_mul, action.act_mul,
      action.act_inv]
    simp [mul_assoc]

@[simp]
theorem twist_apply
    (z : ContinuousOneCocycle action) (a : A) (g : G) :
    z.twist a g =
      a⁻¹ * z g * action.act g a :=
  rfl

@[simp]
theorem twist_one
    (z : ContinuousOneCocycle action) :
    z.twist 1 = z := by
  ext g
  simp

theorem twist_twist
    (z : ContinuousOneCocycle action) (a b : A) :
    (z.twist a).twist b =
      z.twist (a * b) := by
  ext g
  simp only [twist_apply, mul_inv_rev, action.act_mul]
  simp [mul_assoc]

/-- Pull a continuous cocycle back along a continuous group homomorphism. -/
def restrict
    (z : ContinuousOneCocycle action)
    (f : H →ₜ* G) :
    ContinuousOneCocycle (action.comap f) where
  toFun h := z (f h)
  continuous_toFun :=
    z.continuous_toFun.comp f.continuous_toFun
  map_mul' g h := by
    change z (f (g * h)) =
      z (f g) * action.act (f g) (z (f h))
    rw [map_mul, z.map_mul']

theorem restrict_twist
    (z : ContinuousOneCocycle action)
    (f : H →ₜ* G) (a : A) :
    (z.twist a).restrict f =
      (z.restrict f).twist a := by
  ext
  rfl

section AbelianCoefficients

variable [IsMulCommutative A]

/-- The identity continuous cocycle for an abelian coefficient group. -/
protected def one :
    ContinuousOneCocycle action where
  toFun := fun _ => 1
  continuous_toFun := continuous_const
  map_mul' := by
    intro g h
    simp only [ContinuousGroupAction.act_one, mul_one]

/-- Pointwise multiplication of continuous cocycles with abelian coefficients. -/
protected def mul
    (first second : ContinuousOneCocycle action) :
    ContinuousOneCocycle action where
  toFun g := first g * second g
  continuous_toFun :=
    first.continuous_toFun.mul
      second.continuous_toFun
  map_mul' := by
    intro g h
    rw [first.map_mul', second.map_mul',
      action.act_mul]
    ac_rfl

/-- Pointwise inversion of a continuous cocycle with abelian coefficients. -/
protected def inv
    (cocycle : ContinuousOneCocycle action) :
    ContinuousOneCocycle action where
  toFun g := (cocycle g)⁻¹
  continuous_toFun :=
    continuous_inv.comp cocycle.continuous_toFun
  map_mul' := by
    intro g h
    rw [cocycle.map_mul', mul_inv_rev,
      action.act_inv]
    ac_rfl

instance : One (ContinuousOneCocycle action) :=
  ⟨ContinuousOneCocycle.one⟩

instance : Mul (ContinuousOneCocycle action) :=
  ⟨ContinuousOneCocycle.mul⟩

instance : Inv (ContinuousOneCocycle action) :=
  ⟨ContinuousOneCocycle.inv⟩

omit [IsMulCommutative A] in
@[simp]
theorem one_apply (g : G) :
    (1 : ContinuousOneCocycle action) g = 1 :=
  rfl

@[simp]
theorem mul_apply
    (first second : ContinuousOneCocycle action)
    (g : G) :
    (first * second) g = first g * second g :=
  rfl

@[simp]
theorem inv_apply
    (cocycle : ContinuousOneCocycle action)
    (g : G) :
    cocycle⁻¹ g = (cocycle g)⁻¹ :=
  rfl

instance : CommGroup (ContinuousOneCocycle action) where
  mul_assoc first second third := by
    ext
    simp [mul_assoc]
  one_mul cocycle := by
    ext
    simp
  mul_one cocycle := by
    ext
    simp
  inv_mul_cancel cocycle := by
    ext
    simp
  mul_comm first second := by
    ext
    exact mul_comm' _ _

/--
Changing two abelian cocycles by independent coboundaries changes their
product by the product coboundary.
-/
theorem twist_mul_twist
    (first second : ContinuousOneCocycle action)
    (a b : A) :
    first.twist a * second.twist b =
      (first * second).twist (a * b) := by
  ext g
  simp only [mul_apply, twist_apply,
    mul_inv_rev, action.act_mul]
  ac_rfl

/-- Inversion carries a coboundary change to the inverse coboundary. -/
theorem inv_twist
    (cocycle : ContinuousOneCocycle action)
    (a : A) :
    (cocycle.twist a)⁻¹ =
      cocycle⁻¹.twist a⁻¹ := by
  ext g
  simp only [inv_apply, twist_apply,
    mul_inv_rev, inv_inv, action.act_inv]
  ac_rfl

end AbelianCoefficients

end ContinuousOneCocycle

/-- Cohomology of continuous one-cocycles by continuous coboundaries. -/
def ContinuousOneCocycle.Cohomologous
    {G A : Type u}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group A] [TopologicalSpace A] [IsTopologicalGroup A]
    {action : ContinuousGroupAction G A}
    (z w : ContinuousOneCocycle action) : Prop :=
  ∃ a : A, w = z.twist a

namespace ContinuousOneCocycle.Cohomologous

variable
  {G A : Type u}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group A] [TopologicalSpace A] [IsTopologicalGroup A]
  {action : ContinuousGroupAction G A}
  {z w y : ContinuousOneCocycle action}

theorem refl (z : ContinuousOneCocycle action) :
    z.Cohomologous z :=
  ⟨1, z.twist_one.symm⟩

theorem symm (h : z.Cohomologous w) :
    w.Cohomologous z := by
  rcases h with ⟨a, rfl⟩
  refine ⟨a⁻¹, ?_⟩
  rw [ContinuousOneCocycle.twist_twist]
  simp

theorem trans
    (hzw : z.Cohomologous w)
    (hwy : w.Cohomologous y) :
    z.Cohomologous y := by
  rcases hzw with ⟨a, rfl⟩
  rcases hwy with ⟨b, rfl⟩
  exact ⟨a * b, ContinuousOneCocycle.twist_twist z a b⟩

section AbelianCoefficients

variable [IsMulCommutative A]

/-- Coboundary equivalence is compatible with multiplication of abelian cocycles. -/
theorem mul
    {z₁ z₂ w₁ w₂ :
      ContinuousOneCocycle action}
    (hz : z₁.Cohomologous z₂)
    (hw : w₁.Cohomologous w₂) :
    (z₁ * w₁).Cohomologous (z₂ * w₂) := by
  rcases hz with ⟨a, rfl⟩
  rcases hw with ⟨b, rfl⟩
  exact
    ⟨a * b,
      ContinuousOneCocycle.twist_mul_twist
        z₁ w₁ a b⟩

/-- Coboundary equivalence is compatible with inversion of abelian cocycles. -/
theorem inv
    (hzw : z.Cohomologous w) :
    z⁻¹.Cohomologous w⁻¹ := by
  rcases hzw with ⟨a, rfl⟩
  exact
    ⟨a⁻¹,
      ContinuousOneCocycle.inv_twist z a⟩

end AbelianCoefficients

end ContinuousOneCocycle.Cohomologous

/-- The setoid of continuous cocycles modulo coboundary equivalence. -/
def continuousH1Setoid
    {G A : Type u}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group A] [TopologicalSpace A] [IsTopologicalGroup A]
    (action : ContinuousGroupAction G A) :
    Setoid (ContinuousOneCocycle action) where
  r := ContinuousOneCocycle.Cohomologous
  iseqv :=
    { refl := ContinuousOneCocycle.Cohomologous.refl
      symm := ContinuousOneCocycle.Cohomologous.symm
      trans := ContinuousOneCocycle.Cohomologous.trans }

/-- Continuous nonabelian first cohomology as a pointed quotient set. -/
def ContinuousH1
    {G A : Type u}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group A] [TopologicalSpace A] [IsTopologicalGroup A]
    (action : ContinuousGroupAction G A) : Type u :=
  Quotient (continuousH1Setoid action)

namespace ContinuousH1

variable
  {G H A : Type u}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [Group A] [TopologicalSpace A] [IsTopologicalGroup A]
  {action : ContinuousGroupAction G A}

/-- The cohomology class represented by a continuous cocycle. -/
def classOf
    (z : ContinuousOneCocycle action) :
    ContinuousH1 action :=
  Quotient.mk (continuousH1Setoid action) z

/-- Restriction in continuous `H^1`. -/
def restrict
    (f : H →ₜ* G) :
    ContinuousH1 action →
      ContinuousH1 (action.comap f) :=
  Quotient.map
    (fun z => z.restrict f)
    (by
      intro z w h
      rcases h with ⟨a, rfl⟩
      exact
        ⟨a, ContinuousOneCocycle.restrict_twist z f a⟩)

@[simp]
theorem restrict_classOf
    (f : H →ₜ* G)
    (z : ContinuousOneCocycle action) :
    restrict f (classOf z) =
      classOf (z.restrict f) :=
  rfl

section AbelianCoefficients

variable [IsMulCommutative A]

instance : One (ContinuousH1 action) :=
  ⟨classOf 1⟩

instance : Mul (ContinuousH1 action) where
  mul :=
    Quotient.map₂ (· * ·)
      (by
        intro first first' hFirst
          second second' hSecond
        exact
          ContinuousOneCocycle.Cohomologous.mul
            hFirst hSecond)

instance : Inv (ContinuousH1 action) where
  inv :=
    Quotient.map (·⁻¹)
      (by
        intro first second h
        exact
          ContinuousOneCocycle.Cohomologous.inv h)

omit [IsMulCommutative A] in
@[simp]
theorem classOf_one :
    classOf (1 : ContinuousOneCocycle action) =
      (1 : ContinuousH1 action) :=
  rfl

@[simp]
theorem classOf_mul
    (first second :
      ContinuousOneCocycle action) :
    classOf (first * second) =
      classOf first * classOf second :=
  rfl

@[simp]
theorem classOf_inv
    (cocycle : ContinuousOneCocycle action) :
    classOf cocycle⁻¹ =
      (classOf cocycle)⁻¹ :=
  rfl

/--
For an abelian coefficient group, continuous first cohomology is a
commutative group under pointwise multiplication of cocycles.
-/
instance : CommGroup (ContinuousH1 action) where
  mul_assoc first second third :=
    Quotient.inductionOn₃ first second third
      (by
        intro first second third
        exact congrArg classOf (mul_assoc first second third))
  one_mul cocycle :=
    Quotient.inductionOn cocycle
      (by
        intro representative
        exact congrArg classOf (one_mul representative))
  mul_one cocycle :=
    Quotient.inductionOn cocycle
      (by
        intro representative
        exact congrArg classOf (mul_one representative))
  inv_mul_cancel cocycle :=
    Quotient.inductionOn cocycle
      (by
        intro representative
        exact
          congrArg classOf
            (inv_mul_cancel representative))
  mul_comm first second :=
    Quotient.inductionOn₂ first second
      (by
        intro first second
        exact congrArg classOf (mul_comm first second))

/--
Restriction is a homomorphism on continuous `H¹` with abelian coefficients.
-/
def restrictMonoidHom
    (f : H →ₜ* G) :
    ContinuousH1 action →*
      ContinuousH1 (action.comap f) where
  toFun := restrict f
  map_one' := rfl
  map_mul' first second := by
    refine Quotient.inductionOn₂ first second ?_
    intro firstRepresentative secondRepresentative
    rfl

@[simp]
theorem restrictMonoidHom_apply
    (f : H →ₜ* G)
    (value : ContinuousH1 action) :
    restrictMonoidHom f value =
      restrict f value :=
  rfl

@[simp]
theorem restrict_one
    (f : H →ₜ* G) :
    restrict f (1 : ContinuousH1 action) =
      1 :=
  (restrictMonoidHom f).map_one

@[simp]
theorem restrict_mul
    (f : H →ₜ* G)
    (first second : ContinuousH1 action) :
    restrict f (first * second) =
      restrict f first * restrict f second :=
  (restrictMonoidHom f).map_mul first second

end AbelianCoefficients

end ContinuousH1

/-- The continuous inclusion of an open subgroup into its ambient group. -/
def openSubgroupInclusion
    {G : Type u}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (U : OpenSubgroup G) :
    U →ₜ* G where
  toMonoidHom := U.toSubgroup.subtype
  continuous_toFun := continuous_subtype_val

instance openSubgroupIsTopologicalGroup
    {G : Type u}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (U : OpenSubgroup G) :
    IsTopologicalGroup U := by
  change IsTopologicalGroup U.toSubgroup
  infer_instance

/--
A representative of an element of the direct limit of continuous `H^1` over
open subgroups.  The quotient relation below performs both restriction and
coboundary identification at once.
-/
structure ContinuousH1GermRepresentative
    {G A : Type u}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group A] [TopologicalSpace A] [IsTopologicalGroup A]
    (action : ContinuousGroupAction G A) where
  subgroup : OpenSubgroup G
  cocycle :
    ContinuousOneCocycle
      (action.comap (openSubgroupInclusion subgroup))

namespace ContinuousH1GermRepresentative

variable
  {G H A : Type u}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [Group A] [TopologicalSpace A] [IsTopologicalGroup A]
  {action : ContinuousGroupAction G A}

/-- Evaluate a germ representative after restricting to a smaller open subgroup. -/
def valueOn
    (representative : ContinuousH1GermRepresentative action)
    {U : OpenSubgroup G}
    (hU : U ≤ representative.subgroup)
    (g : U) : A :=
  representative.cocycle
    ⟨g.1, hU g.2⟩

/--
Pull a germ representative back along a continuous group homomorphism.

The new domain of definition is the open inverse image of the original
representative's domain.  Thus this operation implements the restriction maps
between the direct limits over open subgroups, rather than choosing an
unrelated open subgroup in the source.
-/
def pullback
    (representative : ContinuousH1GermRepresentative action)
    (f : H →ₜ* G) :
    ContinuousH1GermRepresentative (action.comap f) where
  subgroup :=
    OpenSubgroup.comap f.toMonoidHom
      f.continuous_toFun representative.subgroup
  cocycle :=
    { toFun := fun h =>
        representative.cocycle
          ⟨f h.1, h.2⟩
      continuous_toFun :=
        representative.cocycle.continuous_toFun.comp
          ((f.continuous_toFun.comp
              continuous_subtype_val).subtype_mk
            (fun h => h.2))
      map_mul' := by
        intro g h
        have hProduct :
            (⟨f ((g * h : _) : H), (g * h).2⟩ :
                representative.subgroup) =
              ⟨f (g : H), g.2⟩ *
                ⟨f (h : H), h.2⟩ := by
          apply SetCoe.ext
          exact map_mul f (g : H) (h : H)
        change
          representative.cocycle
              ⟨f ((g * h : _) : H), (g * h).2⟩ =
            representative.cocycle
                ⟨f (g : H), g.2⟩ *
              (action.comap
                (openSubgroupInclusion
                  representative.subgroup)).act
                ⟨f (g : H), g.2⟩
                (representative.cocycle
                  ⟨f (h : H), h.2⟩)
        rw [hProduct]
        exact
          representative.cocycle.map_mul'
            ⟨f (g : H), g.2⟩
            ⟨f (h : H), h.2⟩ }

@[simp]
theorem pullback_cocycle_apply
    (representative : ContinuousH1GermRepresentative action)
    (f : H →ₜ* G)
    (h : representative.pullback f |>.subgroup) :
    (representative.pullback f).cocycle h =
      representative.cocycle
        ⟨f h.1, h.2⟩ :=
  rfl

section AbelianCoefficients

variable [IsMulCommutative A]

/-- The identity germ representative, defined on the full ambient group. -/
protected def one :
    ContinuousH1GermRepresentative action where
  subgroup := ⊤
  cocycle := 1

/--
Multiply two germ representatives after restricting both to the intersection
of their open domains.
-/
protected def mul
    (first second :
      ContinuousH1GermRepresentative action) :
    ContinuousH1GermRepresentative action where
  subgroup := first.subgroup ⊓ second.subgroup
  cocycle :=
    { toFun := fun g =>
        first.cocycle ⟨g.1, g.2.1⟩ *
          second.cocycle ⟨g.1, g.2.2⟩
      continuous_toFun :=
        (first.cocycle.continuous_toFun.comp
          (continuous_subtype_val.subtype_mk
            (fun g => g.2.1))).mul
        (second.cocycle.continuous_toFun.comp
          (continuous_subtype_val.subtype_mk
            (fun g => g.2.2)))
      map_mul' := by
        intro g h
        have firstProduct :
            (⟨((g * h : _) : G), (g * h).2.1⟩ :
                first.subgroup) =
              ⟨(g : G), g.2.1⟩ *
                ⟨(h : G), h.2.1⟩ := by
          apply SetCoe.ext
          rfl
        have secondProduct :
            (⟨((g * h : _) : G), (g * h).2.2⟩ :
                second.subgroup) =
              ⟨(g : G), g.2.2⟩ *
                ⟨(h : G), h.2.2⟩ := by
          apply SetCoe.ext
          rfl
        rw [firstProduct, secondProduct,
          first.cocycle.map_mul',
          second.cocycle.map_mul']
        change
          first.cocycle ⟨(g : G), g.2.1⟩ *
                action.act (g : G)
                  (first.cocycle
                    ⟨(h : G), h.2.1⟩) *
              (second.cocycle
                  ⟨(g : G), g.2.2⟩ *
                action.act (g : G)
                  (second.cocycle
                    ⟨(h : G), h.2.2⟩)) =
            (first.cocycle
                ⟨(g : G), g.2.1⟩ *
              second.cocycle
                ⟨(g : G), g.2.2⟩) *
              action.act (g : G)
                (first.cocycle
                    ⟨(h : G), h.2.1⟩ *
                  second.cocycle
                    ⟨(h : G), h.2.2⟩)
        rw [ContinuousGroupAction.act_mul]
        ac_rfl }

/-- Invert a germ representative on its existing open domain. -/
protected def inv
    (representative :
      ContinuousH1GermRepresentative action) :
    ContinuousH1GermRepresentative action where
  subgroup := representative.subgroup
  cocycle := representative.cocycle⁻¹

omit [IsMulCommutative A] in
@[simp]
theorem one_cocycle_apply
    (g :
      (ContinuousH1GermRepresentative.one
        (action := action)).subgroup) :
    (ContinuousH1GermRepresentative.one
      (action := action)).cocycle g = 1 :=
  rfl

@[simp]
theorem mul_cocycle_apply
    (first second :
      ContinuousH1GermRepresentative action)
    (g :
      (ContinuousH1GermRepresentative.mul
        first second).subgroup) :
    (ContinuousH1GermRepresentative.mul
        first second).cocycle g =
      first.cocycle ⟨g.1, g.2.1⟩ *
        second.cocycle ⟨g.1, g.2.2⟩ :=
  rfl

@[simp]
theorem inv_cocycle_apply
    (representative :
      ContinuousH1GermRepresentative action)
    (g :
      (ContinuousH1GermRepresentative.inv
        representative).subgroup) :
    (ContinuousH1GermRepresentative.inv
        representative).cocycle g =
      (representative.cocycle g)⁻¹ :=
  rfl

end AbelianCoefficients

/--
Two representatives define the same germ when their restrictions to a common
open subgroup are related by one coboundary.
-/
def Equivalent
    (first second : ContinuousH1GermRepresentative action) : Prop :=
  ∃ (U : OpenSubgroup G)
      (hFirst : U ≤ first.subgroup)
      (hSecond : U ≤ second.subgroup)
      (a : A),
    ∀ g : U,
      second.valueOn hSecond g =
        a⁻¹ * first.valueOn hFirst g *
          action.act (g : G) a

namespace Equivalent

variable
  {first second third :
    ContinuousH1GermRepresentative action}

theorem refl
    (representative : ContinuousH1GermRepresentative action) :
    representative.Equivalent representative := by
  refine
    ⟨representative.subgroup, le_rfl, le_rfl, 1, ?_⟩
  intro
  simp [valueOn]

theorem symm (h : first.Equivalent second) :
    second.Equivalent first := by
  rcases h with ⟨U, hFirst, hSecond, a, h⟩
  refine ⟨U, hSecond, hFirst, a⁻¹, ?_⟩
  intro g
  rw [h g]
  simp [ContinuousGroupAction.act_inv, mul_assoc]

theorem trans
    (hFirstSecond : first.Equivalent second)
    (hSecondThird : second.Equivalent third) :
    first.Equivalent third := by
  rcases hFirstSecond with
    ⟨U, hFirst, hSecondU, a, hU⟩
  rcases hSecondThird with
    ⟨V, hSecondV, hThird, b, hV⟩
  refine
    ⟨U ⊓ V,
      fun _ hg => hFirst hg.1,
      fun _ hg => hThird hg.2,
      a * b, ?_⟩
  intro g
  let gU : U := ⟨g.1, g.2.1⟩
  let gV : V := ⟨g.1, g.2.2⟩
  have hSecondValues :
      second.valueOn hSecondV gV =
        second.valueOn hSecondU gU := by
    rfl
  change
    third.valueOn hThird gV =
      (a * b)⁻¹ * first.valueOn hFirst gU *
        action.act (g : G) (a * b)
  rw [hV gV, hSecondValues, hU gU]
  simp [ContinuousGroupAction.act_mul, mul_assoc]
  rfl

/-- Pullback preserves equality of continuous `H^1` germs. -/
theorem pullback
    {first second :
      ContinuousH1GermRepresentative action}
    (h : first.Equivalent second)
    (f : H →ₜ* G) :
    (first.pullback f).Equivalent
      (second.pullback f) := by
  rcases h with
    ⟨U, hFirst, hSecond, a, hU⟩
  let fU : OpenSubgroup H :=
    OpenSubgroup.comap f.toMonoidHom
      f.continuous_toFun U
  refine
    ⟨fU,
      ?_,
      ?_,
      a,
      ?_⟩
  · intro g hg
    exact hFirst hg
  · intro g hg
    exact hSecond hg
  · intro g
    let gU : U := ⟨f (g : H), g.2⟩
    exact hU gU

section AbelianCoefficients

variable [IsMulCommutative A]

omit [IsMulCommutative A] in
/--
Equality on a common open subgroup presents equality of continuous `H¹`
germs, with the identity coboundary.
-/
theorem of_equal_on
    {first second :
      ContinuousH1GermRepresentative action}
    (U : OpenSubgroup G)
    (hFirst : U ≤ first.subgroup)
    (hSecond : U ≤ second.subgroup)
    (h :
      ∀ g : U,
        second.valueOn hSecond g =
          first.valueOn hFirst g) :
    first.Equivalent second := by
  refine ⟨U, hFirst, hSecond, 1, ?_⟩
  intro g
  simpa using h g

/-- Germ equivalence is compatible with multiplication on intersected domains. -/
theorem mul
    {first₁ first₂ second₁ second₂ :
      ContinuousH1GermRepresentative action}
    (hFirst : first₁.Equivalent first₂)
    (hSecond : second₁.Equivalent second₂) :
    (ContinuousH1GermRepresentative.mul
        first₁ second₁).Equivalent
      (ContinuousH1GermRepresentative.mul
        first₂ second₂) := by
  rcases hFirst with
    ⟨U, hFirst₁, hFirst₂, a, hU⟩
  rcases hSecond with
    ⟨V, hSecond₁, hSecond₂, b, hV⟩
  refine
    ⟨U ⊓ V,
      fun _ hg => ⟨hFirst₁ hg.1, hSecond₁ hg.2⟩,
      fun _ hg => ⟨hFirst₂ hg.1, hSecond₂ hg.2⟩,
      a * b,
      ?_⟩
  intro g
  let gU : U := ⟨g.1, g.2.1⟩
  let gV : V := ⟨g.1, g.2.2⟩
  change
    first₂.valueOn hFirst₂ gU *
        second₂.valueOn hSecond₂ gV =
      (a * b)⁻¹ *
          (first₁.valueOn hFirst₁ gU *
            second₁.valueOn hSecond₁ gV) *
        action.act (g : G) (a * b)
  rw [hU gU, hV gV,
    ContinuousGroupAction.act_mul]
  dsimp only [gU, gV]
  rw [mul_inv_rev]
  ac_rfl

/-- Germ equivalence is compatible with inversion. -/
theorem inv
    {first second :
      ContinuousH1GermRepresentative action}
    (h : first.Equivalent second) :
    (ContinuousH1GermRepresentative.inv
        first).Equivalent
      (ContinuousH1GermRepresentative.inv
        second) := by
  rcases h with ⟨U, hFirst, hSecond, a, hU⟩
  refine ⟨U, hFirst, hSecond, a⁻¹, ?_⟩
  intro g
  change
    (second.valueOn hSecond g)⁻¹ =
      (a⁻¹)⁻¹ *
          (first.valueOn hFirst g)⁻¹ *
        action.act (g : G) a⁻¹
  rw [hU g, ContinuousGroupAction.act_inv]
  simp only [mul_inv_rev, inv_inv]
  ac_rfl

end AbelianCoefficients

end Equivalent

end ContinuousH1GermRepresentative

/-- The setoid presenting the direct limit over open subgroups. -/
def continuousH1GermSetoid
    {G A : Type u}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group A] [TopologicalSpace A] [IsTopologicalGroup A]
    (action : ContinuousGroupAction G A) :
    Setoid (ContinuousH1GermRepresentative action) where
  r := ContinuousH1GermRepresentative.Equivalent
  iseqv :=
    { refl := ContinuousH1GermRepresentative.Equivalent.refl
      symm := ContinuousH1GermRepresentative.Equivalent.symm
      trans := ContinuousH1GermRepresentative.Equivalent.trans }

/--
The direct limit `colim_J H^1_cont(J,A)` over open subgroups, presented as
continuous cocycle germs.
-/
def ContinuousH1Germ
    {G A : Type u}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group A] [TopologicalSpace A] [IsTopologicalGroup A]
    (action : ContinuousGroupAction G A) : Type u :=
  Quotient (continuousH1GermSetoid action)

namespace ContinuousH1Germ

variable
  {G H K A : Type u}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
  [Group A] [TopologicalSpace A] [IsTopologicalGroup A]
  {action : ContinuousGroupAction G A}

/-- The germ determined by a continuous cocycle on an open subgroup. -/
def classOf
    (representative : ContinuousH1GermRepresentative action) :
    ContinuousH1Germ action :=
  Quotient.mk (continuousH1GermSetoid action) representative

/--
Restriction of a continuous `H^1` germ along a continuous group homomorphism.

This is the direct-limit restriction operation used twice in IUT II,
Corollary 2.8(i): first to the indicated subgroup/subquotient and then to a
decomposition group.  The construction itself is general; identifying the
paper's concrete homomorphisms remains separate source data.
-/
def restrict
    (f : H →ₜ* G) :
    ContinuousH1Germ action →
      ContinuousH1Germ (action.comap f) :=
  Quotient.map
    (fun representative => representative.pullback f)
    (by
      intro first second h
      exact
        ContinuousH1GermRepresentative.Equivalent.pullback h f)

@[simp]
theorem restrict_classOf
    (f : H →ₜ* G)
    (representative :
      ContinuousH1GermRepresentative action) :
    restrict f (classOf representative) =
      classOf (representative.pullback f) :=
  rfl

section AbelianCoefficients

variable [IsMulCommutative A]

instance : One (ContinuousH1Germ action) :=
  ⟨classOf
    (ContinuousH1GermRepresentative.one
      (action := action))⟩

instance : Mul (ContinuousH1Germ action) where
  mul :=
    Quotient.map₂
      ContinuousH1GermRepresentative.mul
      (by
        intro first first' hFirst
          second second' hSecond
        exact
          ContinuousH1GermRepresentative.Equivalent.mul
            hFirst hSecond)

instance : Inv (ContinuousH1Germ action) where
  inv :=
    Quotient.map
      ContinuousH1GermRepresentative.inv
      (by
        intro first second h
        exact
          ContinuousH1GermRepresentative.Equivalent.inv h)

omit [IsMulCommutative A] in
@[simp]
theorem classOf_one :
    classOf
        (ContinuousH1GermRepresentative.one
          (action := action)) =
      (1 : ContinuousH1Germ action) :=
  rfl

@[simp]
theorem classOf_mul
    (first second :
      ContinuousH1GermRepresentative action) :
    classOf
        (ContinuousH1GermRepresentative.mul
          first second) =
      classOf first * classOf second :=
  rfl

@[simp]
theorem classOf_inv
    (representative :
      ContinuousH1GermRepresentative action) :
    classOf
        (ContinuousH1GermRepresentative.inv
          representative) =
      (classOf representative)⁻¹ :=
  rfl

/--
The direct limit of continuous `H¹` over open subgroups is a commutative
group for abelian coefficients.
-/
instance : CommGroup (ContinuousH1Germ action) where
  mul_assoc first second third :=
    Quotient.inductionOn₃ first second third
      (by
        intro first second third
        apply Quotient.sound
        let common :=
          (first.subgroup ⊓ second.subgroup) ⊓
            third.subgroup
        refine
          ContinuousH1GermRepresentative.Equivalent.of_equal_on
            (first :=
              ContinuousH1GermRepresentative.mul
                (ContinuousH1GermRepresentative.mul
                  first second)
                third)
            (second :=
              ContinuousH1GermRepresentative.mul
                first
                (ContinuousH1GermRepresentative.mul
                  second third))
            common ?_ ?_ ?_
        · exact le_rfl
        · intro g hg
          exact
            ⟨hg.1.1, ⟨hg.1.2, hg.2⟩⟩
        · intro g
          change
            first.cocycle
                  ⟨(g : G), g.2.1.1⟩ *
                (second.cocycle
                    ⟨(g : G), g.2.1.2⟩ *
                  third.cocycle
                    ⟨(g : G), g.2.2⟩) =
              (first.cocycle
                    ⟨(g : G), g.2.1.1⟩ *
                  second.cocycle
                    ⟨(g : G), g.2.1.2⟩) *
                third.cocycle
                  ⟨(g : G), g.2.2⟩
          rw [mul_assoc])
  one_mul value :=
    Quotient.inductionOn value
      (by
        intro representative
        apply Quotient.sound
        refine
          ContinuousH1GermRepresentative.Equivalent.of_equal_on
            (first :=
              ContinuousH1GermRepresentative.mul
                (ContinuousH1GermRepresentative.one
                  (action := action))
                representative)
            (second := representative)
            representative.subgroup ?_ ?_ ?_
        · intro g hg
          exact ⟨trivial, hg⟩
        · exact le_rfl
        · intro g
          change
            representative.cocycle g =
              1 * representative.cocycle g
          simp)
  mul_one value :=
    Quotient.inductionOn value
      (by
        intro representative
        apply Quotient.sound
        refine
          ContinuousH1GermRepresentative.Equivalent.of_equal_on
            (first :=
              ContinuousH1GermRepresentative.mul
                representative
                (ContinuousH1GermRepresentative.one
                  (action := action)))
            (second := representative)
            representative.subgroup ?_ ?_ ?_
        · intro g hg
          exact ⟨hg, trivial⟩
        · exact le_rfl
        · intro g
          change
            representative.cocycle g =
              representative.cocycle g * 1
          simp)
  inv_mul_cancel value :=
    Quotient.inductionOn value
      (by
        intro representative
        apply Quotient.sound
        refine
          ContinuousH1GermRepresentative.Equivalent.of_equal_on
            (first :=
              ContinuousH1GermRepresentative.mul
                (ContinuousH1GermRepresentative.inv
                  representative)
                representative)
            (second :=
              ContinuousH1GermRepresentative.one
                (action := action))
            representative.subgroup ?_ ?_ ?_
        · intro g hg
          exact ⟨hg, hg⟩
        · intro _ _
          trivial
        · intro g
          change
            1 =
              (representative.cocycle g)⁻¹ *
                representative.cocycle g
          simp)
  mul_comm first second :=
    Quotient.inductionOn₂ first second
      (by
        intro first second
        apply Quotient.sound
        refine
          ContinuousH1GermRepresentative.Equivalent.of_equal_on
            (first :=
              ContinuousH1GermRepresentative.mul
                first second)
            (second :=
              ContinuousH1GermRepresentative.mul
                second first)
            (first.subgroup ⊓ second.subgroup)
            ?_ ?_ ?_
        · exact le_rfl
        · intro g hg
          exact ⟨hg.2, hg.1⟩
        · intro g
          change
            second.cocycle
                  ⟨(g : G), g.2.2⟩ *
                first.cocycle
                  ⟨(g : G), g.2.1⟩ =
              first.cocycle
                  ⟨(g : G), g.2.1⟩ *
                second.cocycle
                  ⟨(g : G), g.2.2⟩
          exact mul_comm' _ _)

/--
Restriction on the direct limit of continuous `H¹` is a homomorphism for
abelian coefficients.
-/
def restrictMonoidHom
    (f : H →ₜ* G) :
    ContinuousH1Germ action →*
      ContinuousH1Germ (action.comap f) where
  toFun := restrict f
  map_one' := by
    apply Quotient.sound
    let pulledOne :=
      (ContinuousH1GermRepresentative.one
        (action := action)).pullback f
    let targetOne :=
      ContinuousH1GermRepresentative.one
        (action := action.comap f)
    refine
      ContinuousH1GermRepresentative.Equivalent.of_equal_on
        (action := action.comap f)
        (first := pulledOne)
        (second := targetOne)
        pulledOne.subgroup le_rfl ?_ ?_
    · intro _ _
      trivial
    · intro g
      rfl
  map_mul' first second := by
    refine Quotient.inductionOn₂ first second ?_
    intro firstRepresentative secondRepresentative
    apply Quotient.sound
    let pulledProduct :=
      (ContinuousH1GermRepresentative.mul
        firstRepresentative
        secondRepresentative).pullback f
    let productOfPullbacks :=
      ContinuousH1GermRepresentative.mul
        (firstRepresentative.pullback f)
        (secondRepresentative.pullback f)
    refine
      ContinuousH1GermRepresentative.Equivalent.of_equal_on
        (action := action.comap f)
        (first := pulledProduct)
        (second := productOfPullbacks)
        pulledProduct.subgroup le_rfl ?_ ?_
    · intro g hg
      exact ⟨hg.1, hg.2⟩
    · intro g
      rfl

@[simp]
theorem restrictMonoidHom_apply
    (f : H →ₜ* G)
    (value : ContinuousH1Germ action) :
    restrictMonoidHom f value =
      restrict f value :=
  rfl

@[simp]
theorem restrict_one
    (f : H →ₜ* G) :
    restrict f (1 : ContinuousH1Germ action) =
      1 :=
  (restrictMonoidHom f).map_one

@[simp]
theorem restrict_mul
    (f : H →ₜ* G)
    (first second : ContinuousH1Germ action) :
    restrict f (first * second) =
      restrict f first * restrict f second :=
  (restrictMonoidHom f).map_mul first second

end AbelianCoefficients

end ContinuousH1Germ

namespace ContinuousH1

variable
  {G A : Type u}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group A] [TopologicalSpace A] [IsTopologicalGroup A]
  {action : ContinuousGroupAction G A}

/--
The canonical map from continuous H1 on one open subgroup to the direct-limit
germ.  It retains the subgroup and regards the cocycle as a germ
representative.
-/
def toGerm
    (subgroup : OpenSubgroup G) :
    ContinuousH1
        (action.comap (openSubgroupInclusion subgroup)) →
      ContinuousH1Germ action :=
  Quotient.map
    (fun cocycle =>
      { subgroup := subgroup
        cocycle := cocycle })
    (by
      intro first second h
      rcases h with ⟨cochain, rfl⟩
      refine
        ⟨subgroup, le_rfl, le_rfl, cochain, ?_⟩
      intro g
      rfl)

@[simp]
theorem toGerm_classOf
    (subgroup : OpenSubgroup G)
    (cocycle :
      ContinuousOneCocycle
        (action.comap
          (openSubgroupInclusion subgroup))) :
    toGerm subgroup (classOf cocycle) =
      ContinuousH1Germ.classOf
        { subgroup := subgroup
          cocycle := cocycle } :=
  rfl

end ContinuousH1

end Iut
