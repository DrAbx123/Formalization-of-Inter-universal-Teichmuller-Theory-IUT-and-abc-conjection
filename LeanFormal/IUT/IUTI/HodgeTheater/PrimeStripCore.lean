import LeanFormal.IUT.IUTII.Frobenioid.PrimeStripDegree
import Mathlib.Algebra.Group.Hom.Basic
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Algebra.Group.Subgroup.Basic

/-!
  The source-facing algebraic core of an IUT prime strip.

  The shapes follow IUT I--II Definition 5.2 and the corresponding public
  implementations, but every operation here is an ordinary Mathlib object:
  local groups, surjective `MonoidHom`s, commutative value monoids, and
  `MulAut` actions.  The forgetful maps and degree laws are proved below.

  This file intentionally stops before the geometric realization by an etale
  fundamental group, a number field, or an elliptic curve.  Thus a
  `DPrimeStrip`/`FPrimeStrip` is concrete source data, while its existence for
  the paper's arithmetic input remains an audited obligation.
-/

namespace LeanFormal.IUT

universe u v

structure DPrimeStrip (V : Type*) where
  Pi : V → Type u
  [groupPi : ∀ v, Group (Pi v)]
  G : V → Type u
  [groupG : ∀ v, Group (G v)]
  proj : ∀ v, Pi v →* G v
  proj_surjective : ∀ v, Function.Surjective (proj v)

attribute [instance] DPrimeStrip.groupPi DPrimeStrip.groupG

namespace DPrimeStrip

variable {V : Type*} (D : DPrimeStrip V)

def geometric (v : V) : Subgroup (D.Pi v) := (D.proj v).ker

@[simp] theorem geometric_carrier (v : V) (x : D.Pi v) :
    x ∈ D.geometric v ↔ D.proj v x = 1 := Iff.rfl

def monoAnalytic : V → Type u := D.G

@[simp] theorem monoAnalytic_apply (v : V) : D.monoAnalytic v = D.G v := rfl

end DPrimeStrip

structure DhPrimeStrip (V : Type*) where
  G : V → Type u
  [groupG : ∀ v, Group (G v)]

attribute [instance] DhPrimeStrip.groupG

def DPrimeStrip.toDh {V : Type*} (D : DPrimeStrip V) : DhPrimeStrip V where
  G := D.G

structure DhPrimeStripEquiv {V : Type*} (D D' : DhPrimeStrip V) where
  isoG : ∀ v, D.G v ≃* D'.G v

structure DPrimeStripEquiv {V : Type*} (D D' : DPrimeStrip V) where
  isoPi : ∀ v, D.Pi v ≃* D'.Pi v
  isoG : ∀ v, D.G v ≃* D'.G v
  compat : ∀ v,
    (D'.proj v).comp (isoPi v).toMonoidHom =
      (isoG v).toMonoidHom.comp (D.proj v)

namespace DPrimeStripEquiv

variable {V : Type*} {D D' : DPrimeStrip V}

theorem compat_apply (φ : DPrimeStripEquiv D D') (v : V) (x : D.Pi v) :
    D'.proj v (φ.isoPi v x) = φ.isoG v (D.proj v x) :=
  DFunLike.congr_fun (φ.compat v) x

def refl (D : DPrimeStrip V) : DPrimeStripEquiv D D where
  isoPi := fun v => MulEquiv.refl (D.Pi v)
  isoG := fun v => MulEquiv.refl (D.G v)
  compat := fun v => by ext x; rfl

def symm (φ : DPrimeStripEquiv D D') : DPrimeStripEquiv D' D where
  isoPi := fun v => (φ.isoPi v).symm
  isoG := fun v => (φ.isoG v).symm
  compat := fun v => by
    ext x
    have h := φ.compat_apply v ((φ.isoPi v).symm x)
    rw [MulEquiv.apply_symm_apply] at h
    change D.proj v ((φ.isoPi v).symm x) =
      (φ.isoG v).symm (D'.proj v x)
    rw [h, MulEquiv.symm_apply_apply]

def trans {D'' : DPrimeStrip V}
    (φ : DPrimeStripEquiv D D') (ψ : DPrimeStripEquiv D' D'') :
    DPrimeStripEquiv D D'' where
  isoPi := fun v => (φ.isoPi v).trans (ψ.isoPi v)
  isoG := fun v => (φ.isoG v).trans (ψ.isoG v)
  compat := fun v => by
    ext x
    change D''.proj v (ψ.isoPi v (φ.isoPi v x)) =
      ψ.isoG v (φ.isoG v (D.proj v x))
    rw [ψ.compat_apply v (φ.isoPi v x), φ.compat_apply v x]

def toDh (φ : DPrimeStripEquiv D D') :
    DhPrimeStripEquiv D.toDh D'.toDh :=
  { isoG := φ.isoG }

end DPrimeStripEquiv

/-
  `DPrimeStrip` and the value monoid may live in independent universes.  Since
  this structure extends `DPrimeStrip`, Lean presents their result through a
  shared `max` universe and its universe linter reports a false-positive
  coupling.  Keep the independent interface and scope the standard linter
  exception to this declaration only.
-/
set_option linter.checkUnivs false in
structure FPrimeStrip (V : Type*) extends DPrimeStrip V where
  Mon : V → Type v
  [commMonoidMon : ∀ v, CommMonoid (Mon v)]
  action : ∀ v, toDPrimeStrip.Pi v →* MulAut (Mon v)
  degree : ∀ v, Mon v →* Multiplicative Real

attribute [instance] FPrimeStrip.commMonoidMon

namespace FPrimeStrip

variable {V : Type*} (F : FPrimeStrip V)

def toD : DPrimeStrip V := F.toDPrimeStrip

@[simp] theorem toD_proj (v : V) : F.toD.proj v = F.proj v := rfl

def monoAnalytic : V → Type u := F.toD.monoAnalytic

@[simp] theorem monoAnalytic_apply (v : V) : F.monoAnalytic v = F.G v := rfl

def degreeData : PrimeStripDegree V where
  Mon := F.Mon
  commMonoidMon := F.commMonoidMon
  degree := F.degree

def totalDegree (s : Finset V) (x : ∀ v, F.Mon v) : Real :=
  F.degreeData.totalDegree s x

theorem totalDegree_mul (s : Finset V) (x y : ∀ v, F.Mon v) :
    F.totalDegree s (fun v => x v * y v) =
      F.totalDegree s x + F.totalDegree s y := by
  exact F.degreeData.totalDegree_mul s x y

theorem totalDegree_one (s : Finset V) :
    F.totalDegree s (fun _ => 1) = 0 := by
  exact F.degreeData.totalDegree_one s

theorem action_mul (v : V) (g h : F.toDPrimeStrip.Pi v) (x : F.Mon v) :
    F.action v (g * h) x = F.action v g (F.action v h x) := by
  rw [(F.action v).map_mul]
  rfl

theorem action_one (v : V) (x : F.Mon v) :
    F.action v 1 x = x := by
  rw [(F.action v).map_one]
  rfl

end FPrimeStrip

structure FPrimeStripEquiv {V : Type*} (F F' : FPrimeStrip V) where
  isoPi : ∀ v, F.toDPrimeStrip.Pi v ≃* F'.toDPrimeStrip.Pi v
  isoG : ∀ v, F.G v ≃* F'.G v
  isoMon : ∀ v, F.Mon v ≃* F'.Mon v
  compatProj : ∀ v,
    (F'.proj v).comp (isoPi v).toMonoidHom =
      (isoG v).toMonoidHom.comp (F.proj v)
  compatAction : ∀ v g x,
    isoMon v (F.action v g x) =
      F'.action v (isoPi v g) (isoMon v x)
  compatDegree : ∀ v x,
    F'.degree v (isoMon v x) = F.degree v x

namespace FPrimeStripEquiv

variable {V : Type*} {F F' : FPrimeStrip V}

theorem compatProj_apply (φ : FPrimeStripEquiv F F') (v : V)
    (x : F.toDPrimeStrip.Pi v) :
    F'.proj v (φ.isoPi v x) = φ.isoG v (F.proj v x) :=
  DFunLike.congr_fun (φ.compatProj v) x

def refl (F : FPrimeStrip V) : FPrimeStripEquiv F F where
  isoPi := fun v => MulEquiv.refl (F.toDPrimeStrip.Pi v)
  isoG := fun v => MulEquiv.refl (F.G v)
  isoMon := fun v => MulEquiv.refl (F.Mon v)
  compatProj := fun v => by ext x; rfl
  compatAction := by intros; rfl
  compatDegree := by intros; rfl

def symm (φ : FPrimeStripEquiv F F') : FPrimeStripEquiv F' F where
  isoPi := fun v => (φ.isoPi v).symm
  isoG := fun v => (φ.isoG v).symm
  isoMon := fun v => (φ.isoMon v).symm
  compatProj := fun v => by
    ext x
    have h := φ.compatProj_apply v ((φ.isoPi v).symm x)
    rw [MulEquiv.apply_symm_apply] at h
    change F.proj v ((φ.isoPi v).symm x) =
      (φ.isoG v).symm (F'.proj v x)
    rw [h, MulEquiv.symm_apply_apply]
  compatAction := by
    intro v g x
    have h := φ.compatAction v ((φ.isoPi v).symm g) ((φ.isoMon v).symm x)
    rw [MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at h
    apply (φ.isoMon v).injective
    simp only [MulEquiv.apply_symm_apply]
    exact h.symm
  compatDegree := by
    intro v x
    rw [← φ.compatDegree v ((φ.isoMon v).symm x)]
    simp

def trans {F'' : FPrimeStrip V}
    (φ : FPrimeStripEquiv F F') (ψ : FPrimeStripEquiv F' F'') :
    FPrimeStripEquiv F F'' where
  isoPi := fun v => (φ.isoPi v).trans (ψ.isoPi v)
  isoG := fun v => (φ.isoG v).trans (ψ.isoG v)
  isoMon := fun v => (φ.isoMon v).trans (ψ.isoMon v)
  compatProj := fun v => by
    ext x
    change F''.proj v (ψ.isoPi v (φ.isoPi v x)) =
      ψ.isoG v (φ.isoG v (F.proj v x))
    rw [ψ.compatProj_apply v (φ.isoPi v x), φ.compatProj_apply v x]
  compatAction := by
    intro v g x
    change ψ.isoMon v (φ.isoMon v (F.action v g x)) =
      F''.action v (ψ.isoPi v (φ.isoPi v g))
        (ψ.isoMon v (φ.isoMon v x))
    rw [φ.compatAction, ψ.compatAction]
  compatDegree := by
    intro v x
    change F''.degree v (ψ.isoMon v (φ.isoMon v x)) = F.degree v x
    rw [ψ.compatDegree, φ.compatDegree]

def toD (φ : FPrimeStripEquiv F F') :
    DPrimeStripEquiv F.toDPrimeStrip F'.toDPrimeStrip where
  isoPi := φ.isoPi
  isoG := φ.isoG
  compat := φ.compatProj

end FPrimeStripEquiv

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def primeStripCore : Obligation :=
  { id := "IUT-I-II.prime-strip-core"
    source := "IUT I, Definition 5.2; IUT II, Sections 3-4"
    status := VerificationStatus.provedKernel
    note :=
      "D/F prime-strip carriers, geometric kernel, mono-analytic forgetful map, " ++
        "group action laws, and global degree additivity are concrete and proved " ++
        "with Mathlib; arithmetic-geometric realization remains pending."
    dependsOn := ["IUT-I-II.prime-strip-degree-kernel"] }

end LeanFormal.IUT.Audit
