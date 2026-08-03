/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Mathlib.Data.Real.Basic

/-!
Labeled copies of the real line and explicit transports between them.

This file is the first small model for the real-line-identification issue around
IUT III, Corollary 3.12. The point is not to model log-volumes yet, but to make
it impossible to silently identify two copies of `Real` without naming the
transport that performs the identification.
-/

namespace Iut
namespace RealLineCopy

/-- A labeled copy of the real line. -/
structure Copy where
  label : String
deriving DecidableEq, Repr

/-- A point of a labeled real-line copy, represented by its coordinate in that copy. -/
structure Point (line : Copy) where
  coord : Real

/-- Constructor for a point with coordinate `x` in a given copy. -/
def point (line : Copy) (x : Real) : Point line :=
  { coord := x }

namespace Point

variable {line : Copy}

@[simp]
theorem point_coord (x : Real) : (point line x).coord = x :=
  rfl

/-- A point of a labeled real-line copy is canonically equivalent to its coordinate. -/
def equivReal (line : Copy) : Point line ≃ Real where
  toFun x := x.coord
  invFun x := point line x
  left_inv := by
    intro x
    cases x
    rfl
  right_inv := by
    intro x
    rfl

/--
The one-coordinate product presentation of a point of a labeled real-line copy.

This is the concrete carrier bridge used by the Stage 1 Step (xi) route when a
principal product has a single real coordinate.  The equivalence is not a
mathematical assumption: both inverse laws are proved by reducing `Point` to
its real coordinate and by case-splitting on `Unit`.
-/
def equivSingleRealProduct (line : Copy) : Point line ≃ (Unit -> Real) :=
  (equivReal line).trans
    { toFun := fun x _ => x
      invFun := fun f => f ()
      left_inv := by
        intro x
        rfl
      right_inv := by
        intro f
        funext u
        cases u
        rfl }

end Point

/-- A positive scaling factor. Positivity records preservation of orientation/order. -/
structure PositiveScale where
  val : Real
  pos : 0 < val

namespace PositiveScale

/-- The unit scaling factor. -/
def one : PositiveScale :=
  { val := 1, pos := by norm_num }

/-- Product of positive scaling factors. -/
def mul (a b : PositiveScale) : PositiveScale :=
  { val := a.val * b.val, pos := mul_pos a.pos b.pos }

@[simp]
theorem one_val : one.val = 1 :=
  rfl

@[simp]
theorem mul_val (a b : PositiveScale) : (mul a b).val = a.val * b.val :=
  rfl

end PositiveScale

/-- A transport between two labeled real-line copies. -/
structure Transport (source target : Copy) where
  scale : PositiveScale

namespace Transport

variable {source middle target : Copy}

/-- The identity transport of a labeled real-line copy. -/
def id (line : Copy) : Transport line line :=
  { scale := PositiveScale.one }

/-- Composition of transports, read as `g` after `f`. -/
def comp (g : Transport middle target) (f : Transport source middle) :
    Transport source target :=
  { scale := PositiveScale.mul g.scale f.scale }

/-- Apply a transport to a point. -/
def map (f : Transport source target) (x : Point source) : Point target :=
  { coord := f.scale.val * x.coord }

@[simp]
theorem id_scale_val (line : Copy) : (id line).scale.val = 1 :=
  rfl

@[simp]
theorem comp_scale_val (g : Transport middle target) (f : Transport source middle) :
    (comp g f).scale.val = g.scale.val * f.scale.val :=
  rfl

@[simp]
theorem map_coord (f : Transport source target) (x : Point source) :
    (map f x).coord = f.scale.val * x.coord :=
  rfl

theorem map_coord_le_map_coord
    (f : Transport source target) {x y : Point source}
    (hxy : x.coord <= y.coord) :
    (map f x).coord <= (map f y).coord := by
  exact mul_le_mul_of_nonneg_left hxy (le_of_lt f.scale.pos)

@[simp]
theorem id_map_coord (line : Copy) (x : Point line) :
    (map (id line) x).coord = x.coord := by
  simp [map, id]

@[simp]
theorem comp_map_coord (g : Transport middle target) (f : Transport source middle)
    (x : Point source) :
    (map (comp g f) x).coord = (map g (map f x)).coord := by
  simp [map, comp, PositiveScale.mul, mul_assoc]

/-- Two transports are pointwise equal when they send every coordinate to the same coordinate. -/
def PointwiseEqual (f g : Transport source target) : Prop :=
  ∀ x : Point source, (map f x).coord = (map g x).coord

theorem scale_eq_of_pointwiseEqual {f g : Transport source target}
    (h : PointwiseEqual f g) : f.scale.val = g.scale.val := by
  have h_one := h (point source 1)
  simpa [PointwiseEqual, map, point] using h_one

theorem pointwiseEqual_of_scale_eq {f g : Transport source target}
    (h : f.scale.val = g.scale.val) : PointwiseEqual f g := by
  intro x
  simp [map, h]

theorem pointwiseEqual_iff_scale_eq (f g : Transport source target) :
    PointwiseEqual f g ↔ f.scale.val = g.scale.val := by
  constructor
  · exact scale_eq_of_pointwiseEqual
  · exact pointwiseEqual_of_scale_eq

/-- A loop transport has trivial monodromy when it is pointwise equal to identity. -/
def TrivialMonodromy {line : Copy} (f : Transport line line) : Prop :=
  PointwiseEqual f (id line)

theorem trivialMonodromy_iff_scale_eq_one {line : Copy} (f : Transport line line) :
    TrivialMonodromy f ↔ f.scale.val = 1 := by
  rw [TrivialMonodromy, pointwiseEqual_iff_scale_eq]
  simp

theorem nontrivialMonodromy_of_scale_ne_one {line : Copy} (f : Transport line line)
    (h : f.scale.val ≠ 1) : ¬ TrivialMonodromy f := by
  intro htrivial
  exact h ((trivialMonodromy_iff_scale_eq_one f).mp htrivial)

/-- A loop transport with a named scaling factor. -/
def scalarLoop (line : Copy) (scale : PositiveScale) : Transport line line :=
  { scale := scale }

theorem scalarLoop_trivial_iff {line : Copy} (scale : PositiveScale) :
    TrivialMonodromy (scalarLoop line scale) ↔ scale.val = 1 :=
  trivialMonodromy_iff_scale_eq_one (scalarLoop line scale)

theorem scalarLoop_nontrivial_of_scale_ne_one {line : Copy} (scale : PositiveScale)
    (h : scale.val ≠ 1) : ¬ TrivialMonodromy (scalarLoop line scale) :=
  nontrivialMonodromy_of_scale_ne_one (scalarLoop line scale) h

end Transport

end RealLineCopy
end Iut
