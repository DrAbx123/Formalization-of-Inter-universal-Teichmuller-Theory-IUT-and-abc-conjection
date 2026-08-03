/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.RealLineCopy

/-!
Small comparison diagrams for transports between labeled real-line copies.

The point of this file is to formalize the elementary obstruction behind scalar
insertion in a coherent diagram: if one path is obtained from another by an
extra positive scalar, then equality of the two induced maps forces that scalar
to be `1`.
-/

namespace Iut
namespace RealLineCopy

/-- Rescale a transport by multiplying its scale on the target side. -/
def Transport.rescale {source target : Copy} (s : PositiveScale)
    (f : Transport source target) : Transport source target :=
  { scale := PositiveScale.mul s f.scale }

namespace Transport

variable {source target : Copy}

@[simp]
theorem rescale_scale_val (s : PositiveScale) (f : Transport source target) :
    (rescale s f).scale.val = s.val * f.scale.val :=
  rfl

/-- Two parallel transports between the same copies. -/
structure ParallelPair (source target : Copy) where
  top : Transport source target
  bottom : Transport source target

namespace ParallelPair

/-- A parallel-pair diagram is coherent when its two paths act identically. -/
def Coherent (p : ParallelPair source target) : Prop :=
  PointwiseEqual p.top p.bottom

theorem coherent_iff_scale_eq (p : ParallelPair source target) :
    Coherent p ↔ p.top.scale.val = p.bottom.scale.val :=
  pointwiseEqual_iff_scale_eq p.top p.bottom

end ParallelPair

/--
If a coherent parallel diagram compares a transport with a scalar-rescaled copy
of itself, then the inserted scalar must be `1`.
-/
theorem coherent_rescale_iff_scale_eq_one (s : PositiveScale)
    (f : Transport source target) :
    ParallelPair.Coherent { top := f, bottom := rescale s f } ↔ s.val = 1 := by
  constructor
  · intro hcoh
    have hscale :
        f.scale.val = s.val * f.scale.val := by
      simpa using
        (ParallelPair.coherent_iff_scale_eq
          ({ top := f, bottom := rescale s f } : ParallelPair source target)).mp hcoh
    have hcancel : 1 = s.val := by
      apply mul_right_cancel₀ (ne_of_gt f.scale.pos)
      calc
        1 * f.scale.val = f.scale.val := one_mul f.scale.val
        _ = s.val * f.scale.val := hscale
    exact hcancel.symm
  · intro hs
    exact
      (ParallelPair.coherent_iff_scale_eq
        ({ top := f, bottom := rescale s f } : ParallelPair source target)).mpr
        (by simp [hs])

theorem incoherent_rescale_of_scale_ne_one (s : PositiveScale)
    (f : Transport source target) (hs : s.val ≠ 1) :
    ¬ ParallelPair.Coherent { top := f, bottom := rescale s f } := by
  intro hcoh
  exact hs ((coherent_rescale_iff_scale_eq_one s f).mp hcoh)

end Transport

end RealLineCopy
end Iut
