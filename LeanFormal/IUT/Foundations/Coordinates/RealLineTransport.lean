import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
  A standard model for labelled real-line coordinates and positive transports.

  This makes the identification map explicit.  It is a model of the ordered
  coordinate bookkeeping in the Step-(xi) discussion, not a construction of
  an IUT Hodge theater or of a holomorphic hull.
-/

namespace LeanFormal.IUT

structure RealCopy where
  label : String
  deriving DecidableEq, Repr

structure RealPoint (line : RealCopy) where
  coord : Real

def RealPoint.mk' (line : RealCopy) (x : Real) : RealPoint line :=
  { coord := x }

structure PositiveScale where
  value : Real
  positive : 0 < value

def PositiveScale.one : PositiveScale :=
  { value := 1, positive := by norm_num }

def PositiveScale.mul (a b : PositiveScale) : PositiveScale :=
  { value := a.value * b.value, positive := mul_pos a.positive b.positive }

structure RealTransport (source target : RealCopy) where
  scale : PositiveScale

def RealTransport.id (line : RealCopy) : RealTransport line line :=
  { scale := PositiveScale.one }

def RealTransport.comp {source middle target : RealCopy}
    (g : RealTransport middle target) (f : RealTransport source middle) :
    RealTransport source target :=
  { scale := PositiveScale.mul g.scale f.scale }

def RealTransport.map {source target : RealCopy}
    (f : RealTransport source target) (x : RealPoint source) : RealPoint target :=
  { coord := f.scale.value * x.coord }

theorem RealTransport.map_monotone {source target : RealCopy}
    (f : RealTransport source target) {x y : RealPoint source}
    (hxy : x.coord ≤ y.coord) :
    (f.map x).coord ≤ (f.map y).coord := by
  exact mul_le_mul_of_nonneg_left hxy (le_of_lt f.scale.positive)

theorem RealTransport.comp_map {source middle target : RealCopy}
    (g : RealTransport middle target) (f : RealTransport source middle)
    (x : RealPoint source) :
    (RealTransport.comp g f).map x = g.map (f.map x) := by
  cases x
  simp [RealTransport.map, RealTransport.comp, PositiveScale.mul, mul_assoc]

theorem RealTransport.log_map {source target : RealCopy}
    (f : RealTransport source target) (x : RealPoint source)
    (hx : 0 < x.coord) :
    Real.log (f.map x).coord = Real.log f.scale.value + Real.log x.coord := by
  change Real.log (f.scale.value * x.coord) = _
  exact Real.log_mul (ne_of_gt f.scale.positive) (ne_of_gt hx)

end LeanFormal.IUT
