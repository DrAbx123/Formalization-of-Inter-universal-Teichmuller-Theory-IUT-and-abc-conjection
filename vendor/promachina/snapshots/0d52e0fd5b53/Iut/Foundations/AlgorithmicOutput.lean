/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.TransportedRegionFamily

/-!
Qualitative properties of algorithmic transported output.

This file gives names to hypotheses such as IPL, SHE, and APT without assigning
mathematical consequences to the names themselves. Later IUT-specific modules
must provide separate theorems that turn these properties into common-target or
measurement data.
-/

namespace Iut
namespace RealLineCopy

/--
Algorithmic output with explicit transported regions and named qualitative
properties.

The properties are deliberately opaque propositions. In particular, a value of
`AlgorithmicOutput` does not by itself provide a common target, a hull, or a
volume estimate.
-/
structure AlgorithmicOutput (source target : Copy) (index : Type u) where
  family : TransportedRegionFamily source target index
  ipl : Prop
  she : Prop
  apt : Prop

namespace AlgorithmicOutput

variable {source target : Copy} {index : Type u}
variable {newIndex : Type v}

/--
Reindex an algorithmic output along a choice map.

The qualitative property names are preserved literally; the transported family
is pulled back along the supplied map.  This is the output-level form of moving
from ambient concrete choices to generated full-label choices.
-/
def reindex (output : AlgorithmicOutput source target index)
    (f : newIndex -> index) :
    AlgorithmicOutput source target newIndex :=
  { family := output.family.reindex f,
    ipl := output.ipl,
    she := output.she,
    apt := output.apt }

@[simp]
theorem reindex_family
    (output : AlgorithmicOutput source target index)
    (f : newIndex -> index) :
    (output.reindex f).family = output.family.reindex f :=
  rfl

def HasIPL (output : AlgorithmicOutput source target index) : Prop :=
  output.ipl

def HasSHE (output : AlgorithmicOutput source target index) : Prop :=
  output.she

def HasAPT (output : AlgorithmicOutput source target index) : Prop :=
  output.apt

/-- Evidence that an algorithmic output satisfies its named qualitative properties. -/
structure Certified (output : AlgorithmicOutput source target index) where
  ipl : output.HasIPL
  she : output.HasSHE
  apt : output.HasAPT

namespace Certified

variable {output : AlgorithmicOutput source target index}

theorem hasIPL (certified : Certified output) : output.HasIPL :=
  certified.ipl

theorem hasSHE (certified : Certified output) : output.HasSHE :=
  certified.she

theorem hasAPT (certified : Certified output) : output.HasAPT :=
  certified.apt

end Certified

def comparison (output : AlgorithmicOutput source target index) (choice : index) :
    RegionComparison source target :=
  output.family.comparison choice

def comparisons (output : AlgorithmicOutput source target index) :
    RegionComparisonFamily source target index :=
  output.family.comparisons

def Holds (output : AlgorithmicOutput source target index)
    (choice : index) (sourcePoint : Point source) : Prop :=
  output.family.Holds choice sourcePoint

@[simp]
theorem reindex_comparison
    (output : AlgorithmicOutput source target index)
    (f : newIndex -> index) (choice : newIndex) :
    (output.reindex f).comparison choice =
      output.comparison (f choice) :=
  rfl

@[simp]
theorem reindex_Holds
    (output : AlgorithmicOutput source target index)
    (f : newIndex -> index) (choice : newIndex) (sourcePoint : Point source) :
    (output.reindex f).Holds choice sourcePoint ↔
      output.Holds (f choice) sourcePoint :=
  Iff.rfl

@[simp]
theorem reindex_hasIPL
    (output : AlgorithmicOutput source target index)
    (f : newIndex -> index) :
    (output.reindex f).HasIPL = output.HasIPL :=
  rfl

@[simp]
theorem reindex_hasSHE
    (output : AlgorithmicOutput source target index)
    (f : newIndex -> index) :
    (output.reindex f).HasSHE = output.HasSHE :=
  rfl

@[simp]
theorem reindex_hasAPT
    (output : AlgorithmicOutput source target index)
    (f : newIndex -> index) :
    (output.reindex f).HasAPT = output.HasAPT :=
  rfl

/-- A measured common-target bound for the transported output family. -/
abbrev CommonTargetBound (output : AlgorithmicOutput source target index)
    (measure : RegionMeasure target) (bound : Real) :=
  output.family.CommonTargetBound measure bound

/-- A common target hull for the transported output family. -/
abbrev CommonTargetHull (output : AlgorithmicOutput source target index) :=
  output.family.CommonTargetHull

/-- A measured common-hull bound for the transported output family. -/
abbrev CommonTargetHullBound (output : AlgorithmicOutput source target index)
    (measure : RegionMeasure target) (bound : Real) :=
  output.family.CommonTargetHullBound measure bound

/-- Certification together with the separate common-target bound data. -/
structure CertifiedCommonTargetBound (output : AlgorithmicOutput source target index)
    (measure : RegionMeasure target) (bound : Real) where
  certified : output.Certified
  commonBound : output.CommonTargetBound measure bound

/-- Certification together with the separate common-hull bound data. -/
structure CertifiedCommonTargetHullBound (output : AlgorithmicOutput source target index)
    (measure : RegionMeasure target) (bound : Real) where
  certified : output.Certified
  commonHullBound : output.CommonTargetHullBound measure bound

namespace CertifiedCommonTargetBound

variable {measure : RegionMeasure target}
variable {output : AlgorithmicOutput source target index}
variable {bound : Real}

theorem choice_targetVolume_le (data : CertifiedCommonTargetBound output measure bound)
    (choice : index) :
    RegionMeasure.targetVolume measure (output.comparison choice) <= bound :=
  TransportedRegionFamily.choice_targetVolume_le_of_commonBound data.commonBound choice

theorem allTargetsAtMost (data : CertifiedCommonTargetBound output measure bound) :
    RegionComparisonFamily.AllTargetsAtMost measure output.comparisons bound :=
  TransportedRegionFamily.allTargetsAtMost_of_commonBound data.commonBound

theorem hasIPL (data : CertifiedCommonTargetBound output measure bound) :
    output.HasIPL :=
  data.certified.hasIPL

theorem hasSHE (data : CertifiedCommonTargetBound output measure bound) :
    output.HasSHE :=
  data.certified.hasSHE

theorem hasAPT (data : CertifiedCommonTargetBound output measure bound) :
    output.HasAPT :=
  data.certified.hasAPT

end CertifiedCommonTargetBound

namespace CertifiedCommonTargetHullBound

variable {measure : RegionMeasure target}
variable {output : AlgorithmicOutput source target index}
variable {bound : Real}

def toCertifiedCommonTargetBound
    (data : CertifiedCommonTargetHullBound output measure bound) :
    output.CertifiedCommonTargetBound measure bound :=
  { certified := data.certified,
    commonBound := data.commonHullBound.toCommonTargetBound }

theorem choice_targetVolume_le
    (data : CertifiedCommonTargetHullBound output measure bound)
    (choice : index) :
    RegionMeasure.targetVolume measure (output.comparison choice) <= bound :=
  TransportedRegionFamily.choice_targetVolume_le_of_commonHullBound
    data.commonHullBound choice

theorem allTargetsAtMost
    (data : CertifiedCommonTargetHullBound output measure bound) :
    RegionComparisonFamily.AllTargetsAtMost measure output.comparisons bound :=
  TransportedRegionFamily.allTargetsAtMost_of_commonHullBound data.commonHullBound

theorem hasIPL (data : CertifiedCommonTargetHullBound output measure bound) :
    output.HasIPL :=
  data.certified.hasIPL

theorem hasSHE (data : CertifiedCommonTargetHullBound output measure bound) :
    output.HasSHE :=
  data.certified.hasSHE

theorem hasAPT (data : CertifiedCommonTargetHullBound output measure bound) :
    output.HasAPT :=
  data.certified.hasAPT

end CertifiedCommonTargetHullBound

end AlgorithmicOutput

end RealLineCopy
end Iut
