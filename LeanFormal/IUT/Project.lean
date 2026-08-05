/-
Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanFormal contributors
-/

import LeanFormal.IUT.Audit.Status
import Iut.Foundations.SourceModelFrobenioidPresentation
import Iut.Foundations.SourceModelRationalMonoidTransport
import Iut.Foundations.SourceModelFrobenioidRationalNaturality
import Iut.Foundations.SourceModelFrobenioidZeroEvaluation
import Iut.Foundations.SourceModelFrobenioidIntegralNaturality
import Iut.Foundations.SourceDefinition52Sequential
import Iut.Foundations.SourceFiniteStageValuationDivisor
import Iut.Foundations.SourceFrobenioidRationalMonoidTransport
import Iut.Foundations.SourceFrobenioidIsotropicBase
import Iut.Foundations.SourceFrobenioidCoAngularBaseChange
import Iut.Foundations.SourceFrobenioidBasePullbackLift
import Iut.Foundations.SourceFrobenioidUniversalProEvaluation
import LeanFormal.IUT.Foundations.Arithmetic.FiniteLabels
import LeanFormal.IUT.Foundations.Arithmetic.Radical
import LeanFormal.IUT.Foundations.Arithmetic.PrimitiveAdditive
import LeanFormal.IUT.Foundations.Arithmetic.PrimeIntervals
import LeanFormal.IUT.Foundations.Arithmetic.PrimeLabels
import LeanFormal.IUT.Foundations.Arithmetic.NormLog
import LeanFormal.IUT.Foundations.Arithmetic.PadicValuation
import LeanFormal.IUT.Foundations.NumberField.FinitePlaces
import LeanFormal.IUT.Foundations.NumberField.FinitePlaceExtension
import LeanFormal.IUT.Foundations.NumberField.LocalQParameter
import LeanFormal.IUT.Foundations.NumberField.LocalQParameterExtension
import LeanFormal.IUT.Foundations.NumberField.LocalQParameterRamification
import LeanFormal.IUT.Foundations.NumberField.Places
import LeanFormal.IUT.Foundations.LinearAlgebra.FiniteDeterminant
import LeanFormal.IUT.Foundations.Theta.GaussianKernel
import LeanFormal.IUT.Foundations.Theta.GaussianSquareSum
import LeanFormal.IUT.Foundations.Coordinates.RealLineTransport
import LeanFormal.IUT.Foundations.Volumes.WeightedVolume
import LeanFormal.IUT.Audit.Upstream.PromachinaReducedWord
import LeanFormal.IUT.Foundations.Geometry.FiniteTransitiveAction
import LeanFormal.IUT.Foundations.Geometry.WeierstrassModel
import LeanFormal.IUT.Foundations.Geometry.PuncturedEllipticCurve
import LeanFormal.IUT.Foundations.Geometry.EllipticTorsion
import LeanFormal.IUT.Foundations.Geometry.LocalReduction
import LeanFormal.IUT.Foundations.Geometry.ReductionBaseChange
import LeanFormal.IUT.IUTI.InitialTheta.SourceObligations
import LeanFormal.IUT.IUTI.InitialTheta.ArithmeticData
import LeanFormal.IUT.IUTI.HodgeTheater.SourceObligations
import LeanFormal.IUT.IUTII.Theta.GaussianKernel
import LeanFormal.IUT.IUTII.Theta.FiniteThetaPacket
import LeanFormal.IUT.IUTII.Theta.EtaleThetaQuotient
import LeanFormal.IUT.IUTII.Frobenioid.PrimeStrips
import LeanFormal.IUT.IUTII.Frobenioid.PrimeStripArithmetic
import LeanFormal.IUT.IUTII.Frobenioid.PrimeStripDegree
import LeanFormal.IUT.IUTI.HodgeTheater.PrimeStripCore
import LeanFormal.IUT.IUTI.HodgeTheater.HodgeTheaterCore
import LeanFormal.IUT.IUTI.HodgeTheater.LocalPrimePlaces
import LeanFormal.IUT.IUTII.Frobenioid.LocalPrimeStrip
import LeanFormal.IUT.IUTII.Frobenioid.LocalIntegralMonoid
import LeanFormal.IUT.IUTII.Frobenioid.LocalTorsionUnits
import LeanFormal.IUT.IUTII.Frobenioid.LocalTorsionCyclotome
import LeanFormal.IUT.IUTII.Frobenioid.LocalMLFTMPair
import LeanFormal.IUT.IUTII.Frobenioid.LocalGroupificationAction
import LeanFormal.IUT.IUTII.Frobenioid.LocalIntegralUnitKummer
import LeanFormal.IUT.IUTII.Frobenioid.LocalUnitKummerMap
import LeanFormal.IUT.IUTII.Frobenioid.LocalUnitKummerInjectivity
import LeanFormal.IUT.IUTII.Frobenioid.LocalTimesMuEvaluation
import LeanFormal.IUT.IUTII.Frobenioid.LocalIntegralFPrimeStrip
import LeanFormal.IUT.IUTII.Frobenioid.LocalMLFPrimeStripBridge
import LeanFormal.IUT.IUTII.Frobenioid.LocalIntegralUnitEvaluationImage
import LeanFormal.IUT.IUTII.Frobenioid.MLFIntegralMonoidComparison
import LeanFormal.IUT.IUTII.Kummer.KummerPolynomial
import LeanFormal.IUT.IUTII.Kummer.RootRealization
import LeanFormal.IUT.IUTII.Kummer.CompatibleRoots
import LeanFormal.IUT.IUTII.Kummer.NatRootSystem
import LeanFormal.IUT.IUTII.Kummer.KummerClass
import LeanFormal.IUT.IUTII.Kummer.RationalRootSystem
import LeanFormal.IUT.IUTII.Kummer.ContinuousKummerGerm
import LeanFormal.IUT.IUTII.Kummer.CanonicalKummerMap
import LeanFormal.IUT.IUTII.Kummer.LocalGaloisKummerAction
import LeanFormal.IUT.IUTII.Kummer.TimesMuQuotient
import LeanFormal.IUT.IUTII.Kummer.TimesMuIsm
import LeanFormal.IUT.IUTII.Kummer.LocalFieldRigidity
import LeanFormal.IUT.IUTII.Kummer.KummerRootRatio
import LeanFormal.IUT.IUTII.Kummer.VerticalLogKummer
import LeanFormal.IUT.IUTII.Kummer.VerticalCorrespondence
import LeanFormal.IUT.IUTIII.Theorem311.Obligations
import LeanFormal.IUT.IUTIII.Theorem311.Output.MultiradialAlgorithm
import LeanFormal.IUT.IUTIII.Theorem311.Indeterminacy.Ind1
import LeanFormal.IUT.IUTIII.Theorem311.Indeterminacy.Ind2
import LeanFormal.IUT.IUTIII.Theorem311.Indeterminacy.Ind3
import LeanFormal.IUT.IUTIII.Theorem311.Indeterminacy.QuotientTransport
import LeanFormal.IUT.IUTIII.Theorem311.Indeterminacy.OrbitTransport
import LeanFormal.IUT.IUTIII.Theorem311.Indeterminacy.UpperSemi
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.Contract
import LeanFormal.IUT.IUTIII.Corollary312.Comparison
import LeanFormal.IUT.IUTIII.Corollary312.Obligations
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.IPL
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.SHE
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.APT
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.Volume
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.ThetaPacketBridge
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.FiniteCertificateBridge
import LeanFormal.IUT.IUTIII.Corollary312.Routes
import LeanFormal.IUT.IUTIV.Estimates.Section1
import LeanFormal.IUT.IUTIV.Estimates.Section2
import LeanFormal.IUT.ABCBridge.Statement
import LeanFormal.IUT.ABCBridge.Arithmetic.PrimitiveTriple
import LeanFormal.IUT.ABCBridge.Bridge.IUTToABC

/-!
  Single production entry point for the source-oriented IUT project.

  The import order follows the dependency layers in
  `papers/motizuki_corpus/DEPENDENCY_LAYERS.md`. Diagnostic and intentionally
  failing files are not imported here.
-/
