param(
  [string[]]$Modules = @(
    'LeanFormal/IUT/Audit/Status.lean',
    'LeanFormal/IUT/Foundations/Arithmetic/FiniteLabels.lean',
    'LeanFormal/IUT/Foundations/Arithmetic/Radical.lean',
    'LeanFormal/IUT/Foundations/Arithmetic/PrimitiveAdditive.lean',
    'LeanFormal/IUT/Foundations/Arithmetic/PrimeIntervals.lean',
    'LeanFormal/IUT/Foundations/Arithmetic/PrimeLabels.lean',
    'LeanFormal/IUT/Foundations/Arithmetic/NormLog.lean',
    'LeanFormal/IUT/Foundations/Arithmetic/PadicValuation.lean',
    'LeanFormal/IUT/Foundations/NumberField/FinitePlaces.lean',
    'LeanFormal/IUT/Foundations/NumberField/FinitePlaceExtension.lean',
    'LeanFormal/IUT/Foundations/NumberField/LocalQParameter.lean',
    'LeanFormal/IUT/Foundations/NumberField/Places.lean',
    'LeanFormal/IUT/Foundations/LinearAlgebra/FiniteDeterminant.lean',
    'LeanFormal/IUT/Foundations/Theta/GaussianKernel.lean',
    'LeanFormal/IUT/Foundations/Theta/GaussianSquareSum.lean',
    'LeanFormal/IUT/Foundations/Coordinates/RealLineTransport.lean',
    'LeanFormal/IUT/Foundations/Volumes/WeightedVolume.lean',
    'LeanFormal/IUT/Foundations/Geometry/FiniteTransitiveAction.lean',
    'LeanFormal/IUT/Foundations/Geometry/WeierstrassModel.lean',
    'LeanFormal/IUT/Foundations/Geometry/PuncturedEllipticCurve.lean',
    'LeanFormal/IUT/Foundations/Geometry/EllipticTorsion.lean',
    'LeanFormal/IUT/Foundations/Geometry/LocalReduction.lean',
    'LeanFormal/IUT/Foundations/Geometry/ReductionBaseChange.lean',
    'LeanFormal/IUT/IUTI/InitialTheta/SourceObligations.lean',
    'LeanFormal/IUT/IUTI/InitialTheta/ArithmeticData.lean',
    'LeanFormal/IUT/IUTI/HodgeTheater/SourceObligations.lean',
    'LeanFormal/IUT/IUTII/Theta/GaussianKernel.lean',
    'LeanFormal/IUT/IUTII/Theta/FiniteThetaPacket.lean',
    'LeanFormal/IUT/IUTII/Theta/EtaleThetaQuotient.lean',
    'LeanFormal/IUT/IUTII/Frobenioid/PrimeStrips.lean',
    'LeanFormal/IUT/IUTII/Frobenioid/PrimeStripArithmetic.lean',
    'LeanFormal/IUT/IUTII/Frobenioid/PrimeStripDegree.lean',
    'LeanFormal/IUT/IUTI/HodgeTheater/PrimeStripCore.lean',
    'LeanFormal/IUT/IUTI/HodgeTheater/HodgeTheaterCore.lean',
    'LeanFormal/IUT/IUTI/HodgeTheater/LocalPrimePlaces.lean',
    'LeanFormal/IUT/IUTII/Frobenioid/LocalPrimeStrip.lean',
    'LeanFormal/IUT/IUTII/Kummer/KummerPolynomial.lean',
    'LeanFormal/IUT/IUTII/Kummer/RootRealization.lean',
    'LeanFormal/IUT/IUTII/Kummer/CompatibleRoots.lean',
    'LeanFormal/IUT/IUTII/Kummer/NatRootSystem.lean',
    'LeanFormal/IUT/IUTII/Kummer/KummerClass.lean',
    'LeanFormal/IUT/IUTII/Kummer/KummerRootRatio.lean',
    'LeanFormal/IUT/IUTII/Kummer/VerticalLogKummer.lean',
    'LeanFormal/IUT/IUTII/Kummer/VerticalCorrespondence.lean',
    'LeanFormal/IUT/IUTIII/Theorem311/Obligations.lean',
    'LeanFormal/IUT/IUTIII/Theorem311/Output/MultiradialAlgorithm.lean',
    'LeanFormal/IUT/IUTIII/Theorem311/Indeterminacy/Ind1.lean',
    'LeanFormal/IUT/IUTIII/Theorem311/Indeterminacy/Ind2.lean',
    'LeanFormal/IUT/IUTIII/Theorem311/Indeterminacy/Ind3.lean',
    'LeanFormal/IUT/IUTIII/Theorem311/Indeterminacy/QuotientTransport.lean',
    'LeanFormal/IUT/IUTIII/Theorem311/Indeterminacy/OrbitTransport.lean',
    'LeanFormal/IUT/IUTIII/Theorem311/Indeterminacy/UpperSemi.lean',
    'LeanFormal/IUT/IUTIII/Corollary312/StepXI/Contract.lean',
    'LeanFormal/IUT/IUTIII/Corollary312/Comparison.lean',
    'LeanFormal/IUT/IUTIII/Corollary312/Obligations.lean',
    'LeanFormal/IUT/IUTIII/Corollary312/StepXI/IPL.lean',
    'LeanFormal/IUT/IUTIII/Corollary312/StepXI/SHE.lean',
    'LeanFormal/IUT/IUTIII/Corollary312/StepXI/APT.lean',
    'LeanFormal/IUT/IUTIII/Corollary312/StepXI/HolomorphicHull/Volume.lean',
    'LeanFormal/IUT/IUTIII/Corollary312/StepXI/ThetaPacketBridge.lean',
    'LeanFormal/IUT/IUTIII/Corollary312/StepXI/FiniteCertificateBridge.lean',
    'LeanFormal/IUT/IUTIII/Corollary312/Routes.lean',
    'LeanFormal/IUT/IUTIV/Estimates/Section1.lean',
    'LeanFormal/IUT/IUTIV/Estimates/Section2.lean',
    'LeanFormal/IUT/ABCBridge/Statement.lean',
    'LeanFormal/IUT/ABCBridge/Arithmetic/PrimitiveTriple.lean',
    'LeanFormal/IUT/ABCBridge/Bridge/IUTToABC.lean',
    'LeanFormal/IUT/Project.lean'
  )
)

$repoRoot = Split-Path -Parent $PSScriptRoot
$runStamp = Get-Date -Format 'yyyyMMdd-HHmmss'
$runRoot = Join-Path $repoRoot "logs\lean\serial-$runStamp"
New-Item -ItemType Directory -Force -Path $runRoot | Out-Null
$lakePath = (Get-Command lake -ErrorAction Stop).Source
$results = [System.Collections.Generic.List[object]]::new()

foreach ($module in $Modules) {
  $safeName = ($module -replace '[\\/:]', '_') -replace '\.lean$', ''
  $stdoutPath = Join-Path $runRoot "$safeName.stdout.log"
  $stderrPath = Join-Path $runRoot "$safeName.stderr.log"
  $oleanRelative = ($module -replace '/', '\') -replace '\.lean$', '.olean'
  $oleanPath = Join-Path $repoRoot (Join-Path '.lake\build\lib\lean' $oleanRelative)
  New-Item -ItemType Directory -Force -Path (Split-Path -Parent $oleanPath) | Out-Null
  $started = Get-Date
  # Keep elaboration deterministic and avoid competing with the editor's
  # background workers for Mathlib cache locks.
  & $lakePath env lean -j 1 $module -o $oleanPath 1> $stdoutPath 2> $stderrPath
  $exitCode = $LASTEXITCODE
  $finished = Get-Date
  $result = [pscustomobject]@{
    module = $module
    started = $started.ToString('o')
    finished = $finished.ToString('o')
    exitCode = $exitCode
    stdout = $stdoutPath
    stderr = $stderrPath
  }
  $results.Add($result)
  $result | ConvertTo-Json -Compress
  if ($exitCode -ne 0) {
    Write-Warning "module failed: $module"
  }
}

$summaryPath = Join-Path $runRoot 'summary.json'
$results | ConvertTo-Json -Depth 4 | Set-Content -Encoding UTF8 $summaryPath
Write-Output "summary=$summaryPath"
if (($results | Where-Object { $_.exitCode -ne 0 }).Count -gt 0) { exit 1 }
exit 0
