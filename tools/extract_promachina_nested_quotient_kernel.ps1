param(
  [string]$SourceRoot = 'logs/upstream/promachina-iut-lean-581e2b89',
  [string]$Target = 'Iut/Foundations/SourceNestedNormalQuotientSystem.lean'
)

$repoRoot = Split-Path -Parent $PSScriptRoot
$sourceRelative = Join-Path -Path $SourceRoot `
  -ChildPath 'Iut/Foundations/SourceBadLocalArithmeticTemperedTower.lean'
$sourcePath = Join-Path $repoRoot $sourceRelative
$targetPath = Join-Path $repoRoot $Target
$expectedSha256 =
  'F0702536E68E4EF47BEAF606D6928D63E9BF885ABEF56F6B7E8818BA8997E77B'

if (-not (Test-Path -LiteralPath $sourcePath)) {
  throw "Audited source file not found: $sourcePath"
}
$actualSha256 = (Get-FileHash -Algorithm SHA256 -LiteralPath $sourcePath).Hash
if ($actualSha256 -ne $expectedSha256) {
  throw "Audited source hash changed: expected $expectedSha256, got $actualSha256"
}

$lines = Get-Content -LiteralPath $sourcePath
if ($lines.Count -lt 645) {
  throw "Audited source is too short: expected at least 645 lines."
}

# Source lines 511--610 contain the quotient system through continuity of the
# canonical map. Lines 620--645 contain its coordinate formula and injectivity.
$bodyLines = @($lines[510..609]) + @($lines[619..644])
$body = $bodyLines -join "`n"
$body = $body.Replace(
  "structure SourceNestedNormalQuotientSystem`n    (group : TopologicalGroupCat.{u}) where",
  "structure SourceNestedNormalQuotientSystem`n    (group : Type u) [Group group] [TopologicalSpace group]`n    [IsTopologicalGroup group] where")
$body = $body.Replace(
  "variable {group : TopologicalGroupCat.{u}}`nvariable (system : SourceNestedNormalQuotientSystem group)",
  "variable {group : Type u} [Group group] [TopologicalSpace group]`n  [IsTopologicalGroup group]`nvariable (system : SourceNestedNormalQuotientSystem group)")
$oldContinuityProof =
  "  simpa only [system.transition_mk refines] using`n" +
  "    (QuotientGroup.continuous_mk : Continuous`n" +
  "      (QuotientGroup.mk' (system.kernel coarser)))"
$newContinuityProof =
  "  rw [show (fun value : group =>`n" +
  "      system.transition refines`n" +
  "        (QuotientGroup.mk' (system.kernel finer) value)) =`n" +
  "      (QuotientGroup.mk : group -> system.Level coarser) by`n" +
  "    funext value`n" +
  "    exact system.transition_mk refines value]`n" +
  "  exact QuotientGroup.continuous_mk"
if (-not $body.Contains($oldContinuityProof)) {
  throw 'Continuity proof source block changed.'
}
$body = $body.Replace($oldContinuityProof, $newContinuityProof)

if ($body -notmatch 'structure SourceNestedNormalQuotientSystem' -or
    $body -notmatch 'theorem canonicalMap_injective' -or
    $body -match 'limitTopologicalGroup') {
  throw 'Extracted body failed its structural guard.'
}

$header = @'
/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors

Extracted from promachina/iut-lean@581e2b898b8429cbb696f75c4548e732d440650d.
The carrier was generalized from TopologicalGroupCat to an arbitrary
topological group; the source-specific topological-group wrapper was omitted.
-/
import Mathlib.Topology.Algebra.Group.Quotient

/-!
# Nested normal quotient systems

A decreasing sequence of normal subgroups defines a tower of quotient groups.
This module constructs its transition maps and compatible-family limit, then
proves that the canonical map into the limit is injective when the kernels
have trivial intersection.
-/

namespace Iut

universe u

'@

$footer = @'

end Iut
'@

New-Item -ItemType Directory -Force -Path (Split-Path -Parent $targetPath) |
  Out-Null
[IO.File]::WriteAllText(
  $targetPath, $header + $body + $footer + [Environment]::NewLine,
  [Text.UTF8Encoding]::new($false))

[pscustomobject]@{
  source = [IO.Path]::GetRelativePath($repoRoot, $sourcePath) -replace '\\', '/'
  sourceSha256 = $actualSha256
  sourceLines = @('511-610', '620-645')
  target = $Target -replace '\\', '/'
  targetSha256 = (Get-FileHash -Algorithm SHA256 -LiteralPath $targetPath).Hash
} | ConvertTo-Json
