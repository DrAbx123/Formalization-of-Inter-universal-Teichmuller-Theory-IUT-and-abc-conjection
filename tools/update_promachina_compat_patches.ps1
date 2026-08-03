param(
  [string]$SnapshotName = '0d52e0fd5b53',
  [string]$TargetVersion = '4.32.2'
)

$repoRoot = Split-Path -Parent $PSScriptRoot
$vendorRoot = Join-Path $repoRoot 'vendor\promachina'
$snapshotRoot = Join-Path $vendorRoot ("snapshots\$SnapshotName")
$manifestPath = Join-Path $snapshotRoot 'LEANFORMAL_SNAPSHOT_MANIFEST.json'
$sourceRegisterPath = Join-Path $vendorRoot 'semigraph-residual-separation-source.json'
$patchRoot = Join-Path $vendorRoot ("patches\$TargetVersion")
$gitPath = (Get-Command git -ErrorAction Stop).Source

if (-not (Test-Path -LiteralPath $manifestPath)) {
  throw "Snapshot manifest not found: $manifestPath"
}
if (-not (Test-Path -LiteralPath $sourceRegisterPath)) {
  throw "Source register not found: $sourceRegisterPath"
}

$snapshot = Get-Content -Raw -LiteralPath $manifestPath | ConvertFrom-Json
$register = Get-Content -Raw -LiteralPath $sourceRegisterPath | ConvertFrom-Json
if (-not $snapshot.commit.StartsWith($SnapshotName)) {
  throw "Snapshot directory $SnapshotName does not match commit $($snapshot.commit)."
}

New-Item -ItemType Directory -Force -Path $patchRoot | Out-Null
$results = [System.Collections.Generic.List[object]]::new()

foreach ($entry in $register.files) {
  $relativePath = $entry.relativePath -replace '/', '\'
  $sourcePath = Join-Path $snapshotRoot $relativePath
  $targetPath = Join-Path $repoRoot $relativePath
  if (-not (Test-Path -LiteralPath $sourcePath)) {
    throw "Snapshot source missing: $sourcePath"
  }
  if (-not (Test-Path -LiteralPath $targetPath)) {
    throw "Production target missing: $targetPath"
  }

  $sourceHash = (Get-FileHash -Algorithm SHA256 -LiteralPath $sourcePath).Hash
  $targetHash = (Get-FileHash -Algorithm SHA256 -LiteralPath $targetPath).Hash
  if ($sourceHash -eq $targetHash) {
    $results.Add([pscustomobject]@{
      module = $entry.module
      status = 'identical'
      sourceSha256 = $sourceHash
      targetSha256 = $targetHash
      patch = $null
    })
    continue
  }

  $sourceRelative =
    ([IO.Path]::GetRelativePath($repoRoot, $sourcePath) -replace '\\', '/')
  $targetRelative =
    ([IO.Path]::GetRelativePath($repoRoot, $targetPath) -replace '\\', '/')
  $process = [Diagnostics.Process]::new()
  $process.StartInfo = [Diagnostics.ProcessStartInfo]::new()
  $process.StartInfo.FileName = $gitPath
  $process.StartInfo.WorkingDirectory = $repoRoot
  $process.StartInfo.UseShellExecute = $false
  $process.StartInfo.RedirectStandardOutput = $true
  $process.StartInfo.RedirectStandardError = $true
  foreach ($argument in @(
      'diff', '--no-index', '--binary', '--', $sourceRelative, $targetRelative)) {
    $process.StartInfo.ArgumentList.Add($argument)
  }
  if (-not $process.Start()) {
    throw "Failed to start git diff for $relativePath."
  }
  $diff = $process.StandardOutput.ReadToEnd()
  $diagnostics = $process.StandardError.ReadToEnd()
  $process.WaitForExit()
  if ($process.ExitCode -ne 1) {
    throw "git diff failed for $relativePath (exit $($process.ExitCode)): $diagnostics"
  }

  $patchName = ([IO.Path]::GetFileNameWithoutExtension($relativePath)) + '.patch'
  $patchPath = Join-Path $patchRoot $patchName
  [IO.File]::WriteAllText($patchPath, $diff, [Text.UTF8Encoding]::new($false))
  $results.Add([pscustomobject]@{
    module = $entry.module
    status = 'patched'
    sourceSha256 = $sourceHash
    targetSha256 = $targetHash
    patch = ([IO.Path]::GetRelativePath($repoRoot, $patchPath) -replace '\\', '/')
  })
}

$summary = [pscustomobject]@{
  repository = $snapshot.repository
  sourceCommit = $snapshot.commit
  targetVersion = $TargetVersion
  generatedAt = (Get-Date).ToString('o')
  changedFiles = @($results | Where-Object status -eq 'patched').Count
  identicalFiles = @($results | Where-Object status -eq 'identical').Count
  files = $results
}
$summaryJson = $summary | ConvertTo-Json -Depth 5
$patchManifestPath = Join-Path $patchRoot 'MANIFEST.json'
[IO.File]::WriteAllText(
  $patchManifestPath, $summaryJson + [Environment]::NewLine,
  [Text.UTF8Encoding]::new($false))
$summaryJson
