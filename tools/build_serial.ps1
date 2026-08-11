[CmdletBinding()]
param(
  [Parameter(Mandatory = $true, Position = 0)]
  [string[]]$Module,
  [switch]$Force
)

$ErrorActionPreference = 'Stop'
$workspace = (Get-Location).Path
$buildRoot = Join-Path $workspace '.lake/build/lib/lean'

# The source roots mirror the package names used by LEAN_PATH.  Package
# modules are visited only when their cached olean is absent or stale.
$sourceRoots = @(
  # Project-qualified module names (for example LeanFormal.IUT...) are
  # rooted at the workspace itself.
  $workspace,
  (Join-Path $workspace 'LeanFormal'),
  (Join-Path $workspace 'Iut'),
  (Join-Path $workspace '.lake/packages/mathlib'),
  (Join-Path $workspace '.lake/packages/batteries'),
  (Join-Path $workspace '.lake/packages/aesop'),
  (Join-Path $workspace '.lake/packages/Qq'),
  (Join-Path $workspace '.lake/packages/proofwidgets'),
  (Join-Path $workspace '.lake/packages/importGraph'),
  (Join-Path $workspace '.lake/packages/LeanSearchClient'),
  (Join-Path $workspace '.lake/packages/plausible'),
  (Join-Path $workspace '.lake/packages/Cli')
)

$packageBuildRoots = @(
  (Join-Path $workspace '.lake/build/lib/lean'),
  (Join-Path $workspace '.lake/packages/mathlib/.lake/build/lib/lean'),
  (Join-Path $workspace '.lake/packages/batteries/.lake/build/lib/lean'),
  (Join-Path $workspace '.lake/packages/aesop/.lake/build/lib/lean'),
  (Join-Path $workspace '.lake/packages/Qq/.lake/build/lib/lean'),
  (Join-Path $workspace '.lake/packages/proofwidgets/.lake/build/lib/lean'),
  (Join-Path $workspace '.lake/packages/importGraph/.lake/build/lib/lean'),
  (Join-Path $workspace '.lake/packages/LeanSearchClient/.lake/build/lib/lean'),
  (Join-Path $workspace '.lake/packages/plausible/.lake/build/lib/lean'),
  (Join-Path $workspace '.lake/packages/Cli/.lake/build/lib/lean'),
  'c:\Users\Administrator\.elan\toolchains\leanprover--lean4---v4.32.2\lib\lean'
)

function Get-RelativeModulePath([string]$name) {
  return ($name -replace '\.', [IO.Path]::DirectorySeparatorChar) + '.lean'
}

function Resolve-Source([string]$name) {
  $relative = Get-RelativeModulePath $name
  foreach ($root in $sourceRoots) {
    $candidate = Join-Path $root $relative
    if (Test-Path -LiteralPath $candidate -PathType Leaf) {
      return (Resolve-Path -LiteralPath $candidate).Path
    }
  }
  return $null
}

function Get-BuildRootForSource([string]$source) {
  if ([string]::IsNullOrWhiteSpace($source)) {
    return $buildRoot
  }

  $normalized = $source.Replace('/', '\')
  $packageRoots = @{
    (Join-Path $workspace '.lake\packages\mathlib') = (Join-Path $workspace '.lake\packages\mathlib\.lake\build\lib\lean')
    (Join-Path $workspace '.lake\packages\batteries') = (Join-Path $workspace '.lake\packages\batteries\.lake\build\lib\lean')
    (Join-Path $workspace '.lake\packages\aesop') = (Join-Path $workspace '.lake\packages\aesop\.lake\build\lib\lean')
    (Join-Path $workspace '.lake\packages\Qq') = (Join-Path $workspace '.lake\packages\Qq\.lake\build\lib\lean')
    (Join-Path $workspace '.lake\packages\proofwidgets') = (Join-Path $workspace '.lake\packages\proofwidgets\.lake\build\lib\lean')
    (Join-Path $workspace '.lake\packages\importGraph') = (Join-Path $workspace '.lake\packages\importGraph\.lake\build\lib\lean')
    (Join-Path $workspace '.lake\packages\LeanSearchClient') = (Join-Path $workspace '.lake\packages\LeanSearchClient\.lake\build\lib\lean')
    (Join-Path $workspace '.lake\packages\plausible') = (Join-Path $workspace '.lake\packages\plausible\.lake\build\lib\lean')
    (Join-Path $workspace '.lake\packages\Cli') = (Join-Path $workspace '.lake\packages\Cli\.lake\build\lib\lean')
  }
  foreach ($packageSource in $packageRoots.Keys) {
    $prefix = ((Resolve-Path -LiteralPath $packageSource).Path).Replace('/', '\') + '\'
    if ($normalized.StartsWith($prefix, [System.StringComparison]::OrdinalIgnoreCase)) {
      return $packageRoots[$packageSource]
    }
  }
  return $buildRoot
}

function Resolve-Olean([string]$name, [string]$source = $null) {
  $relative = ($name -replace '\.', [IO.Path]::DirectorySeparatorChar) + '.olean'
  if (-not [string]::IsNullOrWhiteSpace($source)) {
    $expectedRoot = Get-BuildRootForSource $source
    $expected = Join-Path $expectedRoot $relative
    if (Test-Path -LiteralPath $expected -PathType Leaf) {
      return (Resolve-Path -LiteralPath $expected).Path
    }
    # A package source must be rebuilt in its package-local output tree.  Do
    # not mistake a same-named project-root object for a valid cache entry.
    if ($expectedRoot -ne $buildRoot) {
      return $null
    }
  }
  foreach ($root in $packageBuildRoots) {
    $candidate = Join-Path $root $relative
    if (Test-Path -LiteralPath $candidate -PathType Leaf) {
      return (Resolve-Path -LiteralPath $candidate).Path
    }
  }
  return $null
}

function Get-Imports([string]$source) {
  $imports = New-Object System.Collections.Generic.List[string]
  $commentDepth = 0
  foreach ($line in (Get-Content -LiteralPath $source)) {
    # Mathlib documentation contains nested `/- ... -/` examples.  Count
    # comment depth instead of using a boolean so imports in those examples
    # never enter the dependency graph.
    $trimmed = $line.TrimStart()
    if ($commentDepth -eq 0 -and $trimmed -notmatch '^--' -and
        $line -cmatch '^\s*(?:(?:public|private)\s+)?import\s+([A-Z][A-Za-z0-9_]*(?:\.[A-Za-z0-9_]+)*)') {
      $imports.Add($Matches[1])
    }
    $opens = ([regex]::Matches($line, '/-')).Count
    $closes = ([regex]::Matches($line, '-/')).Count
    $commentDepth = [Math]::Max(0, $commentDepth + $opens - $closes)
  }
  return $imports
}

function Needs-Build([string]$source, [string]$olean) {
  if ([string]::IsNullOrWhiteSpace($source)) { return $false }
  if ($Force -or [string]::IsNullOrWhiteSpace($olean)) { return $true }
  return (Get-Item -LiteralPath $source).LastWriteTimeUtc -gt
    (Get-Item -LiteralPath $olean).LastWriteTimeUtc
}

$visitState = @{}
$order = New-Object System.Collections.Generic.List[string]

function Visit([string]$name) {
  if ($visitState.ContainsKey($name)) {
    if ($visitState[$name] -eq 'visiting') {
      throw "Import cycle encountered at $name"
    }
    return
  }

  $source = Resolve-Source $name
  $olean = Resolve-Olean $name $source
  if ($null -eq $source) {
    if ($null -ne $olean) {
      $visitState[$name] = 'done'
      return
    }
    throw "Cannot resolve source or olean for module $name"
  }

  # A current cached object is a dependency boundary.  Do not walk into the
  # package's source graph (Mathlib has intentional import cycles through its
  # generated root modules) when no rebuild is needed.
  if (-not $Force -and $null -ne $olean -and
      (Get-Item -LiteralPath $olean).LastWriteTimeUtc -ge
      (Get-Item -LiteralPath $source).LastWriteTimeUtc) {
    $visitState[$name] = 'done'
    return
  }

  $visitState[$name] = 'visiting'
  foreach ($import in (Get-Imports $source)) {
    Visit $import
  }
  $visitState[$name] = 'done'
  $order.Add($name)
}

foreach ($target in $Module) {
  Visit $target
}

$total = $order.Count
$number = 0
foreach ($name in $order) {
  $number++
  $source = Resolve-Source $name
  $olean = Resolve-Olean $name $source
  if ([string]::IsNullOrWhiteSpace($source) -and -not [string]::IsNullOrWhiteSpace($olean)) {
    Write-Host ("[{0}/{1}] reused {2}" -f $number, $total, $name)
    continue
  }
  if (-not (Needs-Build $source $olean)) {
    Write-Host ("[{0}/{1}] reused {2}" -f $number, $total, $name)
    continue
  }

  $relative = ($name -replace '\.', [IO.Path]::DirectorySeparatorChar) + '.olean'
  $output = Join-Path (Get-BuildRootForSource $source) $relative
  $outputDirectory = Split-Path -Parent $output
  New-Item -ItemType Directory -Force -Path $outputDirectory | Out-Null
  Write-Host ("[{0}/{1}] building {2}" -f $number, $total, $name)
  & lake env lean $source -o $output
  if ($LASTEXITCODE -ne 0) {
    throw "Serial build failed at $name (exit code $LASTEXITCODE)"
  }
}

Write-Host ("Serial build completed successfully ({0} modules)." -f $total)
