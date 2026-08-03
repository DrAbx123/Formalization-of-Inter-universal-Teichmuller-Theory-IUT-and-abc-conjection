param(
  [string]$SourceRoot = "LeanFormal/IUT"
)

$repoRoot = Split-Path -Parent $PSScriptRoot
$root = Join-Path $repoRoot $SourceRoot
$violations = [System.Collections.Generic.List[object]]::new()

Get-ChildItem -LiteralPath $root -Recurse -Filter '*.lean' -File | ForEach-Object {
  $path = $_.FullName
  $lineNumber = 0
  Get-Content -LiteralPath $path | ForEach-Object {
    $lineNumber++
    if ($_ -match '^\s*(axiom|opaque)\s+[A-Za-z_][A-Za-z0-9_\.]*(\s|$)') {
      $violations.Add([pscustomobject]@{
        file = $path
        line = $lineNumber
        text = $_
      })
    }
  }
}

if ($violations.Count -ne 0) {
  $violations | ConvertTo-Json -Depth 4
  throw "Custom top-level axiom/opaque declarations found in production source."
}

[pscustomobject]@{
  sourceRoot = $root
  customAxiomDeclarations = 0
  checkedAt = (Get-Date).ToString('o')
} | ConvertTo-Json
exit 0
