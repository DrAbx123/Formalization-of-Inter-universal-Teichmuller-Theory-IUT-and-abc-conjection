$repoRoot = Split-Path -Parent $PSScriptRoot
$auditScript = Join-Path $PSScriptRoot 'run_axiom_audit_logged.ps1'

$auditJson = & $auditScript | ConvertFrom-Json
if ($auditJson.exitCode -ne 0) {
  Write-Error "axiom audit failed with exit code $($auditJson.exitCode)"
  exit 1
}

$stdout = Get-Content -Raw -LiteralPath $auditJson.stdout
$sorryLines = @($stdout -split "`r?`n" | Where-Object { $_ -match 'sorryAx' })

if ($sorryLines.Count -ne 0) {
  Write-Error "unexpected production sorryAx boundary:`n$($sorryLines -join "`n")"
  exit 1
}

[pscustomobject]@{
  audit = $auditJson
  sorryAxLines = $sorryLines.Count
  boundaryPassed = $true
} | ConvertTo-Json -Depth 6
exit 0
