$repoRoot = Split-Path -Parent $PSScriptRoot
$runStamp = Get-Date -Format 'yyyyMMdd-HHmmss'
$runRoot = Join-Path $repoRoot "logs\lean\axioms-$runStamp"
New-Item -ItemType Directory -Force -Path $runRoot | Out-Null
$lakePath = (Get-Command lake -ErrorAction Stop).Source
$stdoutPath = Join-Path $runRoot 'axiom_audit.stdout.log'
$stderrPath = Join-Path $runRoot 'axiom_audit.stderr.log'
$started = Get-Date
& $lakePath env lean -j 1 verification/axiom_audit.lean 1> $stdoutPath 2> $stderrPath
$exitCode = $LASTEXITCODE
$finished = Get-Date
$status = [pscustomobject]@{
  command = "$lakePath env lean -j 1 verification/axiom_audit.lean"
  started = $started.ToString('o')
  finished = $finished.ToString('o')
  exitCode = $exitCode
  stdout = $stdoutPath
  stderr = $stderrPath
}
$statusPath = Join-Path $runRoot 'status.json'
$status | ConvertTo-Json | Set-Content -Encoding UTF8 $statusPath
Write-Output (Get-Content -Raw $statusPath)
exit $exitCode
