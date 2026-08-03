param(
  [string[]]$LakeArguments = @('build', 'LeanFormal')
)

$repoRoot = Split-Path -Parent $PSScriptRoot
$logRoot = Join-Path $repoRoot 'logs\lean'
New-Item -ItemType Directory -Force -Path $logRoot | Out-Null

$stamp = Get-Date -Format 'yyyyMMdd-HHmmss'
$stdoutPath = Join-Path $logRoot "run-$stamp.stdout.log"
$stderrPath = Join-Path $logRoot "run-$stamp.stderr.log"
$statusPath = Join-Path $logRoot "run-$stamp.status.json"
$lakePath = (Get-Command lake -ErrorAction Stop).Source

$started = Get-Date
& $lakePath @LakeArguments 1> $stdoutPath 2> $stderrPath
$exitCode = $LASTEXITCODE
$finished = Get-Date

[pscustomobject]@{
  command = ($lakePath + ' ' + ($LakeArguments -join ' '))
  started = $started.ToString('o')
  finished = $finished.ToString('o')
  exitCode = $exitCode
  stdout = $stdoutPath
  stderr = $stderrPath
} | ConvertTo-Json | Set-Content -Encoding UTF8 $statusPath

Write-Output (Get-Content -Raw $statusPath)
exit $exitCode
