$repoRoot = Split-Path -Parent $PSScriptRoot
$runStamp = Get-Date -Format 'yyyyMMdd-HHmmss'
$runRoot = Join-Path $repoRoot "logs\lean\abc-$runStamp"
New-Item -ItemType Directory -Force -Path $runRoot | Out-Null
$lakePath = (Get-Command lake -ErrorAction Stop).Source
$checks = @(
  [pscustomobject]@{ name = 'without-sorry'; file = 'verification/abc_without_sorry.lean'; expectedExit = 1 },
  [pscustomobject]@{ name = 'with-sorry'; file = 'verification/abc_with_sorry.lean'; expectedExit = 0 }
)
$results = [System.Collections.Generic.List[object]]::new()

foreach ($check in $checks) {
  $stdoutPath = Join-Path $runRoot "$($check.name).stdout.log"
  $stderrPath = Join-Path $runRoot "$($check.name).stderr.log"
  $started = Get-Date
  & $lakePath env lean $check.file 1> $stdoutPath 2> $stderrPath
  $exitCode = $LASTEXITCODE
  $finished = Get-Date
  $results.Add([pscustomobject]@{
    name = $check.name
    file = $check.file
    expectedExit = $check.expectedExit
    exitCode = $exitCode
    expectationMet = ($exitCode -eq $check.expectedExit)
    started = $started.ToString('o')
    finished = $finished.ToString('o')
    stdout = $stdoutPath
    stderr = $stderrPath
  })
}

$summaryPath = Join-Path $runRoot 'summary.json'
$results | ConvertTo-Json -Depth 4 | Set-Content -Encoding UTF8 $summaryPath
Write-Output "summary=$summaryPath"
if (($results | Where-Object { -not $_.expectationMet }).Count -gt 0) { exit 1 }
exit 0
