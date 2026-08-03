param(
  [string]$OutputRoot = "logs/source-audit"
)

$ErrorActionPreference = "Stop"

$runId = Get-Date -Format "yyyyMMdd-HHmmss"
$runDirectory = Join-Path $OutputRoot "run-$runId"
New-Item -ItemType Directory -Force -Path $runDirectory | Out-Null

$sources = @(
  [pscustomobject]@{
    path = "papers/motizuki_corpus/raw/Inter-universal Teichmuller Theory III.pdf"
    expectedSha256 = "9A7EE3C77B1C7717210C0613EB39B6844649D0040DC3D9E1BE7D544F8F91A0B9"
  },
  [pscustomobject]@{
    path = "papers/motizuki_corpus/raw/Semi-graphs of Anabelioids.pdf"
    expectedSha256 = "DCC05B22FF858AF670C9346CA7A483D4D9B640DF5561EC0E82C27314A2416892"
  }
)

$textFiles = @(
  [pscustomobject]@{
    path = "papers/motizuki_corpus/text/pagewise/Inter-universal Teichmuller Theory III.pagewise.plain.txt"
    expectedPages = 199
  },
  [pscustomobject]@{
    path = "papers/motizuki_corpus/text/pagewise/Inter-universal Teichmuller Theory III.pagewise.layout.txt"
    expectedPages = 199
  },
  [pscustomobject]@{
    path = "papers/motizuki_corpus/text/pagewise/Semi-graphs of Anabelioids.pagewise.plain.txt"
    expectedPages = 92
  },
  [pscustomobject]@{
    path = "papers/motizuki_corpus/text/pagewise/Semi-graphs of Anabelioids.pagewise.layout.txt"
    expectedPages = 92
  },
  [pscustomobject]@{
    path = "papers/motizuki_corpus/text/source_audit/IUTIII_Theorem311_pp153-159_Corollary312_pp173-186.plain.txt"
    expectedPages = 21
  },
  [pscustomobject]@{
    path = "papers/motizuki_corpus/text/source_audit/IUTIII_Theorem311_pp153-159_Corollary312_pp173-186.layout.txt"
    expectedPages = 21
  },
  [pscustomobject]@{
    path = "papers/motizuki_corpus/text/source_audit/IUTIII_Theorem311_through_Corollary312_pp153-186.plain.txt"
    expectedPages = 34
  },
  [pscustomobject]@{
    path = "papers/motizuki_corpus/text/source_audit/IUTIII_Theorem311_through_Corollary312_pp153-186.layout.txt"
    expectedPages = 34
  },
  [pscustomobject]@{
    path = "papers/motizuki_corpus/text/source_audit/SemiGraphs_Definition_pp11-12_Corollary17_p20_Proposition36_pp37-40.plain.txt"
    expectedPages = 7
  },
  [pscustomobject]@{
    path = "papers/motizuki_corpus/text/source_audit/SemiGraphs_Definition_pp11-12_Corollary17_p20_Proposition36_pp37-40.layout.txt"
    expectedPages = 7
  }
)

$sourceResults = foreach ($source in $sources) {
  $actualSha256 = (Get-FileHash -Algorithm SHA256 -LiteralPath $source.path).Hash
  [pscustomobject]@{
    path = $source.path
    expectedSha256 = $source.expectedSha256
    actualSha256 = $actualSha256
    passed = $actualSha256 -eq $source.expectedSha256
  }
}

$textResults = foreach ($textFile in $textFiles) {
  $pageMarkers = (Select-String -LiteralPath $textFile.path -Pattern '^===== PDF PHYSICAL PAGE [0-9]+ =====$').Count
  [pscustomobject]@{
    path = $textFile.path
    expectedPages = $textFile.expectedPages
    actualPageMarkers = $pageMarkers
    passed = $pageMarkers -eq $textFile.expectedPages
  }
}

$passed =
  ($sourceResults | Where-Object { -not $_.passed }).Count -eq 0 -and
  ($textResults | Where-Object { -not $_.passed }).Count -eq 0

$summary = [pscustomobject]@{
  runId = $runId
  purpose = "Source hash and page-delimited text reproducibility only"
  mathematicalProofClaim = $false
  passed = $passed
  sources = $sourceResults
  textFiles = $textResults
}

$summaryPath = Join-Path $runDirectory "summary.json"
$summary | ConvertTo-Json -Depth 5 | Set-Content -Encoding UTF8 -LiteralPath $summaryPath
$summary | ConvertTo-Json -Depth 5

if (-not $passed) {
  exit 1
}
