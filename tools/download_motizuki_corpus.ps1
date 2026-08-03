param(
  [string]$Workspace = (Get-Location).Path
)

$ErrorActionPreference = 'Stop'
$baseUri = [Uri]'https://www.kurims.kyoto-u.ac.jp/~motizuki/'
$entryPages = @(
  'papers-japanese.html',
  'top-japanese.html',
  'CV-japanese.html',
  'students-japanese.html',
  'thoughts-japanese.html',
  'news-japanese.html',
  'research-japanese.html',
  'travel-japanese.html'
)

$root = Join-Path $Workspace 'papers\motizuki_corpus'
$raw = Join-Path $root 'raw'
$pages = Join-Path $root 'pages'
New-Item -ItemType Directory -Force -Path $raw,$pages | Out-Null

$pageRows = [System.Collections.Generic.List[object]]::new()
$pdfRows = [System.Collections.Generic.List[object]]::new()

foreach ($entry in $entryPages) {
  $pageUri = [Uri]::new($baseUri, $entry)
  $pagePath = Join-Path $pages $entry
  try {
    $response = Invoke-WebRequest -Uri $pageUri.AbsoluteUri
    [IO.File]::WriteAllText($pagePath, $response.Content, [Text.Encoding]::UTF8)
    $pageRows.Add([pscustomobject]@{
      page = $entry
      url = $pageUri.AbsoluteUri
      status = $response.StatusCode
      bytes = (Get-Item -LiteralPath $pagePath).Length
    })
  } catch {
    $pageRows.Add([pscustomobject]@{
      page = $entry
      url = $pageUri.AbsoluteUri
      status = 'error'
      bytes = 0
    })
  }
}

$allPdfLinks = [System.Collections.Generic.HashSet[string]]::new([StringComparer]::OrdinalIgnoreCase)
foreach ($entry in $entryPages) {
  $pagePath = Join-Path $pages $entry
  if (-not (Test-Path -LiteralPath $pagePath)) { continue }
  $html = Get-Content -Raw -LiteralPath $pagePath
  $matches = [regex]::Matches($html, '(?i)(?:href\s*=\s*["''])([^"'']+\.pdf)(?:["''])')
  foreach ($match in $matches) {
    $href = $match.Groups[1].Value
    try {
      $pdfUri = [Uri]::new($baseUri, $href)
      [void]$allPdfLinks.Add($pdfUri.AbsoluteUri)
    } catch { }
  }
}

foreach ($pdfUriText in ($allPdfLinks | Sort-Object)) {
  $pdfUri = [Uri]$pdfUriText
  $fileName = [IO.Path]::GetFileName([Uri]::UnescapeDataString($pdfUri.AbsolutePath))
  if ([string]::IsNullOrWhiteSpace($fileName)) { continue }
  $filePath = Join-Path $raw $fileName
  $status = 'downloaded'
  try {
    if (-not (Test-Path -LiteralPath $filePath)) {
      Invoke-WebRequest -Uri $pdfUri.AbsoluteUri -OutFile $filePath
    } else {
      $status = 'already-present'
    }
    $hash = (Get-FileHash -Algorithm SHA256 -LiteralPath $filePath).Hash
    $bytes = (Get-Item -LiteralPath $filePath).Length
  } catch {
    $status = 'error'
    $hash = ''
    $bytes = 0
  }
  $pdfRows.Add([pscustomobject]@{
    file = $fileName
    url = $pdfUri.AbsoluteUri
    status = $status
    bytes = $bytes
    sha256 = $hash
  })
}

$pageRows | Export-Csv -NoTypeInformation -Encoding UTF8 -LiteralPath (Join-Path $root 'pages.csv')
$pdfRows | Export-Csv -NoTypeInformation -Encoding UTF8 -LiteralPath (Join-Path $root 'pdfs.csv')
Write-Output ("pages={0} unique_pdfs={1} downloaded_root={2}" -f $pageRows.Count, $pdfRows.Count, $root)
