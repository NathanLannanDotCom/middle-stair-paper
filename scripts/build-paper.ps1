param(
    [switch]$NoDownload
)

$ErrorActionPreference = 'Stop'
$root = [System.IO.Path]::GetFullPath((Join-Path $PSScriptRoot '..'))
$paperDir = [System.IO.Path]::GetFullPath((Join-Path $root 'paper'))
$outputDir = [System.IO.Path]::GetFullPath((Join-Path $root 'output\pdf'))
$buildDir = [System.IO.Path]::GetFullPath((Join-Path $root 'tmp\pdfs\build'))
$toolDir = [System.IO.Path]::GetFullPath((Join-Path $root '.tools\tectonic-0.16.9'))

foreach ($path in @($paperDir, $outputDir, $buildDir, $toolDir)) {
    if (-not $path.StartsWith($root, [System.StringComparison]::OrdinalIgnoreCase)) {
        throw "Path escaped repository root: $path"
    }
}

New-Item -ItemType Directory -Force -Path $outputDir, $buildDir | Out-Null

$tectonicCommand = Get-Command tectonic -ErrorAction SilentlyContinue
if ($tectonicCommand) {
    $tectonic = $tectonicCommand.Source
} else {
    $tectonic = Join-Path $toolDir 'tectonic.exe'
    if (-not (Test-Path -LiteralPath $tectonic)) {
        if ($NoDownload) {
            throw 'Tectonic is unavailable and -NoDownload was requested.'
        }

        New-Item -ItemType Directory -Force -Path $toolDir | Out-Null
        $zip = Join-Path $buildDir 'tectonic-0.16.9-windows-msvc.zip'
        $url = 'https://github.com/tectonic-typesetting/tectonic/releases/download/tectonic%400.16.9/tectonic-0.16.9-x86_64-pc-windows-msvc.zip'
        Write-Output 'Downloading pinned Tectonic 0.16.9 from its official GitHub release...'
        Invoke-WebRequest -Uri $url -OutFile $zip
        Expand-Archive -LiteralPath $zip -DestinationPath $toolDir -Force

        if (-not (Test-Path -LiteralPath $tectonic)) {
            $found = Get-ChildItem -LiteralPath $toolDir -Recurse -File -Filter 'tectonic.exe' |
                Select-Object -First 1
            if (-not $found) { throw 'The Tectonic archive did not contain tectonic.exe.' }
            Copy-Item -LiteralPath $found.FullName -Destination $tectonic
        }
    }
}

Push-Location $paperDir
try {
    & $tectonic --keep-logs --keep-intermediates --outdir $buildDir main.tex
    if ($LASTEXITCODE -ne 0) { throw "Tectonic failed with exit code $LASTEXITCODE" }
} finally {
    Pop-Location
}

$builtPdf = Join-Path $buildDir 'main.pdf'
$finalPdf = Join-Path $outputDir 'middle-stair.pdf'
if (-not (Test-Path -LiteralPath $builtPdf)) {
    throw "Expected PDF was not created: $builtPdf"
}
Copy-Item -LiteralPath $builtPdf -Destination $finalPdf -Force
Write-Output "Paper built successfully: $finalPdf"
