param()

$ErrorActionPreference = 'Stop'

& (Join-Path $PSScriptRoot 'verify-formal.ps1')
if ($LASTEXITCODE -ne 0) { throw 'Formal verification script failed.' }

& (Join-Path $PSScriptRoot 'build-paper.ps1')
if ($LASTEXITCODE -ne 0) { throw 'Paper build script failed.' }

Write-Output 'Repository verification completed successfully.'
