param(
    [switch]$SkipCache
)

$ErrorActionPreference = 'Stop'
$root = [System.IO.Path]::GetFullPath((Join-Path $PSScriptRoot '..'))
$formal = [System.IO.Path]::GetFullPath((Join-Path $root 'formal'))

if (-not $formal.StartsWith($root, [System.StringComparison]::OrdinalIgnoreCase)) {
    throw "Formal directory escaped repository root: $formal"
}

$lakeCommand = Get-Command lake -ErrorAction SilentlyContinue
if ($lakeCommand) {
    $lake = $lakeCommand.Source
} else {
    $lake = Join-Path $HOME '.elan\bin\lake.exe'
    if (-not (Test-Path -LiteralPath $lake)) {
        throw 'Lake was not found on PATH or under $HOME\.elan\bin.'
    }
}

Push-Location $formal
try {
    if (-not $SkipCache) {
        # Use mathlib's signed release cache when available. A cache failure is
        # an optimization failure, not a proof failure; Lake can still build.
        & $lake exe cache get
        if ($LASTEXITCODE -ne 0) {
            Write-Warning 'mathlib cache download failed; continuing with a source build.'
        }
    }

    & $lake -KmaxJobs=1 build
    if ($LASTEXITCODE -ne 0) { throw "lake build failed with exit code $LASTEXITCODE" }

    $axiomLines = @(& $lake env lean AxiomAudit.lean 2>&1)
    $axiomExitCode = $LASTEXITCODE
    $axiomLines | ForEach-Object { Write-Output $_ }
    if ($axiomExitCode -ne 0) {
        throw "axiom audit failed with exit code $axiomExitCode"
    }

    $axiomText = $axiomLines -join [System.Environment]::NewLine
    $groups = [System.Text.RegularExpressions.Regex]::Matches(
        $axiomText,
        'depends on axioms:\s*\[([^]]*)\]',
        [System.Text.RegularExpressions.RegexOptions]::Singleline
    )
    if ($groups.Count -eq 0) {
        throw 'Could not parse the #print axioms output.'
    }

    $allowedAxioms = @('propext', 'Classical.choice', 'Quot.sound')
    $observedAxioms = @(
        foreach ($group in $groups) {
            foreach ($name in (($group.Groups[1].Value -replace "`r?`n", ' ') -split ',')) {
                $trimmed = $name.Trim()
                if ($trimmed) { $trimmed }
            }
        }
    ) | Sort-Object -Unique
    $unexpectedAxioms = @($observedAxioms | Where-Object { $_ -notin $allowedAxioms })
    if ($unexpectedAxioms.Count -ne 0) {
        throw "Unexpected axiom dependencies: $($unexpectedAxioms -join ', ')"
    }
} finally {
    Pop-Location
}

Write-Output 'Formal verification completed successfully.'
