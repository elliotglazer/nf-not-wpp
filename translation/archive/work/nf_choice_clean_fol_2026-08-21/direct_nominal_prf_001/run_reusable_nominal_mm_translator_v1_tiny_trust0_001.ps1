$ErrorActionPreference = 'Stop'

# Deferred trust-zero kernel check for the three-theorem real-source validation.
# This runner is append-only and was intentionally staged without being run.
$direct = (Resolve-Path -LiteralPath $PSScriptRoot).Path
$choice = (Resolve-Path -LiteralPath (Join-Path $direct '..')).Path
$sourceRoot = Join-Path $direct 'rmmv1e2e1'
$sourceResource = Join-Path $sourceRoot 'resource.json'
$sourceAudit = Join-Path $sourceRoot 'source_audit.json'
$e2eResource = Join-Path $direct 'reusable_nominal_mm_translator_v1_e2e_001\resource.json'
$alphaResource = Join-Path $direct 'a3848k1\resource.json'
$priorResource = Join-Path $direct 'wpp_chunk_007_008_compile_attempt_003\resource.json'
$outputRoot = Join-Path $direct 'rmmv1k1'
$lean = 'C:\Users\glaze\.elan\toolchains\leanprover--lean4---v4.30.0-rc2\bin\lean.exe'
$allowedAxioms = @('propext', 'Classical.choice', 'Quot.sound')

$pins = [ordered]@{
  sourceResource = 'A7E309822EC5455924D137472C2E7207D45413DB1B463E2452248D862984097E'
  sourceAudit = 'BBFF923E098A2CF74D81852FD77A87C53D4FE5293F824F61CC7521F6999E2183'
  e2eResource = 'CB3FB972EC085A3CC7F91C421E6BD583955B46C5EC7B844B63B1F17EDFC12DA0'
  alphaResource = '5299F0DA88C07150FCEBB96F2C04CC0DCDFF6C3FC48265C65BA407BC8DBC9FCA'
  priorResource = 'BD59FB0A8CDE1FF3D2DBB8AA580007638B3C39FC4B297AA7981D3435E5A0843B'
  lean = '5BEAD9B39D9A23306507FB59277995B94E71787D86D76A9ED3FB248B1ED3F995'
  exactSource = '868DF831E63E28AA924CC099510CD9E5D3BE18CD8416A20B335F5BBF3B42ED3F'
}

function Assert-Sha([string]$Path, [string]$Expected) {
  $actual = (Get-FileHash -Algorithm SHA256 -LiteralPath $Path).Hash
  if ($actual -ne $Expected) { throw "Pinned input mismatch: $Path $actual" }
}

if (Test-Path -LiteralPath $outputRoot) {
  throw "Refusing to overwrite append-only kernel output: $outputRoot"
}
foreach ($pair in @(
    @($sourceResource, $pins.sourceResource),
    @($sourceAudit, $pins.sourceAudit),
    @($e2eResource, $pins.e2eResource),
    @($alphaResource, $pins.alphaResource),
    @($priorResource, $pins.priorResource),
    @($lean, $pins.lean))) {
  Assert-Sha $pair[0] $pair[1]
}

$source = Get-Content -Raw -LiteralPath $sourceResource | ConvertFrom-Json
$audit = Get-Content -Raw -LiteralPath $sourceAudit | ConvertFrom-Json
$e2e = Get-Content -Raw -LiteralPath $e2eResource | ConvertFrom-Json
$alpha = Get-Content -Raw -LiteralPath $alphaResource | ConvertFrom-Json
$prior = Get-Content -Raw -LiteralPath $priorResource | ConvertFrom-Json

if ($source.status -ne 'PASS_SOURCE_ONLY_EMITTED_STRUCTURAL' -or
    $source.sourceSha256 -ne $pins.exactSource -or
    $source.endpoint -ne 'wppfiniteblocknotwppndv' -or
    [int]$source.startTheoremOrdinal -ne 1 -or [int]$source.endTheoremOrdinal -ne 3 -or
    [int]$source.theoremCount -ne 3 -or [int]$source.partCount -ne 3 -or
    [int]$source.genericDvFallbackCount -ne 0 -or
    @($source.forbiddenGeneratedSourceTokens).Count -ne 0) {
  throw 'Generated source boundary mismatch'
}
if ($audit.status -ne 'PASS_SOURCE_ONLY_EMITTED_STRUCTURAL' -or
    -not $audit.checks.metamathProofsVerified -or
    -not $audit.checks.allTheoremBodiesPartitionedByteExactly -or
    -not $audit.checks.allOversizedPartsAreSingletons -or
    -not $audit.checks.genericDvFallbackCountZero -or
    -not $audit.checks.forbiddenGeneratedTokensAbsent) {
  throw 'Generated source audit mismatch'
}
if ($e2e.status -ne 'PASS_SOURCE_ONLY_REAL_CANONICAL_INTERVAL' -or
    -not $e2e.checks.leanNotStarted -or -not $e2e.checks.byteExactTheoremStreamReconstruction) {
  throw 'End-to-end source-only validation mismatch'
}
if ($alpha.status -ne 'PASS_KERNEL_FIRST_USE_PREFIX_48_EXACT_THREE' -or
    [int]$alpha.firstUsePrefix.endOrdinal -ne 48 -or
    -not $alpha.audit.exactAllowedThreeAll) {
  throw 'Accepted trust-zero alpha frontier mismatch'
}
if ($prior.status -ne 'PASS' -or [int]$prior.prefixChunkCount -ne 8 -or
    [int]$prior.settings.trust -ne 0 -or [int]$prior.settings.threads -ne 1 -or
    [int64]$prior.settings.maxHeartbeats -ne 5000000) {
  throw 'Accepted trust-zero replay dependency mismatch'
}

$expectedParts = @(
  [ordered]@{ module = 'RmmTiny001Part001'; label = 'a1ii'; sha256 = '9C7C721318E9A662C98724A1DCA766594DFD94E01445E5229E10CB20187E2E6E' },
  [ordered]@{ module = 'RmmTiny001Part002'; label = 'mp2b'; sha256 = '5B2A4338991415E2A35C7315BDAF43F7C7FCE90340AB69C019AF2DCE0678BC4E' },
  [ordered]@{ module = 'RmmTiny001Part003'; label = 'a1i'; sha256 = 'DEBFAB14AC18DA94185F2DE1718D62E26438C0F427E5DECBA3AFE18356AA02DA' }
)
$jobs = @()
for ($index = 0; $index -lt $expectedParts.Count; $index++) {
  $expected = $expectedParts[$index]
  $part = $source.parts[$index]
  if ($part.module -ne $expected.module -or $part.lastLabel -ne $expected.label -or
      $part.sourceSha256 -ne $expected.sha256) {
    throw "Part boundary mismatch at index $index"
  }
  Assert-Sha ([string]$part.source) ([string]$expected.sha256)
  $jobs += [ordered]@{
    module = [string]$part.module
    source = [string]$part.source
    endpoint = 'NFChoice.DirectNominalPrf.WPPReplay.g_' + [string]$expected.label
  }
}
$umbrella = $source.umbrellaModule
if ($umbrella.module -ne 'RmmTiny001' -or
    $umbrella.sourceSha256 -ne 'A4443A38D57EEB656AADAEA59AB204BA00C77D33F622FF52421074EE192B0B1F') {
  throw 'Umbrella boundary mismatch'
}
Assert-Sha ([string]$umbrella.source) ([string]$umbrella.sourceSha256)
$jobs += [ordered]@{
  module = [string]$umbrella.module
  source = [string]$umbrella.source
  endpoint = 'NFChoice.DirectNominalPrf.WPPReplay.g_a1i'
}

$extraNames = @(
  'direct_certificate_005_nf_handlers_001\semantic_completeness_bridge_001\xp_audit_004',
  'direct_certificate_005_nf_handlers_001\semantic_completeness_bridge_001\audit_003',
  'direct_certificate_005_nf_handlers_001\bounded_nominal_attempt_004',
  'direct_certificate_005_nf_handlers_001\partial_total_attempt_002',
  'compiler\nf_compact_leaf_final_gate_001\audit_009',
  'compiler\nf_compact_leaf_endpoints_001\audit_002',
  'compiler\nf_compact_leaf_semantic_adapters_001\audit_004',
  'compiler\nf_compact_leaf_gate_001\audit_002',
  'df_leaf_semantics\nf_leaf_wrappers\audit_001',
  'nf6_kernel_001'
)
$leanPath = @($outputRoot, $sourceRoot)
$leanPath += @($source.alphaFrontier.oleanRoots)
$leanPath += @($extraNames | ForEach-Object { Join-Path $choice $_ })
$leanPath += @($prior.leanPath)
$leanPath = @($leanPath | Select-Object -Unique)
foreach ($path in $leanPath | Select-Object -Skip 1) {
  if (-not (Test-Path -LiteralPath $path)) { throw "Missing LEAN_PATH root: $path" }
}

New-Item -ItemType Directory -Path $outputRoot | Out-Null

function Invoke-KernelJob([object]$Job) {
  $output = Join-Path $outputRoot ($Job.module + '.olean')
  $stdoutPath = Join-Path $outputRoot ($Job.module + '.stdout.txt')
  $stderrPath = Join-Path $outputRoot ($Job.module + '.stderr.txt')
  $arguments = @('--trust=0', '--threads=1', '-DmaxHeartbeats=5000000',
    '-DmaxRecDepth=30000', '-o', $output, [string]$Job.source)
  $start = [Diagnostics.ProcessStartInfo]::new()
  $start.FileName = $lean
  $start.UseShellExecute = $false
  $start.CreateNoWindow = $true
  $start.RedirectStandardOutput = $true
  $start.RedirectStandardError = $true
  $start.Environment['LEAN_PATH'] = ($leanPath -join ';')
  foreach ($argument in $arguments) { [void]$start.ArgumentList.Add($argument) }
  $process = [Diagnostics.Process]::new()
  $process.StartInfo = $start
  $clock = [Diagnostics.Stopwatch]::StartNew()
  [void]$process.Start()
  $outTask = $process.StandardOutput.ReadToEndAsync()
  $errTask = $process.StandardError.ReadToEndAsync()
  [long]$peak = 0
  $killed = $false
  $killReason = $null
  while (-not $process.WaitForExit(200)) {
    $process.Refresh()
    if ($process.WorkingSet64 -gt $peak) { $peak = $process.WorkingSet64 }
    if ($process.WorkingSet64 -gt 4GB) {
      $killed = $true; $killReason = 'RSS_LIMIT'; $process.Kill($true); $process.WaitForExit(); break
    }
    if ($clock.Elapsed.TotalSeconds -gt 300) {
      $killed = $true; $killReason = 'WALL_LIMIT'; $process.Kill($true); $process.WaitForExit(); break
    }
  }
  $process.WaitForExit()
  $clock.Stop()
  try { $process.Refresh(); if ($process.WorkingSet64 -gt $peak) { $peak = $process.WorkingSet64 } } catch { }
  $stdout = $outTask.GetAwaiter().GetResult()
  $stderr = $errTask.GetAwaiter().GetResult()
  [IO.File]::WriteAllText($stdoutPath, $stdout)
  [IO.File]::WriteAllText($stderrPath, $stderr)
  $reports = @([regex]::Matches($stdout,
      "(?m)^'([^']+)' depends on axioms: \[([^\]]*)\]\s*$") | ForEach-Object {
      [ordered]@{
        theorem = $_.Groups[1].Value
        axioms = @($_.Groups[2].Value.Split(',') | ForEach-Object { $_.Trim() } |
          Where-Object { $_ })
      }
    })
  $reports += @([regex]::Matches($stdout,
      "(?m)^'([^']+)' does not depend on any axioms\s*$") | ForEach-Object {
      [ordered]@{ theorem = $_.Groups[1].Value; axioms = @() }
    })
  $oneExpectedReport = $reports.Count -eq 1 -and $reports[0].theorem -eq $Job.endpoint
  $outsideAllowed = @($reports | ForEach-Object { $_.axioms } |
    Where-Object { $_ -notin $allowedAxioms })
  $allowedSubset = $oneExpectedReport -and $outsideAllowed.Count -eq 0 -and
    $stdout -notmatch '\bsorryAx\b'
  $passed = $process.ExitCode -eq 0 -and -not $killed -and $stderr.Length -eq 0 -and
    (Test-Path -LiteralPath $output) -and $allowedSubset
  return [ordered]@{
    status = if ($passed) { 'PASS' } else { 'FAIL' }
    module = $Job.module; endpoint = $Job.endpoint; arguments = $arguments
    source = $Job.source; sourceSha256 = (Get-FileHash -Algorithm SHA256 -LiteralPath $Job.source).Hash
    exitCode = $process.ExitCode; killed = $killed; killReason = $killReason
    elapsedSeconds = $clock.Elapsed.TotalSeconds; peakRssBytes = $peak
    output = $output
    outputSha256 = if (Test-Path -LiteralPath $output) { (Get-FileHash -Algorithm SHA256 -LiteralPath $output).Hash } else { $null }
    stdout = $stdoutPath; stdoutSha256 = (Get-FileHash -Algorithm SHA256 -LiteralPath $stdoutPath).Hash
    stderr = $stderrPath; stderrSha256 = (Get-FileHash -Algorithm SHA256 -LiteralPath $stderrPath).Hash
    emptyStderr = ($stderr.Length -eq 0); axiomReports = $reports
    noAxiomsOutsideAllowedThree = $allowedSubset
  }
}

$results = @()
foreach ($job in $jobs) { $results += Invoke-KernelJob $job }
$passedAll = @($results | Where-Object { $_.status -ne 'PASS' }).Count -eq 0
$resource = [ordered]@{
  schema = 'nf-reusable-nominal-mm-translator-tiny-trust0-kernel-audit-v1'
  status = if ($passedAll) { 'PASS_TRUST_ZERO_ALLOWED_SUBSET' } else { 'FAIL_CLOSED' }
  settings = [ordered]@{
    trust = 0; threads = 1; maxHeartbeats = 5000000; maxRecDepth = 30000
    wallLimitSecondsPerModule = 300; rssLimitBytes = 4GB; sequential = $true
    appendOnlyOutput = $true
  }
  dependencyPins = [ordered]@{
    generatedSourceResource = [ordered]@{ path = $sourceResource; sha256 = $pins.sourceResource }
    generatedSourceAudit = [ordered]@{ path = $sourceAudit; sha256 = $pins.sourceAudit }
    endToEndSourceAudit = [ordered]@{ path = $e2eResource; sha256 = $pins.e2eResource }
    acceptedAlphaPrefix48 = [ordered]@{ path = $alphaResource; sha256 = $pins.alphaResource }
    acceptedChunk8 = [ordered]@{ path = $priorResource; sha256 = $pins.priorResource }
    lean = [ordered]@{ path = $lean; sha256 = $pins.lean }
    exactMetamathSourceSha256 = $pins.exactSource
  }
  allowedAxioms = $allowedAxioms
  leanPath = $leanPath
  results = $results
  runner = [ordered]@{
    path = $PSCommandPath
    sha256 = (Get-FileHash -Algorithm SHA256 -LiteralPath $PSCommandPath).Hash
  }
}
$resourcePath = Join-Path $outputRoot 'resource.json'
[IO.File]::WriteAllText($resourcePath, (ConvertTo-Json $resource -Depth 14) + "`n")
Write-Host ("{0}; resource SHA256 {1}" -f $resource.status,
  (Get-FileHash -Algorithm SHA256 -LiteralPath $resourcePath).Hash)
if (-not $passedAll) { throw "Trust-zero kernel audit failed; see $resourcePath" }
