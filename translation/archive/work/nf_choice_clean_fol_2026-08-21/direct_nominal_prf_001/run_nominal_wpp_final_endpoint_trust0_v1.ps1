[CmdletBinding()]
param(
  [Parameter(Mandatory=$true)][string]$PackageAuditResource,
  [Parameter(Mandatory=$true)][string]$PackageAuditResourceSha256,
  [Parameter(Mandatory=$true)][string]$FinalSourceResource,
  [Parameter(Mandatory=$true)][string]$FinalSourceResourceSha256,
  [Parameter(Mandatory=$true)][string]$FinalKernelResource,
  [Parameter(Mandatory=$true)][string]$FinalKernelResourceSha256,
  [Parameter(Mandatory=$true)][string]$OutputRoot,
  [Parameter(Mandatory=$true)][string]$PythonExecutable,
  [Parameter(Mandatory=$true)][string]$PythonExecutableSha256,
  [Parameter(Mandatory=$true)][string]$LeanExecutable,
  [Parameter(Mandatory=$true)][string]$LeanExecutableSha256,
  [int]$MaxHeartbeats = 5000000,
  [int]$MaxRecDepth = 30000,
  [int]$WallSeconds = 1200
)

$ErrorActionPreference = 'Stop'
Set-StrictMode -Version Latest

$allowed = @('propext', 'Classical.choice', 'Quot.sound')
$finalModule = 'NominalWPPFinalEndpointV1'
$finalTheorem = 'NFChoice.DirectNominalPrf.Nominal.WPPFinalEndpointV1.hailperinNF_proves_not_WPP'
$bridgeTheorems = @(
  'NFChoice.DirectNominalPrf.Nominal.ClosedEndpointBridgeV1.valid_of_closed_nprf',
  'NFChoice.DirectNominalPrf.Nominal.ClosedEndpointBridgeV1.hailperinNF_derives_not_WPP_of_nominal'
)
$utf8NoBom = [Text.UTF8Encoding]::new($false)

function Get-Property($Object, [string]$Name) {
  if ($null -eq $Object) { return $null }
  $property = $Object.PSObject.Properties[$Name]
  if ($null -eq $property) { return $null }
  return $property.Value
}

function Read-Json([string]$Path) {
  return [IO.File]::ReadAllText($Path) | ConvertFrom-Json
}

function Resolve-RecordedPath([string]$Value, [string]$Anchor) {
  if ([IO.Path]::IsPathRooted($Value)) {
    return (Resolve-Path -LiteralPath $Value).Path
  }
  $base = Split-Path -Parent $Anchor
  return (Resolve-Path -LiteralPath (Join-Path $base $Value)).Path
}

function Assert-Hash([string]$Path, [string]$Expected, [string]$Context) {
  if ($Expected -notmatch '^[A-Fa-f0-9]{64}$') {
    throw "Malformed SHA-256 pin for $Context"
  }
  $actual = (Get-FileHash -Algorithm SHA256 -LiteralPath $Path).Hash
  if ($actual -ne $Expected.ToUpperInvariant()) {
    throw "SHA-256 mismatch for ${Context}: $actual"
  }
  return $actual
}

function Assert-AllowedThree($Value, [string]$Context) {
  $items = @($Value)
  if ($items.Count -ne 3) { throw "$Context does not list exactly three axioms" }
  for ($i = 0; $i -lt 3; $i++) {
    if ([string]$items[$i] -ne $allowed[$i]) {
      throw "$Context allowed-axiom list mismatch"
    }
  }
}

function Assert-NoForbiddenLean([string]$Path) {
  $text = [IO.File]::ReadAllText($Path)
  if ([regex]::IsMatch($text, '(?m)^\s*(axiom|opaque)\b|\bsorry\b')) {
    throw "Forbidden Lean declaration or placeholder: $Path"
  }
}

function Assert-ExactPrints([string]$Stdout, [string[]]$Theorems) {
  $lines = @(($Stdout -split "`r?`n") | Where-Object { $_ -ne '' })
  if ($lines.Count -ne $Theorems.Count) {
    throw "Expected $($Theorems.Count) exact-three lines, found $($lines.Count)"
  }
  for ($i = 0; $i -lt $Theorems.Count; $i++) {
    $expected = "'$($Theorems[$i])' depends on axioms: [propext, Classical.choice, Quot.sound]"
    if ($lines[$i] -ne $expected) {
      throw "Exact-three print mismatch for $($Theorems[$i])"
    }
  }
}

function Invoke-CheckedProcess(
  [string]$Executable,
  [string[]]$Arguments,
  [hashtable]$Environment,
  [int]$TimeoutSeconds
) {
  $info = [Diagnostics.ProcessStartInfo]::new()
  $info.FileName = $Executable
  $info.UseShellExecute = $false
  $info.RedirectStandardOutput = $true
  $info.RedirectStandardError = $true
  $info.CreateNoWindow = $true
  foreach ($argument in $Arguments) { [void]$info.ArgumentList.Add($argument) }
  foreach ($key in $Environment.Keys) { $info.Environment[$key] = [string]$Environment[$key] }
  $process = [Diagnostics.Process]::new()
  $process.StartInfo = $info
  $clock = [Diagnostics.Stopwatch]::StartNew()
  if (-not $process.Start()) { throw "Could not start $Executable" }
  $stdoutTask = $process.StandardOutput.ReadToEndAsync()
  $stderrTask = $process.StandardError.ReadToEndAsync()
  $finished = $process.WaitForExit($TimeoutSeconds * 1000)
  $killed = $false
  if (-not $finished) {
    $killed = $true
    try { $process.Kill($true) } catch { }
    [void]$process.WaitForExit(30000)
  }
  $stdout = $stdoutTask.GetAwaiter().GetResult()
  $stderr = $stderrTask.GetAwaiter().GetResult()
  $clock.Stop()
  $record = [ordered]@{
    arguments = $Arguments
    exitCode = if ($finished) { $process.ExitCode } else { $null }
    killed = $killed
    elapsedSeconds = $clock.Elapsed.TotalSeconds
    stdoutText = $stdout
    stderrText = $stderr
  }
  $process.Dispose()
  return $record
}

function Write-JsonExclusive([string]$Path, $Value) {
  if (Test-Path -LiteralPath $Path) { throw "Refusing to overwrite $Path" }
  [IO.File]::WriteAllText($Path, (ConvertTo-Json $Value -Depth 30) + "`n", $utf8NoBom)
}

$packagePath = (Resolve-Path -LiteralPath $PackageAuditResource).Path
[void](Assert-Hash $packagePath $PackageAuditResourceSha256 'package audit resource')
$package = Read-Json $packagePath
if ([string](Get-Property $package 'status') -ne 'PASS_SOURCE_ONLY_FINAL_ENDPOINT_PACKAGE_V1') {
  throw 'Final endpoint package has not passed its source-only audit'
}
if ((Get-Property $package 'leanStartedByThisAudit') -ne $false) {
  throw 'Package audit unexpectedly started Lean'
}

$files = Get-Property $package 'files'
$generatorRecord = Get-Property $files 'generator'
$templateRecord = Get-Property $files 'template'
$bridgeRecord = Get-Property $files 'bridge'
$runnerRecord = Get-Property $files 'runner'
$generator = Resolve-RecordedPath ([string](Get-Property $generatorRecord 'path')) $packagePath
$template = Resolve-RecordedPath ([string](Get-Property $templateRecord 'path')) $packagePath
$bridge = Resolve-RecordedPath ([string](Get-Property $bridgeRecord 'path')) $packagePath
$thisRunner = (Resolve-Path -LiteralPath $PSCommandPath).Path
[void](Assert-Hash $generator ([string](Get-Property $generatorRecord 'sha256')) 'generator')
[void](Assert-Hash $template ([string](Get-Property $templateRecord 'sha256')) 'template')
[void](Assert-Hash $bridge ([string](Get-Property $bridgeRecord 'sha256')) 'bridge')
[void](Assert-Hash $thisRunner ([string](Get-Property $runnerRecord 'sha256')) 'runner')
Assert-NoForbiddenLean $template
Assert-NoForbiddenLean $bridge

$python = (Resolve-Path -LiteralPath $PythonExecutable).Path
$lean = (Resolve-Path -LiteralPath $LeanExecutable).Path
[void](Assert-Hash $python $PythonExecutableSha256 'Python executable')
[void](Assert-Hash $lean $LeanExecutableSha256 'Lean executable')
$sourceResourcePath = (Resolve-Path -LiteralPath $FinalSourceResource).Path
$kernelResourcePath = (Resolve-Path -LiteralPath $FinalKernelResource).Path
[void](Assert-Hash $sourceResourcePath $FinalSourceResourceSha256 'final source resource')
[void](Assert-Hash $kernelResourcePath $FinalKernelResourceSha256 'final kernel resource')

$output = [IO.Path]::GetFullPath($OutputRoot)
if (Test-Path -LiteralPath $output) {
  throw "Output root must not exist (append-only contract): $output"
}

$generatorArguments = @(
  $generator,
  '--final-source-resource', $sourceResourcePath,
  '--final-source-resource-sha256', $FinalSourceResourceSha256,
  '--final-kernel-resource', $kernelResourcePath,
  '--final-kernel-resource-sha256', $FinalKernelResourceSha256,
  '--template', $template,
  '--template-sha256', ([string](Get-Property $templateRecord 'sha256')),
  '--output-dir', $output
)
$generatorRun = Invoke-CheckedProcess $python $generatorArguments @{} $WallSeconds
if ($generatorRun.killed -or $generatorRun.exitCode -ne 0 -or $generatorRun.stderrText.Length -ne 0) {
  throw "Source-only final wrapper generation failed: $($generatorRun.stderrText)"
}

$sourceProvenancePath = Join-Path $output 'source_resource.json'
$wrapper = Join-Path $output ($finalModule + '.lean')
if (-not (Test-Path -LiteralPath $sourceProvenancePath) -or
    -not (Test-Path -LiteralPath $wrapper)) {
  throw 'Generator did not publish the expected append-only artifacts'
}
$sourceProvenance = Read-Json $sourceProvenancePath
if ([string](Get-Property $sourceProvenance 'status') -ne
    'PASS_SOURCE_ONLY_READY_FOR_TRUST_ZERO') {
  throw 'Generated source provenance did not pass'
}
Assert-NoForbiddenLean $wrapper

$kernel = Read-Json $kernelResourcePath
if ([string](Get-Property $kernel 'status') -ne
    'PASS_TRUST_ZERO_ALL_PARTS_AND_UMBRELLA_EXACT_THREE') {
  throw 'Final replay kernel resource is not complete'
}
Assert-AllowedThree (Get-Property $kernel 'allowedAxioms') 'final replay kernel resource'
$kernelSourceRecord = Get-Property $kernel 'sourceResource'
if ([string](Get-Property $kernelSourceRecord 'sha256') -ne
    $FinalSourceResourceSha256.ToUpperInvariant()) {
  throw 'Final kernel/source resource linkage mismatch'
}

$leanRoots = [Collections.Generic.List[string]]::new()
[void]$leanRoots.Add($output)
foreach ($record in @(Get-Property $package 'supportOleans')) {
  $support = Resolve-RecordedPath ([string](Get-Property $record 'path')) $packagePath
  $supportHash = [string](Get-Property $record 'sha256')
  $supportModule = [string](Get-Property $record 'module')
  [void](Assert-Hash $support $supportHash $supportModule)
  if (-not $leanRoots.Contains((Split-Path -Parent $support))) {
    [void]$leanRoots.Add((Split-Path -Parent $support))
  }
}
foreach ($value in @(Get-Property $kernel 'leanPath')) {
  $root = Resolve-RecordedPath ([string]$value) $kernelResourcePath
  if (-not (Test-Path -LiteralPath $root -PathType Container)) {
    throw "Missing final kernel LEAN_PATH root: $root"
  }
  if (-not $leanRoots.Contains($root)) { [void]$leanRoots.Add($root) }
}
$processEnvironment = @{ LEAN_PATH = [string]::Join([IO.Path]::PathSeparator, $leanRoots) }

function Invoke-LeanModule(
  [string]$Name,
  [string]$Source,
  [string[]]$PrintedTheorems
) {
  $olean = Join-Path $output ($Name + '.olean')
  $arguments = @(
    '--trust=0', '--threads=1',
    "-DmaxHeartbeats=$MaxHeartbeats",
    "-DmaxRecDepth=$MaxRecDepth",
    '-Dlinter.constructorNameAsVariable=false',
    '-o', $olean, $Source
  )
  $run = Invoke-CheckedProcess $lean $arguments $processEnvironment $WallSeconds
  $stdoutPath = Join-Path $output ($Name + '.stdout.txt')
  $stderrPath = Join-Path $output ($Name + '.stderr.txt')
  [IO.File]::WriteAllText($stdoutPath, $run.stdoutText, $utf8NoBom)
  [IO.File]::WriteAllText($stderrPath, $run.stderrText, $utf8NoBom)
  $exactThree = $false
  if (-not $run.killed -and $run.exitCode -eq 0 -and
      $run.stderrText.Length -eq 0 -and (Test-Path -LiteralPath $olean)) {
    Assert-ExactPrints $run.stdoutText $PrintedTheorems
    $exactThree = $true
  }
  return [ordered]@{
    module = $Name
    source = $Source
    sourceSha256 = (Get-FileHash -Algorithm SHA256 -LiteralPath $Source).Hash
    printedTheorems = $PrintedTheorems
    arguments = $run.arguments
    trust = 0
    threads = 1
    exitCode = $run.exitCode
    killed = $run.killed
    elapsedSeconds = $run.elapsedSeconds
    emptyStderr = $run.stderrText.Length -eq 0
    exactAllowedThree = $exactThree
    output = $olean
    outputSha256 = if (Test-Path -LiteralPath $olean) {
      (Get-FileHash -Algorithm SHA256 -LiteralPath $olean).Hash
    } else { $null }
    stdout = $stdoutPath
    stdoutSha256 = (Get-FileHash -Algorithm SHA256 -LiteralPath $stdoutPath).Hash
    stderr = $stderrPath
    stderrSha256 = (Get-FileHash -Algorithm SHA256 -LiteralPath $stderrPath).Hash
  }
}

$commands = @()
$status = 'FAIL_CLOSED_BRIDGE'
$failure = $null
try {
  $bridgeCommand = Invoke-LeanModule 'NominalClosedEndpointBridgeV1' $bridge $bridgeTheorems
  $commands += $bridgeCommand
  if (-not $bridgeCommand.exactAllowedThree) { throw 'Bridge trust-zero check failed' }
  $status = 'FAIL_CLOSED_FINAL_WRAPPER'
  $finalCommand = Invoke-LeanModule $finalModule $wrapper @($finalTheorem)
  $commands += $finalCommand
  if (-not $finalCommand.exactAllowedThree) { throw 'Final wrapper trust-zero check failed' }
  $status = 'PASS_TRUST_ZERO_EXACT_ELEVEN_NF_PROVES_NOT_WPP_EXACT_THREE'
} catch {
  $failure = $_.Exception.Message
}

$resource = [ordered]@{
  schema = 'nf-nominal-wpp-final-endpoint-kernel-v1'
  status = $status
  createdUtc = [DateTime]::UtcNow.ToString('o')
  packageAuditResource = @{ path=$packagePath; sha256=$PackageAuditResourceSha256.ToUpperInvariant() }
  sourceResource = @{ path=$sourceResourcePath; sha256=$FinalSourceResourceSha256.ToUpperInvariant() }
  replayKernelResource = @{ path=$kernelResourcePath; sha256=$FinalKernelResourceSha256.ToUpperInvariant() }
  generatedSourceResource = @{
    path=$sourceProvenancePath
    sha256=(Get-FileHash -Algorithm SHA256 -LiteralPath $sourceProvenancePath).Hash
  }
  publicTheorem = $finalTheorem
  publicType = "LiteralHailperinNF ⊢ₛ' Fol.bd_not SourceWPPFOL"
  objectTheoryAxiomCount = 11
  allowedAxioms = $allowed
  settings = @{
    trust=0; threads=1; maxHeartbeats=$MaxHeartbeats; maxRecDepth=$MaxRecDepth
    sequentialSingleLeanProcess=$true; wallSeconds=$WallSeconds
    leanExecutable=$lean; leanExecutableSha256=$LeanExecutableSha256.ToUpperInvariant()
    pythonExecutable=$python; pythonExecutableSha256=$PythonExecutableSha256.ToUpperInvariant()
  }
  leanPath = @($leanRoots)
  generator = @{
    path=$generator; arguments=$generatorArguments; exitCode=$generatorRun.exitCode
    stdout=$generatorRun.stdoutText; emptyStderr=$generatorRun.stderrText.Length -eq 0
  }
  commands = $commands
  failure = $failure
}
$resourcePath = Join-Path $output 'resource.json'
Write-JsonExclusive $resourcePath $resource
if ($status -ne 'PASS_TRUST_ZERO_EXACT_ELEVEN_NF_PROVES_NOT_WPP_EXACT_THREE') {
  throw "Final endpoint run failed closed: $failure"
}
Write-Output $resourcePath
