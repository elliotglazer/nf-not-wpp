param(
  [Parameter(Mandatory=$true)][string]$Source,
  [string]$Endpoint = 'wppfiniteblocknotwppndv',
  [string]$PythonExe = 'C:\Users\glaze\.cache\codex-runtimes\codex-primary-runtime\dependencies\python\python.exe'
)

$ErrorActionPreference = 'Stop'
Set-StrictMode -Version 2.0

$Here = Split-Path -Parent $MyInvocation.MyCommand.Path
$Workspace = (Resolve-Path (Join-Path $Here '..\..\..')).Path
$Source = (Resolve-Path -LiteralPath $Source).Path
$PythonExe = (Resolve-Path -LiteralPath $PythonExe).Path

$LimitBytes = [int64]1610612736 # exactly 1.5 GiB
$PinnedCommit = '697060e119ab3f4f1a8dae4451f5cbacd9803626'
$ExpectedHashes = @{
  python = 'D8E3F0ADF246DB00358C0C4ED349CF714898178F9558FB0E944F79F5C07F8EAA'
  primary = '4E0B837A73B736F6B6698840FDCA66057C01489CD09956ABA4573175D73E21D8'
  secondary = '1D340B258C0E324518BE13C2A6A475C1586A62250A912A4DD632F5CE862E200C'
  strict = '29EE7F7C324F8F09A16FFB0104699674E25B6C84C691B68EE7FFBEE25AF9B497'
  normalizer = '16A5315980EC294D761CBFF44CDAFD7521AC99330798F5A6FCF67E8E4E12E780'
  mm0_hs = '64D73FD69F3123AE5D573B7B4B0817D9F403DD7B366107B9D1AA20E16058368B'
  mm0_c = '6E573D7AD05455C9B1B002A75744E0C7FDD359EF187A456E514CADBBD0C58288'
}

$Primary = Join-Path $Workspace 'work\formalization_continue\root_integration\local_mm_verify_compressed.py'
$Secondary = Join-Path $Workspace 'work\formalization_continue\release_final_2026-08-17\formalization_continue\reconstruct\mmverify_simple.py'
$Strict = Join-Path $Workspace 'work\mm0_conversion_2026-08-20\strict_scope\local_mm_verify_compressed_strict_scope.py'
$Normalizer = Join-Path $Workspace 'work\mm0_conversion_2026-08-20\input_prep\normalize_compressed_preloads_for_mm0.py'
$MM0HS = Join-Path $Workspace 'work\mm0_conversion_2026-08-20\toolchain\bin\mm0-hs.exe'
$MM0C = Join-Path $Workspace 'work\mm0_conversion_2026-08-20\toolchain\bin\mm0-c.exe'
$PinFile = Join-Path $Workspace 'work\mm0_conversion_2026-08-20\toolchain\PINNED_VERSION.txt'

function Get-Sha256([string]$Path) {
  return (Get-FileHash -Algorithm SHA256 -LiteralPath $Path).Hash.ToUpperInvariant()
}

function Write-Json([string]$Path, $Object) {
  $json = ($Object | ConvertTo-Json -Depth 12) + "`n"
  [IO.File]::WriteAllText($Path, $json, (New-Object Text.UTF8Encoding($false)))
}

function Assert-Hash([string]$Name, [string]$Path, [string]$Expected) {
  if (-not (Test-Path -LiteralPath $Path -PathType Leaf)) {
    throw "Missing pinned tool $Name at $Path"
  }
  $actual = Get-Sha256 $Path
  if ($actual -ne $Expected) {
    throw "Pinned-tool hash mismatch for ${Name}: expected $Expected, got $actual"
  }
  return [ordered]@{ path=$Path; sha256=$actual }
}

function Quote-NativeArgument([string]$Arg) {
  if ($Arg.Contains('"')) { throw "Native argument contains an unsupported quote: $Arg" }
  return '"' + $Arg + '"'
}

function Invoke-Guarded {
  param(
    [Parameter(Mandatory=$true)][string]$Name,
    [Parameter(Mandatory=$true)][string]$Executable,
    [Parameter(Mandatory=$true)][string[]]$Arguments,
    [string]$StandardInputPath = ''
  )

  $stdout = Join-Path $Logs ($Name + '.stdout.txt')
  $stderr = Join-Path $Logs ($Name + '.stderr.txt')
  $resource = Join-Path $Logs ($Name + '.resource.json')
  $argString = (($Arguments | ForEach-Object { Quote-NativeArgument $_ }) -join ' ')
  $start = Get-Date
  $timer = [Diagnostics.Stopwatch]::StartNew()

  $startArgs = @{
    FilePath = $Executable
    ArgumentList = $argString
    WorkingDirectory = $Workspace
    PassThru = $true
    WindowStyle = 'Hidden'
    RedirectStandardOutput = $stdout
    RedirectStandardError = $stderr
  }
  if ($StandardInputPath) {
    $startArgs.RedirectStandardInput = $StandardInputPath
  }
  $proc = Start-Process @startArgs
  $peakWorking = [int64]0
  $peakPrivate = [int64]0
  $guardKilled = $false

  while (-not $proc.HasExited) {
    Start-Sleep -Milliseconds 100
    try {
      $proc.Refresh()
      if ($proc.WorkingSet64 -gt $peakWorking) { $peakWorking = $proc.WorkingSet64 }
      if ($proc.PrivateMemorySize64 -gt $peakPrivate) { $peakPrivate = $proc.PrivateMemorySize64 }
      if ($proc.WorkingSet64 -gt $LimitBytes -or $proc.PrivateMemorySize64 -gt $LimitBytes) {
        $guardKilled = $true
        Stop-Process -Id $proc.Id -Force
        $proc.WaitForExit()
        break
      }
    } catch [InvalidOperationException] {
      break
    }
  }
  $proc.WaitForExit()
  $timer.Stop()
  $exitCode = $null
  if (-not $guardKilled) { $exitCode = $proc.ExitCode }

  $exactCommand = ('& ' + (Quote-NativeArgument $Executable) + ' ' + $argString)
  if ($StandardInputPath) {
    $exactCommand += (' < ' + (Quote-NativeArgument $StandardInputPath))
  }
  $result = [ordered]@{
    name = $Name
    executable = $Executable
    executable_sha256 = Get-Sha256 $Executable
    arguments = $Arguments
    exact_command = $exactCommand
    standard_input = $StandardInputPath
    started = $start.ToString('o')
    elapsed_seconds = [math]::Round($timer.Elapsed.TotalSeconds, 3)
    limit_bytes = $LimitBytes
    limit_mib = 1536
    peak_working_set_bytes = $peakWorking
    peak_working_set_mib = [math]::Round($peakWorking / 1MB, 3)
    peak_private_bytes = $peakPrivate
    peak_private_mib = [math]::Round($peakPrivate / 1MB, 3)
    guard_killed = $guardKilled
    exit_code = $exitCode
    stdout = $stdout
    stdout_bytes = (Get-Item -LiteralPath $stdout).Length
    stdout_sha256 = Get-Sha256 $stdout
    stderr = $stderr
    stderr_bytes = (Get-Item -LiteralPath $stderr).Length
    stderr_sha256 = Get-Sha256 $stderr
    metamath_executable_invoked = $false
  }
  Write-Json $resource $result
  $null = $Stages.Add([pscustomobject]$result)
  if ($guardKilled) { throw "$Name exceeded the sampled 1.5 GiB kill guard" }
  if ($exitCode -ne 0) { throw "$Name exited with code $exitCode; see $stderr" }
  return [pscustomobject]$result
}

function Read-JsonLog([string]$Path) {
  return (Get-Content -LiteralPath $Path -Raw | ConvertFrom-Json)
}

function Invoke-SourceAudit([string]$Path, [string]$Prefix) {
  $primaryJson = Join-Path $Logs ($Prefix + '_primary.verifier.json')
  $r = Invoke-Guarded -Name ($Prefix + '_primary') -Executable $PythonExe -Arguments @($Primary,$Path,$primaryJson)
  $primaryResult = Read-JsonLog $primaryJson
  if (-not $primaryResult.ok -or $primaryResult.trusted -ne 0) {
    throw "$Prefix primary verification did not return ok/trusted=0"
  }

  $r = Invoke-Guarded -Name ($Prefix + '_secondary') -Executable $PythonExe -Arguments @($Secondary,$Path)
  $secondaryText = Get-Content -LiteralPath $r.stdout -Raw
  if ($secondaryText -notmatch '^OK\s+\d+\s+proofs,\s+\d+\s+statements') {
    throw "$Prefix secondary verification did not emit its OK summary"
  }

  $strictJson = Join-Path $Logs ($Prefix + '_strict.verifier.json')
  $r = Invoke-Guarded -Name ($Prefix + '_strict') -Executable $PythonExe -Arguments @($Strict,$Path,$strictJson)
  $strictResult = Read-JsonLog $strictJson
  if (-not $strictResult.ok -or $strictResult.status -ne 'PASS' -or
      $strictResult.rejected_proof_count -ne 0 -or
      $strictResult.inactive_hypothesis_reference_count -ne 0 -or
      $strictResult.trusted_scope_clean_proofs -ne 0) {
    throw "$Prefix strict-scope verification was not completely clean"
  }
}

function File-Record([string]$Path) {
  $item = Get-Item -LiteralPath $Path
  return [ordered]@{ path=$item.FullName; bytes=$item.Length; sha256=(Get-Sha256 $item.FullName) }
}

function Test-ByteIdentical([string]$Left, [string]$Right) {
  $li = Get-Item -LiteralPath $Left
  $ri = Get-Item -LiteralPath $Right
  if ($li.Length -ne $ri.Length) { return $false }
  $a = [IO.File]::ReadAllBytes($li.FullName)
  $b = [IO.File]::ReadAllBytes($ri.FullName)
  for ($i=0; $i -lt $a.Length; $i++) {
    if ($a[$i] -ne $b[$i]) { return $false }
  }
  return $true
}

if (-not (Test-Path -LiteralPath $Source -PathType Leaf)) {
  throw "Source is not a file: $Source"
}
if ([IO.Path]::GetExtension($Source) -ne '.mm') {
  throw "Source must be a Metamath .mm file: $Source"
}
if ($Endpoint -notmatch '^[A-Za-z0-9_.-]+$') {
  throw "Unsafe endpoint label syntax: $Endpoint"
}

$toolRecords = [ordered]@{}
$toolRecords.python = Assert-Hash 'python' $PythonExe $ExpectedHashes.python
$toolRecords.primary = Assert-Hash 'primary verifier' $Primary $ExpectedHashes.primary
$toolRecords.secondary = Assert-Hash 'secondary verifier' $Secondary $ExpectedHashes.secondary
$toolRecords.strict = Assert-Hash 'strict verifier' $Strict $ExpectedHashes.strict
$toolRecords.normalizer = Assert-Hash 'preload normalizer' $Normalizer $ExpectedHashes.normalizer
$toolRecords.mm0_hs = Assert-Hash 'mm0-hs' $MM0HS $ExpectedHashes.mm0_hs
$toolRecords.mm0_c = Assert-Hash 'mm0-c' $MM0C $ExpectedHashes.mm0_c
$toolRecords.runner = [ordered]@{
  path = $MyInvocation.MyCommand.Path
  sha256 = Get-Sha256 $MyInvocation.MyCommand.Path
}
$pinText = Get-Content -LiteralPath $PinFile -Raw
if ($pinText -notmatch ('(?m)^commit=' + [regex]::Escape($PinnedCommit) + '$')) {
  throw "Pinned commit file does not name $PinnedCommit"
}

$sourceHash = Get-Sha256 $Source
$stamp = (Get-Date).ToUniversalTime().ToString('yyyyMMddTHHmmssZ')
$safeStem = ([IO.Path]::GetFileNameWithoutExtension($Source) -replace '[^A-Za-z0-9_.-]','_')
$RunDir = Join-Path $Here ('run_' + $stamp + '_' + $safeStem + '_' + $sourceHash.Substring(0,12))
if (Test-Path -LiteralPath $RunDir) { throw "Run directory already exists: $RunDir" }
$null = New-Item -ItemType Directory -Path $RunDir
$Logs = Join-Path $RunDir 'logs'
$null = New-Item -ItemType Directory -Path $Logs
$Stages = New-Object System.Collections.ArrayList
$AuditPath = Join-Path $RunDir 'final_conversion_audit.json'

$Normalized = Join-Path $RunDir 'normalized_for_mm0.mm'
$TextMM0 = Join-Path $RunDir 'verified_text.mm0'
$TextMMU = Join-Path $RunDir 'verified_text.mmu'
$DirectMM0 = Join-Path $RunDir 'direct.mm0'
$DirectMMB = Join-Path $RunDir 'proof.mmb'

try {
  Invoke-SourceAudit $Source 'source'

  $null = Invoke-Guarded -Name 'normalize_mandatory_e_preloads' -Executable $PythonExe -Arguments @($Normalizer,$Source,$Normalized)
  if (-not (Test-Path -LiteralPath $Normalized -PathType Leaf)) { throw 'Normalizer did not create its output' }
  $normalizerReportPath = [IO.Path]::ChangeExtension($Normalized, '.preload_normalization.json')
  if (-not (Test-Path -LiteralPath $normalizerReportPath -PathType Leaf)) { throw 'Normalizer report is missing' }
  $normalizerReport = Read-JsonLog $normalizerReportPath
  if ($normalizerReport.assertion_or_hypothesis_tokens_changed -ne 0) {
    throw 'Normalizer reports an assertion/hypothesis token change'
  }
  Invoke-SourceAudit $Normalized 'normalized'

  $null = Invoke-Guarded -Name 'from_mm_textual_pair' -Executable $MM0HS -Arguments @(
    'from-mm',$Normalized,'-f',$Endpoint,'-o',$TextMM0,$TextMMU
  )
  if ((Get-Item -LiteralPath $TextMM0).Length -eq 0 -or (Get-Item -LiteralPath $TextMMU).Length -eq 0) {
    throw 'Textual MM0/MMU import produced an empty file'
  }

  $verifyMMU = Invoke-Guarded -Name 'verify_mmu' -Executable $MM0HS -Arguments @('verify',$TextMM0,$TextMMU)
  $verifyText = Get-Content -LiteralPath $verifyMMU.stdout -Raw
  if ($verifyText -notmatch '(?m)^spec checked\s*$' -or $verifyText -notmatch '(?m)^verified\s*$') {
    throw 'MM0/MMU verification did not print both spec checked and verified'
  }

  $null = Invoke-Guarded -Name 'from_mm_direct_mmb' -Executable $MM0HS -Arguments @(
    'from-mm',$Normalized,'-f',$Endpoint,'-o',$DirectMM0,$DirectMMB
  )
  if ((Get-Item -LiteralPath $DirectMM0).Length -eq 0 -or (Get-Item -LiteralPath $DirectMMB).Length -eq 0) {
    throw 'Direct MM0/MMB import produced an empty file'
  }

  $mm0Equal = Test-ByteIdentical $TextMM0 $DirectMM0
  if (-not $mm0Equal) { throw 'Textual and direct imports produced different MM0 byte streams' }

  $null = Invoke-Guarded -Name 'mm0_c_parser_verification' -Executable $MM0C `
    -Arguments @($DirectMMB) -StandardInputPath $DirectMM0

  $outputs = [ordered]@{
    normalized_metamath = File-Record $Normalized
    normalizer_report = File-Record $normalizerReportPath
    textual_mm0 = File-Record $TextMM0
    textual_mmu = File-Record $TextMMU
    direct_mm0 = File-Record $DirectMM0
    direct_mmb = File-Record $DirectMMB
  }
  $audit = [ordered]@{
    schema = 'mm0-final-conversion-audit-v1'
    status = 'COMPLETE'
    source = File-Record $Source
    endpoint = $Endpoint
    pinned_commit = $PinnedCommit
    tools = $toolRecords
    memory_guard_bytes = $LimitBytes
    memory_guard_mib = 1536
    stages = @($Stages)
    outputs = $outputs
    mm0_byte_identical = $mm0Equal
    normalized_assertion_or_hypothesis_tokens_changed = $normalizerReport.assertion_or_hypothesis_tokens_changed
    parser_enabled_mm0_c_exit_code = 0
    metamath_executable_invoked = $false
    proof_artifact_candidate = $true
  }
  Write-Json $AuditPath $audit
  Write-Output $AuditPath
} catch {
  $failure = [ordered]@{
    schema = 'mm0-final-conversion-audit-v1'
    status = 'FAILED'
    source = [ordered]@{ path=$Source; sha256=$sourceHash }
    endpoint = $Endpoint
    pinned_commit = $PinnedCommit
    tools = $toolRecords
    memory_guard_bytes = $LimitBytes
    stages = @($Stages)
    error = ($_ | Out-String)
    metamath_executable_invoked = $false
    proof_artifact_candidate = $false
  }
  Write-Json $AuditPath $failure
  throw
}
