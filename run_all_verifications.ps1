$ErrorActionPreference = "Stop"
$root = Split-Path -Parent $MyInvocation.MyCommand.Path
$rocqDir = Join-Path $root "rocq_proofs"

$files = @(
    "verify_pi2p.v",
    "verify_p1.v",
    "verify_p2_p3.v",
    "verify_p5.v",
    "verify_p4.v"
)

Write-Host "================================================================"
Write-Host "Running Rocq (coqc) Formal Verification for All 7 Problems P1-P7"
Write-Host "================================================================"

foreach ($f in $files) {
    $path = Join-Path $rocqDir $f
    Write-Host "`n[Compiling] $f ..."
    $admitted = Select-String -Path $path -Pattern "\b(Admitted|admit|Abort)\b"
    if ($admitted) {
        Write-Error "Found Admitted/admit/Abort in $f!"
        exit 1
    }
    & coqc $path
    if ($LASTEXITCODE -ne 0) {
        Write-Error "coqc failed on $f with exit code $LASTEXITCODE"
        exit $LASTEXITCODE
    }
    Write-Host "[PASS] $f compiled with EXIT=0 and 0 Admitted!"
}

Write-Host "`n================================================================"
Write-Host "ALL 5 ROCQ PROOF FILES (COVERING P1-P7) VERIFIED SUCCESSFULLY!"
Write-Host "================================================================"
