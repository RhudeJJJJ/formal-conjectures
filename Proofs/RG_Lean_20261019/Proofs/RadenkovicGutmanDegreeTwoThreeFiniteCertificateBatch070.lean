/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteKeysData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3500
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3501
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3502
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3503
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3504
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3505
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3506
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3507
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3508
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3509
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3510
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3511
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3512
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3513
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3514
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3515
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3516
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3517
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3518
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3519
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3520
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3521
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3522
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3523
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3524
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3525
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3526
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3527
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3528
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3529
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3530
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3531
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3532
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3533
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3534
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3535
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3536
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3537
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3538
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3539
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3540
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3541
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3542
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3543
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3544
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3545
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3546
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3547
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3548
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3549
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeTwoThreeFiniteActualCases
theorem certified_keys070 : ∀ k ∈ keys070, Certified k := by
  apply certified_cons (by exact certified3500)
  apply certified_cons (by exact certified3500swap)
  apply certified_cons (by exact certified3501)
  apply certified_cons (by exact certified3501swap)
  apply certified_cons (by exact certified3502)
  apply certified_cons (by exact certified3502swap)
  apply certified_cons (by exact certified3503)
  apply certified_cons (by exact certified3503swap)
  apply certified_cons (by exact certified3504)
  apply certified_cons (by exact certified3504swap)
  apply certified_cons (by exact certified3505)
  apply certified_cons (by exact certified3505swap)
  apply certified_cons (by exact certified3506)
  apply certified_cons (by exact certified3506swap)
  apply certified_cons (by exact certified3507)
  apply certified_cons (by exact certified3507swap)
  apply certified_cons (by exact certified3508)
  apply certified_cons (by exact certified3508swap)
  apply certified_cons (by exact certified3509)
  apply certified_cons (by exact certified3509swap)
  apply certified_cons (by exact certified3510)
  apply certified_cons (by exact certified3510swap)
  apply certified_cons (by exact certified3511)
  apply certified_cons (by exact certified3511swap)
  apply certified_cons (by exact certified3512)
  apply certified_cons (by exact certified3512swap)
  apply certified_cons (by exact certified3513)
  apply certified_cons (by exact certified3513swap)
  apply certified_cons (by exact certified3514)
  apply certified_cons (by exact certified3514swap)
  apply certified_cons (by exact certified3515)
  apply certified_cons (by exact certified3515swap)
  apply certified_cons (by exact certified3516)
  apply certified_cons (by exact certified3516swap)
  apply certified_cons (by exact certified3517)
  apply certified_cons (by exact certified3517swap)
  apply certified_cons (by exact certified3518)
  apply certified_cons (by exact certified3518swap)
  apply certified_cons (by exact certified3519)
  apply certified_cons (by exact certified3519swap)
  apply certified_cons (by exact certified3520)
  apply certified_cons (by exact certified3520swap)
  apply certified_cons (by exact certified3521)
  apply certified_cons (by exact certified3521swap)
  apply certified_cons (by exact certified3522)
  apply certified_cons (by exact certified3522swap)
  apply certified_cons (by exact certified3523)
  apply certified_cons (by exact certified3523swap)
  apply certified_cons (by exact certified3524)
  apply certified_cons (by exact certified3524swap)
  apply certified_cons (by exact certified3525)
  apply certified_cons (by exact certified3525swap)
  apply certified_cons (by exact certified3526)
  apply certified_cons (by exact certified3526swap)
  apply certified_cons (by exact certified3527)
  apply certified_cons (by exact certified3527swap)
  apply certified_cons (by exact certified3528)
  apply certified_cons (by exact certified3528swap)
  apply certified_cons (by exact certified3529)
  apply certified_cons (by exact certified3529swap)
  apply certified_cons (by exact certified3530)
  apply certified_cons (by exact certified3530swap)
  apply certified_cons (by exact certified3531)
  apply certified_cons (by exact certified3531swap)
  apply certified_cons (by exact certified3532)
  apply certified_cons (by exact certified3532swap)
  apply certified_cons (by exact certified3533)
  apply certified_cons (by exact certified3533swap)
  apply certified_cons (by exact certified3534)
  apply certified_cons (by exact certified3534swap)
  apply certified_cons (by exact certified3535)
  apply certified_cons (by exact certified3535swap)
  apply certified_cons (by exact certified3536)
  apply certified_cons (by exact certified3536swap)
  apply certified_cons (by exact certified3537)
  apply certified_cons (by exact certified3537swap)
  apply certified_cons (by exact certified3538)
  apply certified_cons (by exact certified3538swap)
  apply certified_cons (by exact certified3539)
  apply certified_cons (by exact certified3539swap)
  apply certified_cons (by exact certified3540)
  apply certified_cons (by exact certified3540swap)
  apply certified_cons (by exact certified3541)
  apply certified_cons (by exact certified3541swap)
  apply certified_cons (by exact certified3542)
  apply certified_cons (by exact certified3542swap)
  apply certified_cons (by exact certified3543)
  apply certified_cons (by exact certified3543swap)
  apply certified_cons (by exact certified3544)
  apply certified_cons (by exact certified3544swap)
  apply certified_cons (by exact certified3545)
  apply certified_cons (by exact certified3545swap)
  apply certified_cons (by exact certified3546)
  apply certified_cons (by exact certified3546swap)
  apply certified_cons (by exact certified3547)
  apply certified_cons (by exact certified3547swap)
  apply certified_cons (by exact certified3548)
  apply certified_cons (by exact certified3548swap)
  apply certified_cons (by exact certified3549)
  apply certified_cons (by exact certified3549swap)
  simp
#print axioms certified_keys070
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
