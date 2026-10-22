/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteKeysData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3450
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3451
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3452
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3453
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3454
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3455
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3456
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3457
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3458
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3459
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3460
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3461
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3462
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3463
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3464
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3465
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3466
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3467
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3468
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3469
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3470
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3471
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3472
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3473
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3474
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3475
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3476
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3477
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3478
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3479
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3480
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3481
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3482
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3483
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3484
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3485
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3486
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3487
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3488
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3489
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3490
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3491
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3492
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3493
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3494
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3495
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3496
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3497
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3498
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3499
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeTwoThreeFiniteActualCases
theorem certified_keys069 : ∀ k ∈ keys069, Certified k := by
  apply certified_cons (by exact certified3450)
  apply certified_cons (by exact certified3450swap)
  apply certified_cons (by exact certified3451)
  apply certified_cons (by exact certified3451swap)
  apply certified_cons (by exact certified3452)
  apply certified_cons (by exact certified3452swap)
  apply certified_cons (by exact certified3453)
  apply certified_cons (by exact certified3453swap)
  apply certified_cons (by exact certified3454)
  apply certified_cons (by exact certified3454swap)
  apply certified_cons (by exact certified3455)
  apply certified_cons (by exact certified3455swap)
  apply certified_cons (by exact certified3456)
  apply certified_cons (by exact certified3456swap)
  apply certified_cons (by exact certified3457)
  apply certified_cons (by exact certified3457swap)
  apply certified_cons (by exact certified3458)
  apply certified_cons (by exact certified3458swap)
  apply certified_cons (by exact certified3459)
  apply certified_cons (by exact certified3459swap)
  apply certified_cons (by exact certified3460)
  apply certified_cons (by exact certified3460swap)
  apply certified_cons (by exact certified3461)
  apply certified_cons (by exact certified3461swap)
  apply certified_cons (by exact certified3462)
  apply certified_cons (by exact certified3462swap)
  apply certified_cons (by exact certified3463)
  apply certified_cons (by exact certified3463swap)
  apply certified_cons (by exact certified3464)
  apply certified_cons (by exact certified3464swap)
  apply certified_cons (by exact certified3465)
  apply certified_cons (by exact certified3465swap)
  apply certified_cons (by exact certified3466)
  apply certified_cons (by exact certified3466swap)
  apply certified_cons (by exact certified3467)
  apply certified_cons (by exact certified3467swap)
  apply certified_cons (by exact certified3468)
  apply certified_cons (by exact certified3468swap)
  apply certified_cons (by exact certified3469)
  apply certified_cons (by exact certified3469swap)
  apply certified_cons (by exact certified3470)
  apply certified_cons (by exact certified3470swap)
  apply certified_cons (by exact certified3471)
  apply certified_cons (by exact certified3471swap)
  apply certified_cons (by exact certified3472)
  apply certified_cons (by exact certified3472swap)
  apply certified_cons (by exact certified3473)
  apply certified_cons (by exact certified3473swap)
  apply certified_cons (by exact certified3474)
  apply certified_cons (by exact certified3474swap)
  apply certified_cons (by exact certified3475)
  apply certified_cons (by exact certified3475swap)
  apply certified_cons (by exact certified3476)
  apply certified_cons (by exact certified3476swap)
  apply certified_cons (by exact certified3477)
  apply certified_cons (by exact certified3477swap)
  apply certified_cons (by exact certified3478)
  apply certified_cons (by exact certified3478swap)
  apply certified_cons (by exact certified3479)
  apply certified_cons (by exact certified3479swap)
  apply certified_cons (by exact certified3480)
  apply certified_cons (by exact certified3480swap)
  apply certified_cons (by exact certified3481)
  apply certified_cons (by exact certified3481swap)
  apply certified_cons (by exact certified3482)
  apply certified_cons (by exact certified3482swap)
  apply certified_cons (by exact certified3483)
  apply certified_cons (by exact certified3483swap)
  apply certified_cons (by exact certified3484)
  apply certified_cons (by exact certified3484swap)
  apply certified_cons (by exact certified3485)
  apply certified_cons (by exact certified3485swap)
  apply certified_cons (by exact certified3486)
  apply certified_cons (by exact certified3486swap)
  apply certified_cons (by exact certified3487)
  apply certified_cons (by exact certified3487swap)
  apply certified_cons (by exact certified3488)
  apply certified_cons (by exact certified3488swap)
  apply certified_cons (by exact certified3489)
  apply certified_cons (by exact certified3489swap)
  apply certified_cons (by exact certified3490)
  apply certified_cons (by exact certified3490swap)
  apply certified_cons (by exact certified3491)
  apply certified_cons (by exact certified3491swap)
  apply certified_cons (by exact certified3492)
  apply certified_cons (by exact certified3492swap)
  apply certified_cons (by exact certified3493)
  apply certified_cons (by exact certified3493swap)
  apply certified_cons (by exact certified3494)
  apply certified_cons (by exact certified3494swap)
  apply certified_cons (by exact certified3495)
  apply certified_cons (by exact certified3495swap)
  apply certified_cons (by exact certified3496)
  apply certified_cons (by exact certified3496swap)
  apply certified_cons (by exact certified3497)
  apply certified_cons (by exact certified3497swap)
  apply certified_cons (by exact certified3498)
  apply certified_cons (by exact certified3498swap)
  apply certified_cons (by exact certified3499)
  apply certified_cons (by exact certified3499swap)
  simp
#print axioms certified_keys069
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
