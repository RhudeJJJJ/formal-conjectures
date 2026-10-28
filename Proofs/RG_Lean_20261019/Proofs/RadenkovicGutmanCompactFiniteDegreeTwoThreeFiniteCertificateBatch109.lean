/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteKeysData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5450
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5451
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5452
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5453
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5454
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5455
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5456
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5457
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5458
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5459
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5460
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5461
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5462
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5463
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5464
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5465
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5466
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5467
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5468
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5469
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5470
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5471
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5472
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5473
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5474
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5475
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5476
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5477
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5478
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5479
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5480
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5481
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5482
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5483
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5484
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5485
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5486
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5487
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5488
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5489
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5490
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5491
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5492
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5493
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5494
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5495
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5496
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5497
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5498
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5499
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeTwoThreeFiniteActualCases
theorem certified_keys109 : ∀ k ∈ keys109, Certified k := by
  apply certified_cons (by exact certified5450)
  apply certified_cons (by exact certified5451)
  apply certified_cons (by exact certified5452)
  apply certified_cons (by exact certified5453)
  apply certified_cons (by exact certified5454)
  apply certified_cons (by exact certified5455)
  apply certified_cons (by exact certified5456)
  apply certified_cons (by exact certified5456swap)
  apply certified_cons (by exact certified5457)
  apply certified_cons (by exact certified5457swap)
  apply certified_cons (by exact certified5458)
  apply certified_cons (by exact certified5458swap)
  apply certified_cons (by exact certified5459)
  apply certified_cons (by exact certified5459swap)
  apply certified_cons (by exact certified5460)
  apply certified_cons (by exact certified5460swap)
  apply certified_cons (by exact certified5461)
  apply certified_cons (by exact certified5461swap)
  apply certified_cons (by exact certified5462)
  apply certified_cons (by exact certified5462swap)
  apply certified_cons (by exact certified5463)
  apply certified_cons (by exact certified5463swap)
  apply certified_cons (by exact certified5464)
  apply certified_cons (by exact certified5464swap)
  apply certified_cons (by exact certified5465)
  apply certified_cons (by exact certified5465swap)
  apply certified_cons (by exact certified5466)
  apply certified_cons (by exact certified5466swap)
  apply certified_cons (by exact certified5467)
  apply certified_cons (by exact certified5467swap)
  apply certified_cons (by exact certified5468)
  apply certified_cons (by exact certified5468swap)
  apply certified_cons (by exact certified5469)
  apply certified_cons (by exact certified5469swap)
  apply certified_cons (by exact certified5470)
  apply certified_cons (by exact certified5470swap)
  apply certified_cons (by exact certified5471)
  apply certified_cons (by exact certified5471swap)
  apply certified_cons (by exact certified5472)
  apply certified_cons (by exact certified5472swap)
  apply certified_cons (by exact certified5473)
  apply certified_cons (by exact certified5473swap)
  apply certified_cons (by exact certified5474)
  apply certified_cons (by exact certified5474swap)
  apply certified_cons (by exact certified5475)
  apply certified_cons (by exact certified5475swap)
  apply certified_cons (by exact certified5476)
  apply certified_cons (by exact certified5476swap)
  apply certified_cons (by exact certified5477)
  apply certified_cons (by exact certified5477swap)
  apply certified_cons (by exact certified5478)
  apply certified_cons (by exact certified5478swap)
  apply certified_cons (by exact certified5479)
  apply certified_cons (by exact certified5479swap)
  apply certified_cons (by exact certified5480)
  apply certified_cons (by exact certified5480swap)
  apply certified_cons (by exact certified5481)
  apply certified_cons (by exact certified5481swap)
  apply certified_cons (by exact certified5482)
  apply certified_cons (by exact certified5482swap)
  apply certified_cons (by exact certified5483)
  apply certified_cons (by exact certified5483swap)
  apply certified_cons (by exact certified5484)
  apply certified_cons (by exact certified5484swap)
  apply certified_cons (by exact certified5485)
  apply certified_cons (by exact certified5485swap)
  apply certified_cons (by exact certified5486)
  apply certified_cons (by exact certified5486swap)
  apply certified_cons (by exact certified5487)
  apply certified_cons (by exact certified5487swap)
  apply certified_cons (by exact certified5488)
  apply certified_cons (by exact certified5488swap)
  apply certified_cons (by exact certified5489)
  apply certified_cons (by exact certified5490)
  apply certified_cons (by exact certified5490swap)
  apply certified_cons (by exact certified5491)
  apply certified_cons (by exact certified5491swap)
  apply certified_cons (by exact certified5492)
  apply certified_cons (by exact certified5492swap)
  apply certified_cons (by exact certified5493)
  apply certified_cons (by exact certified5494)
  apply certified_cons (by exact certified5495)
  apply certified_cons (by exact certified5496)
  apply certified_cons (by exact certified5497)
  apply certified_cons (by exact certified5498)
  apply certified_cons (by exact certified5499)
  simp
#print axioms certified_keys109
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
