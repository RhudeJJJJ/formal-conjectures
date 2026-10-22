/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteKeysData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0450
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0451
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0452
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0453
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0454
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0455
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0456
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0457
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0458
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0459
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0460
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0461
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0462
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0463
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0464
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0465
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0466
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0467
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0468
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0469
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0470
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0471
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0472
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0473
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0474
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0475
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0476
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0477
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0478
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0479
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0480
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0481
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0482
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0483
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0484
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0485
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0486
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0487
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0488
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0489
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0490
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0491
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0492
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0493
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0494
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0495
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0496
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0497
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0498
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0499
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeTwoThreeFiniteActualCases
theorem certified_keys009 : ∀ k ∈ keys009, Certified k := by
  apply certified_cons (by exact certified0450)
  apply certified_cons (by exact certified0451)
  apply certified_cons (by exact certified0452)
  apply certified_cons (by exact certified0453)
  apply certified_cons (by exact certified0454)
  apply certified_cons (by exact certified0455)
  apply certified_cons (by exact certified0456)
  apply certified_cons (by exact certified0457)
  apply certified_cons (by exact certified0458)
  apply certified_cons (by exact certified0459)
  apply certified_cons (by exact certified0460)
  apply certified_cons (by exact certified0461)
  apply certified_cons (by exact certified0462)
  apply certified_cons (by exact certified0463)
  apply certified_cons (by exact certified0464)
  apply certified_cons (by exact certified0465)
  apply certified_cons (by exact certified0466)
  apply certified_cons (by exact certified0467)
  apply certified_cons (by exact certified0468)
  apply certified_cons (by exact certified0469)
  apply certified_cons (by exact certified0470)
  apply certified_cons (by exact certified0471)
  apply certified_cons (by exact certified0472)
  apply certified_cons (by exact certified0473)
  apply certified_cons (by exact certified0474)
  apply certified_cons (by exact certified0475)
  apply certified_cons (by exact certified0476)
  apply certified_cons (by exact certified0477)
  apply certified_cons (by exact certified0478)
  apply certified_cons (by exact certified0479)
  apply certified_cons (by exact certified0480)
  apply certified_cons (by exact certified0481)
  apply certified_cons (by exact certified0482)
  apply certified_cons (by exact certified0483)
  apply certified_cons (by exact certified0484)
  apply certified_cons (by exact certified0485)
  apply certified_cons (by exact certified0486)
  apply certified_cons (by exact certified0487)
  apply certified_cons (by exact certified0488)
  apply certified_cons (by exact certified0489)
  apply certified_cons (by exact certified0490)
  apply certified_cons (by exact certified0491)
  apply certified_cons (by exact certified0492)
  apply certified_cons (by exact certified0493)
  apply certified_cons (by exact certified0494)
  apply certified_cons (by exact certified0495)
  apply certified_cons (by exact certified0496)
  apply certified_cons (by exact certified0497)
  apply certified_cons (by exact certified0498)
  apply certified_cons (by exact certified0499)
  simp
#print axioms certified_keys009
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
