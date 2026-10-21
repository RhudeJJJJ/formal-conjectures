/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeOneSmallKeysData
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0450
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0451
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0452
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0453
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0454
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0455
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0456
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0457
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0458
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0459
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0460
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0461
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0462
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0463
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0464
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0465
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0466
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0467
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0468
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0469
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0470
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0471
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0472
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0473
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0474
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0475
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0476
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0477
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0478
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0479
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0480
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0481
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0482
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0483
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0484
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0485
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0486
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0487
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0488
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0489
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0490
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0491
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0492
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0493
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0494
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0495
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0496
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0497
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0498
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0499
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeOneSmallActualCases
theorem certified_keys09 : ∀ k ∈ keys09, Certified k := by
  apply certified_cons (by exact certified0450)
  apply certified_cons (by exact certified0450swap)
  apply certified_cons (by exact certified0451)
  apply certified_cons (by exact certified0452)
  apply certified_cons (by exact certified0452swap)
  apply certified_cons (by exact certified0453)
  apply certified_cons (by exact certified0454)
  apply certified_cons (by exact certified0454swap)
  apply certified_cons (by exact certified0455)
  apply certified_cons (by exact certified0455swap)
  apply certified_cons (by exact certified0456)
  apply certified_cons (by exact certified0456swap)
  apply certified_cons (by exact certified0457)
  apply certified_cons (by exact certified0458)
  apply certified_cons (by exact certified0458swap)
  apply certified_cons (by exact certified0459)
  apply certified_cons (by exact certified0460)
  apply certified_cons (by exact certified0460swap)
  apply certified_cons (by exact certified0461)
  apply certified_cons (by exact certified0461swap)
  apply certified_cons (by exact certified0462)
  apply certified_cons (by exact certified0462swap)
  apply certified_cons (by exact certified0463)
  apply certified_cons (by exact certified0464)
  apply certified_cons (by exact certified0464swap)
  apply certified_cons (by exact certified0465)
  apply certified_cons (by exact certified0466)
  apply certified_cons (by exact certified0466swap)
  apply certified_cons (by exact certified0467)
  apply certified_cons (by exact certified0467swap)
  apply certified_cons (by exact certified0468)
  apply certified_cons (by exact certified0468swap)
  apply certified_cons (by exact certified0469)
  apply certified_cons (by exact certified0470)
  apply certified_cons (by exact certified0470swap)
  apply certified_cons (by exact certified0471)
  apply certified_cons (by exact certified0472)
  apply certified_cons (by exact certified0472swap)
  apply certified_cons (by exact certified0473)
  apply certified_cons (by exact certified0473swap)
  apply certified_cons (by exact certified0474)
  apply certified_cons (by exact certified0474swap)
  apply certified_cons (by exact certified0475)
  apply certified_cons (by exact certified0476)
  apply certified_cons (by exact certified0476swap)
  apply certified_cons (by exact certified0477)
  apply certified_cons (by exact certified0478)
  apply certified_cons (by exact certified0478swap)
  apply certified_cons (by exact certified0479)
  apply certified_cons (by exact certified0479swap)
  apply certified_cons (by exact certified0480)
  apply certified_cons (by exact certified0480swap)
  apply certified_cons (by exact certified0481)
  apply certified_cons (by exact certified0482)
  apply certified_cons (by exact certified0482swap)
  apply certified_cons (by exact certified0483)
  apply certified_cons (by exact certified0484)
  apply certified_cons (by exact certified0484swap)
  apply certified_cons (by exact certified0485)
  apply certified_cons (by exact certified0485swap)
  apply certified_cons (by exact certified0486)
  apply certified_cons (by exact certified0486swap)
  apply certified_cons (by exact certified0487)
  apply certified_cons (by exact certified0488)
  apply certified_cons (by exact certified0488swap)
  apply certified_cons (by exact certified0489)
  apply certified_cons (by exact certified0490)
  apply certified_cons (by exact certified0490swap)
  apply certified_cons (by exact certified0491)
  apply certified_cons (by exact certified0491swap)
  apply certified_cons (by exact certified0492)
  apply certified_cons (by exact certified0492swap)
  apply certified_cons (by exact certified0493)
  apply certified_cons (by exact certified0494)
  apply certified_cons (by exact certified0494swap)
  apply certified_cons (by exact certified0495)
  apply certified_cons (by exact certified0496)
  apply certified_cons (by exact certified0496swap)
  apply certified_cons (by exact certified0497)
  apply certified_cons (by exact certified0497swap)
  apply certified_cons (by exact certified0498)
  apply certified_cons (by exact certified0498swap)
  apply certified_cons (by exact certified0499)
  simp
#print axioms certified_keys09
end Gebendorfer.RadenkovicGutman.DegreeOneSmallKeys
