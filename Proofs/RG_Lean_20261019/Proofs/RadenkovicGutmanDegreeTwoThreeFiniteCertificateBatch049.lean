/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteKeysData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2450
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2451
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2452
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2453
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2454
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2455
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2456
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2457
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2458
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2459
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2460
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2461
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2462
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2463
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2464
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2465
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2466
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2467
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2468
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2469
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2470
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2471
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2472
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2473
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2474
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2475
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2476
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2477
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2478
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2479
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2480
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2481
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2482
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2483
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2484
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2485
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2486
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2487
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2488
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2489
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2490
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2491
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2492
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2493
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2494
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2495
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2496
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2497
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2498
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2499
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeTwoThreeFiniteActualCases
theorem certified_keys049 : ∀ k ∈ keys049, Certified k := by
  apply certified_cons (by exact certified2450)
  apply certified_cons (by exact certified2450swap)
  apply certified_cons (by exact certified2451)
  apply certified_cons (by exact certified2451swap)
  apply certified_cons (by exact certified2452)
  apply certified_cons (by exact certified2452swap)
  apply certified_cons (by exact certified2453)
  apply certified_cons (by exact certified2453swap)
  apply certified_cons (by exact certified2454)
  apply certified_cons (by exact certified2454swap)
  apply certified_cons (by exact certified2455)
  apply certified_cons (by exact certified2455swap)
  apply certified_cons (by exact certified2456)
  apply certified_cons (by exact certified2456swap)
  apply certified_cons (by exact certified2457)
  apply certified_cons (by exact certified2457swap)
  apply certified_cons (by exact certified2458)
  apply certified_cons (by exact certified2458swap)
  apply certified_cons (by exact certified2459)
  apply certified_cons (by exact certified2459swap)
  apply certified_cons (by exact certified2460)
  apply certified_cons (by exact certified2460swap)
  apply certified_cons (by exact certified2461)
  apply certified_cons (by exact certified2461swap)
  apply certified_cons (by exact certified2462)
  apply certified_cons (by exact certified2462swap)
  apply certified_cons (by exact certified2463)
  apply certified_cons (by exact certified2463swap)
  apply certified_cons (by exact certified2464)
  apply certified_cons (by exact certified2464swap)
  apply certified_cons (by exact certified2465)
  apply certified_cons (by exact certified2465swap)
  apply certified_cons (by exact certified2466)
  apply certified_cons (by exact certified2466swap)
  apply certified_cons (by exact certified2467)
  apply certified_cons (by exact certified2467swap)
  apply certified_cons (by exact certified2468)
  apply certified_cons (by exact certified2468swap)
  apply certified_cons (by exact certified2469)
  apply certified_cons (by exact certified2469swap)
  apply certified_cons (by exact certified2470)
  apply certified_cons (by exact certified2470swap)
  apply certified_cons (by exact certified2471)
  apply certified_cons (by exact certified2471swap)
  apply certified_cons (by exact certified2472)
  apply certified_cons (by exact certified2472swap)
  apply certified_cons (by exact certified2473)
  apply certified_cons (by exact certified2473swap)
  apply certified_cons (by exact certified2474)
  apply certified_cons (by exact certified2474swap)
  apply certified_cons (by exact certified2475)
  apply certified_cons (by exact certified2475swap)
  apply certified_cons (by exact certified2476)
  apply certified_cons (by exact certified2476swap)
  apply certified_cons (by exact certified2477)
  apply certified_cons (by exact certified2477swap)
  apply certified_cons (by exact certified2478)
  apply certified_cons (by exact certified2478swap)
  apply certified_cons (by exact certified2479)
  apply certified_cons (by exact certified2479swap)
  apply certified_cons (by exact certified2480)
  apply certified_cons (by exact certified2480swap)
  apply certified_cons (by exact certified2481)
  apply certified_cons (by exact certified2481swap)
  apply certified_cons (by exact certified2482)
  apply certified_cons (by exact certified2482swap)
  apply certified_cons (by exact certified2483)
  apply certified_cons (by exact certified2483swap)
  apply certified_cons (by exact certified2484)
  apply certified_cons (by exact certified2484swap)
  apply certified_cons (by exact certified2485)
  apply certified_cons (by exact certified2485swap)
  apply certified_cons (by exact certified2486)
  apply certified_cons (by exact certified2486swap)
  apply certified_cons (by exact certified2487)
  apply certified_cons (by exact certified2487swap)
  apply certified_cons (by exact certified2488)
  apply certified_cons (by exact certified2488swap)
  apply certified_cons (by exact certified2489)
  apply certified_cons (by exact certified2489swap)
  apply certified_cons (by exact certified2490)
  apply certified_cons (by exact certified2490swap)
  apply certified_cons (by exact certified2491)
  apply certified_cons (by exact certified2491swap)
  apply certified_cons (by exact certified2492)
  apply certified_cons (by exact certified2492swap)
  apply certified_cons (by exact certified2493)
  apply certified_cons (by exact certified2493swap)
  apply certified_cons (by exact certified2494)
  apply certified_cons (by exact certified2494swap)
  apply certified_cons (by exact certified2495)
  apply certified_cons (by exact certified2495swap)
  apply certified_cons (by exact certified2496)
  apply certified_cons (by exact certified2496swap)
  apply certified_cons (by exact certified2497)
  apply certified_cons (by exact certified2497swap)
  apply certified_cons (by exact certified2498)
  apply certified_cons (by exact certified2498swap)
  apply certified_cons (by exact certified2499)
  apply certified_cons (by exact certified2499swap)
  simp
#print axioms certified_keys049
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
