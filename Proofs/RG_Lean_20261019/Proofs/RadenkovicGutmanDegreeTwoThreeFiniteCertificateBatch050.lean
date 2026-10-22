/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteKeysData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2500
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2501
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2502
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2503
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2504
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2505
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2506
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2507
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2508
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2509
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2510
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2511
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2512
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2513
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2514
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2515
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2516
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2517
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2518
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2519
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2520
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2521
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2522
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2523
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2524
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2525
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2526
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2527
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2528
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2529
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2530
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2531
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2532
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2533
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2534
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2535
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2536
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2537
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2538
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2539
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2540
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2541
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2542
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2543
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2544
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2545
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2546
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2547
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2548
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2549
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeTwoThreeFiniteActualCases
theorem certified_keys050 : ∀ k ∈ keys050, Certified k := by
  apply certified_cons (by exact certified2500)
  apply certified_cons (by exact certified2500swap)
  apply certified_cons (by exact certified2501)
  apply certified_cons (by exact certified2501swap)
  apply certified_cons (by exact certified2502)
  apply certified_cons (by exact certified2502swap)
  apply certified_cons (by exact certified2503)
  apply certified_cons (by exact certified2503swap)
  apply certified_cons (by exact certified2504)
  apply certified_cons (by exact certified2504swap)
  apply certified_cons (by exact certified2505)
  apply certified_cons (by exact certified2505swap)
  apply certified_cons (by exact certified2506)
  apply certified_cons (by exact certified2506swap)
  apply certified_cons (by exact certified2507)
  apply certified_cons (by exact certified2507swap)
  apply certified_cons (by exact certified2508)
  apply certified_cons (by exact certified2508swap)
  apply certified_cons (by exact certified2509)
  apply certified_cons (by exact certified2509swap)
  apply certified_cons (by exact certified2510)
  apply certified_cons (by exact certified2510swap)
  apply certified_cons (by exact certified2511)
  apply certified_cons (by exact certified2511swap)
  apply certified_cons (by exact certified2512)
  apply certified_cons (by exact certified2512swap)
  apply certified_cons (by exact certified2513)
  apply certified_cons (by exact certified2513swap)
  apply certified_cons (by exact certified2514)
  apply certified_cons (by exact certified2514swap)
  apply certified_cons (by exact certified2515)
  apply certified_cons (by exact certified2515swap)
  apply certified_cons (by exact certified2516)
  apply certified_cons (by exact certified2516swap)
  apply certified_cons (by exact certified2517)
  apply certified_cons (by exact certified2517swap)
  apply certified_cons (by exact certified2518)
  apply certified_cons (by exact certified2518swap)
  apply certified_cons (by exact certified2519)
  apply certified_cons (by exact certified2519swap)
  apply certified_cons (by exact certified2520)
  apply certified_cons (by exact certified2520swap)
  apply certified_cons (by exact certified2521)
  apply certified_cons (by exact certified2521swap)
  apply certified_cons (by exact certified2522)
  apply certified_cons (by exact certified2522swap)
  apply certified_cons (by exact certified2523)
  apply certified_cons (by exact certified2523swap)
  apply certified_cons (by exact certified2524)
  apply certified_cons (by exact certified2524swap)
  apply certified_cons (by exact certified2525)
  apply certified_cons (by exact certified2525swap)
  apply certified_cons (by exact certified2526)
  apply certified_cons (by exact certified2526swap)
  apply certified_cons (by exact certified2527)
  apply certified_cons (by exact certified2527swap)
  apply certified_cons (by exact certified2528)
  apply certified_cons (by exact certified2528swap)
  apply certified_cons (by exact certified2529)
  apply certified_cons (by exact certified2529swap)
  apply certified_cons (by exact certified2530)
  apply certified_cons (by exact certified2530swap)
  apply certified_cons (by exact certified2531)
  apply certified_cons (by exact certified2531swap)
  apply certified_cons (by exact certified2532)
  apply certified_cons (by exact certified2532swap)
  apply certified_cons (by exact certified2533)
  apply certified_cons (by exact certified2533swap)
  apply certified_cons (by exact certified2534)
  apply certified_cons (by exact certified2534swap)
  apply certified_cons (by exact certified2535)
  apply certified_cons (by exact certified2535swap)
  apply certified_cons (by exact certified2536)
  apply certified_cons (by exact certified2536swap)
  apply certified_cons (by exact certified2537)
  apply certified_cons (by exact certified2537swap)
  apply certified_cons (by exact certified2538)
  apply certified_cons (by exact certified2538swap)
  apply certified_cons (by exact certified2539)
  apply certified_cons (by exact certified2539swap)
  apply certified_cons (by exact certified2540)
  apply certified_cons (by exact certified2540swap)
  apply certified_cons (by exact certified2541)
  apply certified_cons (by exact certified2541swap)
  apply certified_cons (by exact certified2542)
  apply certified_cons (by exact certified2542swap)
  apply certified_cons (by exact certified2543)
  apply certified_cons (by exact certified2543swap)
  apply certified_cons (by exact certified2544)
  apply certified_cons (by exact certified2544swap)
  apply certified_cons (by exact certified2545)
  apply certified_cons (by exact certified2545swap)
  apply certified_cons (by exact certified2546)
  apply certified_cons (by exact certified2546swap)
  apply certified_cons (by exact certified2547)
  apply certified_cons (by exact certified2547swap)
  apply certified_cons (by exact certified2548)
  apply certified_cons (by exact certified2548swap)
  apply certified_cons (by exact certified2549)
  apply certified_cons (by exact certified2549swap)
  simp
#print axioms certified_keys050
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
