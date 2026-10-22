/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteKeysData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2550
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2551
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2552
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2553
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2554
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2555
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2556
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2557
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2558
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2559
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2560
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2561
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2562
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2563
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2564
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2565
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2566
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2567
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2568
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2569
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2570
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2571
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2572
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2573
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2574
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2575
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2576
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2577
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2578
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2579
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2580
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2581
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2582
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2583
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2584
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2585
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2586
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2587
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2588
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2589
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2590
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2591
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2592
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2593
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2594
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2595
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2596
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2597
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2598
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2599
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeTwoThreeFiniteActualCases
theorem certified_keys051 : ∀ k ∈ keys051, Certified k := by
  apply certified_cons (by exact certified2550)
  apply certified_cons (by exact certified2550swap)
  apply certified_cons (by exact certified2551)
  apply certified_cons (by exact certified2551swap)
  apply certified_cons (by exact certified2552)
  apply certified_cons (by exact certified2552swap)
  apply certified_cons (by exact certified2553)
  apply certified_cons (by exact certified2553swap)
  apply certified_cons (by exact certified2554)
  apply certified_cons (by exact certified2554swap)
  apply certified_cons (by exact certified2555)
  apply certified_cons (by exact certified2555swap)
  apply certified_cons (by exact certified2556)
  apply certified_cons (by exact certified2556swap)
  apply certified_cons (by exact certified2557)
  apply certified_cons (by exact certified2557swap)
  apply certified_cons (by exact certified2558)
  apply certified_cons (by exact certified2558swap)
  apply certified_cons (by exact certified2559)
  apply certified_cons (by exact certified2559swap)
  apply certified_cons (by exact certified2560)
  apply certified_cons (by exact certified2560swap)
  apply certified_cons (by exact certified2561)
  apply certified_cons (by exact certified2561swap)
  apply certified_cons (by exact certified2562)
  apply certified_cons (by exact certified2562swap)
  apply certified_cons (by exact certified2563)
  apply certified_cons (by exact certified2563swap)
  apply certified_cons (by exact certified2564)
  apply certified_cons (by exact certified2564swap)
  apply certified_cons (by exact certified2565)
  apply certified_cons (by exact certified2565swap)
  apply certified_cons (by exact certified2566)
  apply certified_cons (by exact certified2566swap)
  apply certified_cons (by exact certified2567)
  apply certified_cons (by exact certified2567swap)
  apply certified_cons (by exact certified2568)
  apply certified_cons (by exact certified2568swap)
  apply certified_cons (by exact certified2569)
  apply certified_cons (by exact certified2569swap)
  apply certified_cons (by exact certified2570)
  apply certified_cons (by exact certified2570swap)
  apply certified_cons (by exact certified2571)
  apply certified_cons (by exact certified2571swap)
  apply certified_cons (by exact certified2572)
  apply certified_cons (by exact certified2572swap)
  apply certified_cons (by exact certified2573)
  apply certified_cons (by exact certified2573swap)
  apply certified_cons (by exact certified2574)
  apply certified_cons (by exact certified2574swap)
  apply certified_cons (by exact certified2575)
  apply certified_cons (by exact certified2575swap)
  apply certified_cons (by exact certified2576)
  apply certified_cons (by exact certified2576swap)
  apply certified_cons (by exact certified2577)
  apply certified_cons (by exact certified2577swap)
  apply certified_cons (by exact certified2578)
  apply certified_cons (by exact certified2578swap)
  apply certified_cons (by exact certified2579)
  apply certified_cons (by exact certified2579swap)
  apply certified_cons (by exact certified2580)
  apply certified_cons (by exact certified2580swap)
  apply certified_cons (by exact certified2581)
  apply certified_cons (by exact certified2581swap)
  apply certified_cons (by exact certified2582)
  apply certified_cons (by exact certified2582swap)
  apply certified_cons (by exact certified2583)
  apply certified_cons (by exact certified2583swap)
  apply certified_cons (by exact certified2584)
  apply certified_cons (by exact certified2584swap)
  apply certified_cons (by exact certified2585)
  apply certified_cons (by exact certified2585swap)
  apply certified_cons (by exact certified2586)
  apply certified_cons (by exact certified2586swap)
  apply certified_cons (by exact certified2587)
  apply certified_cons (by exact certified2587swap)
  apply certified_cons (by exact certified2588)
  apply certified_cons (by exact certified2588swap)
  apply certified_cons (by exact certified2589)
  apply certified_cons (by exact certified2589swap)
  apply certified_cons (by exact certified2590)
  apply certified_cons (by exact certified2590swap)
  apply certified_cons (by exact certified2591)
  apply certified_cons (by exact certified2591swap)
  apply certified_cons (by exact certified2592)
  apply certified_cons (by exact certified2592swap)
  apply certified_cons (by exact certified2593)
  apply certified_cons (by exact certified2593swap)
  apply certified_cons (by exact certified2594)
  apply certified_cons (by exact certified2594swap)
  apply certified_cons (by exact certified2595)
  apply certified_cons (by exact certified2595swap)
  apply certified_cons (by exact certified2596)
  apply certified_cons (by exact certified2596swap)
  apply certified_cons (by exact certified2597)
  apply certified_cons (by exact certified2597swap)
  apply certified_cons (by exact certified2598)
  apply certified_cons (by exact certified2598swap)
  apply certified_cons (by exact certified2599)
  apply certified_cons (by exact certified2599swap)
  simp
#print axioms certified_keys051
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
