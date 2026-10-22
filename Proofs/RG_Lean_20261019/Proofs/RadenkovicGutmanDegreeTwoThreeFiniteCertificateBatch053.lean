/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteKeysData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2650
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2651
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2652
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2653
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2654
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2655
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2656
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2657
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2658
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2659
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2660
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2661
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2662
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2663
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2664
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2665
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2666
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2667
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2668
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2669
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2670
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2671
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2672
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2673
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2674
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2675
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2676
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2677
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2678
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2679
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2680
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2681
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2682
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2683
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2684
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2685
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2686
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2687
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2688
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2689
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2690
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2691
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2692
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2693
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2694
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2695
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2696
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2697
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2698
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2699
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeTwoThreeFiniteActualCases
theorem certified_keys053 : ∀ k ∈ keys053, Certified k := by
  apply certified_cons (by exact certified2650)
  apply certified_cons (by exact certified2650swap)
  apply certified_cons (by exact certified2651)
  apply certified_cons (by exact certified2651swap)
  apply certified_cons (by exact certified2652)
  apply certified_cons (by exact certified2652swap)
  apply certified_cons (by exact certified2653)
  apply certified_cons (by exact certified2653swap)
  apply certified_cons (by exact certified2654)
  apply certified_cons (by exact certified2654swap)
  apply certified_cons (by exact certified2655)
  apply certified_cons (by exact certified2655swap)
  apply certified_cons (by exact certified2656)
  apply certified_cons (by exact certified2656swap)
  apply certified_cons (by exact certified2657)
  apply certified_cons (by exact certified2657swap)
  apply certified_cons (by exact certified2658)
  apply certified_cons (by exact certified2658swap)
  apply certified_cons (by exact certified2659)
  apply certified_cons (by exact certified2659swap)
  apply certified_cons (by exact certified2660)
  apply certified_cons (by exact certified2660swap)
  apply certified_cons (by exact certified2661)
  apply certified_cons (by exact certified2661swap)
  apply certified_cons (by exact certified2662)
  apply certified_cons (by exact certified2662swap)
  apply certified_cons (by exact certified2663)
  apply certified_cons (by exact certified2663swap)
  apply certified_cons (by exact certified2664)
  apply certified_cons (by exact certified2664swap)
  apply certified_cons (by exact certified2665)
  apply certified_cons (by exact certified2665swap)
  apply certified_cons (by exact certified2666)
  apply certified_cons (by exact certified2666swap)
  apply certified_cons (by exact certified2667)
  apply certified_cons (by exact certified2667swap)
  apply certified_cons (by exact certified2668)
  apply certified_cons (by exact certified2668swap)
  apply certified_cons (by exact certified2669)
  apply certified_cons (by exact certified2669swap)
  apply certified_cons (by exact certified2670)
  apply certified_cons (by exact certified2670swap)
  apply certified_cons (by exact certified2671)
  apply certified_cons (by exact certified2671swap)
  apply certified_cons (by exact certified2672)
  apply certified_cons (by exact certified2672swap)
  apply certified_cons (by exact certified2673)
  apply certified_cons (by exact certified2673swap)
  apply certified_cons (by exact certified2674)
  apply certified_cons (by exact certified2674swap)
  apply certified_cons (by exact certified2675)
  apply certified_cons (by exact certified2675swap)
  apply certified_cons (by exact certified2676)
  apply certified_cons (by exact certified2676swap)
  apply certified_cons (by exact certified2677)
  apply certified_cons (by exact certified2677swap)
  apply certified_cons (by exact certified2678)
  apply certified_cons (by exact certified2678swap)
  apply certified_cons (by exact certified2679)
  apply certified_cons (by exact certified2679swap)
  apply certified_cons (by exact certified2680)
  apply certified_cons (by exact certified2680swap)
  apply certified_cons (by exact certified2681)
  apply certified_cons (by exact certified2681swap)
  apply certified_cons (by exact certified2682)
  apply certified_cons (by exact certified2682swap)
  apply certified_cons (by exact certified2683)
  apply certified_cons (by exact certified2683swap)
  apply certified_cons (by exact certified2684)
  apply certified_cons (by exact certified2684swap)
  apply certified_cons (by exact certified2685)
  apply certified_cons (by exact certified2685swap)
  apply certified_cons (by exact certified2686)
  apply certified_cons (by exact certified2686swap)
  apply certified_cons (by exact certified2687)
  apply certified_cons (by exact certified2687swap)
  apply certified_cons (by exact certified2688)
  apply certified_cons (by exact certified2688swap)
  apply certified_cons (by exact certified2689)
  apply certified_cons (by exact certified2689swap)
  apply certified_cons (by exact certified2690)
  apply certified_cons (by exact certified2690swap)
  apply certified_cons (by exact certified2691)
  apply certified_cons (by exact certified2691swap)
  apply certified_cons (by exact certified2692)
  apply certified_cons (by exact certified2692swap)
  apply certified_cons (by exact certified2693)
  apply certified_cons (by exact certified2693swap)
  apply certified_cons (by exact certified2694)
  apply certified_cons (by exact certified2694swap)
  apply certified_cons (by exact certified2695)
  apply certified_cons (by exact certified2695swap)
  apply certified_cons (by exact certified2696)
  apply certified_cons (by exact certified2696swap)
  apply certified_cons (by exact certified2697)
  apply certified_cons (by exact certified2697swap)
  apply certified_cons (by exact certified2698)
  apply certified_cons (by exact certified2698swap)
  apply certified_cons (by exact certified2699)
  apply certified_cons (by exact certified2699swap)
  simp
#print axioms certified_keys053
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
