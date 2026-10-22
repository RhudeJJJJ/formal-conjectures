/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteKeysData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2600
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2601
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2602
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2603
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2604
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2605
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2606
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2607
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2608
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2609
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2610
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2611
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2612
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2613
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2614
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2615
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2616
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2617
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2618
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2619
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2620
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2621
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2622
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2623
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2624
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2625
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2626
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2627
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2628
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2629
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2630
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2631
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2632
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2633
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2634
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2635
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2636
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2637
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2638
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2639
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2640
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2641
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2642
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2643
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2644
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2645
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2646
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2647
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2648
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2649
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeTwoThreeFiniteActualCases
theorem certified_keys052 : ∀ k ∈ keys052, Certified k := by
  apply certified_cons (by exact certified2600)
  apply certified_cons (by exact certified2600swap)
  apply certified_cons (by exact certified2601)
  apply certified_cons (by exact certified2601swap)
  apply certified_cons (by exact certified2602)
  apply certified_cons (by exact certified2602swap)
  apply certified_cons (by exact certified2603)
  apply certified_cons (by exact certified2603swap)
  apply certified_cons (by exact certified2604)
  apply certified_cons (by exact certified2604swap)
  apply certified_cons (by exact certified2605)
  apply certified_cons (by exact certified2605swap)
  apply certified_cons (by exact certified2606)
  apply certified_cons (by exact certified2606swap)
  apply certified_cons (by exact certified2607)
  apply certified_cons (by exact certified2607swap)
  apply certified_cons (by exact certified2608)
  apply certified_cons (by exact certified2608swap)
  apply certified_cons (by exact certified2609)
  apply certified_cons (by exact certified2609swap)
  apply certified_cons (by exact certified2610)
  apply certified_cons (by exact certified2610swap)
  apply certified_cons (by exact certified2611)
  apply certified_cons (by exact certified2611swap)
  apply certified_cons (by exact certified2612)
  apply certified_cons (by exact certified2612swap)
  apply certified_cons (by exact certified2613)
  apply certified_cons (by exact certified2613swap)
  apply certified_cons (by exact certified2614)
  apply certified_cons (by exact certified2614swap)
  apply certified_cons (by exact certified2615)
  apply certified_cons (by exact certified2615swap)
  apply certified_cons (by exact certified2616)
  apply certified_cons (by exact certified2616swap)
  apply certified_cons (by exact certified2617)
  apply certified_cons (by exact certified2617swap)
  apply certified_cons (by exact certified2618)
  apply certified_cons (by exact certified2618swap)
  apply certified_cons (by exact certified2619)
  apply certified_cons (by exact certified2619swap)
  apply certified_cons (by exact certified2620)
  apply certified_cons (by exact certified2620swap)
  apply certified_cons (by exact certified2621)
  apply certified_cons (by exact certified2621swap)
  apply certified_cons (by exact certified2622)
  apply certified_cons (by exact certified2622swap)
  apply certified_cons (by exact certified2623)
  apply certified_cons (by exact certified2623swap)
  apply certified_cons (by exact certified2624)
  apply certified_cons (by exact certified2624swap)
  apply certified_cons (by exact certified2625)
  apply certified_cons (by exact certified2625swap)
  apply certified_cons (by exact certified2626)
  apply certified_cons (by exact certified2626swap)
  apply certified_cons (by exact certified2627)
  apply certified_cons (by exact certified2627swap)
  apply certified_cons (by exact certified2628)
  apply certified_cons (by exact certified2628swap)
  apply certified_cons (by exact certified2629)
  apply certified_cons (by exact certified2629swap)
  apply certified_cons (by exact certified2630)
  apply certified_cons (by exact certified2630swap)
  apply certified_cons (by exact certified2631)
  apply certified_cons (by exact certified2631swap)
  apply certified_cons (by exact certified2632)
  apply certified_cons (by exact certified2632swap)
  apply certified_cons (by exact certified2633)
  apply certified_cons (by exact certified2633swap)
  apply certified_cons (by exact certified2634)
  apply certified_cons (by exact certified2634swap)
  apply certified_cons (by exact certified2635)
  apply certified_cons (by exact certified2635swap)
  apply certified_cons (by exact certified2636)
  apply certified_cons (by exact certified2636swap)
  apply certified_cons (by exact certified2637)
  apply certified_cons (by exact certified2637swap)
  apply certified_cons (by exact certified2638)
  apply certified_cons (by exact certified2638swap)
  apply certified_cons (by exact certified2639)
  apply certified_cons (by exact certified2639swap)
  apply certified_cons (by exact certified2640)
  apply certified_cons (by exact certified2640swap)
  apply certified_cons (by exact certified2641)
  apply certified_cons (by exact certified2641swap)
  apply certified_cons (by exact certified2642)
  apply certified_cons (by exact certified2642swap)
  apply certified_cons (by exact certified2643)
  apply certified_cons (by exact certified2643swap)
  apply certified_cons (by exact certified2644)
  apply certified_cons (by exact certified2644swap)
  apply certified_cons (by exact certified2645)
  apply certified_cons (by exact certified2645swap)
  apply certified_cons (by exact certified2646)
  apply certified_cons (by exact certified2646swap)
  apply certified_cons (by exact certified2647)
  apply certified_cons (by exact certified2647swap)
  apply certified_cons (by exact certified2648)
  apply certified_cons (by exact certified2648swap)
  apply certified_cons (by exact certified2649)
  apply certified_cons (by exact certified2649swap)
  simp
#print axioms certified_keys052
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
