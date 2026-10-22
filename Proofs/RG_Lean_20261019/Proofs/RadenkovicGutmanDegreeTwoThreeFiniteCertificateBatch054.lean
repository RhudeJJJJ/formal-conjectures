/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteKeysData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2700
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2701
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2702
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2703
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2704
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2705
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2706
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2707
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2708
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2709
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2710
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2711
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2712
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2713
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2714
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2715
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2716
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2717
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2718
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2719
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2720
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2721
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2722
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2723
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2724
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2725
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2726
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2727
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2728
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2729
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2730
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2731
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2732
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2733
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2734
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2735
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2736
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2737
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2738
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2739
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2740
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2741
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2742
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2743
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2744
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2745
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2746
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2747
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2748
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2749
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeTwoThreeFiniteActualCases
theorem certified_keys054 : ∀ k ∈ keys054, Certified k := by
  apply certified_cons (by exact certified2700)
  apply certified_cons (by exact certified2700swap)
  apply certified_cons (by exact certified2701)
  apply certified_cons (by exact certified2701swap)
  apply certified_cons (by exact certified2702)
  apply certified_cons (by exact certified2702swap)
  apply certified_cons (by exact certified2703)
  apply certified_cons (by exact certified2703swap)
  apply certified_cons (by exact certified2704)
  apply certified_cons (by exact certified2704swap)
  apply certified_cons (by exact certified2705)
  apply certified_cons (by exact certified2705swap)
  apply certified_cons (by exact certified2706)
  apply certified_cons (by exact certified2706swap)
  apply certified_cons (by exact certified2707)
  apply certified_cons (by exact certified2707swap)
  apply certified_cons (by exact certified2708)
  apply certified_cons (by exact certified2708swap)
  apply certified_cons (by exact certified2709)
  apply certified_cons (by exact certified2709swap)
  apply certified_cons (by exact certified2710)
  apply certified_cons (by exact certified2710swap)
  apply certified_cons (by exact certified2711)
  apply certified_cons (by exact certified2711swap)
  apply certified_cons (by exact certified2712)
  apply certified_cons (by exact certified2712swap)
  apply certified_cons (by exact certified2713)
  apply certified_cons (by exact certified2713swap)
  apply certified_cons (by exact certified2714)
  apply certified_cons (by exact certified2714swap)
  apply certified_cons (by exact certified2715)
  apply certified_cons (by exact certified2715swap)
  apply certified_cons (by exact certified2716)
  apply certified_cons (by exact certified2716swap)
  apply certified_cons (by exact certified2717)
  apply certified_cons (by exact certified2717swap)
  apply certified_cons (by exact certified2718)
  apply certified_cons (by exact certified2718swap)
  apply certified_cons (by exact certified2719)
  apply certified_cons (by exact certified2719swap)
  apply certified_cons (by exact certified2720)
  apply certified_cons (by exact certified2720swap)
  apply certified_cons (by exact certified2721)
  apply certified_cons (by exact certified2721swap)
  apply certified_cons (by exact certified2722)
  apply certified_cons (by exact certified2722swap)
  apply certified_cons (by exact certified2723)
  apply certified_cons (by exact certified2723swap)
  apply certified_cons (by exact certified2724)
  apply certified_cons (by exact certified2724swap)
  apply certified_cons (by exact certified2725)
  apply certified_cons (by exact certified2725swap)
  apply certified_cons (by exact certified2726)
  apply certified_cons (by exact certified2726swap)
  apply certified_cons (by exact certified2727)
  apply certified_cons (by exact certified2727swap)
  apply certified_cons (by exact certified2728)
  apply certified_cons (by exact certified2728swap)
  apply certified_cons (by exact certified2729)
  apply certified_cons (by exact certified2729swap)
  apply certified_cons (by exact certified2730)
  apply certified_cons (by exact certified2730swap)
  apply certified_cons (by exact certified2731)
  apply certified_cons (by exact certified2731swap)
  apply certified_cons (by exact certified2732)
  apply certified_cons (by exact certified2732swap)
  apply certified_cons (by exact certified2733)
  apply certified_cons (by exact certified2733swap)
  apply certified_cons (by exact certified2734)
  apply certified_cons (by exact certified2734swap)
  apply certified_cons (by exact certified2735)
  apply certified_cons (by exact certified2735swap)
  apply certified_cons (by exact certified2736)
  apply certified_cons (by exact certified2736swap)
  apply certified_cons (by exact certified2737)
  apply certified_cons (by exact certified2737swap)
  apply certified_cons (by exact certified2738)
  apply certified_cons (by exact certified2738swap)
  apply certified_cons (by exact certified2739)
  apply certified_cons (by exact certified2739swap)
  apply certified_cons (by exact certified2740)
  apply certified_cons (by exact certified2740swap)
  apply certified_cons (by exact certified2741)
  apply certified_cons (by exact certified2741swap)
  apply certified_cons (by exact certified2742)
  apply certified_cons (by exact certified2742swap)
  apply certified_cons (by exact certified2743)
  apply certified_cons (by exact certified2743swap)
  apply certified_cons (by exact certified2744)
  apply certified_cons (by exact certified2744swap)
  apply certified_cons (by exact certified2745)
  apply certified_cons (by exact certified2745swap)
  apply certified_cons (by exact certified2746)
  apply certified_cons (by exact certified2746swap)
  apply certified_cons (by exact certified2747)
  apply certified_cons (by exact certified2747swap)
  apply certified_cons (by exact certified2748)
  apply certified_cons (by exact certified2748swap)
  apply certified_cons (by exact certified2749)
  apply certified_cons (by exact certified2749swap)
  simp
#print axioms certified_keys054
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
