/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteKeysData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2750
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2751
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2752
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2753
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2754
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2755
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2756
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2757
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2758
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2759
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2760
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2761
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2762
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2763
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2764
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2765
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2766
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2767
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2768
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2769
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2770
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2771
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2772
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2773
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2774
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2775
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2776
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2777
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2778
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2779
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2780
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2781
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2782
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2783
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2784
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2785
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2786
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2787
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2788
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2789
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2790
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2791
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2792
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2793
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2794
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2795
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2796
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2797
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2798
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2799
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeTwoThreeFiniteActualCases
theorem certified_keys055 : ∀ k ∈ keys055, Certified k := by
  apply certified_cons (by exact certified2750)
  apply certified_cons (by exact certified2750swap)
  apply certified_cons (by exact certified2751)
  apply certified_cons (by exact certified2751swap)
  apply certified_cons (by exact certified2752)
  apply certified_cons (by exact certified2752swap)
  apply certified_cons (by exact certified2753)
  apply certified_cons (by exact certified2753swap)
  apply certified_cons (by exact certified2754)
  apply certified_cons (by exact certified2754swap)
  apply certified_cons (by exact certified2755)
  apply certified_cons (by exact certified2755swap)
  apply certified_cons (by exact certified2756)
  apply certified_cons (by exact certified2756swap)
  apply certified_cons (by exact certified2757)
  apply certified_cons (by exact certified2757swap)
  apply certified_cons (by exact certified2758)
  apply certified_cons (by exact certified2758swap)
  apply certified_cons (by exact certified2759)
  apply certified_cons (by exact certified2759swap)
  apply certified_cons (by exact certified2760)
  apply certified_cons (by exact certified2760swap)
  apply certified_cons (by exact certified2761)
  apply certified_cons (by exact certified2761swap)
  apply certified_cons (by exact certified2762)
  apply certified_cons (by exact certified2762swap)
  apply certified_cons (by exact certified2763)
  apply certified_cons (by exact certified2763swap)
  apply certified_cons (by exact certified2764)
  apply certified_cons (by exact certified2764swap)
  apply certified_cons (by exact certified2765)
  apply certified_cons (by exact certified2765swap)
  apply certified_cons (by exact certified2766)
  apply certified_cons (by exact certified2766swap)
  apply certified_cons (by exact certified2767)
  apply certified_cons (by exact certified2767swap)
  apply certified_cons (by exact certified2768)
  apply certified_cons (by exact certified2768swap)
  apply certified_cons (by exact certified2769)
  apply certified_cons (by exact certified2769swap)
  apply certified_cons (by exact certified2770)
  apply certified_cons (by exact certified2770swap)
  apply certified_cons (by exact certified2771)
  apply certified_cons (by exact certified2771swap)
  apply certified_cons (by exact certified2772)
  apply certified_cons (by exact certified2772swap)
  apply certified_cons (by exact certified2773)
  apply certified_cons (by exact certified2773swap)
  apply certified_cons (by exact certified2774)
  apply certified_cons (by exact certified2774swap)
  apply certified_cons (by exact certified2775)
  apply certified_cons (by exact certified2775swap)
  apply certified_cons (by exact certified2776)
  apply certified_cons (by exact certified2776swap)
  apply certified_cons (by exact certified2777)
  apply certified_cons (by exact certified2777swap)
  apply certified_cons (by exact certified2778)
  apply certified_cons (by exact certified2778swap)
  apply certified_cons (by exact certified2779)
  apply certified_cons (by exact certified2779swap)
  apply certified_cons (by exact certified2780)
  apply certified_cons (by exact certified2780swap)
  apply certified_cons (by exact certified2781)
  apply certified_cons (by exact certified2781swap)
  apply certified_cons (by exact certified2782)
  apply certified_cons (by exact certified2782swap)
  apply certified_cons (by exact certified2783)
  apply certified_cons (by exact certified2783swap)
  apply certified_cons (by exact certified2784)
  apply certified_cons (by exact certified2784swap)
  apply certified_cons (by exact certified2785)
  apply certified_cons (by exact certified2785swap)
  apply certified_cons (by exact certified2786)
  apply certified_cons (by exact certified2786swap)
  apply certified_cons (by exact certified2787)
  apply certified_cons (by exact certified2787swap)
  apply certified_cons (by exact certified2788)
  apply certified_cons (by exact certified2788swap)
  apply certified_cons (by exact certified2789)
  apply certified_cons (by exact certified2789swap)
  apply certified_cons (by exact certified2790)
  apply certified_cons (by exact certified2790swap)
  apply certified_cons (by exact certified2791)
  apply certified_cons (by exact certified2791swap)
  apply certified_cons (by exact certified2792)
  apply certified_cons (by exact certified2792swap)
  apply certified_cons (by exact certified2793)
  apply certified_cons (by exact certified2793swap)
  apply certified_cons (by exact certified2794)
  apply certified_cons (by exact certified2794swap)
  apply certified_cons (by exact certified2795)
  apply certified_cons (by exact certified2795swap)
  apply certified_cons (by exact certified2796)
  apply certified_cons (by exact certified2796swap)
  apply certified_cons (by exact certified2797)
  apply certified_cons (by exact certified2797swap)
  apply certified_cons (by exact certified2798)
  apply certified_cons (by exact certified2798swap)
  apply certified_cons (by exact certified2799)
  apply certified_cons (by exact certified2799swap)
  simp
#print axioms certified_keys055
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
