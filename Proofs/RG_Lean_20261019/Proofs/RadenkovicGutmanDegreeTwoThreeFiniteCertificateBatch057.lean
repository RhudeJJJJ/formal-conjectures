/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteKeysData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2850
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2851
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2852
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2853
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2854
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2855
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2856
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2857
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2858
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2859
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2860
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2861
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2862
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2863
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2864
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2865
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2866
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2867
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2868
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2869
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2870
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2871
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2872
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2873
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2874
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2875
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2876
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2877
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2878
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2879
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2880
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2881
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2882
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2883
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2884
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2885
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2886
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2887
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2888
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2889
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2890
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2891
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2892
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2893
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2894
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2895
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2896
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2897
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2898
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2899
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeTwoThreeFiniteActualCases
theorem certified_keys057 : ∀ k ∈ keys057, Certified k := by
  apply certified_cons (by exact certified2850)
  apply certified_cons (by exact certified2850swap)
  apply certified_cons (by exact certified2851)
  apply certified_cons (by exact certified2851swap)
  apply certified_cons (by exact certified2852)
  apply certified_cons (by exact certified2852swap)
  apply certified_cons (by exact certified2853)
  apply certified_cons (by exact certified2853swap)
  apply certified_cons (by exact certified2854)
  apply certified_cons (by exact certified2854swap)
  apply certified_cons (by exact certified2855)
  apply certified_cons (by exact certified2855swap)
  apply certified_cons (by exact certified2856)
  apply certified_cons (by exact certified2856swap)
  apply certified_cons (by exact certified2857)
  apply certified_cons (by exact certified2857swap)
  apply certified_cons (by exact certified2858)
  apply certified_cons (by exact certified2858swap)
  apply certified_cons (by exact certified2859)
  apply certified_cons (by exact certified2859swap)
  apply certified_cons (by exact certified2860)
  apply certified_cons (by exact certified2860swap)
  apply certified_cons (by exact certified2861)
  apply certified_cons (by exact certified2861swap)
  apply certified_cons (by exact certified2862)
  apply certified_cons (by exact certified2862swap)
  apply certified_cons (by exact certified2863)
  apply certified_cons (by exact certified2863swap)
  apply certified_cons (by exact certified2864)
  apply certified_cons (by exact certified2864swap)
  apply certified_cons (by exact certified2865)
  apply certified_cons (by exact certified2865swap)
  apply certified_cons (by exact certified2866)
  apply certified_cons (by exact certified2866swap)
  apply certified_cons (by exact certified2867)
  apply certified_cons (by exact certified2867swap)
  apply certified_cons (by exact certified2868)
  apply certified_cons (by exact certified2868swap)
  apply certified_cons (by exact certified2869)
  apply certified_cons (by exact certified2869swap)
  apply certified_cons (by exact certified2870)
  apply certified_cons (by exact certified2870swap)
  apply certified_cons (by exact certified2871)
  apply certified_cons (by exact certified2871swap)
  apply certified_cons (by exact certified2872)
  apply certified_cons (by exact certified2872swap)
  apply certified_cons (by exact certified2873)
  apply certified_cons (by exact certified2873swap)
  apply certified_cons (by exact certified2874)
  apply certified_cons (by exact certified2874swap)
  apply certified_cons (by exact certified2875)
  apply certified_cons (by exact certified2875swap)
  apply certified_cons (by exact certified2876)
  apply certified_cons (by exact certified2876swap)
  apply certified_cons (by exact certified2877)
  apply certified_cons (by exact certified2877swap)
  apply certified_cons (by exact certified2878)
  apply certified_cons (by exact certified2878swap)
  apply certified_cons (by exact certified2879)
  apply certified_cons (by exact certified2879swap)
  apply certified_cons (by exact certified2880)
  apply certified_cons (by exact certified2880swap)
  apply certified_cons (by exact certified2881)
  apply certified_cons (by exact certified2881swap)
  apply certified_cons (by exact certified2882)
  apply certified_cons (by exact certified2882swap)
  apply certified_cons (by exact certified2883)
  apply certified_cons (by exact certified2883swap)
  apply certified_cons (by exact certified2884)
  apply certified_cons (by exact certified2884swap)
  apply certified_cons (by exact certified2885)
  apply certified_cons (by exact certified2885swap)
  apply certified_cons (by exact certified2886)
  apply certified_cons (by exact certified2886swap)
  apply certified_cons (by exact certified2887)
  apply certified_cons (by exact certified2887swap)
  apply certified_cons (by exact certified2888)
  apply certified_cons (by exact certified2888swap)
  apply certified_cons (by exact certified2889)
  apply certified_cons (by exact certified2889swap)
  apply certified_cons (by exact certified2890)
  apply certified_cons (by exact certified2890swap)
  apply certified_cons (by exact certified2891)
  apply certified_cons (by exact certified2891swap)
  apply certified_cons (by exact certified2892)
  apply certified_cons (by exact certified2892swap)
  apply certified_cons (by exact certified2893)
  apply certified_cons (by exact certified2893swap)
  apply certified_cons (by exact certified2894)
  apply certified_cons (by exact certified2894swap)
  apply certified_cons (by exact certified2895)
  apply certified_cons (by exact certified2895swap)
  apply certified_cons (by exact certified2896)
  apply certified_cons (by exact certified2896swap)
  apply certified_cons (by exact certified2897)
  apply certified_cons (by exact certified2897swap)
  apply certified_cons (by exact certified2898)
  apply certified_cons (by exact certified2898swap)
  apply certified_cons (by exact certified2899)
  apply certified_cons (by exact certified2899swap)
  simp
#print axioms certified_keys057
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
