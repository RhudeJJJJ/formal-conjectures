/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteKeysData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2900
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2901
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2902
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2903
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2904
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2905
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2906
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2907
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2908
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2909
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2910
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2911
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2912
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2913
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2914
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2915
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2916
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2917
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2918
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2919
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2920
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2921
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2922
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2923
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2924
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2925
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2926
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2927
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2928
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2929
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2930
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2931
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2932
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2933
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2934
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2935
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2936
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2937
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2938
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2939
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2940
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2941
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2942
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2943
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2944
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2945
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2946
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2947
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2948
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2949
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeTwoThreeFiniteActualCases
theorem certified_keys058 : ∀ k ∈ keys058, Certified k := by
  apply certified_cons (by exact certified2900)
  apply certified_cons (by exact certified2900swap)
  apply certified_cons (by exact certified2901)
  apply certified_cons (by exact certified2901swap)
  apply certified_cons (by exact certified2902)
  apply certified_cons (by exact certified2902swap)
  apply certified_cons (by exact certified2903)
  apply certified_cons (by exact certified2903swap)
  apply certified_cons (by exact certified2904)
  apply certified_cons (by exact certified2904swap)
  apply certified_cons (by exact certified2905)
  apply certified_cons (by exact certified2905swap)
  apply certified_cons (by exact certified2906)
  apply certified_cons (by exact certified2906swap)
  apply certified_cons (by exact certified2907)
  apply certified_cons (by exact certified2907swap)
  apply certified_cons (by exact certified2908)
  apply certified_cons (by exact certified2908swap)
  apply certified_cons (by exact certified2909)
  apply certified_cons (by exact certified2909swap)
  apply certified_cons (by exact certified2910)
  apply certified_cons (by exact certified2910swap)
  apply certified_cons (by exact certified2911)
  apply certified_cons (by exact certified2911swap)
  apply certified_cons (by exact certified2912)
  apply certified_cons (by exact certified2912swap)
  apply certified_cons (by exact certified2913)
  apply certified_cons (by exact certified2913swap)
  apply certified_cons (by exact certified2914)
  apply certified_cons (by exact certified2914swap)
  apply certified_cons (by exact certified2915)
  apply certified_cons (by exact certified2915swap)
  apply certified_cons (by exact certified2916)
  apply certified_cons (by exact certified2916swap)
  apply certified_cons (by exact certified2917)
  apply certified_cons (by exact certified2917swap)
  apply certified_cons (by exact certified2918)
  apply certified_cons (by exact certified2918swap)
  apply certified_cons (by exact certified2919)
  apply certified_cons (by exact certified2919swap)
  apply certified_cons (by exact certified2920)
  apply certified_cons (by exact certified2920swap)
  apply certified_cons (by exact certified2921)
  apply certified_cons (by exact certified2921swap)
  apply certified_cons (by exact certified2922)
  apply certified_cons (by exact certified2922swap)
  apply certified_cons (by exact certified2923)
  apply certified_cons (by exact certified2923swap)
  apply certified_cons (by exact certified2924)
  apply certified_cons (by exact certified2924swap)
  apply certified_cons (by exact certified2925)
  apply certified_cons (by exact certified2925swap)
  apply certified_cons (by exact certified2926)
  apply certified_cons (by exact certified2926swap)
  apply certified_cons (by exact certified2927)
  apply certified_cons (by exact certified2927swap)
  apply certified_cons (by exact certified2928)
  apply certified_cons (by exact certified2928swap)
  apply certified_cons (by exact certified2929)
  apply certified_cons (by exact certified2929swap)
  apply certified_cons (by exact certified2930)
  apply certified_cons (by exact certified2930swap)
  apply certified_cons (by exact certified2931)
  apply certified_cons (by exact certified2931swap)
  apply certified_cons (by exact certified2932)
  apply certified_cons (by exact certified2932swap)
  apply certified_cons (by exact certified2933)
  apply certified_cons (by exact certified2933swap)
  apply certified_cons (by exact certified2934)
  apply certified_cons (by exact certified2934swap)
  apply certified_cons (by exact certified2935)
  apply certified_cons (by exact certified2935swap)
  apply certified_cons (by exact certified2936)
  apply certified_cons (by exact certified2936swap)
  apply certified_cons (by exact certified2937)
  apply certified_cons (by exact certified2937swap)
  apply certified_cons (by exact certified2938)
  apply certified_cons (by exact certified2938swap)
  apply certified_cons (by exact certified2939)
  apply certified_cons (by exact certified2939swap)
  apply certified_cons (by exact certified2940)
  apply certified_cons (by exact certified2940swap)
  apply certified_cons (by exact certified2941)
  apply certified_cons (by exact certified2941swap)
  apply certified_cons (by exact certified2942)
  apply certified_cons (by exact certified2942swap)
  apply certified_cons (by exact certified2943)
  apply certified_cons (by exact certified2943swap)
  apply certified_cons (by exact certified2944)
  apply certified_cons (by exact certified2944swap)
  apply certified_cons (by exact certified2945)
  apply certified_cons (by exact certified2945swap)
  apply certified_cons (by exact certified2946)
  apply certified_cons (by exact certified2946swap)
  apply certified_cons (by exact certified2947)
  apply certified_cons (by exact certified2947swap)
  apply certified_cons (by exact certified2948)
  apply certified_cons (by exact certified2948swap)
  apply certified_cons (by exact certified2949)
  apply certified_cons (by exact certified2949swap)
  simp
#print axioms certified_keys058
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
