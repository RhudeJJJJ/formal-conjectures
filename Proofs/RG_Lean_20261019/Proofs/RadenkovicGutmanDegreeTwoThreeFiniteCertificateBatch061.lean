/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteKeysData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3050
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3051
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3052
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3053
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3054
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3055
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3056
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3057
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3058
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3059
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3060
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3061
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3062
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3063
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3064
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3065
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3066
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3067
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3068
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3069
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3070
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3071
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3072
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3073
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3074
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3075
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3076
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3077
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3078
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3079
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3080
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3081
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3082
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3083
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3084
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3085
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3086
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3087
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3088
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3089
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3090
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3091
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3092
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3093
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3094
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3095
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3096
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3097
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3098
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3099
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeTwoThreeFiniteActualCases
theorem certified_keys061 : ∀ k ∈ keys061, Certified k := by
  apply certified_cons (by exact certified3050)
  apply certified_cons (by exact certified3050swap)
  apply certified_cons (by exact certified3051)
  apply certified_cons (by exact certified3051swap)
  apply certified_cons (by exact certified3052)
  apply certified_cons (by exact certified3052swap)
  apply certified_cons (by exact certified3053)
  apply certified_cons (by exact certified3053swap)
  apply certified_cons (by exact certified3054)
  apply certified_cons (by exact certified3054swap)
  apply certified_cons (by exact certified3055)
  apply certified_cons (by exact certified3055swap)
  apply certified_cons (by exact certified3056)
  apply certified_cons (by exact certified3056swap)
  apply certified_cons (by exact certified3057)
  apply certified_cons (by exact certified3057swap)
  apply certified_cons (by exact certified3058)
  apply certified_cons (by exact certified3058swap)
  apply certified_cons (by exact certified3059)
  apply certified_cons (by exact certified3059swap)
  apply certified_cons (by exact certified3060)
  apply certified_cons (by exact certified3060swap)
  apply certified_cons (by exact certified3061)
  apply certified_cons (by exact certified3061swap)
  apply certified_cons (by exact certified3062)
  apply certified_cons (by exact certified3062swap)
  apply certified_cons (by exact certified3063)
  apply certified_cons (by exact certified3063swap)
  apply certified_cons (by exact certified3064)
  apply certified_cons (by exact certified3064swap)
  apply certified_cons (by exact certified3065)
  apply certified_cons (by exact certified3065swap)
  apply certified_cons (by exact certified3066)
  apply certified_cons (by exact certified3066swap)
  apply certified_cons (by exact certified3067)
  apply certified_cons (by exact certified3067swap)
  apply certified_cons (by exact certified3068)
  apply certified_cons (by exact certified3068swap)
  apply certified_cons (by exact certified3069)
  apply certified_cons (by exact certified3069swap)
  apply certified_cons (by exact certified3070)
  apply certified_cons (by exact certified3070swap)
  apply certified_cons (by exact certified3071)
  apply certified_cons (by exact certified3071swap)
  apply certified_cons (by exact certified3072)
  apply certified_cons (by exact certified3072swap)
  apply certified_cons (by exact certified3073)
  apply certified_cons (by exact certified3073swap)
  apply certified_cons (by exact certified3074)
  apply certified_cons (by exact certified3074swap)
  apply certified_cons (by exact certified3075)
  apply certified_cons (by exact certified3075swap)
  apply certified_cons (by exact certified3076)
  apply certified_cons (by exact certified3076swap)
  apply certified_cons (by exact certified3077)
  apply certified_cons (by exact certified3077swap)
  apply certified_cons (by exact certified3078)
  apply certified_cons (by exact certified3078swap)
  apply certified_cons (by exact certified3079)
  apply certified_cons (by exact certified3079swap)
  apply certified_cons (by exact certified3080)
  apply certified_cons (by exact certified3080swap)
  apply certified_cons (by exact certified3081)
  apply certified_cons (by exact certified3081swap)
  apply certified_cons (by exact certified3082)
  apply certified_cons (by exact certified3082swap)
  apply certified_cons (by exact certified3083)
  apply certified_cons (by exact certified3083swap)
  apply certified_cons (by exact certified3084)
  apply certified_cons (by exact certified3084swap)
  apply certified_cons (by exact certified3085)
  apply certified_cons (by exact certified3085swap)
  apply certified_cons (by exact certified3086)
  apply certified_cons (by exact certified3086swap)
  apply certified_cons (by exact certified3087)
  apply certified_cons (by exact certified3087swap)
  apply certified_cons (by exact certified3088)
  apply certified_cons (by exact certified3088swap)
  apply certified_cons (by exact certified3089)
  apply certified_cons (by exact certified3089swap)
  apply certified_cons (by exact certified3090)
  apply certified_cons (by exact certified3090swap)
  apply certified_cons (by exact certified3091)
  apply certified_cons (by exact certified3091swap)
  apply certified_cons (by exact certified3092)
  apply certified_cons (by exact certified3092swap)
  apply certified_cons (by exact certified3093)
  apply certified_cons (by exact certified3093swap)
  apply certified_cons (by exact certified3094)
  apply certified_cons (by exact certified3094swap)
  apply certified_cons (by exact certified3095)
  apply certified_cons (by exact certified3095swap)
  apply certified_cons (by exact certified3096)
  apply certified_cons (by exact certified3096swap)
  apply certified_cons (by exact certified3097)
  apply certified_cons (by exact certified3097swap)
  apply certified_cons (by exact certified3098)
  apply certified_cons (by exact certified3098swap)
  apply certified_cons (by exact certified3099)
  apply certified_cons (by exact certified3099swap)
  simp
#print axioms certified_keys061
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
