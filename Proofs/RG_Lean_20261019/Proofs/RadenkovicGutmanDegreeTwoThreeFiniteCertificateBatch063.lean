/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteKeysData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3150
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3151
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3152
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3153
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3154
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3155
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3156
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3157
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3158
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3159
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3160
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3161
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3162
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3163
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3164
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3165
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3166
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3167
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3168
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3169
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3170
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3171
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3172
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3173
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3174
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3175
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3176
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3177
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3178
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3179
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3180
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3181
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3182
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3183
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3184
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3185
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3186
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3187
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3188
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3189
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3190
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3191
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3192
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3193
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3194
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3195
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3196
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3197
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3198
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3199
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeTwoThreeFiniteActualCases
theorem certified_keys063 : ∀ k ∈ keys063, Certified k := by
  apply certified_cons (by exact certified3150)
  apply certified_cons (by exact certified3150swap)
  apply certified_cons (by exact certified3151)
  apply certified_cons (by exact certified3151swap)
  apply certified_cons (by exact certified3152)
  apply certified_cons (by exact certified3152swap)
  apply certified_cons (by exact certified3153)
  apply certified_cons (by exact certified3153swap)
  apply certified_cons (by exact certified3154)
  apply certified_cons (by exact certified3154swap)
  apply certified_cons (by exact certified3155)
  apply certified_cons (by exact certified3155swap)
  apply certified_cons (by exact certified3156)
  apply certified_cons (by exact certified3156swap)
  apply certified_cons (by exact certified3157)
  apply certified_cons (by exact certified3157swap)
  apply certified_cons (by exact certified3158)
  apply certified_cons (by exact certified3158swap)
  apply certified_cons (by exact certified3159)
  apply certified_cons (by exact certified3159swap)
  apply certified_cons (by exact certified3160)
  apply certified_cons (by exact certified3160swap)
  apply certified_cons (by exact certified3161)
  apply certified_cons (by exact certified3161swap)
  apply certified_cons (by exact certified3162)
  apply certified_cons (by exact certified3162swap)
  apply certified_cons (by exact certified3163)
  apply certified_cons (by exact certified3163swap)
  apply certified_cons (by exact certified3164)
  apply certified_cons (by exact certified3164swap)
  apply certified_cons (by exact certified3165)
  apply certified_cons (by exact certified3165swap)
  apply certified_cons (by exact certified3166)
  apply certified_cons (by exact certified3166swap)
  apply certified_cons (by exact certified3167)
  apply certified_cons (by exact certified3167swap)
  apply certified_cons (by exact certified3168)
  apply certified_cons (by exact certified3168swap)
  apply certified_cons (by exact certified3169)
  apply certified_cons (by exact certified3169swap)
  apply certified_cons (by exact certified3170)
  apply certified_cons (by exact certified3170swap)
  apply certified_cons (by exact certified3171)
  apply certified_cons (by exact certified3171swap)
  apply certified_cons (by exact certified3172)
  apply certified_cons (by exact certified3172swap)
  apply certified_cons (by exact certified3173)
  apply certified_cons (by exact certified3173swap)
  apply certified_cons (by exact certified3174)
  apply certified_cons (by exact certified3174swap)
  apply certified_cons (by exact certified3175)
  apply certified_cons (by exact certified3175swap)
  apply certified_cons (by exact certified3176)
  apply certified_cons (by exact certified3176swap)
  apply certified_cons (by exact certified3177)
  apply certified_cons (by exact certified3177swap)
  apply certified_cons (by exact certified3178)
  apply certified_cons (by exact certified3178swap)
  apply certified_cons (by exact certified3179)
  apply certified_cons (by exact certified3179swap)
  apply certified_cons (by exact certified3180)
  apply certified_cons (by exact certified3180swap)
  apply certified_cons (by exact certified3181)
  apply certified_cons (by exact certified3181swap)
  apply certified_cons (by exact certified3182)
  apply certified_cons (by exact certified3182swap)
  apply certified_cons (by exact certified3183)
  apply certified_cons (by exact certified3183swap)
  apply certified_cons (by exact certified3184)
  apply certified_cons (by exact certified3184swap)
  apply certified_cons (by exact certified3185)
  apply certified_cons (by exact certified3185swap)
  apply certified_cons (by exact certified3186)
  apply certified_cons (by exact certified3186swap)
  apply certified_cons (by exact certified3187)
  apply certified_cons (by exact certified3187swap)
  apply certified_cons (by exact certified3188)
  apply certified_cons (by exact certified3188swap)
  apply certified_cons (by exact certified3189)
  apply certified_cons (by exact certified3189swap)
  apply certified_cons (by exact certified3190)
  apply certified_cons (by exact certified3190swap)
  apply certified_cons (by exact certified3191)
  apply certified_cons (by exact certified3191swap)
  apply certified_cons (by exact certified3192)
  apply certified_cons (by exact certified3192swap)
  apply certified_cons (by exact certified3193)
  apply certified_cons (by exact certified3193swap)
  apply certified_cons (by exact certified3194)
  apply certified_cons (by exact certified3194swap)
  apply certified_cons (by exact certified3195)
  apply certified_cons (by exact certified3195swap)
  apply certified_cons (by exact certified3196)
  apply certified_cons (by exact certified3196swap)
  apply certified_cons (by exact certified3197)
  apply certified_cons (by exact certified3197swap)
  apply certified_cons (by exact certified3198)
  apply certified_cons (by exact certified3198swap)
  apply certified_cons (by exact certified3199)
  apply certified_cons (by exact certified3199swap)
  simp
#print axioms certified_keys063
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
