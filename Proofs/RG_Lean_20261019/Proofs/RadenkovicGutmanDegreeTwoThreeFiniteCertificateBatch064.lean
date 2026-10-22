/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteKeysData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3200
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3201
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3202
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3203
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3204
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3205
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3206
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3207
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3208
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3209
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3210
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3211
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3212
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3213
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3214
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3215
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3216
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3217
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3218
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3219
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3220
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3221
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3222
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3223
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3224
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3225
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3226
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3227
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3228
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3229
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3230
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3231
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3232
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3233
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3234
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3235
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3236
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3237
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3238
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3239
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3240
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3241
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3242
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3243
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3244
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3245
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3246
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3247
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3248
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3249
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeTwoThreeFiniteActualCases
theorem certified_keys064 : ∀ k ∈ keys064, Certified k := by
  apply certified_cons (by exact certified3200)
  apply certified_cons (by exact certified3200swap)
  apply certified_cons (by exact certified3201)
  apply certified_cons (by exact certified3201swap)
  apply certified_cons (by exact certified3202)
  apply certified_cons (by exact certified3202swap)
  apply certified_cons (by exact certified3203)
  apply certified_cons (by exact certified3203swap)
  apply certified_cons (by exact certified3204)
  apply certified_cons (by exact certified3204swap)
  apply certified_cons (by exact certified3205)
  apply certified_cons (by exact certified3205swap)
  apply certified_cons (by exact certified3206)
  apply certified_cons (by exact certified3206swap)
  apply certified_cons (by exact certified3207)
  apply certified_cons (by exact certified3207swap)
  apply certified_cons (by exact certified3208)
  apply certified_cons (by exact certified3208swap)
  apply certified_cons (by exact certified3209)
  apply certified_cons (by exact certified3209swap)
  apply certified_cons (by exact certified3210)
  apply certified_cons (by exact certified3210swap)
  apply certified_cons (by exact certified3211)
  apply certified_cons (by exact certified3211swap)
  apply certified_cons (by exact certified3212)
  apply certified_cons (by exact certified3212swap)
  apply certified_cons (by exact certified3213)
  apply certified_cons (by exact certified3213swap)
  apply certified_cons (by exact certified3214)
  apply certified_cons (by exact certified3214swap)
  apply certified_cons (by exact certified3215)
  apply certified_cons (by exact certified3215swap)
  apply certified_cons (by exact certified3216)
  apply certified_cons (by exact certified3216swap)
  apply certified_cons (by exact certified3217)
  apply certified_cons (by exact certified3217swap)
  apply certified_cons (by exact certified3218)
  apply certified_cons (by exact certified3218swap)
  apply certified_cons (by exact certified3219)
  apply certified_cons (by exact certified3219swap)
  apply certified_cons (by exact certified3220)
  apply certified_cons (by exact certified3220swap)
  apply certified_cons (by exact certified3221)
  apply certified_cons (by exact certified3221swap)
  apply certified_cons (by exact certified3222)
  apply certified_cons (by exact certified3222swap)
  apply certified_cons (by exact certified3223)
  apply certified_cons (by exact certified3223swap)
  apply certified_cons (by exact certified3224)
  apply certified_cons (by exact certified3224swap)
  apply certified_cons (by exact certified3225)
  apply certified_cons (by exact certified3225swap)
  apply certified_cons (by exact certified3226)
  apply certified_cons (by exact certified3226swap)
  apply certified_cons (by exact certified3227)
  apply certified_cons (by exact certified3227swap)
  apply certified_cons (by exact certified3228)
  apply certified_cons (by exact certified3228swap)
  apply certified_cons (by exact certified3229)
  apply certified_cons (by exact certified3229swap)
  apply certified_cons (by exact certified3230)
  apply certified_cons (by exact certified3230swap)
  apply certified_cons (by exact certified3231)
  apply certified_cons (by exact certified3231swap)
  apply certified_cons (by exact certified3232)
  apply certified_cons (by exact certified3232swap)
  apply certified_cons (by exact certified3233)
  apply certified_cons (by exact certified3233swap)
  apply certified_cons (by exact certified3234)
  apply certified_cons (by exact certified3234swap)
  apply certified_cons (by exact certified3235)
  apply certified_cons (by exact certified3235swap)
  apply certified_cons (by exact certified3236)
  apply certified_cons (by exact certified3236swap)
  apply certified_cons (by exact certified3237)
  apply certified_cons (by exact certified3237swap)
  apply certified_cons (by exact certified3238)
  apply certified_cons (by exact certified3238swap)
  apply certified_cons (by exact certified3239)
  apply certified_cons (by exact certified3239swap)
  apply certified_cons (by exact certified3240)
  apply certified_cons (by exact certified3240swap)
  apply certified_cons (by exact certified3241)
  apply certified_cons (by exact certified3241swap)
  apply certified_cons (by exact certified3242)
  apply certified_cons (by exact certified3242swap)
  apply certified_cons (by exact certified3243)
  apply certified_cons (by exact certified3243swap)
  apply certified_cons (by exact certified3244)
  apply certified_cons (by exact certified3244swap)
  apply certified_cons (by exact certified3245)
  apply certified_cons (by exact certified3245swap)
  apply certified_cons (by exact certified3246)
  apply certified_cons (by exact certified3246swap)
  apply certified_cons (by exact certified3247)
  apply certified_cons (by exact certified3247swap)
  apply certified_cons (by exact certified3248)
  apply certified_cons (by exact certified3248swap)
  apply certified_cons (by exact certified3249)
  apply certified_cons (by exact certified3249swap)
  simp
#print axioms certified_keys064
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
