/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteKeysData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3250
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3251
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3252
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3253
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3254
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3255
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3256
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3257
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3258
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3259
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3260
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3261
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3262
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3263
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3264
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3265
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3266
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3267
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3268
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3269
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3270
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3271
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3272
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3273
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3274
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3275
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3276
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3277
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3278
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3279
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3280
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3281
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3282
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3283
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3284
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3285
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3286
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3287
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3288
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3289
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3290
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3291
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3292
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3293
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3294
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3295
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3296
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3297
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3298
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3299
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeTwoThreeFiniteActualCases
theorem certified_keys065 : ∀ k ∈ keys065, Certified k := by
  apply certified_cons (by exact certified3250)
  apply certified_cons (by exact certified3250swap)
  apply certified_cons (by exact certified3251)
  apply certified_cons (by exact certified3251swap)
  apply certified_cons (by exact certified3252)
  apply certified_cons (by exact certified3252swap)
  apply certified_cons (by exact certified3253)
  apply certified_cons (by exact certified3253swap)
  apply certified_cons (by exact certified3254)
  apply certified_cons (by exact certified3254swap)
  apply certified_cons (by exact certified3255)
  apply certified_cons (by exact certified3255swap)
  apply certified_cons (by exact certified3256)
  apply certified_cons (by exact certified3256swap)
  apply certified_cons (by exact certified3257)
  apply certified_cons (by exact certified3257swap)
  apply certified_cons (by exact certified3258)
  apply certified_cons (by exact certified3258swap)
  apply certified_cons (by exact certified3259)
  apply certified_cons (by exact certified3259swap)
  apply certified_cons (by exact certified3260)
  apply certified_cons (by exact certified3260swap)
  apply certified_cons (by exact certified3261)
  apply certified_cons (by exact certified3261swap)
  apply certified_cons (by exact certified3262)
  apply certified_cons (by exact certified3262swap)
  apply certified_cons (by exact certified3263)
  apply certified_cons (by exact certified3263swap)
  apply certified_cons (by exact certified3264)
  apply certified_cons (by exact certified3264swap)
  apply certified_cons (by exact certified3265)
  apply certified_cons (by exact certified3265swap)
  apply certified_cons (by exact certified3266)
  apply certified_cons (by exact certified3266swap)
  apply certified_cons (by exact certified3267)
  apply certified_cons (by exact certified3267swap)
  apply certified_cons (by exact certified3268)
  apply certified_cons (by exact certified3268swap)
  apply certified_cons (by exact certified3269)
  apply certified_cons (by exact certified3269swap)
  apply certified_cons (by exact certified3270)
  apply certified_cons (by exact certified3270swap)
  apply certified_cons (by exact certified3271)
  apply certified_cons (by exact certified3271swap)
  apply certified_cons (by exact certified3272)
  apply certified_cons (by exact certified3272swap)
  apply certified_cons (by exact certified3273)
  apply certified_cons (by exact certified3273swap)
  apply certified_cons (by exact certified3274)
  apply certified_cons (by exact certified3274swap)
  apply certified_cons (by exact certified3275)
  apply certified_cons (by exact certified3275swap)
  apply certified_cons (by exact certified3276)
  apply certified_cons (by exact certified3276swap)
  apply certified_cons (by exact certified3277)
  apply certified_cons (by exact certified3277swap)
  apply certified_cons (by exact certified3278)
  apply certified_cons (by exact certified3278swap)
  apply certified_cons (by exact certified3279)
  apply certified_cons (by exact certified3279swap)
  apply certified_cons (by exact certified3280)
  apply certified_cons (by exact certified3280swap)
  apply certified_cons (by exact certified3281)
  apply certified_cons (by exact certified3281swap)
  apply certified_cons (by exact certified3282)
  apply certified_cons (by exact certified3282swap)
  apply certified_cons (by exact certified3283)
  apply certified_cons (by exact certified3283swap)
  apply certified_cons (by exact certified3284)
  apply certified_cons (by exact certified3284swap)
  apply certified_cons (by exact certified3285)
  apply certified_cons (by exact certified3285swap)
  apply certified_cons (by exact certified3286)
  apply certified_cons (by exact certified3286swap)
  apply certified_cons (by exact certified3287)
  apply certified_cons (by exact certified3287swap)
  apply certified_cons (by exact certified3288)
  apply certified_cons (by exact certified3288swap)
  apply certified_cons (by exact certified3289)
  apply certified_cons (by exact certified3289swap)
  apply certified_cons (by exact certified3290)
  apply certified_cons (by exact certified3290swap)
  apply certified_cons (by exact certified3291)
  apply certified_cons (by exact certified3291swap)
  apply certified_cons (by exact certified3292)
  apply certified_cons (by exact certified3292swap)
  apply certified_cons (by exact certified3293)
  apply certified_cons (by exact certified3293swap)
  apply certified_cons (by exact certified3294)
  apply certified_cons (by exact certified3294swap)
  apply certified_cons (by exact certified3295)
  apply certified_cons (by exact certified3295swap)
  apply certified_cons (by exact certified3296)
  apply certified_cons (by exact certified3296swap)
  apply certified_cons (by exact certified3297)
  apply certified_cons (by exact certified3297swap)
  apply certified_cons (by exact certified3298)
  apply certified_cons (by exact certified3298swap)
  apply certified_cons (by exact certified3299)
  apply certified_cons (by exact certified3299swap)
  simp
#print axioms certified_keys065
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
