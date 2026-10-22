/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteKeysData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3300
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3301
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3302
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3303
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3304
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3305
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3306
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3307
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3308
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3309
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3310
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3311
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3312
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3313
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3314
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3315
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3316
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3317
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3318
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3319
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3320
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3321
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3322
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3323
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3324
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3325
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3326
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3327
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3328
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3329
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3330
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3331
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3332
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3333
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3334
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3335
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3336
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3337
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3338
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3339
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3340
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3341
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3342
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3343
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3344
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3345
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3346
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3347
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3348
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3349
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeTwoThreeFiniteActualCases
theorem certified_keys066 : ∀ k ∈ keys066, Certified k := by
  apply certified_cons (by exact certified3300)
  apply certified_cons (by exact certified3300swap)
  apply certified_cons (by exact certified3301)
  apply certified_cons (by exact certified3301swap)
  apply certified_cons (by exact certified3302)
  apply certified_cons (by exact certified3302swap)
  apply certified_cons (by exact certified3303)
  apply certified_cons (by exact certified3303swap)
  apply certified_cons (by exact certified3304)
  apply certified_cons (by exact certified3304swap)
  apply certified_cons (by exact certified3305)
  apply certified_cons (by exact certified3305swap)
  apply certified_cons (by exact certified3306)
  apply certified_cons (by exact certified3306swap)
  apply certified_cons (by exact certified3307)
  apply certified_cons (by exact certified3307swap)
  apply certified_cons (by exact certified3308)
  apply certified_cons (by exact certified3308swap)
  apply certified_cons (by exact certified3309)
  apply certified_cons (by exact certified3309swap)
  apply certified_cons (by exact certified3310)
  apply certified_cons (by exact certified3310swap)
  apply certified_cons (by exact certified3311)
  apply certified_cons (by exact certified3311swap)
  apply certified_cons (by exact certified3312)
  apply certified_cons (by exact certified3312swap)
  apply certified_cons (by exact certified3313)
  apply certified_cons (by exact certified3313swap)
  apply certified_cons (by exact certified3314)
  apply certified_cons (by exact certified3314swap)
  apply certified_cons (by exact certified3315)
  apply certified_cons (by exact certified3315swap)
  apply certified_cons (by exact certified3316)
  apply certified_cons (by exact certified3316swap)
  apply certified_cons (by exact certified3317)
  apply certified_cons (by exact certified3317swap)
  apply certified_cons (by exact certified3318)
  apply certified_cons (by exact certified3318swap)
  apply certified_cons (by exact certified3319)
  apply certified_cons (by exact certified3319swap)
  apply certified_cons (by exact certified3320)
  apply certified_cons (by exact certified3320swap)
  apply certified_cons (by exact certified3321)
  apply certified_cons (by exact certified3321swap)
  apply certified_cons (by exact certified3322)
  apply certified_cons (by exact certified3322swap)
  apply certified_cons (by exact certified3323)
  apply certified_cons (by exact certified3323swap)
  apply certified_cons (by exact certified3324)
  apply certified_cons (by exact certified3324swap)
  apply certified_cons (by exact certified3325)
  apply certified_cons (by exact certified3325swap)
  apply certified_cons (by exact certified3326)
  apply certified_cons (by exact certified3326swap)
  apply certified_cons (by exact certified3327)
  apply certified_cons (by exact certified3327swap)
  apply certified_cons (by exact certified3328)
  apply certified_cons (by exact certified3328swap)
  apply certified_cons (by exact certified3329)
  apply certified_cons (by exact certified3329swap)
  apply certified_cons (by exact certified3330)
  apply certified_cons (by exact certified3330swap)
  apply certified_cons (by exact certified3331)
  apply certified_cons (by exact certified3331swap)
  apply certified_cons (by exact certified3332)
  apply certified_cons (by exact certified3332swap)
  apply certified_cons (by exact certified3333)
  apply certified_cons (by exact certified3333swap)
  apply certified_cons (by exact certified3334)
  apply certified_cons (by exact certified3334swap)
  apply certified_cons (by exact certified3335)
  apply certified_cons (by exact certified3335swap)
  apply certified_cons (by exact certified3336)
  apply certified_cons (by exact certified3336swap)
  apply certified_cons (by exact certified3337)
  apply certified_cons (by exact certified3337swap)
  apply certified_cons (by exact certified3338)
  apply certified_cons (by exact certified3338swap)
  apply certified_cons (by exact certified3339)
  apply certified_cons (by exact certified3339swap)
  apply certified_cons (by exact certified3340)
  apply certified_cons (by exact certified3340swap)
  apply certified_cons (by exact certified3341)
  apply certified_cons (by exact certified3341swap)
  apply certified_cons (by exact certified3342)
  apply certified_cons (by exact certified3342swap)
  apply certified_cons (by exact certified3343)
  apply certified_cons (by exact certified3343swap)
  apply certified_cons (by exact certified3344)
  apply certified_cons (by exact certified3344swap)
  apply certified_cons (by exact certified3345)
  apply certified_cons (by exact certified3345swap)
  apply certified_cons (by exact certified3346)
  apply certified_cons (by exact certified3346swap)
  apply certified_cons (by exact certified3347)
  apply certified_cons (by exact certified3347swap)
  apply certified_cons (by exact certified3348)
  apply certified_cons (by exact certified3348swap)
  apply certified_cons (by exact certified3349)
  apply certified_cons (by exact certified3349swap)
  simp
#print axioms certified_keys066
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
