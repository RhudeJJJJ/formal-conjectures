/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteKeysData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3350
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3351
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3352
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3353
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3354
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3355
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3356
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3357
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3358
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3359
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3360
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3361
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3362
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3363
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3364
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3365
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3366
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3367
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3368
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3369
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3370
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3371
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3372
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3373
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3374
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3375
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3376
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3377
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3378
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3379
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3380
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3381
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3382
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3383
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3384
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3385
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3386
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3387
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3388
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3389
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3390
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3391
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3392
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3393
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3394
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3395
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3396
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3397
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3398
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3399
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeTwoThreeFiniteActualCases
theorem certified_keys067 : ∀ k ∈ keys067, Certified k := by
  apply certified_cons (by exact certified3350)
  apply certified_cons (by exact certified3350swap)
  apply certified_cons (by exact certified3351)
  apply certified_cons (by exact certified3351swap)
  apply certified_cons (by exact certified3352)
  apply certified_cons (by exact certified3352swap)
  apply certified_cons (by exact certified3353)
  apply certified_cons (by exact certified3353swap)
  apply certified_cons (by exact certified3354)
  apply certified_cons (by exact certified3354swap)
  apply certified_cons (by exact certified3355)
  apply certified_cons (by exact certified3355swap)
  apply certified_cons (by exact certified3356)
  apply certified_cons (by exact certified3356swap)
  apply certified_cons (by exact certified3357)
  apply certified_cons (by exact certified3357swap)
  apply certified_cons (by exact certified3358)
  apply certified_cons (by exact certified3358swap)
  apply certified_cons (by exact certified3359)
  apply certified_cons (by exact certified3359swap)
  apply certified_cons (by exact certified3360)
  apply certified_cons (by exact certified3360swap)
  apply certified_cons (by exact certified3361)
  apply certified_cons (by exact certified3361swap)
  apply certified_cons (by exact certified3362)
  apply certified_cons (by exact certified3362swap)
  apply certified_cons (by exact certified3363)
  apply certified_cons (by exact certified3363swap)
  apply certified_cons (by exact certified3364)
  apply certified_cons (by exact certified3364swap)
  apply certified_cons (by exact certified3365)
  apply certified_cons (by exact certified3365swap)
  apply certified_cons (by exact certified3366)
  apply certified_cons (by exact certified3366swap)
  apply certified_cons (by exact certified3367)
  apply certified_cons (by exact certified3367swap)
  apply certified_cons (by exact certified3368)
  apply certified_cons (by exact certified3368swap)
  apply certified_cons (by exact certified3369)
  apply certified_cons (by exact certified3369swap)
  apply certified_cons (by exact certified3370)
  apply certified_cons (by exact certified3370swap)
  apply certified_cons (by exact certified3371)
  apply certified_cons (by exact certified3371swap)
  apply certified_cons (by exact certified3372)
  apply certified_cons (by exact certified3372swap)
  apply certified_cons (by exact certified3373)
  apply certified_cons (by exact certified3373swap)
  apply certified_cons (by exact certified3374)
  apply certified_cons (by exact certified3374swap)
  apply certified_cons (by exact certified3375)
  apply certified_cons (by exact certified3375swap)
  apply certified_cons (by exact certified3376)
  apply certified_cons (by exact certified3376swap)
  apply certified_cons (by exact certified3377)
  apply certified_cons (by exact certified3377swap)
  apply certified_cons (by exact certified3378)
  apply certified_cons (by exact certified3378swap)
  apply certified_cons (by exact certified3379)
  apply certified_cons (by exact certified3379swap)
  apply certified_cons (by exact certified3380)
  apply certified_cons (by exact certified3380swap)
  apply certified_cons (by exact certified3381)
  apply certified_cons (by exact certified3381swap)
  apply certified_cons (by exact certified3382)
  apply certified_cons (by exact certified3382swap)
  apply certified_cons (by exact certified3383)
  apply certified_cons (by exact certified3383swap)
  apply certified_cons (by exact certified3384)
  apply certified_cons (by exact certified3384swap)
  apply certified_cons (by exact certified3385)
  apply certified_cons (by exact certified3385swap)
  apply certified_cons (by exact certified3386)
  apply certified_cons (by exact certified3386swap)
  apply certified_cons (by exact certified3387)
  apply certified_cons (by exact certified3387swap)
  apply certified_cons (by exact certified3388)
  apply certified_cons (by exact certified3388swap)
  apply certified_cons (by exact certified3389)
  apply certified_cons (by exact certified3389swap)
  apply certified_cons (by exact certified3390)
  apply certified_cons (by exact certified3390swap)
  apply certified_cons (by exact certified3391)
  apply certified_cons (by exact certified3391swap)
  apply certified_cons (by exact certified3392)
  apply certified_cons (by exact certified3392swap)
  apply certified_cons (by exact certified3393)
  apply certified_cons (by exact certified3393swap)
  apply certified_cons (by exact certified3394)
  apply certified_cons (by exact certified3394swap)
  apply certified_cons (by exact certified3395)
  apply certified_cons (by exact certified3395swap)
  apply certified_cons (by exact certified3396)
  apply certified_cons (by exact certified3396swap)
  apply certified_cons (by exact certified3397)
  apply certified_cons (by exact certified3397swap)
  apply certified_cons (by exact certified3398)
  apply certified_cons (by exact certified3398swap)
  apply certified_cons (by exact certified3399)
  apply certified_cons (by exact certified3399swap)
  simp
#print axioms certified_keys067
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
