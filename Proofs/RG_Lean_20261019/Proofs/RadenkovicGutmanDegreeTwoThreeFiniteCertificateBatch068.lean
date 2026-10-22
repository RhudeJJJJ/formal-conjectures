/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteKeysData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3400
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3401
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3402
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3403
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3404
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3405
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3406
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3407
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3408
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3409
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3410
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3411
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3412
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3413
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3414
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3415
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3416
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3417
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3418
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3419
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3420
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3421
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3422
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3423
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3424
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3425
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3426
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3427
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3428
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3429
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3430
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3431
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3432
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3433
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3434
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3435
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3436
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3437
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3438
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3439
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3440
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3441
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3442
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3443
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3444
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3445
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3446
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3447
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3448
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3449
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeTwoThreeFiniteActualCases
theorem certified_keys068 : ∀ k ∈ keys068, Certified k := by
  apply certified_cons (by exact certified3400)
  apply certified_cons (by exact certified3400swap)
  apply certified_cons (by exact certified3401)
  apply certified_cons (by exact certified3401swap)
  apply certified_cons (by exact certified3402)
  apply certified_cons (by exact certified3402swap)
  apply certified_cons (by exact certified3403)
  apply certified_cons (by exact certified3403swap)
  apply certified_cons (by exact certified3404)
  apply certified_cons (by exact certified3404swap)
  apply certified_cons (by exact certified3405)
  apply certified_cons (by exact certified3405swap)
  apply certified_cons (by exact certified3406)
  apply certified_cons (by exact certified3406swap)
  apply certified_cons (by exact certified3407)
  apply certified_cons (by exact certified3407swap)
  apply certified_cons (by exact certified3408)
  apply certified_cons (by exact certified3408swap)
  apply certified_cons (by exact certified3409)
  apply certified_cons (by exact certified3409swap)
  apply certified_cons (by exact certified3410)
  apply certified_cons (by exact certified3410swap)
  apply certified_cons (by exact certified3411)
  apply certified_cons (by exact certified3411swap)
  apply certified_cons (by exact certified3412)
  apply certified_cons (by exact certified3412swap)
  apply certified_cons (by exact certified3413)
  apply certified_cons (by exact certified3413swap)
  apply certified_cons (by exact certified3414)
  apply certified_cons (by exact certified3414swap)
  apply certified_cons (by exact certified3415)
  apply certified_cons (by exact certified3415swap)
  apply certified_cons (by exact certified3416)
  apply certified_cons (by exact certified3416swap)
  apply certified_cons (by exact certified3417)
  apply certified_cons (by exact certified3417swap)
  apply certified_cons (by exact certified3418)
  apply certified_cons (by exact certified3418swap)
  apply certified_cons (by exact certified3419)
  apply certified_cons (by exact certified3419swap)
  apply certified_cons (by exact certified3420)
  apply certified_cons (by exact certified3420swap)
  apply certified_cons (by exact certified3421)
  apply certified_cons (by exact certified3421swap)
  apply certified_cons (by exact certified3422)
  apply certified_cons (by exact certified3422swap)
  apply certified_cons (by exact certified3423)
  apply certified_cons (by exact certified3423swap)
  apply certified_cons (by exact certified3424)
  apply certified_cons (by exact certified3424swap)
  apply certified_cons (by exact certified3425)
  apply certified_cons (by exact certified3425swap)
  apply certified_cons (by exact certified3426)
  apply certified_cons (by exact certified3426swap)
  apply certified_cons (by exact certified3427)
  apply certified_cons (by exact certified3427swap)
  apply certified_cons (by exact certified3428)
  apply certified_cons (by exact certified3428swap)
  apply certified_cons (by exact certified3429)
  apply certified_cons (by exact certified3429swap)
  apply certified_cons (by exact certified3430)
  apply certified_cons (by exact certified3430swap)
  apply certified_cons (by exact certified3431)
  apply certified_cons (by exact certified3431swap)
  apply certified_cons (by exact certified3432)
  apply certified_cons (by exact certified3432swap)
  apply certified_cons (by exact certified3433)
  apply certified_cons (by exact certified3433swap)
  apply certified_cons (by exact certified3434)
  apply certified_cons (by exact certified3434swap)
  apply certified_cons (by exact certified3435)
  apply certified_cons (by exact certified3435swap)
  apply certified_cons (by exact certified3436)
  apply certified_cons (by exact certified3436swap)
  apply certified_cons (by exact certified3437)
  apply certified_cons (by exact certified3437swap)
  apply certified_cons (by exact certified3438)
  apply certified_cons (by exact certified3438swap)
  apply certified_cons (by exact certified3439)
  apply certified_cons (by exact certified3439swap)
  apply certified_cons (by exact certified3440)
  apply certified_cons (by exact certified3440swap)
  apply certified_cons (by exact certified3441)
  apply certified_cons (by exact certified3441swap)
  apply certified_cons (by exact certified3442)
  apply certified_cons (by exact certified3442swap)
  apply certified_cons (by exact certified3443)
  apply certified_cons (by exact certified3443swap)
  apply certified_cons (by exact certified3444)
  apply certified_cons (by exact certified3444swap)
  apply certified_cons (by exact certified3445)
  apply certified_cons (by exact certified3445swap)
  apply certified_cons (by exact certified3446)
  apply certified_cons (by exact certified3446swap)
  apply certified_cons (by exact certified3447)
  apply certified_cons (by exact certified3447swap)
  apply certified_cons (by exact certified3448)
  apply certified_cons (by exact certified3448swap)
  apply certified_cons (by exact certified3449)
  apply certified_cons (by exact certified3449swap)
  simp
#print axioms certified_keys068
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
