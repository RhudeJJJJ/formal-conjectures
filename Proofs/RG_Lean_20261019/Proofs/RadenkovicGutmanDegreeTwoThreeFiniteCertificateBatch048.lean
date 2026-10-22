/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteKeysData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2400
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2401
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2402
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2403
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2404
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2405
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2406
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2407
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2408
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2409
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2410
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2411
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2412
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2413
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2414
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2415
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2416
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2417
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2418
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2419
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2420
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2421
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2422
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2423
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2424
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2425
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2426
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2427
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2428
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2429
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2430
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2431
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2432
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2433
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2434
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2435
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2436
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2437
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2438
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2439
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2440
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2441
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2442
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2443
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2444
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2445
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2446
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2447
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2448
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2449
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeTwoThreeFiniteActualCases
theorem certified_keys048 : ∀ k ∈ keys048, Certified k := by
  apply certified_cons (by exact certified2400)
  apply certified_cons (by exact certified2400swap)
  apply certified_cons (by exact certified2401)
  apply certified_cons (by exact certified2401swap)
  apply certified_cons (by exact certified2402)
  apply certified_cons (by exact certified2402swap)
  apply certified_cons (by exact certified2403)
  apply certified_cons (by exact certified2403swap)
  apply certified_cons (by exact certified2404)
  apply certified_cons (by exact certified2404swap)
  apply certified_cons (by exact certified2405)
  apply certified_cons (by exact certified2405swap)
  apply certified_cons (by exact certified2406)
  apply certified_cons (by exact certified2406swap)
  apply certified_cons (by exact certified2407)
  apply certified_cons (by exact certified2407swap)
  apply certified_cons (by exact certified2408)
  apply certified_cons (by exact certified2408swap)
  apply certified_cons (by exact certified2409)
  apply certified_cons (by exact certified2409swap)
  apply certified_cons (by exact certified2410)
  apply certified_cons (by exact certified2410swap)
  apply certified_cons (by exact certified2411)
  apply certified_cons (by exact certified2411swap)
  apply certified_cons (by exact certified2412)
  apply certified_cons (by exact certified2412swap)
  apply certified_cons (by exact certified2413)
  apply certified_cons (by exact certified2413swap)
  apply certified_cons (by exact certified2414)
  apply certified_cons (by exact certified2414swap)
  apply certified_cons (by exact certified2415)
  apply certified_cons (by exact certified2415swap)
  apply certified_cons (by exact certified2416)
  apply certified_cons (by exact certified2416swap)
  apply certified_cons (by exact certified2417)
  apply certified_cons (by exact certified2417swap)
  apply certified_cons (by exact certified2418)
  apply certified_cons (by exact certified2418swap)
  apply certified_cons (by exact certified2419)
  apply certified_cons (by exact certified2419swap)
  apply certified_cons (by exact certified2420)
  apply certified_cons (by exact certified2420swap)
  apply certified_cons (by exact certified2421)
  apply certified_cons (by exact certified2421swap)
  apply certified_cons (by exact certified2422)
  apply certified_cons (by exact certified2422swap)
  apply certified_cons (by exact certified2423)
  apply certified_cons (by exact certified2423swap)
  apply certified_cons (by exact certified2424)
  apply certified_cons (by exact certified2424swap)
  apply certified_cons (by exact certified2425)
  apply certified_cons (by exact certified2425swap)
  apply certified_cons (by exact certified2426)
  apply certified_cons (by exact certified2426swap)
  apply certified_cons (by exact certified2427)
  apply certified_cons (by exact certified2427swap)
  apply certified_cons (by exact certified2428)
  apply certified_cons (by exact certified2428swap)
  apply certified_cons (by exact certified2429)
  apply certified_cons (by exact certified2429swap)
  apply certified_cons (by exact certified2430)
  apply certified_cons (by exact certified2430swap)
  apply certified_cons (by exact certified2431)
  apply certified_cons (by exact certified2431swap)
  apply certified_cons (by exact certified2432)
  apply certified_cons (by exact certified2432swap)
  apply certified_cons (by exact certified2433)
  apply certified_cons (by exact certified2433swap)
  apply certified_cons (by exact certified2434)
  apply certified_cons (by exact certified2434swap)
  apply certified_cons (by exact certified2435)
  apply certified_cons (by exact certified2435swap)
  apply certified_cons (by exact certified2436)
  apply certified_cons (by exact certified2436swap)
  apply certified_cons (by exact certified2437)
  apply certified_cons (by exact certified2437swap)
  apply certified_cons (by exact certified2438)
  apply certified_cons (by exact certified2438swap)
  apply certified_cons (by exact certified2439)
  apply certified_cons (by exact certified2439swap)
  apply certified_cons (by exact certified2440)
  apply certified_cons (by exact certified2440swap)
  apply certified_cons (by exact certified2441)
  apply certified_cons (by exact certified2441swap)
  apply certified_cons (by exact certified2442)
  apply certified_cons (by exact certified2442swap)
  apply certified_cons (by exact certified2443)
  apply certified_cons (by exact certified2443swap)
  apply certified_cons (by exact certified2444)
  apply certified_cons (by exact certified2444swap)
  apply certified_cons (by exact certified2445)
  apply certified_cons (by exact certified2445swap)
  apply certified_cons (by exact certified2446)
  apply certified_cons (by exact certified2446swap)
  apply certified_cons (by exact certified2447)
  apply certified_cons (by exact certified2447swap)
  apply certified_cons (by exact certified2448)
  apply certified_cons (by exact certified2448swap)
  apply certified_cons (by exact certified2449)
  apply certified_cons (by exact certified2449swap)
  simp
#print axioms certified_keys048
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
