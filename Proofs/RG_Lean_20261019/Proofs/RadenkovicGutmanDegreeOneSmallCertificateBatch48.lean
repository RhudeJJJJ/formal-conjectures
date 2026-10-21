/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeOneSmallKeysData
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2400
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2401
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2402
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2403
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2404
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2405
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2406
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2407
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2408
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2409
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2410
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2411
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2412
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2413
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2414
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2415
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2416
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2417
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2418
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2419
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2420
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2421
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2422
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2423
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2424
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2425
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2426
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2427
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2428
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2429
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2430
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2431
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2432
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2433
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2434
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2435
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2436
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2437
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2438
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2439
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2440
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2441
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2442
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2443
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2444
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2445
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2446
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2447
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2448
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2449
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeOneSmallActualCases
theorem certified_keys48 : ∀ k ∈ keys48, Certified k := by
  apply certified_cons (by exact certified2400)
  apply certified_cons (by exact certified2401)
  apply certified_cons (by exact certified2402)
  apply certified_cons (by exact certified2403)
  apply certified_cons (by exact certified2404)
  apply certified_cons (by exact certified2405)
  apply certified_cons (by exact certified2406)
  apply certified_cons (by exact certified2407)
  apply certified_cons (by exact certified2408)
  apply certified_cons (by exact certified2409)
  apply certified_cons (by exact certified2410)
  apply certified_cons (by exact certified2411)
  apply certified_cons (by exact certified2412)
  apply certified_cons (by exact certified2413)
  apply certified_cons (by exact certified2414)
  apply certified_cons (by exact certified2415)
  apply certified_cons (by exact certified2416)
  apply certified_cons (by exact certified2417)
  apply certified_cons (by exact certified2418)
  apply certified_cons (by exact certified2419)
  apply certified_cons (by exact certified2420)
  apply certified_cons (by exact certified2421)
  apply certified_cons (by exact certified2422)
  apply certified_cons (by exact certified2423)
  apply certified_cons (by exact certified2424)
  apply certified_cons (by exact certified2425)
  apply certified_cons (by exact certified2426)
  apply certified_cons (by exact certified2427)
  apply certified_cons (by exact certified2428)
  apply certified_cons (by exact certified2429)
  apply certified_cons (by exact certified2430)
  apply certified_cons (by exact certified2431)
  apply certified_cons (by exact certified2432)
  apply certified_cons (by exact certified2433)
  apply certified_cons (by exact certified2434)
  apply certified_cons (by exact certified2435)
  apply certified_cons (by exact certified2436)
  apply certified_cons (by exact certified2437)
  apply certified_cons (by exact certified2438)
  apply certified_cons (by exact certified2439)
  apply certified_cons (by exact certified2440)
  apply certified_cons (by exact certified2441)
  apply certified_cons (by exact certified2442)
  apply certified_cons (by exact certified2443)
  apply certified_cons (by exact certified2444)
  apply certified_cons (by exact certified2445)
  apply certified_cons (by exact certified2446)
  apply certified_cons (by exact certified2447)
  apply certified_cons (by exact certified2448)
  apply certified_cons (by exact certified2449)
  simp
#print axioms certified_keys48
end Gebendorfer.RadenkovicGutman.DegreeOneSmallKeys
