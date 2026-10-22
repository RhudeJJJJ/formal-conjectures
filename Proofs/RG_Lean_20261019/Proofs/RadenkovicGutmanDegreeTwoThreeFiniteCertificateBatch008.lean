/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteKeysData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0400
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0401
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0402
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0403
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0404
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0405
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0406
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0407
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0408
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0409
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0410
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0411
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0412
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0413
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0414
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0415
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0416
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0417
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0418
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0419
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0420
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0421
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0422
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0423
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0424
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0425
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0426
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0427
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0428
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0429
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0430
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0431
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0432
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0433
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0434
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0435
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0436
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0437
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0438
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0439
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0440
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0441
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0442
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0443
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0444
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0445
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0446
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0447
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0448
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0449
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeTwoThreeFiniteActualCases
theorem certified_keys008 : ∀ k ∈ keys008, Certified k := by
  apply certified_cons (by exact certified0400)
  apply certified_cons (by exact certified0401)
  apply certified_cons (by exact certified0402)
  apply certified_cons (by exact certified0403)
  apply certified_cons (by exact certified0404)
  apply certified_cons (by exact certified0405)
  apply certified_cons (by exact certified0406)
  apply certified_cons (by exact certified0407)
  apply certified_cons (by exact certified0408)
  apply certified_cons (by exact certified0409)
  apply certified_cons (by exact certified0410)
  apply certified_cons (by exact certified0411)
  apply certified_cons (by exact certified0412)
  apply certified_cons (by exact certified0413)
  apply certified_cons (by exact certified0414)
  apply certified_cons (by exact certified0415)
  apply certified_cons (by exact certified0416)
  apply certified_cons (by exact certified0417)
  apply certified_cons (by exact certified0418)
  apply certified_cons (by exact certified0419)
  apply certified_cons (by exact certified0420)
  apply certified_cons (by exact certified0421)
  apply certified_cons (by exact certified0422)
  apply certified_cons (by exact certified0423)
  apply certified_cons (by exact certified0424)
  apply certified_cons (by exact certified0425)
  apply certified_cons (by exact certified0426)
  apply certified_cons (by exact certified0427)
  apply certified_cons (by exact certified0428)
  apply certified_cons (by exact certified0429)
  apply certified_cons (by exact certified0430)
  apply certified_cons (by exact certified0431)
  apply certified_cons (by exact certified0432)
  apply certified_cons (by exact certified0433)
  apply certified_cons (by exact certified0434)
  apply certified_cons (by exact certified0435)
  apply certified_cons (by exact certified0436)
  apply certified_cons (by exact certified0437)
  apply certified_cons (by exact certified0438)
  apply certified_cons (by exact certified0439)
  apply certified_cons (by exact certified0440)
  apply certified_cons (by exact certified0441)
  apply certified_cons (by exact certified0442)
  apply certified_cons (by exact certified0443)
  apply certified_cons (by exact certified0444)
  apply certified_cons (by exact certified0445)
  apply certified_cons (by exact certified0446)
  apply certified_cons (by exact certified0447)
  apply certified_cons (by exact certified0448)
  apply certified_cons (by exact certified0449)
  simp
#print axioms certified_keys008
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
