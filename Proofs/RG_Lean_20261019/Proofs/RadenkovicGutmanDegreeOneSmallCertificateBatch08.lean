/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeOneSmallKeysData
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0400
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0401
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0402
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0403
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0404
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0405
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0406
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0407
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0408
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0409
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0410
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0411
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0412
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0413
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0414
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0415
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0416
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0417
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0418
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0419
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0420
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0421
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0422
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0423
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0424
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0425
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0426
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0427
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0428
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0429
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0430
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0431
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0432
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0433
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0434
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0435
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0436
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0437
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0438
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0439
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0440
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0441
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0442
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0443
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0444
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0445
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0446
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0447
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0448
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0449
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeOneSmallActualCases
theorem certified_keys08 : ∀ k ∈ keys08, Certified k := by
  apply certified_cons (by exact certified0400)
  apply certified_cons (by exact certified0400swap)
  apply certified_cons (by exact certified0401)
  apply certified_cons (by exact certified0402)
  apply certified_cons (by exact certified0403)
  apply certified_cons (by exact certified0403swap)
  apply certified_cons (by exact certified0404)
  apply certified_cons (by exact certified0404swap)
  apply certified_cons (by exact certified0405)
  apply certified_cons (by exact certified0405swap)
  apply certified_cons (by exact certified0406)
  apply certified_cons (by exact certified0406swap)
  apply certified_cons (by exact certified0407)
  apply certified_cons (by exact certified0408)
  apply certified_cons (by exact certified0408swap)
  apply certified_cons (by exact certified0409)
  apply certified_cons (by exact certified0409swap)
  apply certified_cons (by exact certified0410)
  apply certified_cons (by exact certified0411)
  apply certified_cons (by exact certified0412)
  apply certified_cons (by exact certified0412swap)
  apply certified_cons (by exact certified0413)
  apply certified_cons (by exact certified0413swap)
  apply certified_cons (by exact certified0414)
  apply certified_cons (by exact certified0414swap)
  apply certified_cons (by exact certified0415)
  apply certified_cons (by exact certified0415swap)
  apply certified_cons (by exact certified0416)
  apply certified_cons (by exact certified0417)
  apply certified_cons (by exact certified0417swap)
  apply certified_cons (by exact certified0418)
  apply certified_cons (by exact certified0418swap)
  apply certified_cons (by exact certified0419)
  apply certified_cons (by exact certified0420)
  apply certified_cons (by exact certified0421)
  apply certified_cons (by exact certified0421swap)
  apply certified_cons (by exact certified0422)
  apply certified_cons (by exact certified0422swap)
  apply certified_cons (by exact certified0423)
  apply certified_cons (by exact certified0423swap)
  apply certified_cons (by exact certified0424)
  apply certified_cons (by exact certified0424swap)
  apply certified_cons (by exact certified0425)
  apply certified_cons (by exact certified0426)
  apply certified_cons (by exact certified0426swap)
  apply certified_cons (by exact certified0427)
  apply certified_cons (by exact certified0427swap)
  apply certified_cons (by exact certified0428)
  apply certified_cons (by exact certified0429)
  apply certified_cons (by exact certified0430)
  apply certified_cons (by exact certified0430swap)
  apply certified_cons (by exact certified0431)
  apply certified_cons (by exact certified0431swap)
  apply certified_cons (by exact certified0432)
  apply certified_cons (by exact certified0432swap)
  apply certified_cons (by exact certified0433)
  apply certified_cons (by exact certified0433swap)
  apply certified_cons (by exact certified0434)
  apply certified_cons (by exact certified0435)
  apply certified_cons (by exact certified0435swap)
  apply certified_cons (by exact certified0436)
  apply certified_cons (by exact certified0436swap)
  apply certified_cons (by exact certified0437)
  apply certified_cons (by exact certified0438)
  apply certified_cons (by exact certified0439)
  apply certified_cons (by exact certified0439swap)
  apply certified_cons (by exact certified0440)
  apply certified_cons (by exact certified0440swap)
  apply certified_cons (by exact certified0441)
  apply certified_cons (by exact certified0441swap)
  apply certified_cons (by exact certified0442)
  apply certified_cons (by exact certified0442swap)
  apply certified_cons (by exact certified0443)
  apply certified_cons (by exact certified0444)
  apply certified_cons (by exact certified0444swap)
  apply certified_cons (by exact certified0445)
  apply certified_cons (by exact certified0445swap)
  apply certified_cons (by exact certified0446)
  apply certified_cons (by exact certified0447)
  apply certified_cons (by exact certified0448)
  apply certified_cons (by exact certified0448swap)
  apply certified_cons (by exact certified0449)
  apply certified_cons (by exact certified0449swap)
  simp
#print axioms certified_keys08
end Gebendorfer.RadenkovicGutman.DegreeOneSmallKeys
