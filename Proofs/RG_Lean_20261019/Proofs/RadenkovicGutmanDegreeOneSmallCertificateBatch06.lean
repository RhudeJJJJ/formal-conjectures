/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeOneSmallKeysData
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0300
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0301
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0302
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0303
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0304
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0305
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0306
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0307
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0308
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0309
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0310
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0311
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0312
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0313
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0314
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0315
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0316
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0317
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0318
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0319
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0320
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0321
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0322
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0323
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0324
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0325
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0326
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0327
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0328
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0329
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0330
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0331
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0332
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0333
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0334
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0335
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0336
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0337
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0338
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0339
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0340
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0341
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0342
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0343
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0344
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0345
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0346
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0347
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0348
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0349
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeOneSmallActualCases
theorem certified_keys06 : ∀ k ∈ keys06, Certified k := by
  apply certified_cons (by exact certified0300)
  apply certified_cons (by exact certified0300swap)
  apply certified_cons (by exact certified0301)
  apply certified_cons (by exact certified0301swap)
  apply certified_cons (by exact certified0302)
  apply certified_cons (by exact certified0303)
  apply certified_cons (by exact certified0304)
  apply certified_cons (by exact certified0304swap)
  apply certified_cons (by exact certified0305)
  apply certified_cons (by exact certified0305swap)
  apply certified_cons (by exact certified0306)
  apply certified_cons (by exact certified0306swap)
  apply certified_cons (by exact certified0307)
  apply certified_cons (by exact certified0307swap)
  apply certified_cons (by exact certified0308)
  apply certified_cons (by exact certified0309)
  apply certified_cons (by exact certified0309swap)
  apply certified_cons (by exact certified0310)
  apply certified_cons (by exact certified0310swap)
  apply certified_cons (by exact certified0311)
  apply certified_cons (by exact certified0312)
  apply certified_cons (by exact certified0313)
  apply certified_cons (by exact certified0313swap)
  apply certified_cons (by exact certified0314)
  apply certified_cons (by exact certified0314swap)
  apply certified_cons (by exact certified0315)
  apply certified_cons (by exact certified0315swap)
  apply certified_cons (by exact certified0316)
  apply certified_cons (by exact certified0316swap)
  apply certified_cons (by exact certified0317)
  apply certified_cons (by exact certified0318)
  apply certified_cons (by exact certified0318swap)
  apply certified_cons (by exact certified0319)
  apply certified_cons (by exact certified0319swap)
  apply certified_cons (by exact certified0320)
  apply certified_cons (by exact certified0321)
  apply certified_cons (by exact certified0322)
  apply certified_cons (by exact certified0322swap)
  apply certified_cons (by exact certified0323)
  apply certified_cons (by exact certified0323swap)
  apply certified_cons (by exact certified0324)
  apply certified_cons (by exact certified0324swap)
  apply certified_cons (by exact certified0325)
  apply certified_cons (by exact certified0325swap)
  apply certified_cons (by exact certified0326)
  apply certified_cons (by exact certified0327)
  apply certified_cons (by exact certified0327swap)
  apply certified_cons (by exact certified0328)
  apply certified_cons (by exact certified0328swap)
  apply certified_cons (by exact certified0329)
  apply certified_cons (by exact certified0330)
  apply certified_cons (by exact certified0331)
  apply certified_cons (by exact certified0331swap)
  apply certified_cons (by exact certified0332)
  apply certified_cons (by exact certified0332swap)
  apply certified_cons (by exact certified0333)
  apply certified_cons (by exact certified0333swap)
  apply certified_cons (by exact certified0334)
  apply certified_cons (by exact certified0334swap)
  apply certified_cons (by exact certified0335)
  apply certified_cons (by exact certified0336)
  apply certified_cons (by exact certified0336swap)
  apply certified_cons (by exact certified0337)
  apply certified_cons (by exact certified0337swap)
  apply certified_cons (by exact certified0338)
  apply certified_cons (by exact certified0339)
  apply certified_cons (by exact certified0340)
  apply certified_cons (by exact certified0340swap)
  apply certified_cons (by exact certified0341)
  apply certified_cons (by exact certified0341swap)
  apply certified_cons (by exact certified0342)
  apply certified_cons (by exact certified0342swap)
  apply certified_cons (by exact certified0343)
  apply certified_cons (by exact certified0343swap)
  apply certified_cons (by exact certified0344)
  apply certified_cons (by exact certified0345)
  apply certified_cons (by exact certified0345swap)
  apply certified_cons (by exact certified0346)
  apply certified_cons (by exact certified0346swap)
  apply certified_cons (by exact certified0347)
  apply certified_cons (by exact certified0348)
  apply certified_cons (by exact certified0349)
  apply certified_cons (by exact certified0349swap)
  simp
#print axioms certified_keys06
end Gebendorfer.RadenkovicGutman.DegreeOneSmallKeys
