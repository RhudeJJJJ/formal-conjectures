/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteKeysData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0300
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0301
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0302
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0303
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0304
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0305
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0306
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0307
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0308
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0309
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0310
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0311
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0312
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0313
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0314
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0315
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0316
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0317
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0318
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0319
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0320
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0321
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0322
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0323
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0324
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0325
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0326
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0327
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0328
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0329
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0330
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0331
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0332
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0333
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0334
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0335
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0336
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0337
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0338
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0339
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0340
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0341
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0342
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0343
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0344
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0345
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0346
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0347
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0348
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0349
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeTwoThreeFiniteActualCases
theorem certified_keys006 : ∀ k ∈ keys006, Certified k := by
  apply certified_cons (by exact certified0300)
  apply certified_cons (by exact certified0301)
  apply certified_cons (by exact certified0302)
  apply certified_cons (by exact certified0303)
  apply certified_cons (by exact certified0304)
  apply certified_cons (by exact certified0305)
  apply certified_cons (by exact certified0306)
  apply certified_cons (by exact certified0307)
  apply certified_cons (by exact certified0308)
  apply certified_cons (by exact certified0309)
  apply certified_cons (by exact certified0310)
  apply certified_cons (by exact certified0311)
  apply certified_cons (by exact certified0312)
  apply certified_cons (by exact certified0313)
  apply certified_cons (by exact certified0314)
  apply certified_cons (by exact certified0315)
  apply certified_cons (by exact certified0316)
  apply certified_cons (by exact certified0317)
  apply certified_cons (by exact certified0318)
  apply certified_cons (by exact certified0319)
  apply certified_cons (by exact certified0320)
  apply certified_cons (by exact certified0321)
  apply certified_cons (by exact certified0322)
  apply certified_cons (by exact certified0323)
  apply certified_cons (by exact certified0324)
  apply certified_cons (by exact certified0325)
  apply certified_cons (by exact certified0326)
  apply certified_cons (by exact certified0327)
  apply certified_cons (by exact certified0328)
  apply certified_cons (by exact certified0329)
  apply certified_cons (by exact certified0330)
  apply certified_cons (by exact certified0331)
  apply certified_cons (by exact certified0332)
  apply certified_cons (by exact certified0333)
  apply certified_cons (by exact certified0334)
  apply certified_cons (by exact certified0335)
  apply certified_cons (by exact certified0336)
  apply certified_cons (by exact certified0337)
  apply certified_cons (by exact certified0338)
  apply certified_cons (by exact certified0339)
  apply certified_cons (by exact certified0340)
  apply certified_cons (by exact certified0341)
  apply certified_cons (by exact certified0342)
  apply certified_cons (by exact certified0343)
  apply certified_cons (by exact certified0344)
  apply certified_cons (by exact certified0345)
  apply certified_cons (by exact certified0346)
  apply certified_cons (by exact certified0347)
  apply certified_cons (by exact certified0348)
  apply certified_cons (by exact certified0349)
  simp
#print axioms certified_keys006
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
