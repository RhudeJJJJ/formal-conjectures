/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteKeysData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5300
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5301
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5302
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5303
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5304
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5305
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5306
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5307
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5308
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5309
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5310
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5311
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5312
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5313
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5314
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5315
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5316
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5317
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5318
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5319
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5320
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5321
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5322
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5323
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5324
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5325
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5326
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5327
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5328
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5329
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5330
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5331
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5332
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5333
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5334
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5335
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5336
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5337
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5338
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5339
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5340
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5341
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5342
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5343
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5344
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5345
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5346
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5347
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5348
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5349
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeTwoThreeFiniteActualCases
theorem certified_keys106 : ∀ k ∈ keys106, Certified k := by
  apply certified_cons (by exact certified5300)
  apply certified_cons (by exact certified5300swap)
  apply certified_cons (by exact certified5301)
  apply certified_cons (by exact certified5301swap)
  apply certified_cons (by exact certified5302)
  apply certified_cons (by exact certified5302swap)
  apply certified_cons (by exact certified5303)
  apply certified_cons (by exact certified5303swap)
  apply certified_cons (by exact certified5304)
  apply certified_cons (by exact certified5304swap)
  apply certified_cons (by exact certified5305)
  apply certified_cons (by exact certified5305swap)
  apply certified_cons (by exact certified5306)
  apply certified_cons (by exact certified5306swap)
  apply certified_cons (by exact certified5307)
  apply certified_cons (by exact certified5307swap)
  apply certified_cons (by exact certified5308)
  apply certified_cons (by exact certified5308swap)
  apply certified_cons (by exact certified5309)
  apply certified_cons (by exact certified5309swap)
  apply certified_cons (by exact certified5310)
  apply certified_cons (by exact certified5310swap)
  apply certified_cons (by exact certified5311)
  apply certified_cons (by exact certified5311swap)
  apply certified_cons (by exact certified5312)
  apply certified_cons (by exact certified5312swap)
  apply certified_cons (by exact certified5313)
  apply certified_cons (by exact certified5313swap)
  apply certified_cons (by exact certified5314)
  apply certified_cons (by exact certified5314swap)
  apply certified_cons (by exact certified5315)
  apply certified_cons (by exact certified5315swap)
  apply certified_cons (by exact certified5316)
  apply certified_cons (by exact certified5316swap)
  apply certified_cons (by exact certified5317)
  apply certified_cons (by exact certified5317swap)
  apply certified_cons (by exact certified5318)
  apply certified_cons (by exact certified5318swap)
  apply certified_cons (by exact certified5319)
  apply certified_cons (by exact certified5319swap)
  apply certified_cons (by exact certified5320)
  apply certified_cons (by exact certified5320swap)
  apply certified_cons (by exact certified5321)
  apply certified_cons (by exact certified5321swap)
  apply certified_cons (by exact certified5322)
  apply certified_cons (by exact certified5322swap)
  apply certified_cons (by exact certified5323)
  apply certified_cons (by exact certified5323swap)
  apply certified_cons (by exact certified5324)
  apply certified_cons (by exact certified5324swap)
  apply certified_cons (by exact certified5325)
  apply certified_cons (by exact certified5325swap)
  apply certified_cons (by exact certified5326)
  apply certified_cons (by exact certified5326swap)
  apply certified_cons (by exact certified5327)
  apply certified_cons (by exact certified5327swap)
  apply certified_cons (by exact certified5328)
  apply certified_cons (by exact certified5328swap)
  apply certified_cons (by exact certified5329)
  apply certified_cons (by exact certified5329swap)
  apply certified_cons (by exact certified5330)
  apply certified_cons (by exact certified5330swap)
  apply certified_cons (by exact certified5331)
  apply certified_cons (by exact certified5331swap)
  apply certified_cons (by exact certified5332)
  apply certified_cons (by exact certified5332swap)
  apply certified_cons (by exact certified5333)
  apply certified_cons (by exact certified5333swap)
  apply certified_cons (by exact certified5334)
  apply certified_cons (by exact certified5334swap)
  apply certified_cons (by exact certified5335)
  apply certified_cons (by exact certified5335swap)
  apply certified_cons (by exact certified5336)
  apply certified_cons (by exact certified5336swap)
  apply certified_cons (by exact certified5337)
  apply certified_cons (by exact certified5337swap)
  apply certified_cons (by exact certified5338)
  apply certified_cons (by exact certified5338swap)
  apply certified_cons (by exact certified5339)
  apply certified_cons (by exact certified5339swap)
  apply certified_cons (by exact certified5340)
  apply certified_cons (by exact certified5340swap)
  apply certified_cons (by exact certified5341)
  apply certified_cons (by exact certified5341swap)
  apply certified_cons (by exact certified5342)
  apply certified_cons (by exact certified5342swap)
  apply certified_cons (by exact certified5343)
  apply certified_cons (by exact certified5343swap)
  apply certified_cons (by exact certified5344)
  apply certified_cons (by exact certified5344swap)
  apply certified_cons (by exact certified5345)
  apply certified_cons (by exact certified5345swap)
  apply certified_cons (by exact certified5346)
  apply certified_cons (by exact certified5346swap)
  apply certified_cons (by exact certified5347)
  apply certified_cons (by exact certified5347swap)
  apply certified_cons (by exact certified5348)
  apply certified_cons (by exact certified5348swap)
  apply certified_cons (by exact certified5349)
  apply certified_cons (by exact certified5349swap)
  simp
#print axioms certified_keys106
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
