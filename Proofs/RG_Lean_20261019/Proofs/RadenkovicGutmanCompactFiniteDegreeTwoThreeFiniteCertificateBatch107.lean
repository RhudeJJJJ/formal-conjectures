/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteKeysData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5350
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5351
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5352
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5353
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5354
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5355
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5356
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5357
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5358
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5359
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5360
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5361
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5362
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5363
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5364
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5365
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5366
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5367
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5368
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5369
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5370
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5371
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5372
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5373
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5374
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5375
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5376
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5377
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5378
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5379
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5380
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5381
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5382
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5383
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5384
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5385
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5386
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5387
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5388
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5389
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5390
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5391
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5392
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5393
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5394
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5395
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5396
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5397
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5398
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5399
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeTwoThreeFiniteActualCases
theorem certified_keys107 : ∀ k ∈ keys107, Certified k := by
  apply certified_cons (by exact certified5350)
  apply certified_cons (by exact certified5350swap)
  apply certified_cons (by exact certified5351)
  apply certified_cons (by exact certified5351swap)
  apply certified_cons (by exact certified5352)
  apply certified_cons (by exact certified5352swap)
  apply certified_cons (by exact certified5353)
  apply certified_cons (by exact certified5353swap)
  apply certified_cons (by exact certified5354)
  apply certified_cons (by exact certified5354swap)
  apply certified_cons (by exact certified5355)
  apply certified_cons (by exact certified5355swap)
  apply certified_cons (by exact certified5356)
  apply certified_cons (by exact certified5356swap)
  apply certified_cons (by exact certified5357)
  apply certified_cons (by exact certified5357swap)
  apply certified_cons (by exact certified5358)
  apply certified_cons (by exact certified5358swap)
  apply certified_cons (by exact certified5359)
  apply certified_cons (by exact certified5359swap)
  apply certified_cons (by exact certified5360)
  apply certified_cons (by exact certified5360swap)
  apply certified_cons (by exact certified5361)
  apply certified_cons (by exact certified5361swap)
  apply certified_cons (by exact certified5362)
  apply certified_cons (by exact certified5362swap)
  apply certified_cons (by exact certified5363)
  apply certified_cons (by exact certified5363swap)
  apply certified_cons (by exact certified5364)
  apply certified_cons (by exact certified5364swap)
  apply certified_cons (by exact certified5365)
  apply certified_cons (by exact certified5365swap)
  apply certified_cons (by exact certified5366)
  apply certified_cons (by exact certified5366swap)
  apply certified_cons (by exact certified5367)
  apply certified_cons (by exact certified5367swap)
  apply certified_cons (by exact certified5368)
  apply certified_cons (by exact certified5368swap)
  apply certified_cons (by exact certified5369)
  apply certified_cons (by exact certified5369swap)
  apply certified_cons (by exact certified5370)
  apply certified_cons (by exact certified5370swap)
  apply certified_cons (by exact certified5371)
  apply certified_cons (by exact certified5372)
  apply certified_cons (by exact certified5373)
  apply certified_cons (by exact certified5374)
  apply certified_cons (by exact certified5375)
  apply certified_cons (by exact certified5376)
  apply certified_cons (by exact certified5377)
  apply certified_cons (by exact certified5378)
  apply certified_cons (by exact certified5379)
  apply certified_cons (by exact certified5380)
  apply certified_cons (by exact certified5381)
  apply certified_cons (by exact certified5382)
  apply certified_cons (by exact certified5383)
  apply certified_cons (by exact certified5384)
  apply certified_cons (by exact certified5385)
  apply certified_cons (by exact certified5386)
  apply certified_cons (by exact certified5387)
  apply certified_cons (by exact certified5388)
  apply certified_cons (by exact certified5389)
  apply certified_cons (by exact certified5390)
  apply certified_cons (by exact certified5391)
  apply certified_cons (by exact certified5392)
  apply certified_cons (by exact certified5393)
  apply certified_cons (by exact certified5394)
  apply certified_cons (by exact certified5395)
  apply certified_cons (by exact certified5396)
  apply certified_cons (by exact certified5397)
  apply certified_cons (by exact certified5398)
  apply certified_cons (by exact certified5398swap)
  apply certified_cons (by exact certified5399)
  apply certified_cons (by exact certified5399swap)
  simp
#print axioms certified_keys107
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
