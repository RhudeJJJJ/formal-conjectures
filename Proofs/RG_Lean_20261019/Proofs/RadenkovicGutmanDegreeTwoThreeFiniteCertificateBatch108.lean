/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteKeysData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5400
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5401
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5402
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5403
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5404
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5405
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5406
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5407
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5408
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5409
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5410
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5411
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5412
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5413
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5414
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5415
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5416
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5417
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5418
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5419
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5420
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5421
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5422
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5423
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5424
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5425
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5426
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5427
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5428
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5429
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5430
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5431
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5432
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5433
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5434
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5435
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5436
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5437
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5438
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5439
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5440
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5441
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5442
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5443
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5444
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5445
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5446
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5447
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5448
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5449
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeTwoThreeFiniteActualCases
theorem certified_keys108 : ∀ k ∈ keys108, Certified k := by
  apply certified_cons (by exact certified5400)
  apply certified_cons (by exact certified5400swap)
  apply certified_cons (by exact certified5401)
  apply certified_cons (by exact certified5401swap)
  apply certified_cons (by exact certified5402)
  apply certified_cons (by exact certified5402swap)
  apply certified_cons (by exact certified5403)
  apply certified_cons (by exact certified5403swap)
  apply certified_cons (by exact certified5404)
  apply certified_cons (by exact certified5404swap)
  apply certified_cons (by exact certified5405)
  apply certified_cons (by exact certified5405swap)
  apply certified_cons (by exact certified5406)
  apply certified_cons (by exact certified5406swap)
  apply certified_cons (by exact certified5407)
  apply certified_cons (by exact certified5407swap)
  apply certified_cons (by exact certified5408)
  apply certified_cons (by exact certified5408swap)
  apply certified_cons (by exact certified5409)
  apply certified_cons (by exact certified5409swap)
  apply certified_cons (by exact certified5410)
  apply certified_cons (by exact certified5410swap)
  apply certified_cons (by exact certified5411)
  apply certified_cons (by exact certified5411swap)
  apply certified_cons (by exact certified5412)
  apply certified_cons (by exact certified5412swap)
  apply certified_cons (by exact certified5413)
  apply certified_cons (by exact certified5413swap)
  apply certified_cons (by exact certified5414)
  apply certified_cons (by exact certified5414swap)
  apply certified_cons (by exact certified5415)
  apply certified_cons (by exact certified5415swap)
  apply certified_cons (by exact certified5416)
  apply certified_cons (by exact certified5416swap)
  apply certified_cons (by exact certified5417)
  apply certified_cons (by exact certified5418)
  apply certified_cons (by exact certified5419)
  apply certified_cons (by exact certified5420)
  apply certified_cons (by exact certified5421)
  apply certified_cons (by exact certified5422)
  apply certified_cons (by exact certified5422swap)
  apply certified_cons (by exact certified5423)
  apply certified_cons (by exact certified5423swap)
  apply certified_cons (by exact certified5424)
  apply certified_cons (by exact certified5424swap)
  apply certified_cons (by exact certified5425)
  apply certified_cons (by exact certified5426)
  apply certified_cons (by exact certified5427)
  apply certified_cons (by exact certified5428)
  apply certified_cons (by exact certified5429)
  apply certified_cons (by exact certified5430)
  apply certified_cons (by exact certified5431)
  apply certified_cons (by exact certified5432)
  apply certified_cons (by exact certified5433)
  apply certified_cons (by exact certified5434)
  apply certified_cons (by exact certified5435)
  apply certified_cons (by exact certified5436)
  apply certified_cons (by exact certified5437)
  apply certified_cons (by exact certified5438)
  apply certified_cons (by exact certified5439)
  apply certified_cons (by exact certified5440)
  apply certified_cons (by exact certified5441)
  apply certified_cons (by exact certified5442)
  apply certified_cons (by exact certified5443)
  apply certified_cons (by exact certified5444)
  apply certified_cons (by exact certified5445)
  apply certified_cons (by exact certified5446)
  apply certified_cons (by exact certified5447)
  apply certified_cons (by exact certified5448)
  apply certified_cons (by exact certified5449)
  simp
#print axioms certified_keys108
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
