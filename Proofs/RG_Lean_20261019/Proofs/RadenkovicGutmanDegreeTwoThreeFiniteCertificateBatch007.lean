/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteKeysData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0350
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0351
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0352
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0353
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0354
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0355
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0356
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0357
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0358
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0359
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0360
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0361
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0362
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0363
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0364
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0365
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0366
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0367
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0368
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0369
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0370
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0371
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0372
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0373
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0374
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0375
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0376
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0377
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0378
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0379
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0380
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0381
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0382
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0383
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0384
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0385
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0386
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0387
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0388
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0389
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0390
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0391
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0392
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0393
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0394
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0395
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0396
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0397
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0398
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0399
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeTwoThreeFiniteActualCases
theorem certified_keys007 : ∀ k ∈ keys007, Certified k := by
  apply certified_cons (by exact certified0350)
  apply certified_cons (by exact certified0351)
  apply certified_cons (by exact certified0352)
  apply certified_cons (by exact certified0353)
  apply certified_cons (by exact certified0354)
  apply certified_cons (by exact certified0355)
  apply certified_cons (by exact certified0356)
  apply certified_cons (by exact certified0357)
  apply certified_cons (by exact certified0358)
  apply certified_cons (by exact certified0359)
  apply certified_cons (by exact certified0360)
  apply certified_cons (by exact certified0361)
  apply certified_cons (by exact certified0362)
  apply certified_cons (by exact certified0363)
  apply certified_cons (by exact certified0364)
  apply certified_cons (by exact certified0365)
  apply certified_cons (by exact certified0366)
  apply certified_cons (by exact certified0367)
  apply certified_cons (by exact certified0368)
  apply certified_cons (by exact certified0369)
  apply certified_cons (by exact certified0370)
  apply certified_cons (by exact certified0371)
  apply certified_cons (by exact certified0372)
  apply certified_cons (by exact certified0373)
  apply certified_cons (by exact certified0374)
  apply certified_cons (by exact certified0375)
  apply certified_cons (by exact certified0376)
  apply certified_cons (by exact certified0377)
  apply certified_cons (by exact certified0378)
  apply certified_cons (by exact certified0379)
  apply certified_cons (by exact certified0380)
  apply certified_cons (by exact certified0381)
  apply certified_cons (by exact certified0382)
  apply certified_cons (by exact certified0383)
  apply certified_cons (by exact certified0384)
  apply certified_cons (by exact certified0385)
  apply certified_cons (by exact certified0386)
  apply certified_cons (by exact certified0387)
  apply certified_cons (by exact certified0388)
  apply certified_cons (by exact certified0389)
  apply certified_cons (by exact certified0390)
  apply certified_cons (by exact certified0391)
  apply certified_cons (by exact certified0392)
  apply certified_cons (by exact certified0393)
  apply certified_cons (by exact certified0394)
  apply certified_cons (by exact certified0395)
  apply certified_cons (by exact certified0396)
  apply certified_cons (by exact certified0397)
  apply certified_cons (by exact certified0398)
  apply certified_cons (by exact certified0399)
  simp
#print axioms certified_keys007
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
