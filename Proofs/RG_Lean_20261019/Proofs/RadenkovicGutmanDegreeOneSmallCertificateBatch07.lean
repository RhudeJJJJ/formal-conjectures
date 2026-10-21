/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeOneSmallKeysData
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0350
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0351
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0352
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0353
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0354
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0355
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0356
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0357
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0358
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0359
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0360
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0361
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0362
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0363
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0364
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0365
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0366
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0367
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0368
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0369
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0370
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0371
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0372
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0373
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0374
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0375
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0376
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0377
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0378
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0379
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0380
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0381
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0382
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0383
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0384
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0385
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0386
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0387
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0388
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0389
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0390
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0391
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0392
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0393
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0394
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0395
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0396
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0397
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0398
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0399
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeOneSmallActualCases
theorem certified_keys07 : ∀ k ∈ keys07, Certified k := by
  apply certified_cons (by exact certified0350)
  apply certified_cons (by exact certified0350swap)
  apply certified_cons (by exact certified0351)
  apply certified_cons (by exact certified0351swap)
  apply certified_cons (by exact certified0352)
  apply certified_cons (by exact certified0352swap)
  apply certified_cons (by exact certified0353)
  apply certified_cons (by exact certified0354)
  apply certified_cons (by exact certified0354swap)
  apply certified_cons (by exact certified0355)
  apply certified_cons (by exact certified0355swap)
  apply certified_cons (by exact certified0356)
  apply certified_cons (by exact certified0357)
  apply certified_cons (by exact certified0358)
  apply certified_cons (by exact certified0358swap)
  apply certified_cons (by exact certified0359)
  apply certified_cons (by exact certified0359swap)
  apply certified_cons (by exact certified0360)
  apply certified_cons (by exact certified0360swap)
  apply certified_cons (by exact certified0361)
  apply certified_cons (by exact certified0361swap)
  apply certified_cons (by exact certified0362)
  apply certified_cons (by exact certified0363)
  apply certified_cons (by exact certified0363swap)
  apply certified_cons (by exact certified0364)
  apply certified_cons (by exact certified0364swap)
  apply certified_cons (by exact certified0365)
  apply certified_cons (by exact certified0366)
  apply certified_cons (by exact certified0367)
  apply certified_cons (by exact certified0367swap)
  apply certified_cons (by exact certified0368)
  apply certified_cons (by exact certified0368swap)
  apply certified_cons (by exact certified0369)
  apply certified_cons (by exact certified0369swap)
  apply certified_cons (by exact certified0370)
  apply certified_cons (by exact certified0370swap)
  apply certified_cons (by exact certified0371)
  apply certified_cons (by exact certified0372)
  apply certified_cons (by exact certified0372swap)
  apply certified_cons (by exact certified0373)
  apply certified_cons (by exact certified0373swap)
  apply certified_cons (by exact certified0374)
  apply certified_cons (by exact certified0375)
  apply certified_cons (by exact certified0376)
  apply certified_cons (by exact certified0376swap)
  apply certified_cons (by exact certified0377)
  apply certified_cons (by exact certified0377swap)
  apply certified_cons (by exact certified0378)
  apply certified_cons (by exact certified0378swap)
  apply certified_cons (by exact certified0379)
  apply certified_cons (by exact certified0379swap)
  apply certified_cons (by exact certified0380)
  apply certified_cons (by exact certified0381)
  apply certified_cons (by exact certified0381swap)
  apply certified_cons (by exact certified0382)
  apply certified_cons (by exact certified0382swap)
  apply certified_cons (by exact certified0383)
  apply certified_cons (by exact certified0384)
  apply certified_cons (by exact certified0385)
  apply certified_cons (by exact certified0385swap)
  apply certified_cons (by exact certified0386)
  apply certified_cons (by exact certified0386swap)
  apply certified_cons (by exact certified0387)
  apply certified_cons (by exact certified0387swap)
  apply certified_cons (by exact certified0388)
  apply certified_cons (by exact certified0388swap)
  apply certified_cons (by exact certified0389)
  apply certified_cons (by exact certified0390)
  apply certified_cons (by exact certified0390swap)
  apply certified_cons (by exact certified0391)
  apply certified_cons (by exact certified0391swap)
  apply certified_cons (by exact certified0392)
  apply certified_cons (by exact certified0393)
  apply certified_cons (by exact certified0394)
  apply certified_cons (by exact certified0394swap)
  apply certified_cons (by exact certified0395)
  apply certified_cons (by exact certified0395swap)
  apply certified_cons (by exact certified0396)
  apply certified_cons (by exact certified0396swap)
  apply certified_cons (by exact certified0397)
  apply certified_cons (by exact certified0397swap)
  apply certified_cons (by exact certified0398)
  apply certified_cons (by exact certified0399)
  apply certified_cons (by exact certified0399swap)
  simp
#print axioms certified_keys07
end Gebendorfer.RadenkovicGutman.DegreeOneSmallKeys
