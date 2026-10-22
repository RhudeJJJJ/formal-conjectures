/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteKeysData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0250
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0251
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0252
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0253
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0254
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0255
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0256
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0257
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0258
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0259
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0260
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0261
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0262
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0263
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0264
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0265
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0266
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0267
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0268
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0269
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0270
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0271
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0272
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0273
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0274
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0275
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0276
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0277
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0278
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0279
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0280
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0281
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0282
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0283
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0284
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0285
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0286
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0287
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0288
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0289
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0290
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0291
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0292
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0293
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0294
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0295
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0296
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0297
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0298
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0299
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeTwoThreeFiniteActualCases
theorem certified_keys005 : ∀ k ∈ keys005, Certified k := by
  apply certified_cons (by exact certified0250)
  apply certified_cons (by exact certified0251)
  apply certified_cons (by exact certified0252)
  apply certified_cons (by exact certified0253)
  apply certified_cons (by exact certified0254)
  apply certified_cons (by exact certified0255)
  apply certified_cons (by exact certified0256)
  apply certified_cons (by exact certified0257)
  apply certified_cons (by exact certified0258)
  apply certified_cons (by exact certified0259)
  apply certified_cons (by exact certified0260)
  apply certified_cons (by exact certified0261)
  apply certified_cons (by exact certified0262)
  apply certified_cons (by exact certified0263)
  apply certified_cons (by exact certified0264)
  apply certified_cons (by exact certified0265)
  apply certified_cons (by exact certified0266)
  apply certified_cons (by exact certified0267)
  apply certified_cons (by exact certified0268)
  apply certified_cons (by exact certified0269)
  apply certified_cons (by exact certified0270)
  apply certified_cons (by exact certified0271)
  apply certified_cons (by exact certified0272)
  apply certified_cons (by exact certified0273)
  apply certified_cons (by exact certified0274)
  apply certified_cons (by exact certified0275)
  apply certified_cons (by exact certified0276)
  apply certified_cons (by exact certified0277)
  apply certified_cons (by exact certified0278)
  apply certified_cons (by exact certified0279)
  apply certified_cons (by exact certified0280)
  apply certified_cons (by exact certified0281)
  apply certified_cons (by exact certified0282)
  apply certified_cons (by exact certified0283)
  apply certified_cons (by exact certified0284)
  apply certified_cons (by exact certified0285)
  apply certified_cons (by exact certified0286)
  apply certified_cons (by exact certified0287)
  apply certified_cons (by exact certified0288)
  apply certified_cons (by exact certified0289)
  apply certified_cons (by exact certified0290)
  apply certified_cons (by exact certified0291)
  apply certified_cons (by exact certified0292)
  apply certified_cons (by exact certified0293)
  apply certified_cons (by exact certified0294)
  apply certified_cons (by exact certified0295)
  apply certified_cons (by exact certified0296)
  apply certified_cons (by exact certified0297)
  apply certified_cons (by exact certified0298)
  apply certified_cons (by exact certified0299)
  simp
#print axioms certified_keys005
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
