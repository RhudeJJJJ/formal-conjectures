/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeOneSmallKeysData
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0250
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0251
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0252
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0253
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0254
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0255
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0256
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0257
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0258
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0259
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0260
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0261
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0262
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0263
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0264
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0265
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0266
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0267
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0268
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0269
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0270
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0271
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0272
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0273
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0274
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0275
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0276
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0277
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0278
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0279
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0280
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0281
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0282
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0283
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0284
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0285
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0286
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0287
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0288
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0289
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0290
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0291
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0292
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0293
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0294
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0295
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0296
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0297
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0298
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0299
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeOneSmallActualCases
theorem certified_keys05 : ∀ k ∈ keys05, Certified k := by
  apply certified_cons (by exact certified0250)
  apply certified_cons (by exact certified0250swap)
  apply certified_cons (by exact certified0251)
  apply certified_cons (by exact certified0251swap)
  apply certified_cons (by exact certified0252)
  apply certified_cons (by exact certified0252swap)
  apply certified_cons (by exact certified0253)
  apply certified_cons (by exact certified0254)
  apply certified_cons (by exact certified0254swap)
  apply certified_cons (by exact certified0255)
  apply certified_cons (by exact certified0256)
  apply certified_cons (by exact certified0256swap)
  apply certified_cons (by exact certified0257)
  apply certified_cons (by exact certified0257swap)
  apply certified_cons (by exact certified0258)
  apply certified_cons (by exact certified0258swap)
  apply certified_cons (by exact certified0259)
  apply certified_cons (by exact certified0259swap)
  apply certified_cons (by exact certified0260)
  apply certified_cons (by exact certified0260swap)
  apply certified_cons (by exact certified0261)
  apply certified_cons (by exact certified0262)
  apply certified_cons (by exact certified0262swap)
  apply certified_cons (by exact certified0263)
  apply certified_cons (by exact certified0263swap)
  apply certified_cons (by exact certified0264)
  apply certified_cons (by exact certified0264swap)
  apply certified_cons (by exact certified0265)
  apply certified_cons (by exact certified0266)
  apply certified_cons (by exact certified0266swap)
  apply certified_cons (by exact certified0267)
  apply certified_cons (by exact certified0268)
  apply certified_cons (by exact certified0268swap)
  apply certified_cons (by exact certified0269)
  apply certified_cons (by exact certified0269swap)
  apply certified_cons (by exact certified0270)
  apply certified_cons (by exact certified0270swap)
  apply certified_cons (by exact certified0271)
  apply certified_cons (by exact certified0271swap)
  apply certified_cons (by exact certified0272)
  apply certified_cons (by exact certified0273)
  apply certified_cons (by exact certified0273swap)
  apply certified_cons (by exact certified0274)
  apply certified_cons (by exact certified0274swap)
  apply certified_cons (by exact certified0275)
  apply certified_cons (by exact certified0276)
  apply certified_cons (by exact certified0277)
  apply certified_cons (by exact certified0277swap)
  apply certified_cons (by exact certified0278)
  apply certified_cons (by exact certified0278swap)
  apply certified_cons (by exact certified0279)
  apply certified_cons (by exact certified0279swap)
  apply certified_cons (by exact certified0280)
  apply certified_cons (by exact certified0280swap)
  apply certified_cons (by exact certified0281)
  apply certified_cons (by exact certified0282)
  apply certified_cons (by exact certified0282swap)
  apply certified_cons (by exact certified0283)
  apply certified_cons (by exact certified0283swap)
  apply certified_cons (by exact certified0284)
  apply certified_cons (by exact certified0285)
  apply certified_cons (by exact certified0286)
  apply certified_cons (by exact certified0286swap)
  apply certified_cons (by exact certified0287)
  apply certified_cons (by exact certified0287swap)
  apply certified_cons (by exact certified0288)
  apply certified_cons (by exact certified0288swap)
  apply certified_cons (by exact certified0289)
  apply certified_cons (by exact certified0289swap)
  apply certified_cons (by exact certified0290)
  apply certified_cons (by exact certified0291)
  apply certified_cons (by exact certified0291swap)
  apply certified_cons (by exact certified0292)
  apply certified_cons (by exact certified0292swap)
  apply certified_cons (by exact certified0293)
  apply certified_cons (by exact certified0294)
  apply certified_cons (by exact certified0295)
  apply certified_cons (by exact certified0295swap)
  apply certified_cons (by exact certified0296)
  apply certified_cons (by exact certified0296swap)
  apply certified_cons (by exact certified0297)
  apply certified_cons (by exact certified0297swap)
  apply certified_cons (by exact certified0298)
  apply certified_cons (by exact certified0298swap)
  apply certified_cons (by exact certified0299)
  simp
#print axioms certified_keys05
end Gebendorfer.RadenkovicGutman.DegreeOneSmallKeys
