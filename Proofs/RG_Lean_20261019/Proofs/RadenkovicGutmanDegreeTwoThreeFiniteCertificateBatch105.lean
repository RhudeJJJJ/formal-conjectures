/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteKeysData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5250
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5251
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5252
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5253
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5254
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5255
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5256
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5257
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5258
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5259
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5260
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5261
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5262
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5263
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5264
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5265
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5266
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5267
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5268
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5269
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5270
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5271
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5272
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5273
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5274
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5275
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5276
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5277
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5278
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5279
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5280
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5281
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5282
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5283
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5284
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5285
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5286
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5287
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5288
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5289
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5290
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5291
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5292
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5293
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5294
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5295
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5296
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5297
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5298
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5299
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeTwoThreeFiniteActualCases
theorem certified_keys105 : ∀ k ∈ keys105, Certified k := by
  apply certified_cons (by exact certified5250)
  apply certified_cons (by exact certified5250swap)
  apply certified_cons (by exact certified5251)
  apply certified_cons (by exact certified5251swap)
  apply certified_cons (by exact certified5252)
  apply certified_cons (by exact certified5252swap)
  apply certified_cons (by exact certified5253)
  apply certified_cons (by exact certified5253swap)
  apply certified_cons (by exact certified5254)
  apply certified_cons (by exact certified5254swap)
  apply certified_cons (by exact certified5255)
  apply certified_cons (by exact certified5255swap)
  apply certified_cons (by exact certified5256)
  apply certified_cons (by exact certified5256swap)
  apply certified_cons (by exact certified5257)
  apply certified_cons (by exact certified5257swap)
  apply certified_cons (by exact certified5258)
  apply certified_cons (by exact certified5258swap)
  apply certified_cons (by exact certified5259)
  apply certified_cons (by exact certified5259swap)
  apply certified_cons (by exact certified5260)
  apply certified_cons (by exact certified5260swap)
  apply certified_cons (by exact certified5261)
  apply certified_cons (by exact certified5261swap)
  apply certified_cons (by exact certified5262)
  apply certified_cons (by exact certified5262swap)
  apply certified_cons (by exact certified5263)
  apply certified_cons (by exact certified5263swap)
  apply certified_cons (by exact certified5264)
  apply certified_cons (by exact certified5264swap)
  apply certified_cons (by exact certified5265)
  apply certified_cons (by exact certified5265swap)
  apply certified_cons (by exact certified5266)
  apply certified_cons (by exact certified5266swap)
  apply certified_cons (by exact certified5267)
  apply certified_cons (by exact certified5267swap)
  apply certified_cons (by exact certified5268)
  apply certified_cons (by exact certified5268swap)
  apply certified_cons (by exact certified5269)
  apply certified_cons (by exact certified5269swap)
  apply certified_cons (by exact certified5270)
  apply certified_cons (by exact certified5270swap)
  apply certified_cons (by exact certified5271)
  apply certified_cons (by exact certified5271swap)
  apply certified_cons (by exact certified5272)
  apply certified_cons (by exact certified5272swap)
  apply certified_cons (by exact certified5273)
  apply certified_cons (by exact certified5273swap)
  apply certified_cons (by exact certified5274)
  apply certified_cons (by exact certified5274swap)
  apply certified_cons (by exact certified5275)
  apply certified_cons (by exact certified5275swap)
  apply certified_cons (by exact certified5276)
  apply certified_cons (by exact certified5276swap)
  apply certified_cons (by exact certified5277)
  apply certified_cons (by exact certified5277swap)
  apply certified_cons (by exact certified5278)
  apply certified_cons (by exact certified5278swap)
  apply certified_cons (by exact certified5279)
  apply certified_cons (by exact certified5279swap)
  apply certified_cons (by exact certified5280)
  apply certified_cons (by exact certified5280swap)
  apply certified_cons (by exact certified5281)
  apply certified_cons (by exact certified5281swap)
  apply certified_cons (by exact certified5282)
  apply certified_cons (by exact certified5282swap)
  apply certified_cons (by exact certified5283)
  apply certified_cons (by exact certified5283swap)
  apply certified_cons (by exact certified5284)
  apply certified_cons (by exact certified5284swap)
  apply certified_cons (by exact certified5285)
  apply certified_cons (by exact certified5285swap)
  apply certified_cons (by exact certified5286)
  apply certified_cons (by exact certified5286swap)
  apply certified_cons (by exact certified5287)
  apply certified_cons (by exact certified5287swap)
  apply certified_cons (by exact certified5288)
  apply certified_cons (by exact certified5288swap)
  apply certified_cons (by exact certified5289)
  apply certified_cons (by exact certified5289swap)
  apply certified_cons (by exact certified5290)
  apply certified_cons (by exact certified5290swap)
  apply certified_cons (by exact certified5291)
  apply certified_cons (by exact certified5291swap)
  apply certified_cons (by exact certified5292)
  apply certified_cons (by exact certified5292swap)
  apply certified_cons (by exact certified5293)
  apply certified_cons (by exact certified5293swap)
  apply certified_cons (by exact certified5294)
  apply certified_cons (by exact certified5294swap)
  apply certified_cons (by exact certified5295)
  apply certified_cons (by exact certified5295swap)
  apply certified_cons (by exact certified5296)
  apply certified_cons (by exact certified5296swap)
  apply certified_cons (by exact certified5297)
  apply certified_cons (by exact certified5297swap)
  apply certified_cons (by exact certified5298)
  apply certified_cons (by exact certified5298swap)
  apply certified_cons (by exact certified5299)
  apply certified_cons (by exact certified5299swap)
  simp
#print axioms certified_keys105
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
