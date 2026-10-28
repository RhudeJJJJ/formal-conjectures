/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteKeysData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5250
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5251
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5252
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5253
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5254
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5255
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5256
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5257
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5258
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5259
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5260
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5261
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5262
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5263
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5264
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5265
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5266
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5267
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5268
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5269
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5270
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5271
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5272
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5273
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5274
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5275
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5276
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5277
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5278
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5279
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5280
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5281
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5282
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5283
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5284
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5285
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5286
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5287
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5288
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5289
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5290
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5291
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5292
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5293
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5294
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5295
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5296
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5297
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5298
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5299
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
