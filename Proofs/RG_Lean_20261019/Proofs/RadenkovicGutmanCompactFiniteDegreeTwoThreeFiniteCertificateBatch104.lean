/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteKeysData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5200
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5201
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5202
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5203
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5204
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5205
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5206
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5207
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5208
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5209
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5210
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5211
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5212
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5213
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5214
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5215
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5216
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5217
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5218
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5219
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5220
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5221
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5222
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5223
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5224
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5225
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5226
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5227
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5228
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5229
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5230
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5231
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5232
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5233
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5234
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5235
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5236
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5237
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5238
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5239
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5240
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5241
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5242
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5243
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5244
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5245
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5246
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5247
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5248
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5249
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeTwoThreeFiniteActualCases
theorem certified_keys104 : ∀ k ∈ keys104, Certified k := by
  apply certified_cons (by exact certified5200)
  apply certified_cons (by exact certified5200swap)
  apply certified_cons (by exact certified5201)
  apply certified_cons (by exact certified5201swap)
  apply certified_cons (by exact certified5202)
  apply certified_cons (by exact certified5202swap)
  apply certified_cons (by exact certified5203)
  apply certified_cons (by exact certified5203swap)
  apply certified_cons (by exact certified5204)
  apply certified_cons (by exact certified5204swap)
  apply certified_cons (by exact certified5205)
  apply certified_cons (by exact certified5205swap)
  apply certified_cons (by exact certified5206)
  apply certified_cons (by exact certified5206swap)
  apply certified_cons (by exact certified5207)
  apply certified_cons (by exact certified5207swap)
  apply certified_cons (by exact certified5208)
  apply certified_cons (by exact certified5208swap)
  apply certified_cons (by exact certified5209)
  apply certified_cons (by exact certified5209swap)
  apply certified_cons (by exact certified5210)
  apply certified_cons (by exact certified5210swap)
  apply certified_cons (by exact certified5211)
  apply certified_cons (by exact certified5211swap)
  apply certified_cons (by exact certified5212)
  apply certified_cons (by exact certified5212swap)
  apply certified_cons (by exact certified5213)
  apply certified_cons (by exact certified5213swap)
  apply certified_cons (by exact certified5214)
  apply certified_cons (by exact certified5214swap)
  apply certified_cons (by exact certified5215)
  apply certified_cons (by exact certified5215swap)
  apply certified_cons (by exact certified5216)
  apply certified_cons (by exact certified5216swap)
  apply certified_cons (by exact certified5217)
  apply certified_cons (by exact certified5217swap)
  apply certified_cons (by exact certified5218)
  apply certified_cons (by exact certified5218swap)
  apply certified_cons (by exact certified5219)
  apply certified_cons (by exact certified5219swap)
  apply certified_cons (by exact certified5220)
  apply certified_cons (by exact certified5220swap)
  apply certified_cons (by exact certified5221)
  apply certified_cons (by exact certified5221swap)
  apply certified_cons (by exact certified5222)
  apply certified_cons (by exact certified5222swap)
  apply certified_cons (by exact certified5223)
  apply certified_cons (by exact certified5223swap)
  apply certified_cons (by exact certified5224)
  apply certified_cons (by exact certified5224swap)
  apply certified_cons (by exact certified5225)
  apply certified_cons (by exact certified5225swap)
  apply certified_cons (by exact certified5226)
  apply certified_cons (by exact certified5226swap)
  apply certified_cons (by exact certified5227)
  apply certified_cons (by exact certified5227swap)
  apply certified_cons (by exact certified5228)
  apply certified_cons (by exact certified5228swap)
  apply certified_cons (by exact certified5229)
  apply certified_cons (by exact certified5229swap)
  apply certified_cons (by exact certified5230)
  apply certified_cons (by exact certified5230swap)
  apply certified_cons (by exact certified5231)
  apply certified_cons (by exact certified5231swap)
  apply certified_cons (by exact certified5232)
  apply certified_cons (by exact certified5232swap)
  apply certified_cons (by exact certified5233)
  apply certified_cons (by exact certified5233swap)
  apply certified_cons (by exact certified5234)
  apply certified_cons (by exact certified5234swap)
  apply certified_cons (by exact certified5235)
  apply certified_cons (by exact certified5235swap)
  apply certified_cons (by exact certified5236)
  apply certified_cons (by exact certified5236swap)
  apply certified_cons (by exact certified5237)
  apply certified_cons (by exact certified5237swap)
  apply certified_cons (by exact certified5238)
  apply certified_cons (by exact certified5238swap)
  apply certified_cons (by exact certified5239)
  apply certified_cons (by exact certified5239swap)
  apply certified_cons (by exact certified5240)
  apply certified_cons (by exact certified5240swap)
  apply certified_cons (by exact certified5241)
  apply certified_cons (by exact certified5241swap)
  apply certified_cons (by exact certified5242)
  apply certified_cons (by exact certified5242swap)
  apply certified_cons (by exact certified5243)
  apply certified_cons (by exact certified5243swap)
  apply certified_cons (by exact certified5244)
  apply certified_cons (by exact certified5244swap)
  apply certified_cons (by exact certified5245)
  apply certified_cons (by exact certified5245swap)
  apply certified_cons (by exact certified5246)
  apply certified_cons (by exact certified5246swap)
  apply certified_cons (by exact certified5247)
  apply certified_cons (by exact certified5247swap)
  apply certified_cons (by exact certified5248)
  apply certified_cons (by exact certified5248swap)
  apply certified_cons (by exact certified5249)
  apply certified_cons (by exact certified5249swap)
  simp
#print axioms certified_keys104
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
