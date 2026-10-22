/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteKeysData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5200
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5201
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5202
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5203
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5204
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5205
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5206
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5207
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5208
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5209
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5210
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5211
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5212
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5213
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5214
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5215
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5216
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5217
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5218
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5219
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5220
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5221
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5222
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5223
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5224
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5225
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5226
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5227
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5228
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5229
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5230
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5231
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5232
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5233
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5234
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5235
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5236
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5237
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5238
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5239
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5240
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5241
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5242
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5243
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5244
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5245
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5246
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5247
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5248
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5249
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
