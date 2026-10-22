/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteKeysData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0200
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0201
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0202
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0203
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0204
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0205
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0206
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0207
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0208
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0209
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0210
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0211
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0212
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0213
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0214
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0215
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0216
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0217
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0218
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0219
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0220
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0221
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0222
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0223
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0224
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0225
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0226
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0227
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0228
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0229
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0230
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0231
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0232
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0233
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0234
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0235
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0236
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0237
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0238
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0239
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0240
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0241
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0242
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0243
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0244
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0245
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0246
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0247
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0248
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0249
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeTwoThreeFiniteActualCases
theorem certified_keys004 : ∀ k ∈ keys004, Certified k := by
  apply certified_cons (by exact certified0200)
  apply certified_cons (by exact certified0201)
  apply certified_cons (by exact certified0202)
  apply certified_cons (by exact certified0203)
  apply certified_cons (by exact certified0204)
  apply certified_cons (by exact certified0205)
  apply certified_cons (by exact certified0206)
  apply certified_cons (by exact certified0207)
  apply certified_cons (by exact certified0208)
  apply certified_cons (by exact certified0209)
  apply certified_cons (by exact certified0210)
  apply certified_cons (by exact certified0211)
  apply certified_cons (by exact certified0212)
  apply certified_cons (by exact certified0213)
  apply certified_cons (by exact certified0214)
  apply certified_cons (by exact certified0215)
  apply certified_cons (by exact certified0216)
  apply certified_cons (by exact certified0217)
  apply certified_cons (by exact certified0218)
  apply certified_cons (by exact certified0219)
  apply certified_cons (by exact certified0220)
  apply certified_cons (by exact certified0221)
  apply certified_cons (by exact certified0222)
  apply certified_cons (by exact certified0223)
  apply certified_cons (by exact certified0224)
  apply certified_cons (by exact certified0225)
  apply certified_cons (by exact certified0226)
  apply certified_cons (by exact certified0227)
  apply certified_cons (by exact certified0228)
  apply certified_cons (by exact certified0229)
  apply certified_cons (by exact certified0230)
  apply certified_cons (by exact certified0231)
  apply certified_cons (by exact certified0232)
  apply certified_cons (by exact certified0233)
  apply certified_cons (by exact certified0234)
  apply certified_cons (by exact certified0235)
  apply certified_cons (by exact certified0236)
  apply certified_cons (by exact certified0237)
  apply certified_cons (by exact certified0238)
  apply certified_cons (by exact certified0239)
  apply certified_cons (by exact certified0240)
  apply certified_cons (by exact certified0241)
  apply certified_cons (by exact certified0242)
  apply certified_cons (by exact certified0243)
  apply certified_cons (by exact certified0244)
  apply certified_cons (by exact certified0245)
  apply certified_cons (by exact certified0246)
  apply certified_cons (by exact certified0247)
  apply certified_cons (by exact certified0248)
  apply certified_cons (by exact certified0249)
  simp
#print axioms certified_keys004
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
