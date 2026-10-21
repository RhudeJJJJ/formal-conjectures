/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeOneSmallKeysData
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0200
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0201
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0202
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0203
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0204
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0205
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0206
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0207
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0208
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0209
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0210
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0211
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0212
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0213
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0214
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0215
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0216
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0217
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0218
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0219
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0220
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0221
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0222
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0223
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0224
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0225
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0226
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0227
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0228
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0229
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0230
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0231
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0232
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0233
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0234
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0235
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0236
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0237
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0238
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0239
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0240
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0241
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0242
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0243
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0244
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0245
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0246
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0247
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0248
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0249
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeOneSmallActualCases
theorem certified_keys04 : ∀ k ∈ keys04, Certified k := by
  apply certified_cons (by exact certified0200)
  apply certified_cons (by exact certified0200swap)
  apply certified_cons (by exact certified0201)
  apply certified_cons (by exact certified0202)
  apply certified_cons (by exact certified0202swap)
  apply certified_cons (by exact certified0203)
  apply certified_cons (by exact certified0203swap)
  apply certified_cons (by exact certified0204)
  apply certified_cons (by exact certified0204swap)
  apply certified_cons (by exact certified0205)
  apply certified_cons (by exact certified0206)
  apply certified_cons (by exact certified0206swap)
  apply certified_cons (by exact certified0207)
  apply certified_cons (by exact certified0208)
  apply certified_cons (by exact certified0208swap)
  apply certified_cons (by exact certified0209)
  apply certified_cons (by exact certified0209swap)
  apply certified_cons (by exact certified0210)
  apply certified_cons (by exact certified0210swap)
  apply certified_cons (by exact certified0211)
  apply certified_cons (by exact certified0211swap)
  apply certified_cons (by exact certified0212)
  apply certified_cons (by exact certified0212swap)
  apply certified_cons (by exact certified0213)
  apply certified_cons (by exact certified0214)
  apply certified_cons (by exact certified0214swap)
  apply certified_cons (by exact certified0215)
  apply certified_cons (by exact certified0215swap)
  apply certified_cons (by exact certified0216)
  apply certified_cons (by exact certified0216swap)
  apply certified_cons (by exact certified0217)
  apply certified_cons (by exact certified0218)
  apply certified_cons (by exact certified0218swap)
  apply certified_cons (by exact certified0219)
  apply certified_cons (by exact certified0220)
  apply certified_cons (by exact certified0220swap)
  apply certified_cons (by exact certified0221)
  apply certified_cons (by exact certified0221swap)
  apply certified_cons (by exact certified0222)
  apply certified_cons (by exact certified0222swap)
  apply certified_cons (by exact certified0223)
  apply certified_cons (by exact certified0223swap)
  apply certified_cons (by exact certified0224)
  apply certified_cons (by exact certified0224swap)
  apply certified_cons (by exact certified0225)
  apply certified_cons (by exact certified0226)
  apply certified_cons (by exact certified0226swap)
  apply certified_cons (by exact certified0227)
  apply certified_cons (by exact certified0227swap)
  apply certified_cons (by exact certified0228)
  apply certified_cons (by exact certified0228swap)
  apply certified_cons (by exact certified0229)
  apply certified_cons (by exact certified0230)
  apply certified_cons (by exact certified0230swap)
  apply certified_cons (by exact certified0231)
  apply certified_cons (by exact certified0232)
  apply certified_cons (by exact certified0232swap)
  apply certified_cons (by exact certified0233)
  apply certified_cons (by exact certified0233swap)
  apply certified_cons (by exact certified0234)
  apply certified_cons (by exact certified0234swap)
  apply certified_cons (by exact certified0235)
  apply certified_cons (by exact certified0235swap)
  apply certified_cons (by exact certified0236)
  apply certified_cons (by exact certified0236swap)
  apply certified_cons (by exact certified0237)
  apply certified_cons (by exact certified0238)
  apply certified_cons (by exact certified0238swap)
  apply certified_cons (by exact certified0239)
  apply certified_cons (by exact certified0239swap)
  apply certified_cons (by exact certified0240)
  apply certified_cons (by exact certified0240swap)
  apply certified_cons (by exact certified0241)
  apply certified_cons (by exact certified0242)
  apply certified_cons (by exact certified0242swap)
  apply certified_cons (by exact certified0243)
  apply certified_cons (by exact certified0244)
  apply certified_cons (by exact certified0244swap)
  apply certified_cons (by exact certified0245)
  apply certified_cons (by exact certified0245swap)
  apply certified_cons (by exact certified0246)
  apply certified_cons (by exact certified0246swap)
  apply certified_cons (by exact certified0247)
  apply certified_cons (by exact certified0247swap)
  apply certified_cons (by exact certified0248)
  apply certified_cons (by exact certified0248swap)
  apply certified_cons (by exact certified0249)
  simp
#print axioms certified_keys04
end Gebendorfer.RadenkovicGutman.DegreeOneSmallKeys
