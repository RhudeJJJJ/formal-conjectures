/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeOneSmallKeysData
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2200
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2201
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2202
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2203
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2204
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2205
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2206
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2207
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2208
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2209
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2210
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2211
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2212
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2213
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2214
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2215
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2216
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2217
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2218
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2219
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2220
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2221
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2222
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2223
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2224
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2225
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2226
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2227
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2228
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2229
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2230
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2231
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2232
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2233
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2234
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2235
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2236
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2237
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2238
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2239
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2240
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2241
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2242
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2243
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2244
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2245
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2246
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2247
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2248
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2249
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeOneSmallActualCases
theorem certified_keys44 : ∀ k ∈ keys44, Certified k := by
  apply certified_cons (by exact certified2200)
  apply certified_cons (by exact certified2201)
  apply certified_cons (by exact certified2202)
  apply certified_cons (by exact certified2203)
  apply certified_cons (by exact certified2204)
  apply certified_cons (by exact certified2205)
  apply certified_cons (by exact certified2206)
  apply certified_cons (by exact certified2207)
  apply certified_cons (by exact certified2208)
  apply certified_cons (by exact certified2209)
  apply certified_cons (by exact certified2210)
  apply certified_cons (by exact certified2211)
  apply certified_cons (by exact certified2212)
  apply certified_cons (by exact certified2213)
  apply certified_cons (by exact certified2214)
  apply certified_cons (by exact certified2215)
  apply certified_cons (by exact certified2216)
  apply certified_cons (by exact certified2217)
  apply certified_cons (by exact certified2218)
  apply certified_cons (by exact certified2219)
  apply certified_cons (by exact certified2220)
  apply certified_cons (by exact certified2221)
  apply certified_cons (by exact certified2222)
  apply certified_cons (by exact certified2223)
  apply certified_cons (by exact certified2224)
  apply certified_cons (by exact certified2225)
  apply certified_cons (by exact certified2226)
  apply certified_cons (by exact certified2227)
  apply certified_cons (by exact certified2228)
  apply certified_cons (by exact certified2229)
  apply certified_cons (by exact certified2230)
  apply certified_cons (by exact certified2231)
  apply certified_cons (by exact certified2232)
  apply certified_cons (by exact certified2233)
  apply certified_cons (by exact certified2234)
  apply certified_cons (by exact certified2235)
  apply certified_cons (by exact certified2236)
  apply certified_cons (by exact certified2237)
  apply certified_cons (by exact certified2238)
  apply certified_cons (by exact certified2239)
  apply certified_cons (by exact certified2240)
  apply certified_cons (by exact certified2241)
  apply certified_cons (by exact certified2242)
  apply certified_cons (by exact certified2243)
  apply certified_cons (by exact certified2244)
  apply certified_cons (by exact certified2245)
  apply certified_cons (by exact certified2246)
  apply certified_cons (by exact certified2247)
  apply certified_cons (by exact certified2248)
  apply certified_cons (by exact certified2249)
  simp
#print axioms certified_keys44
end Gebendorfer.RadenkovicGutman.DegreeOneSmallKeys
