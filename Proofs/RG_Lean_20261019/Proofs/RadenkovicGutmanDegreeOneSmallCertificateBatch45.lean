/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeOneSmallKeysData
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2250
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2251
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2252
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2253
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2254
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2255
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2256
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2257
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2258
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2259
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2260
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2261
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2262
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2263
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2264
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2265
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2266
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2267
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2268
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2269
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2270
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2271
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2272
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2273
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2274
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2275
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2276
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2277
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2278
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2279
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2280
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2281
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2282
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2283
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2284
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2285
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2286
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2287
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2288
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2289
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2290
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2291
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2292
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2293
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2294
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2295
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2296
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2297
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2298
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2299
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeOneSmallActualCases
theorem certified_keys45 : ∀ k ∈ keys45, Certified k := by
  apply certified_cons (by exact certified2250)
  apply certified_cons (by exact certified2251)
  apply certified_cons (by exact certified2252)
  apply certified_cons (by exact certified2253)
  apply certified_cons (by exact certified2254)
  apply certified_cons (by exact certified2255)
  apply certified_cons (by exact certified2256)
  apply certified_cons (by exact certified2257)
  apply certified_cons (by exact certified2258)
  apply certified_cons (by exact certified2259)
  apply certified_cons (by exact certified2260)
  apply certified_cons (by exact certified2261)
  apply certified_cons (by exact certified2262)
  apply certified_cons (by exact certified2263)
  apply certified_cons (by exact certified2264)
  apply certified_cons (by exact certified2265)
  apply certified_cons (by exact certified2266)
  apply certified_cons (by exact certified2267)
  apply certified_cons (by exact certified2268)
  apply certified_cons (by exact certified2269)
  apply certified_cons (by exact certified2270)
  apply certified_cons (by exact certified2271)
  apply certified_cons (by exact certified2272)
  apply certified_cons (by exact certified2273)
  apply certified_cons (by exact certified2274)
  apply certified_cons (by exact certified2275)
  apply certified_cons (by exact certified2276)
  apply certified_cons (by exact certified2277)
  apply certified_cons (by exact certified2278)
  apply certified_cons (by exact certified2279)
  apply certified_cons (by exact certified2280)
  apply certified_cons (by exact certified2281)
  apply certified_cons (by exact certified2282)
  apply certified_cons (by exact certified2283)
  apply certified_cons (by exact certified2284)
  apply certified_cons (by exact certified2285)
  apply certified_cons (by exact certified2286)
  apply certified_cons (by exact certified2287)
  apply certified_cons (by exact certified2288)
  apply certified_cons (by exact certified2289)
  apply certified_cons (by exact certified2290)
  apply certified_cons (by exact certified2291)
  apply certified_cons (by exact certified2292)
  apply certified_cons (by exact certified2293)
  apply certified_cons (by exact certified2294)
  apply certified_cons (by exact certified2295)
  apply certified_cons (by exact certified2296)
  apply certified_cons (by exact certified2297)
  apply certified_cons (by exact certified2298)
  apply certified_cons (by exact certified2299)
  simp
#print axioms certified_keys45
end Gebendorfer.RadenkovicGutman.DegreeOneSmallKeys
