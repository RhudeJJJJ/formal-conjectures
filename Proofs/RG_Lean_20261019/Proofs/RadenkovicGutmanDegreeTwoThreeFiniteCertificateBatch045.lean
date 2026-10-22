/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteKeysData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2250
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2251
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2252
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2253
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2254
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2255
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2256
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2257
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2258
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2259
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2260
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2261
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2262
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2263
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2264
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2265
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2266
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2267
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2268
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2269
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2270
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2271
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2272
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2273
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2274
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2275
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2276
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2277
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2278
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2279
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2280
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2281
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2282
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2283
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2284
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2285
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2286
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2287
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2288
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2289
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2290
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2291
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2292
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2293
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2294
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2295
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2296
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2297
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2298
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2299
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeTwoThreeFiniteActualCases
theorem certified_keys045 : ∀ k ∈ keys045, Certified k := by
  apply certified_cons (by exact certified2250)
  apply certified_cons (by exact certified2250swap)
  apply certified_cons (by exact certified2251)
  apply certified_cons (by exact certified2251swap)
  apply certified_cons (by exact certified2252)
  apply certified_cons (by exact certified2252swap)
  apply certified_cons (by exact certified2253)
  apply certified_cons (by exact certified2253swap)
  apply certified_cons (by exact certified2254)
  apply certified_cons (by exact certified2254swap)
  apply certified_cons (by exact certified2255)
  apply certified_cons (by exact certified2255swap)
  apply certified_cons (by exact certified2256)
  apply certified_cons (by exact certified2256swap)
  apply certified_cons (by exact certified2257)
  apply certified_cons (by exact certified2257swap)
  apply certified_cons (by exact certified2258)
  apply certified_cons (by exact certified2258swap)
  apply certified_cons (by exact certified2259)
  apply certified_cons (by exact certified2259swap)
  apply certified_cons (by exact certified2260)
  apply certified_cons (by exact certified2260swap)
  apply certified_cons (by exact certified2261)
  apply certified_cons (by exact certified2261swap)
  apply certified_cons (by exact certified2262)
  apply certified_cons (by exact certified2262swap)
  apply certified_cons (by exact certified2263)
  apply certified_cons (by exact certified2263swap)
  apply certified_cons (by exact certified2264)
  apply certified_cons (by exact certified2264swap)
  apply certified_cons (by exact certified2265)
  apply certified_cons (by exact certified2265swap)
  apply certified_cons (by exact certified2266)
  apply certified_cons (by exact certified2266swap)
  apply certified_cons (by exact certified2267)
  apply certified_cons (by exact certified2267swap)
  apply certified_cons (by exact certified2268)
  apply certified_cons (by exact certified2268swap)
  apply certified_cons (by exact certified2269)
  apply certified_cons (by exact certified2269swap)
  apply certified_cons (by exact certified2270)
  apply certified_cons (by exact certified2270swap)
  apply certified_cons (by exact certified2271)
  apply certified_cons (by exact certified2271swap)
  apply certified_cons (by exact certified2272)
  apply certified_cons (by exact certified2272swap)
  apply certified_cons (by exact certified2273)
  apply certified_cons (by exact certified2273swap)
  apply certified_cons (by exact certified2274)
  apply certified_cons (by exact certified2274swap)
  apply certified_cons (by exact certified2275)
  apply certified_cons (by exact certified2275swap)
  apply certified_cons (by exact certified2276)
  apply certified_cons (by exact certified2276swap)
  apply certified_cons (by exact certified2277)
  apply certified_cons (by exact certified2277swap)
  apply certified_cons (by exact certified2278)
  apply certified_cons (by exact certified2278swap)
  apply certified_cons (by exact certified2279)
  apply certified_cons (by exact certified2279swap)
  apply certified_cons (by exact certified2280)
  apply certified_cons (by exact certified2280swap)
  apply certified_cons (by exact certified2281)
  apply certified_cons (by exact certified2281swap)
  apply certified_cons (by exact certified2282)
  apply certified_cons (by exact certified2282swap)
  apply certified_cons (by exact certified2283)
  apply certified_cons (by exact certified2283swap)
  apply certified_cons (by exact certified2284)
  apply certified_cons (by exact certified2284swap)
  apply certified_cons (by exact certified2285)
  apply certified_cons (by exact certified2285swap)
  apply certified_cons (by exact certified2286)
  apply certified_cons (by exact certified2286swap)
  apply certified_cons (by exact certified2287)
  apply certified_cons (by exact certified2287swap)
  apply certified_cons (by exact certified2288)
  apply certified_cons (by exact certified2288swap)
  apply certified_cons (by exact certified2289)
  apply certified_cons (by exact certified2289swap)
  apply certified_cons (by exact certified2290)
  apply certified_cons (by exact certified2290swap)
  apply certified_cons (by exact certified2291)
  apply certified_cons (by exact certified2291swap)
  apply certified_cons (by exact certified2292)
  apply certified_cons (by exact certified2292swap)
  apply certified_cons (by exact certified2293)
  apply certified_cons (by exact certified2293swap)
  apply certified_cons (by exact certified2294)
  apply certified_cons (by exact certified2294swap)
  apply certified_cons (by exact certified2295)
  apply certified_cons (by exact certified2295swap)
  apply certified_cons (by exact certified2296)
  apply certified_cons (by exact certified2296swap)
  apply certified_cons (by exact certified2297)
  apply certified_cons (by exact certified2297swap)
  apply certified_cons (by exact certified2298)
  apply certified_cons (by exact certified2298swap)
  apply certified_cons (by exact certified2299)
  apply certified_cons (by exact certified2299swap)
  simp
#print axioms certified_keys045
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
