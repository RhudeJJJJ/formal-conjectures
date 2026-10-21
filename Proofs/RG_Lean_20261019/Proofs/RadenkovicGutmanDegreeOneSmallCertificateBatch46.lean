/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeOneSmallKeysData
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2300
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2301
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2302
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2303
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2304
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2305
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2306
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2307
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2308
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2309
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2310
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2311
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2312
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2313
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2314
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2315
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2316
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2317
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2318
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2319
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2320
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2321
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2322
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2323
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2324
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2325
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2326
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2327
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2328
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2329
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2330
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2331
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2332
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2333
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2334
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2335
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2336
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2337
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2338
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2339
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2340
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2341
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2342
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2343
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2344
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2345
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2346
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2347
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2348
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2349
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeOneSmallActualCases
theorem certified_keys46 : ∀ k ∈ keys46, Certified k := by
  apply certified_cons (by exact certified2300)
  apply certified_cons (by exact certified2301)
  apply certified_cons (by exact certified2302)
  apply certified_cons (by exact certified2303)
  apply certified_cons (by exact certified2304)
  apply certified_cons (by exact certified2305)
  apply certified_cons (by exact certified2306)
  apply certified_cons (by exact certified2307)
  apply certified_cons (by exact certified2308)
  apply certified_cons (by exact certified2309)
  apply certified_cons (by exact certified2310)
  apply certified_cons (by exact certified2311)
  apply certified_cons (by exact certified2312)
  apply certified_cons (by exact certified2313)
  apply certified_cons (by exact certified2314)
  apply certified_cons (by exact certified2315)
  apply certified_cons (by exact certified2316)
  apply certified_cons (by exact certified2317)
  apply certified_cons (by exact certified2318)
  apply certified_cons (by exact certified2319)
  apply certified_cons (by exact certified2320)
  apply certified_cons (by exact certified2321)
  apply certified_cons (by exact certified2322)
  apply certified_cons (by exact certified2323)
  apply certified_cons (by exact certified2324)
  apply certified_cons (by exact certified2325)
  apply certified_cons (by exact certified2326)
  apply certified_cons (by exact certified2327)
  apply certified_cons (by exact certified2328)
  apply certified_cons (by exact certified2329)
  apply certified_cons (by exact certified2330)
  apply certified_cons (by exact certified2331)
  apply certified_cons (by exact certified2332)
  apply certified_cons (by exact certified2333)
  apply certified_cons (by exact certified2334)
  apply certified_cons (by exact certified2335)
  apply certified_cons (by exact certified2336)
  apply certified_cons (by exact certified2337)
  apply certified_cons (by exact certified2338)
  apply certified_cons (by exact certified2339)
  apply certified_cons (by exact certified2340)
  apply certified_cons (by exact certified2341)
  apply certified_cons (by exact certified2342)
  apply certified_cons (by exact certified2343)
  apply certified_cons (by exact certified2344)
  apply certified_cons (by exact certified2345)
  apply certified_cons (by exact certified2346)
  apply certified_cons (by exact certified2347)
  apply certified_cons (by exact certified2348)
  apply certified_cons (by exact certified2349)
  simp
#print axioms certified_keys46
end Gebendorfer.RadenkovicGutman.DegreeOneSmallKeys
