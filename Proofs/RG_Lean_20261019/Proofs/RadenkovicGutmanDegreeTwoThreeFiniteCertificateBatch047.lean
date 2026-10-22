/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteKeysData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2350
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2351
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2352
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2353
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2354
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2355
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2356
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2357
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2358
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2359
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2360
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2361
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2362
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2363
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2364
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2365
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2366
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2367
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2368
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2369
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2370
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2371
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2372
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2373
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2374
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2375
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2376
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2377
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2378
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2379
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2380
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2381
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2382
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2383
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2384
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2385
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2386
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2387
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2388
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2389
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2390
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2391
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2392
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2393
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2394
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2395
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2396
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2397
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2398
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2399
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeTwoThreeFiniteActualCases
theorem certified_keys047 : ∀ k ∈ keys047, Certified k := by
  apply certified_cons (by exact certified2350)
  apply certified_cons (by exact certified2350swap)
  apply certified_cons (by exact certified2351)
  apply certified_cons (by exact certified2351swap)
  apply certified_cons (by exact certified2352)
  apply certified_cons (by exact certified2352swap)
  apply certified_cons (by exact certified2353)
  apply certified_cons (by exact certified2353swap)
  apply certified_cons (by exact certified2354)
  apply certified_cons (by exact certified2354swap)
  apply certified_cons (by exact certified2355)
  apply certified_cons (by exact certified2355swap)
  apply certified_cons (by exact certified2356)
  apply certified_cons (by exact certified2356swap)
  apply certified_cons (by exact certified2357)
  apply certified_cons (by exact certified2357swap)
  apply certified_cons (by exact certified2358)
  apply certified_cons (by exact certified2358swap)
  apply certified_cons (by exact certified2359)
  apply certified_cons (by exact certified2359swap)
  apply certified_cons (by exact certified2360)
  apply certified_cons (by exact certified2360swap)
  apply certified_cons (by exact certified2361)
  apply certified_cons (by exact certified2361swap)
  apply certified_cons (by exact certified2362)
  apply certified_cons (by exact certified2362swap)
  apply certified_cons (by exact certified2363)
  apply certified_cons (by exact certified2363swap)
  apply certified_cons (by exact certified2364)
  apply certified_cons (by exact certified2364swap)
  apply certified_cons (by exact certified2365)
  apply certified_cons (by exact certified2365swap)
  apply certified_cons (by exact certified2366)
  apply certified_cons (by exact certified2366swap)
  apply certified_cons (by exact certified2367)
  apply certified_cons (by exact certified2367swap)
  apply certified_cons (by exact certified2368)
  apply certified_cons (by exact certified2368swap)
  apply certified_cons (by exact certified2369)
  apply certified_cons (by exact certified2369swap)
  apply certified_cons (by exact certified2370)
  apply certified_cons (by exact certified2370swap)
  apply certified_cons (by exact certified2371)
  apply certified_cons (by exact certified2371swap)
  apply certified_cons (by exact certified2372)
  apply certified_cons (by exact certified2372swap)
  apply certified_cons (by exact certified2373)
  apply certified_cons (by exact certified2373swap)
  apply certified_cons (by exact certified2374)
  apply certified_cons (by exact certified2374swap)
  apply certified_cons (by exact certified2375)
  apply certified_cons (by exact certified2375swap)
  apply certified_cons (by exact certified2376)
  apply certified_cons (by exact certified2376swap)
  apply certified_cons (by exact certified2377)
  apply certified_cons (by exact certified2377swap)
  apply certified_cons (by exact certified2378)
  apply certified_cons (by exact certified2378swap)
  apply certified_cons (by exact certified2379)
  apply certified_cons (by exact certified2379swap)
  apply certified_cons (by exact certified2380)
  apply certified_cons (by exact certified2380swap)
  apply certified_cons (by exact certified2381)
  apply certified_cons (by exact certified2381swap)
  apply certified_cons (by exact certified2382)
  apply certified_cons (by exact certified2382swap)
  apply certified_cons (by exact certified2383)
  apply certified_cons (by exact certified2383swap)
  apply certified_cons (by exact certified2384)
  apply certified_cons (by exact certified2384swap)
  apply certified_cons (by exact certified2385)
  apply certified_cons (by exact certified2385swap)
  apply certified_cons (by exact certified2386)
  apply certified_cons (by exact certified2386swap)
  apply certified_cons (by exact certified2387)
  apply certified_cons (by exact certified2387swap)
  apply certified_cons (by exact certified2388)
  apply certified_cons (by exact certified2388swap)
  apply certified_cons (by exact certified2389)
  apply certified_cons (by exact certified2389swap)
  apply certified_cons (by exact certified2390)
  apply certified_cons (by exact certified2390swap)
  apply certified_cons (by exact certified2391)
  apply certified_cons (by exact certified2391swap)
  apply certified_cons (by exact certified2392)
  apply certified_cons (by exact certified2392swap)
  apply certified_cons (by exact certified2393)
  apply certified_cons (by exact certified2393swap)
  apply certified_cons (by exact certified2394)
  apply certified_cons (by exact certified2394swap)
  apply certified_cons (by exact certified2395)
  apply certified_cons (by exact certified2395swap)
  apply certified_cons (by exact certified2396)
  apply certified_cons (by exact certified2396swap)
  apply certified_cons (by exact certified2397)
  apply certified_cons (by exact certified2397swap)
  apply certified_cons (by exact certified2398)
  apply certified_cons (by exact certified2398swap)
  apply certified_cons (by exact certified2399)
  apply certified_cons (by exact certified2399swap)
  simp
#print axioms certified_keys047
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
