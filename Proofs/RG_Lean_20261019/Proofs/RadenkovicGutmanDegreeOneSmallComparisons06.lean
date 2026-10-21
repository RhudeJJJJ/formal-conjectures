/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum036
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum040
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum042
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum045
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum047
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum049
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum050
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum052
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum055
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum058
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum074
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum075
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum076
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum081
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum082
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum083
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum091
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum105
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1074
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1081
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1174
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1181
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum120
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1239
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1246
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum127
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1340
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1347
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum136
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum141
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1462
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1463
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum167
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum174
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum175
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum181
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum182
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum187
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum188
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum199
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum201
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum202
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum227
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum263
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum295
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum306
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum325
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum370
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum371
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum372
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum379
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum392
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum395
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum396
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum424
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum427
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum454
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum457
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum476
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum479
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum515
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum518
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum574
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum575
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum858
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum859
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum865
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum870
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum874
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum879
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum882
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum887
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum911
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum915
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum963
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum970
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum976
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallComparisons
set_option maxHeartbeats 0
theorem comparison0300 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum392.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum574.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum574.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum392.actual_graph_bounds.2
  linarith
#print axioms comparison0300
theorem comparison0301 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum858.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum963.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum963.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum858.actual_graph_bounds.2
  linarith
#print axioms comparison0301
theorem comparison0302 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum858.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1462.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1462.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum858.actual_graph_bounds.2
  linarith
#print axioms comparison0302
theorem comparison0303 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum036.graph) (2-2/9) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum047.graph) (2-2/9) := by
  have hs := DegreeOneSmallSpectrum047.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum036.actual_graph_bounds.2
  linarith
#print axioms comparison0303
theorem comparison0304 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum091.graph) (2-2/10) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum083.graph) (2-2/10) := by
  have hs := DegreeOneSmallSpectrum083.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum091.actual_graph_bounds.2
  linarith
#print axioms comparison0304
theorem comparison0305 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum167.graph) (2-2/11) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum227.graph) (2-2/11) := by
  have hs := DegreeOneSmallSpectrum227.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum167.actual_graph_bounds.2
  linarith
#print axioms comparison0305
theorem comparison0306 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum396.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum395.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum395.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum396.actual_graph_bounds.2
  linarith
#print axioms comparison0306
theorem comparison0307 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum859.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum976.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum976.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum859.actual_graph_bounds.2
  linarith
#print axioms comparison0307
theorem comparison0308 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum167.graph) (2-2/11) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum199.graph) (2-2/11) := by
  have hs := DegreeOneSmallSpectrum199.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum167.actual_graph_bounds.2
  linarith
#print axioms comparison0308
theorem comparison0309 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum396.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum575.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum575.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum396.actual_graph_bounds.2
  linarith
#print axioms comparison0309
theorem comparison0310 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum859.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum970.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum970.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum859.actual_graph_bounds.2
  linarith
#print axioms comparison0310
theorem comparison0311 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum859.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1463.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1463.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum859.actual_graph_bounds.2
  linarith
#print axioms comparison0311
theorem comparison0312 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum042.graph) (2-2/9) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum040.graph) (2-2/9) := by
  have hs := DegreeOneSmallSpectrum040.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum042.actual_graph_bounds.2
  linarith
#print axioms comparison0312
theorem comparison0313 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum074.graph) (2-2/10) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum105.graph) (2-2/10) := by
  have hs := DegreeOneSmallSpectrum105.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum074.actual_graph_bounds.2
  linarith
#print axioms comparison0313
theorem comparison0314 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum175.graph) (2-2/11) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum174.graph) (2-2/11) := by
  have hs := DegreeOneSmallSpectrum174.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum175.actual_graph_bounds.2
  linarith
#print axioms comparison0314
theorem comparison0315 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum370.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum427.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum427.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum370.actual_graph_bounds.2
  linarith
#print axioms comparison0315
theorem comparison0316 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum870.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum865.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum865.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum870.actual_graph_bounds.2
  linarith
#print axioms comparison0316
theorem comparison0317 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum175.graph) (2-2/11) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum263.graph) (2-2/11) := by
  have hs := DegreeOneSmallSpectrum263.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum175.actual_graph_bounds.2
  linarith
#print axioms comparison0317
theorem comparison0318 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum370.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum424.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum424.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum370.actual_graph_bounds.2
  linarith
#print axioms comparison0318
theorem comparison0319 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum870.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1081.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1081.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum870.actual_graph_bounds.2
  linarith
#print axioms comparison0319
theorem comparison0320 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum870.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1074.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1074.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum870.actual_graph_bounds.2
  linarith
#print axioms comparison0320
theorem comparison0321 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum047.graph) (2-2/9) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum045.graph) (2-2/9) := by
  have hs := DegreeOneSmallSpectrum045.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum047.actual_graph_bounds.2
  linarith
#print axioms comparison0321
theorem comparison0322 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum075.graph) (2-2/10) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum120.graph) (2-2/10) := by
  have hs := DegreeOneSmallSpectrum120.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum075.actual_graph_bounds.2
  linarith
#print axioms comparison0322
theorem comparison0323 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum182.graph) (2-2/11) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum181.graph) (2-2/11) := by
  have hs := DegreeOneSmallSpectrum181.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum182.actual_graph_bounds.2
  linarith
#print axioms comparison0323
theorem comparison0324 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum371.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum457.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum457.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum371.actual_graph_bounds.2
  linarith
#print axioms comparison0324
theorem comparison0325 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum879.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum874.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum874.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum879.actual_graph_bounds.2
  linarith
#print axioms comparison0325
theorem comparison0326 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum182.graph) (2-2/11) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum295.graph) (2-2/11) := by
  have hs := DegreeOneSmallSpectrum295.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum182.actual_graph_bounds.2
  linarith
#print axioms comparison0326
theorem comparison0327 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum371.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum454.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum454.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum371.actual_graph_bounds.2
  linarith
#print axioms comparison0327
theorem comparison0328 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum879.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1181.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1181.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum879.actual_graph_bounds.2
  linarith
#print axioms comparison0328
theorem comparison0329 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum879.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1174.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1174.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum879.actual_graph_bounds.2
  linarith
#print axioms comparison0329
theorem comparison0330 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum052.graph) (2-2/9) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum045.graph) (2-2/9) := by
  have hs := DegreeOneSmallSpectrum045.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum052.actual_graph_bounds.2
  linarith
#print axioms comparison0330
theorem comparison0331 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum076.graph) (2-2/10) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum127.graph) (2-2/10) := by
  have hs := DegreeOneSmallSpectrum127.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum076.actual_graph_bounds.2
  linarith
#print axioms comparison0331
theorem comparison0332 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum188.graph) (2-2/11) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum187.graph) (2-2/11) := by
  have hs := DegreeOneSmallSpectrum187.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum188.actual_graph_bounds.2
  linarith
#print axioms comparison0332
theorem comparison0333 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum372.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum479.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum479.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum372.actual_graph_bounds.2
  linarith
#print axioms comparison0333
theorem comparison0334 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum887.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum882.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum882.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum887.actual_graph_bounds.2
  linarith
#print axioms comparison0334
theorem comparison0335 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum188.graph) (2-2/11) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum306.graph) (2-2/11) := by
  have hs := DegreeOneSmallSpectrum306.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum188.actual_graph_bounds.2
  linarith
#print axioms comparison0335
theorem comparison0336 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum372.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum476.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum476.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum372.actual_graph_bounds.2
  linarith
#print axioms comparison0336
theorem comparison0337 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum887.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1246.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1246.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum887.actual_graph_bounds.2
  linarith
#print axioms comparison0337
theorem comparison0338 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum887.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1239.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1239.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum887.actual_graph_bounds.2
  linarith
#print axioms comparison0338
theorem comparison0339 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum055.graph) (2-2/9) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum049.graph) (2-2/9) := by
  have hs := DegreeOneSmallSpectrum049.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum055.actual_graph_bounds.2
  linarith
#print axioms comparison0339
theorem comparison0340 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum081.graph) (2-2/10) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum136.graph) (2-2/10) := by
  have hs := DegreeOneSmallSpectrum136.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum081.actual_graph_bounds.2
  linarith
#print axioms comparison0340
theorem comparison0341 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum202.graph) (2-2/11) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum201.graph) (2-2/11) := by
  have hs := DegreeOneSmallSpectrum201.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum202.actual_graph_bounds.2
  linarith
#print axioms comparison0341
theorem comparison0342 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum379.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum518.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum518.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum379.actual_graph_bounds.2
  linarith
#print axioms comparison0342
theorem comparison0343 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum915.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum911.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum911.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum915.actual_graph_bounds.2
  linarith
#print axioms comparison0343
theorem comparison0344 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum202.graph) (2-2/11) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum325.graph) (2-2/11) := by
  have hs := DegreeOneSmallSpectrum325.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum202.actual_graph_bounds.2
  linarith
#print axioms comparison0344
theorem comparison0345 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum379.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum515.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum515.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum379.actual_graph_bounds.2
  linarith
#print axioms comparison0345
theorem comparison0346 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum915.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1347.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1347.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum915.actual_graph_bounds.2
  linarith
#print axioms comparison0346
theorem comparison0347 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum915.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1340.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1340.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum915.actual_graph_bounds.2
  linarith
#print axioms comparison0347
theorem comparison0348 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum058.graph) (2-2/9) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum050.graph) (2-2/9) := by
  have hs := DegreeOneSmallSpectrum050.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum058.actual_graph_bounds.2
  linarith
#print axioms comparison0348
theorem comparison0349 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum082.graph) (2-2/10) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum141.graph) (2-2/10) := by
  have hs := DegreeOneSmallSpectrum141.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum082.actual_graph_bounds.2
  linarith
#print axioms comparison0349
end Gebendorfer.RadenkovicGutman.DegreeOneSmallComparisons
