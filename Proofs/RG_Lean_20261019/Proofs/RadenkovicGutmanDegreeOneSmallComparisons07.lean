/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum039
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum043
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum044
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum046
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum060
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum061
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum062
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum065
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum067
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum083
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum087
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum088
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum095
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum100
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum101
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1027
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1385
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1392
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1427
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum143
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1434
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum144
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum145
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1460
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1461
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1490
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1500
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1597
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum170
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum206
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum207
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum211
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum212
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum221
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum222
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum224
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum225
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum242
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum244
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum256
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum258
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum327
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum328
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum329
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum330
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum380
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum381
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum387
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum388
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum400
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum407
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum411
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum531
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum534
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum547
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum550
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum572
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum573
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum575
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum581
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum624
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum656
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum862
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum863
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum918
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum922
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum925
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum929
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum948
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum951
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum953
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum956
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum993
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum998
import Proofs.RadenkovicGutmanSmallGeFourSpectrum006
import Proofs.RadenkovicGutmanSmallGeFourSpectrum016
import Proofs.RadenkovicGutmanSmallGeFourSpectrum037
import Proofs.RadenkovicGutmanSmallGeFourSpectrum094
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallComparisons
set_option maxHeartbeats 0
theorem comparison0350 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum207.graph) (2-2/11) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum206.graph) (2-2/11) := by
  have hs := DegreeOneSmallSpectrum206.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum207.actual_graph_bounds.2
  linarith
#print axioms comparison0350
theorem comparison0351 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum380.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum534.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum534.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum380.actual_graph_bounds.2
  linarith
#print axioms comparison0351
theorem comparison0352 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum922.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum918.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum918.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum922.actual_graph_bounds.2
  linarith
#print axioms comparison0352
theorem comparison0353 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum207.graph) (2-2/11) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum327.graph) (2-2/11) := by
  have hs := DegreeOneSmallSpectrum327.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum207.actual_graph_bounds.2
  linarith
#print axioms comparison0353
theorem comparison0354 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum380.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum531.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum531.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum380.actual_graph_bounds.2
  linarith
#print axioms comparison0354
theorem comparison0355 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum922.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1392.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1392.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum922.actual_graph_bounds.2
  linarith
#print axioms comparison0355
theorem comparison0356 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum922.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1385.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1385.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum922.actual_graph_bounds.2
  linarith
#print axioms comparison0356
theorem comparison0357 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum060.graph) (2-2/9) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum046.graph) (2-2/9) := by
  have hs := DegreeOneSmallSpectrum046.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum060.actual_graph_bounds.2
  linarith
#print axioms comparison0357
theorem comparison0358 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum083.graph) (2-2/10) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum143.graph) (2-2/10) := by
  have hs := DegreeOneSmallSpectrum143.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum083.actual_graph_bounds.2
  linarith
#print axioms comparison0358
theorem comparison0359 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum212.graph) (2-2/11) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum211.graph) (2-2/11) := by
  have hs := DegreeOneSmallSpectrum211.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum212.actual_graph_bounds.2
  linarith
#print axioms comparison0359
theorem comparison0360 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum381.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum550.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum550.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum381.actual_graph_bounds.2
  linarith
#print axioms comparison0360
theorem comparison0361 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum929.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum925.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum925.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum929.actual_graph_bounds.2
  linarith
#print axioms comparison0361
theorem comparison0362 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum212.graph) (2-2/11) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum328.graph) (2-2/11) := by
  have hs := DegreeOneSmallSpectrum328.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum212.actual_graph_bounds.2
  linarith
#print axioms comparison0362
theorem comparison0363 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum381.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum547.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum547.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum381.actual_graph_bounds.2
  linarith
#print axioms comparison0363
theorem comparison0364 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum929.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1434.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1434.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum929.actual_graph_bounds.2
  linarith
#print axioms comparison0364
theorem comparison0365 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum929.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1427.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1427.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum929.actual_graph_bounds.2
  linarith
#print axioms comparison0365
theorem comparison0366 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum061.graph) (2-2/9) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum043.graph) (2-2/9) := by
  have hs := DegreeOneSmallSpectrum043.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum061.actual_graph_bounds.2
  linarith
#print axioms comparison0366
theorem comparison0367 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum087.graph) (2-2/10) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum144.graph) (2-2/10) := by
  have hs := DegreeOneSmallSpectrum144.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum087.actual_graph_bounds.2
  linarith
#print axioms comparison0367
theorem comparison0368 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum222.graph) (2-2/11) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum221.graph) (2-2/11) := by
  have hs := DegreeOneSmallSpectrum221.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum222.actual_graph_bounds.2
  linarith
#print axioms comparison0368
theorem comparison0369 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum387.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum575.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum575.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum387.actual_graph_bounds.2
  linarith
#print axioms comparison0369
theorem comparison0370 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum951.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum948.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum948.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum951.actual_graph_bounds.2
  linarith
#print axioms comparison0370
theorem comparison0371 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum222.graph) (2-2/11) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum329.graph) (2-2/11) := by
  have hs := DegreeOneSmallSpectrum329.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum222.actual_graph_bounds.2
  linarith
#print axioms comparison0371
theorem comparison0372 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum387.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum572.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum572.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum387.actual_graph_bounds.2
  linarith
#print axioms comparison0372
theorem comparison0373 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum951.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1490.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1490.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum951.actual_graph_bounds.2
  linarith
#print axioms comparison0373
theorem comparison0374 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum951.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1460.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1460.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum951.actual_graph_bounds.2
  linarith
#print axioms comparison0374
theorem comparison0375 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum062.graph) (2-2/9) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum044.graph) (2-2/9) := by
  have hs := DegreeOneSmallSpectrum044.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum062.actual_graph_bounds.2
  linarith
#print axioms comparison0375
theorem comparison0376 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum088.graph) (2-2/10) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum145.graph) (2-2/10) := by
  have hs := DegreeOneSmallSpectrum145.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum088.actual_graph_bounds.2
  linarith
#print axioms comparison0376
theorem comparison0377 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum225.graph) (2-2/11) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum224.graph) (2-2/11) := by
  have hs := DegreeOneSmallSpectrum224.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum225.actual_graph_bounds.2
  linarith
#print axioms comparison0377
theorem comparison0378 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum388.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum581.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum581.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum388.actual_graph_bounds.2
  linarith
#print axioms comparison0378
theorem comparison0379 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum956.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum953.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum953.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum956.actual_graph_bounds.2
  linarith
#print axioms comparison0379
theorem comparison0380 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum225.graph) (2-2/11) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum330.graph) (2-2/11) := by
  have hs := DegreeOneSmallSpectrum330.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum225.actual_graph_bounds.2
  linarith
#print axioms comparison0380
theorem comparison0381 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum388.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum573.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum573.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum388.actual_graph_bounds.2
  linarith
#print axioms comparison0381
theorem comparison0382 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum956.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1500.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1500.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum956.actual_graph_bounds.2
  linarith
#print axioms comparison0382
theorem comparison0383 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum956.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1461.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1461.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum956.actual_graph_bounds.2
  linarith
#print axioms comparison0383
theorem comparison0384 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum006.graph) (2-2/9) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum065.graph) (2-2/9) := by
  have hs := DegreeOneSmallSpectrum065.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum006.actual_graph_bounds.2
  linarith
#print axioms comparison0384
theorem comparison0385 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum016.graph) (2-2/10) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum095.graph) (2-2/10) := by
  have hs := DegreeOneSmallSpectrum095.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum016.actual_graph_bounds.2
  linarith
#print axioms comparison0385
theorem comparison0386 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum037.graph) (2-2/11) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum244.graph) (2-2/11) := by
  have hs := DegreeOneSmallSpectrum244.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum037.actual_graph_bounds.2
  linarith
#print axioms comparison0386
theorem comparison0387 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum094.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum400.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum400.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum094.actual_graph_bounds.2
  linarith
#print axioms comparison0387
theorem comparison0388 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum862.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum998.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum998.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum862.actual_graph_bounds.2
  linarith
#print axioms comparison0388
theorem comparison0389 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum037.graph) (2-2/11) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum242.graph) (2-2/11) := by
  have hs := DegreeOneSmallSpectrum242.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum037.actual_graph_bounds.2
  linarith
#print axioms comparison0389
theorem comparison0390 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum094.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum624.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum624.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum094.actual_graph_bounds.2
  linarith
#print axioms comparison0390
theorem comparison0391 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum862.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum993.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum993.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum862.actual_graph_bounds.2
  linarith
#print axioms comparison0391
theorem comparison0392 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum862.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1597.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1597.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum862.actual_graph_bounds.2
  linarith
#print axioms comparison0392
theorem comparison0393 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum039.graph) (2-2/9) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum067.graph) (2-2/9) := by
  have hs := DegreeOneSmallSpectrum067.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum039.actual_graph_bounds.2
  linarith
#print axioms comparison0393
theorem comparison0394 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum101.graph) (2-2/10) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum100.graph) (2-2/10) := by
  have hs := DegreeOneSmallSpectrum100.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum101.actual_graph_bounds.2
  linarith
#print axioms comparison0394
theorem comparison0395 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum170.graph) (2-2/11) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum258.graph) (2-2/11) := by
  have hs := DegreeOneSmallSpectrum258.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum170.actual_graph_bounds.2
  linarith
#print axioms comparison0395
theorem comparison0396 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum411.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum407.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum407.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum411.actual_graph_bounds.2
  linarith
#print axioms comparison0396
theorem comparison0397 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum863.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1027.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1027.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum863.actual_graph_bounds.2
  linarith
#print axioms comparison0397
theorem comparison0398 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum170.graph) (2-2/11) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum256.graph) (2-2/11) := by
  have hs := DegreeOneSmallSpectrum256.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum170.actual_graph_bounds.2
  linarith
#print axioms comparison0398
theorem comparison0399 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum411.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum656.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum656.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum411.actual_graph_bounds.2
  linarith
#print axioms comparison0399
end Gebendorfer.RadenkovicGutman.DegreeOneSmallComparisons
