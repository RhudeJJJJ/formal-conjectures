/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum012
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum017
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum058
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum074
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum088
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1016
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1021
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum108
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1090
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1095
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1118
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum115
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1216
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1292
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1296
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum130
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1301
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum133
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1418
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1457
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1481
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum159
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum160
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum161
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum175
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum184
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1877
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum207
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum209
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum220
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum229
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum253
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum275
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum318
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum370
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum380
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum388
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum440
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum505
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum862
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum870
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum872
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum881
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum909
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum916
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum922
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum924
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum947
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum952
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum956
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum972
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum974
import Proofs.RadenkovicGutmanDegreeTwoThreeSpectrum140
import Proofs.RadenkovicGutmanDegreeTwoThreeSpectrum144
import Proofs.RadenkovicGutmanDegreeTwoThreeSpectrum148
import Proofs.RadenkovicGutmanSmallGeFourSpectrum000
import Proofs.RadenkovicGutmanSmallGeFourSpectrum003
import Proofs.RadenkovicGutmanSmallGeFourSpectrum004
import Proofs.RadenkovicGutmanSmallGeFourSpectrum007
import Proofs.RadenkovicGutmanSmallGeFourSpectrum016
import Proofs.RadenkovicGutmanSmallGeFourSpectrum017
import Proofs.RadenkovicGutmanSmallGeFourSpectrum019
import Proofs.RadenkovicGutmanSmallGeFourSpectrum023
import Proofs.RadenkovicGutmanSmallGeFourSpectrum030
import Proofs.RadenkovicGutmanSmallGeFourSpectrum031
import Proofs.RadenkovicGutmanSmallGeFourSpectrum037
import Proofs.RadenkovicGutmanSmallGeFourSpectrum038
import Proofs.RadenkovicGutmanSmallGeFourSpectrum039
import Proofs.RadenkovicGutmanSmallGeFourSpectrum045
import Proofs.RadenkovicGutmanSmallGeFourSpectrum047
import Proofs.RadenkovicGutmanSmallGeFourSpectrum054
import Proofs.RadenkovicGutmanSmallGeFourSpectrum055
import Proofs.RadenkovicGutmanSmallGeFourSpectrum066
import Proofs.RadenkovicGutmanSmallGeFourSpectrum067
import Proofs.RadenkovicGutmanSmallGeFourSpectrum094
import Proofs.RadenkovicGutmanSmallGeFourSpectrum095
import Proofs.RadenkovicGutmanSmallGeFourSpectrum099
import Proofs.RadenkovicGutmanSmallGeFourSpectrum104
import Proofs.RadenkovicGutmanSmallGeFourSpectrum110
import Proofs.RadenkovicGutmanSmallGeFourSpectrum192
import Proofs.RadenkovicGutmanSmallGeFourSpectrum193
import Proofs.RadenkovicGutmanSmallGeFourSpectrum194
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteComparisons
set_option maxHeartbeats 0
theorem comparison5450 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum108.graph) (2-2/10) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum017.graph) (2-2/10) := by
  have hs := SmallGeFourSpectrum017.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum108.actual_graph_bounds.2
  linarith
#print axioms comparison5450
theorem comparison5451 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum130.graph) (2-2/10) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum019.graph) (2-2/10) := by
  have hs := SmallGeFourSpectrum019.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum130.actual_graph_bounds.2
  linarith
#print axioms comparison5451
theorem comparison5452 :
    stopLoss (laplacianSpectrum DegreeTwoThreeSpectrum144.graph) (2-2/10) <
      stopLoss (laplacianSpectrum DegreeTwoThreeSpectrum140.graph) (2-2/10) := by
  have hs := DegreeTwoThreeSpectrum140.actual_graph_bounds.1
  have ht := DegreeTwoThreeSpectrum144.actual_graph_bounds.2
  linarith
#print axioms comparison5452
theorem comparison5453 :
    stopLoss (laplacianSpectrum DegreeTwoThreeSpectrum148.graph) (2-2/10) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum030.graph) (2-2/10) := by
  have hs := SmallGeFourSpectrum030.actual_graph_bounds.1
  have ht := DegreeTwoThreeSpectrum148.actual_graph_bounds.2
  linarith
#print axioms comparison5453
theorem comparison5454 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum159.graph) (2-2/10) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum160.graph) (2-2/10) := by
  have hs := DegreeOneSmallSpectrum160.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum159.actual_graph_bounds.2
  linarith
#print axioms comparison5454
theorem comparison5455 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum161.graph) (2-2/10) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum031.graph) (2-2/10) := by
  have hs := SmallGeFourSpectrum031.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum161.actual_graph_bounds.2
  linarith
#print axioms comparison5455
theorem comparison5456 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum012.graph) (2-2/7) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum000.graph) (2-2/7) := by
  have hs := SmallGeFourSpectrum000.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum012.actual_graph_bounds.2
  linarith
#print axioms comparison5456
theorem comparison5457 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum017.graph) (2-2/8) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum003.graph) (2-2/8) := by
  have hs := SmallGeFourSpectrum003.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum017.actual_graph_bounds.2
  linarith
#print axioms comparison5457
theorem comparison5458 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum058.graph) (2-2/9) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum007.graph) (2-2/9) := by
  have hs := SmallGeFourSpectrum007.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum058.actual_graph_bounds.2
  linarith
#print axioms comparison5458
theorem comparison5459 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum088.graph) (2-2/10) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum023.graph) (2-2/10) := by
  have hs := SmallGeFourSpectrum023.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum088.actual_graph_bounds.2
  linarith
#print axioms comparison5459
theorem comparison5460 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum115.graph) (2-2/10) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum017.graph) (2-2/10) := by
  have hs := SmallGeFourSpectrum017.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum115.actual_graph_bounds.2
  linarith
#print axioms comparison5460
theorem comparison5461 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum133.graph) (2-2/10) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum019.graph) (2-2/10) := by
  have hs := SmallGeFourSpectrum019.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum133.actual_graph_bounds.2
  linarith
#print axioms comparison5461
theorem comparison5462 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum229.graph) (2-2/11) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum039.graph) (2-2/11) := by
  have hs := SmallGeFourSpectrum039.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum229.actual_graph_bounds.2
  linarith
#print axioms comparison5462
theorem comparison5463 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum184.graph) (2-2/11) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum054.graph) (2-2/11) := by
  have hs := SmallGeFourSpectrum054.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum184.actual_graph_bounds.2
  linarith
#print axioms comparison5463
theorem comparison5464 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum209.graph) (2-2/11) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum066.graph) (2-2/11) := by
  have hs := SmallGeFourSpectrum066.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum209.actual_graph_bounds.2
  linarith
#print axioms comparison5464
theorem comparison5465 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum220.graph) (2-2/11) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum067.graph) (2-2/11) := by
  have hs := SmallGeFourSpectrum067.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum220.actual_graph_bounds.2
  linarith
#print axioms comparison5465
theorem comparison5466 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum253.graph) (2-2/11) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum045.graph) (2-2/11) := by
  have hs := SmallGeFourSpectrum045.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum253.actual_graph_bounds.2
  linarith
#print axioms comparison5466
theorem comparison5467 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum275.graph) (2-2/11) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum047.graph) (2-2/11) := by
  have hs := SmallGeFourSpectrum047.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum275.actual_graph_bounds.2
  linarith
#print axioms comparison5467
theorem comparison5468 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum318.graph) (2-2/11) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum055.graph) (2-2/11) := by
  have hs := SmallGeFourSpectrum055.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum318.actual_graph_bounds.2
  linarith
#print axioms comparison5468
theorem comparison5469 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum074.graph) (2-2/10) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum016.graph) (2-2/10) := by
  have hs := SmallGeFourSpectrum016.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum074.actual_graph_bounds.2
  linarith
#print axioms comparison5469
theorem comparison5470 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum207.graph) (2-2/11) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum038.graph) (2-2/11) := by
  have hs := SmallGeFourSpectrum038.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum207.actual_graph_bounds.2
  linarith
#print axioms comparison5470
theorem comparison5471 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum388.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum110.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum110.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum388.actual_graph_bounds.2
  linarith
#print axioms comparison5471
theorem comparison5472 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum440.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum095.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum095.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum440.actual_graph_bounds.2
  linarith
#print axioms comparison5472
theorem comparison5473 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum505.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum099.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum099.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum505.actual_graph_bounds.2
  linarith
#print axioms comparison5473
theorem comparison5474 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum974.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum972.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum972.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum974.actual_graph_bounds.2
  linarith
#print axioms comparison5474
theorem comparison5475 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum881.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1216.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1216.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum881.actual_graph_bounds.2
  linarith
#print axioms comparison5475
theorem comparison5476 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum924.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1418.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1418.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum924.actual_graph_bounds.2
  linarith
#print axioms comparison5476
theorem comparison5477 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum947.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1481.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1481.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum947.actual_graph_bounds.2
  linarith
#print axioms comparison5477
theorem comparison5478 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1021.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1016.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1016.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum1021.actual_graph_bounds.2
  linarith
#print axioms comparison5478
theorem comparison5479 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1095.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1090.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1090.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum1095.actual_graph_bounds.2
  linarith
#print axioms comparison5479
theorem comparison5480 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1296.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1292.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1292.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum1296.actual_graph_bounds.2
  linarith
#print axioms comparison5480
theorem comparison5481 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum175.graph) (2-2/11) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum037.graph) (2-2/11) := by
  have hs := SmallGeFourSpectrum037.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum175.actual_graph_bounds.2
  linarith
#print axioms comparison5481
theorem comparison5482 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum380.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum104.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum104.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum380.actual_graph_bounds.2
  linarith
#print axioms comparison5482
theorem comparison5483 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum956.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum952.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum952.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum956.actual_graph_bounds.2
  linarith
#print axioms comparison5483
theorem comparison5484 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum872.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1118.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1118.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum872.actual_graph_bounds.2
  linarith
#print axioms comparison5484
theorem comparison5485 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum909.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1301.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1301.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum909.actual_graph_bounds.2
  linarith
#print axioms comparison5485
theorem comparison5486 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum370.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum094.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum094.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum370.actual_graph_bounds.2
  linarith
#print axioms comparison5486
theorem comparison5487 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum922.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum916.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum916.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum922.actual_graph_bounds.2
  linarith
#print axioms comparison5487
theorem comparison5488 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum870.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum862.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum862.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum870.actual_graph_bounds.2
  linarith
#print axioms comparison5488
theorem comparison5489 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum017.graph) (2-2/8) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum004.graph) (2-2/8) := by
  have hs := SmallGeFourSpectrum004.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum017.actual_graph_bounds.2
  linarith
#print axioms comparison5489
theorem comparison5490 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum175.graph) (2-2/11) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum038.graph) (2-2/11) := by
  have hs := SmallGeFourSpectrum038.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum175.actual_graph_bounds.2
  linarith
#print axioms comparison5490
theorem comparison5491 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum380.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum099.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum099.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum380.actual_graph_bounds.2
  linarith
#print axioms comparison5491
theorem comparison5492 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum370.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum104.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum104.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum370.actual_graph_bounds.2
  linarith
#print axioms comparison5492
theorem comparison5493 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum074.graph) (2-2/10) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum023.graph) (2-2/10) := by
  have hs := SmallGeFourSpectrum023.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum074.actual_graph_bounds.2
  linarith
#print axioms comparison5493
theorem comparison5494 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum207.graph) (2-2/11) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum067.graph) (2-2/11) := by
  have hs := SmallGeFourSpectrum067.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum207.actual_graph_bounds.2
  linarith
#print axioms comparison5494
theorem comparison5495 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum388.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum192.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum192.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum388.actual_graph_bounds.2
  linarith
#print axioms comparison5495
theorem comparison5496 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum440.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum193.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum193.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum440.actual_graph_bounds.2
  linarith
#print axioms comparison5496
theorem comparison5497 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum505.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum194.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum194.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum505.actual_graph_bounds.2
  linarith
#print axioms comparison5497
theorem comparison5498 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum974.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1457.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1457.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum974.actual_graph_bounds.2
  linarith
#print axioms comparison5498
theorem comparison5499 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum881.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1877.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1877.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum881.actual_graph_bounds.2
  linarith
#print axioms comparison5499
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteComparisons
