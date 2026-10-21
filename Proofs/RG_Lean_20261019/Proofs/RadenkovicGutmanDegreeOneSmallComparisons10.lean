/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum079
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum081
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum082
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum083
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum085
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum087
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum088
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum089
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum111
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum117
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum120
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum121
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum124
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1242
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum126
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum127
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum128
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1282
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum129
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1343
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1388
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1430
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1446
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1486
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1488
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1489
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum192
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum197
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum200
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum202
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum205
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum207
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum210
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum211
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum212
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum214
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum215
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum217
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum222
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum225
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum227
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum373
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum379
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum380
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum381
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum382
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum387
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum388
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum389
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum482
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum497
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum508
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum509
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum511
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum512
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum513
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum515
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum516
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum517
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum533
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum549
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum558
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum574
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum580
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum582
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum887
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum893
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum894
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum914
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum915
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum921
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum922
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum928
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum929
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum934
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum935
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum950
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum951
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum955
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum956
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum960
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum961
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallComparisons
set_option maxHeartbeats 0
theorem comparison0500 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum887.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1242.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1242.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum887.actual_graph_bounds.2
  linarith
#print axioms comparison0500
theorem comparison0501 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum079.graph) (2-2/10) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum117.graph) (2-2/10) := by
  have hs := DegreeOneSmallSpectrum117.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum079.actual_graph_bounds.2
  linarith
#print axioms comparison0501
theorem comparison0502 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum197.graph) (2-2/11) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum192.graph) (2-2/11) := by
  have hs := DegreeOneSmallSpectrum192.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum197.actual_graph_bounds.2
  linarith
#print axioms comparison0502
theorem comparison0503 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum373.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum497.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum497.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum373.actual_graph_bounds.2
  linarith
#print axioms comparison0503
theorem comparison0504 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum894.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum893.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum893.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum894.actual_graph_bounds.2
  linarith
#print axioms comparison0504
theorem comparison0505 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum373.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum482.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum482.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum373.actual_graph_bounds.2
  linarith
#print axioms comparison0505
theorem comparison0506 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum894.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1282.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1282.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum894.actual_graph_bounds.2
  linarith
#print axioms comparison0506
theorem comparison0507 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum081.graph) (2-2/10) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum124.graph) (2-2/10) := by
  have hs := DegreeOneSmallSpectrum124.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum081.actual_graph_bounds.2
  linarith
#print axioms comparison0507
theorem comparison0508 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum202.graph) (2-2/11) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum200.graph) (2-2/11) := by
  have hs := DegreeOneSmallSpectrum200.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum202.actual_graph_bounds.2
  linarith
#print axioms comparison0508
theorem comparison0509 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum379.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum517.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum517.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum379.actual_graph_bounds.2
  linarith
#print axioms comparison0509
theorem comparison0510 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum915.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum914.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum914.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum915.actual_graph_bounds.2
  linarith
#print axioms comparison0510
theorem comparison0511 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum379.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum511.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum511.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum379.actual_graph_bounds.2
  linarith
#print axioms comparison0511
theorem comparison0512 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum915.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1343.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1343.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum915.actual_graph_bounds.2
  linarith
#print axioms comparison0512
theorem comparison0513 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum082.graph) (2-2/10) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum126.graph) (2-2/10) := by
  have hs := DegreeOneSmallSpectrum126.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum082.actual_graph_bounds.2
  linarith
#print axioms comparison0513
theorem comparison0514 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum207.graph) (2-2/11) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum205.graph) (2-2/11) := by
  have hs := DegreeOneSmallSpectrum205.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum207.actual_graph_bounds.2
  linarith
#print axioms comparison0514
theorem comparison0515 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum380.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum533.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum533.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum380.actual_graph_bounds.2
  linarith
#print axioms comparison0515
theorem comparison0516 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum922.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum921.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum921.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum922.actual_graph_bounds.2
  linarith
#print axioms comparison0516
theorem comparison0517 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum380.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum512.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum512.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum380.actual_graph_bounds.2
  linarith
#print axioms comparison0517
theorem comparison0518 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum922.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1388.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1388.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum922.actual_graph_bounds.2
  linarith
#print axioms comparison0518
theorem comparison0519 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum083.graph) (2-2/10) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum127.graph) (2-2/10) := by
  have hs := DegreeOneSmallSpectrum127.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum083.actual_graph_bounds.2
  linarith
#print axioms comparison0519
theorem comparison0520 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum212.graph) (2-2/11) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum210.graph) (2-2/11) := by
  have hs := DegreeOneSmallSpectrum210.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum212.actual_graph_bounds.2
  linarith
#print axioms comparison0520
theorem comparison0521 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum381.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum549.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum549.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum381.actual_graph_bounds.2
  linarith
#print axioms comparison0521
theorem comparison0522 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum929.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum928.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum928.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum929.actual_graph_bounds.2
  linarith
#print axioms comparison0522
theorem comparison0523 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum381.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum513.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum513.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum381.actual_graph_bounds.2
  linarith
#print axioms comparison0523
theorem comparison0524 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum929.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1430.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1430.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum929.actual_graph_bounds.2
  linarith
#print axioms comparison0524
theorem comparison0525 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum085.graph) (2-2/10) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum120.graph) (2-2/10) := by
  have hs := DegreeOneSmallSpectrum120.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum085.actual_graph_bounds.2
  linarith
#print axioms comparison0525
theorem comparison0526 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum217.graph) (2-2/11) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum210.graph) (2-2/11) := by
  have hs := DegreeOneSmallSpectrum210.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum217.actual_graph_bounds.2
  linarith
#print axioms comparison0526
theorem comparison0527 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum382.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum558.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum558.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum382.actual_graph_bounds.2
  linarith
#print axioms comparison0527
theorem comparison0528 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum935.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum934.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum934.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum935.actual_graph_bounds.2
  linarith
#print axioms comparison0528
theorem comparison0529 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum382.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum508.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum508.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum382.actual_graph_bounds.2
  linarith
#print axioms comparison0529
theorem comparison0530 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum935.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1446.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1446.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum935.actual_graph_bounds.2
  linarith
#print axioms comparison0530
theorem comparison0531 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum087.graph) (2-2/10) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum128.graph) (2-2/10) := by
  have hs := DegreeOneSmallSpectrum128.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum087.actual_graph_bounds.2
  linarith
#print axioms comparison0531
theorem comparison0532 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum222.graph) (2-2/11) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum214.graph) (2-2/11) := by
  have hs := DegreeOneSmallSpectrum214.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum222.actual_graph_bounds.2
  linarith
#print axioms comparison0532
theorem comparison0533 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum387.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum574.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum574.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum387.actual_graph_bounds.2
  linarith
#print axioms comparison0533
theorem comparison0534 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum951.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum950.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum950.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum951.actual_graph_bounds.2
  linarith
#print axioms comparison0534
theorem comparison0535 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum387.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum515.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum515.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum387.actual_graph_bounds.2
  linarith
#print axioms comparison0535
theorem comparison0536 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum951.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1486.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1486.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum951.actual_graph_bounds.2
  linarith
#print axioms comparison0536
theorem comparison0537 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum088.graph) (2-2/10) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum129.graph) (2-2/10) := by
  have hs := DegreeOneSmallSpectrum129.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum088.actual_graph_bounds.2
  linarith
#print axioms comparison0537
theorem comparison0538 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum225.graph) (2-2/11) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum215.graph) (2-2/11) := by
  have hs := DegreeOneSmallSpectrum215.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum225.actual_graph_bounds.2
  linarith
#print axioms comparison0538
theorem comparison0539 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum388.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum580.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum580.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum388.actual_graph_bounds.2
  linarith
#print axioms comparison0539
theorem comparison0540 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum956.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum955.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum955.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum956.actual_graph_bounds.2
  linarith
#print axioms comparison0540
theorem comparison0541 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum388.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum516.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum516.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum388.actual_graph_bounds.2
  linarith
#print axioms comparison0541
theorem comparison0542 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum956.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1488.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1488.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum956.actual_graph_bounds.2
  linarith
#print axioms comparison0542
theorem comparison0543 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum089.graph) (2-2/10) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum121.graph) (2-2/10) := by
  have hs := DegreeOneSmallSpectrum121.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum089.actual_graph_bounds.2
  linarith
#print axioms comparison0543
theorem comparison0544 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum227.graph) (2-2/11) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum211.graph) (2-2/11) := by
  have hs := DegreeOneSmallSpectrum211.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum227.actual_graph_bounds.2
  linarith
#print axioms comparison0544
theorem comparison0545 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum389.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum582.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum582.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum389.actual_graph_bounds.2
  linarith
#print axioms comparison0545
theorem comparison0546 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum961.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum960.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum960.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum961.actual_graph_bounds.2
  linarith
#print axioms comparison0546
theorem comparison0547 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum389.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum509.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum509.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum389.actual_graph_bounds.2
  linarith
#print axioms comparison0547
theorem comparison0548 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum961.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1489.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1489.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum961.actual_graph_bounds.2
  linarith
#print axioms comparison0548
theorem comparison0549 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum087.graph) (2-2/10) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum111.graph) (2-2/10) := by
  have hs := DegreeOneSmallSpectrum111.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum087.actual_graph_bounds.2
  linarith
#print axioms comparison0549
end Gebendorfer.RadenkovicGutman.DegreeOneSmallComparisons
