/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum088
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum094
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum099
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1005
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1008
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum101
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum102
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1034
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1037
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1056
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1059
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum106
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum109
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1109
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum111
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1112
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum113
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1132
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1135
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum115
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1155
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1158
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum116
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum121
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum128
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1490
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1491
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum170
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum171
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum176
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum177
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum178
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum183
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum208
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum209
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum228
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum229
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum243
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum257
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum264
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum280
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum290
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum298
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum310
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum393
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum394
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum403
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum410
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum411
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum416
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum417
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum433
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum434
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum439
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum440
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum445
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum446
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum463
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum464
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum506
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum507
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum583
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum584
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum622
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum654
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum666
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum703
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum723
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum735
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum862
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum863
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum864
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum871
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum872
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum873
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum970
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum971
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum973
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum974
import Proofs.RadenkovicGutmanSmallGeFourSpectrum016
import Proofs.RadenkovicGutmanSmallGeFourSpectrum037
import Proofs.RadenkovicGutmanSmallGeFourSpectrum094
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallComparisons
set_option maxHeartbeats 0
theorem comparison0550 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum228.graph) (2-2/11) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum208.graph) (2-2/11) := by
  have hs := DegreeOneSmallSpectrum208.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum228.actual_graph_bounds.2
  linarith
#print axioms comparison0550
theorem comparison0551 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum393.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum583.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum583.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum393.actual_graph_bounds.2
  linarith
#print axioms comparison0551
theorem comparison0552 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum971.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum970.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum970.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum971.actual_graph_bounds.2
  linarith
#print axioms comparison0552
theorem comparison0553 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum393.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum506.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum506.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum393.actual_graph_bounds.2
  linarith
#print axioms comparison0553
theorem comparison0554 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum971.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1490.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1490.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum971.actual_graph_bounds.2
  linarith
#print axioms comparison0554
theorem comparison0555 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum088.graph) (2-2/10) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum115.graph) (2-2/10) := by
  have hs := DegreeOneSmallSpectrum115.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum088.actual_graph_bounds.2
  linarith
#print axioms comparison0555
theorem comparison0556 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum229.graph) (2-2/11) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum209.graph) (2-2/11) := by
  have hs := DegreeOneSmallSpectrum209.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum229.actual_graph_bounds.2
  linarith
#print axioms comparison0556
theorem comparison0557 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum394.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum584.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum584.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum394.actual_graph_bounds.2
  linarith
#print axioms comparison0557
theorem comparison0558 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum974.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum973.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum973.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum974.actual_graph_bounds.2
  linarith
#print axioms comparison0558
theorem comparison0559 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum394.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum507.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum507.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum394.actual_graph_bounds.2
  linarith
#print axioms comparison0559
theorem comparison0560 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum974.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1491.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1491.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum974.actual_graph_bounds.2
  linarith
#print axioms comparison0560
theorem comparison0561 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum016.graph) (2-2/10) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum094.graph) (2-2/10) := by
  have hs := DegreeOneSmallSpectrum094.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum016.actual_graph_bounds.2
  linarith
#print axioms comparison0561
theorem comparison0562 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum037.graph) (2-2/11) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum243.graph) (2-2/11) := by
  have hs := DegreeOneSmallSpectrum243.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum037.actual_graph_bounds.2
  linarith
#print axioms comparison0562
theorem comparison0563 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum094.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum403.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum403.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum094.actual_graph_bounds.2
  linarith
#print axioms comparison0563
theorem comparison0564 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum862.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1008.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1008.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum862.actual_graph_bounds.2
  linarith
#print axioms comparison0564
theorem comparison0565 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum094.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum622.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum622.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum094.actual_graph_bounds.2
  linarith
#print axioms comparison0565
theorem comparison0566 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum862.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1005.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1005.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum862.actual_graph_bounds.2
  linarith
#print axioms comparison0566
theorem comparison0567 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum101.graph) (2-2/10) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum099.graph) (2-2/10) := by
  have hs := DegreeOneSmallSpectrum099.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum101.actual_graph_bounds.2
  linarith
#print axioms comparison0567
theorem comparison0568 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum170.graph) (2-2/11) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum257.graph) (2-2/11) := by
  have hs := DegreeOneSmallSpectrum257.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum170.actual_graph_bounds.2
  linarith
#print axioms comparison0568
theorem comparison0569 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum411.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum410.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum410.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum411.actual_graph_bounds.2
  linarith
#print axioms comparison0569
theorem comparison0570 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum863.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1037.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1037.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum863.actual_graph_bounds.2
  linarith
#print axioms comparison0570
theorem comparison0571 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum411.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum654.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum654.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum411.actual_graph_bounds.2
  linarith
#print axioms comparison0571
theorem comparison0572 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum863.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1034.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1034.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum863.actual_graph_bounds.2
  linarith
#print axioms comparison0572
theorem comparison0573 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum106.graph) (2-2/10) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum102.graph) (2-2/10) := by
  have hs := DegreeOneSmallSpectrum102.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum106.actual_graph_bounds.2
  linarith
#print axioms comparison0573
theorem comparison0574 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum171.graph) (2-2/11) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum264.graph) (2-2/11) := by
  have hs := DegreeOneSmallSpectrum264.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum171.actual_graph_bounds.2
  linarith
#print axioms comparison0574
theorem comparison0575 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum417.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum416.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum416.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum417.actual_graph_bounds.2
  linarith
#print axioms comparison0575
theorem comparison0576 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum864.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1059.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1059.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum864.actual_graph_bounds.2
  linarith
#print axioms comparison0576
theorem comparison0577 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum417.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum666.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum666.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum417.actual_graph_bounds.2
  linarith
#print axioms comparison0577
theorem comparison0578 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum864.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1056.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1056.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum864.actual_graph_bounds.2
  linarith
#print axioms comparison0578
theorem comparison0579 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum111.graph) (2-2/10) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum109.graph) (2-2/10) := by
  have hs := DegreeOneSmallSpectrum109.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum111.actual_graph_bounds.2
  linarith
#print axioms comparison0579
theorem comparison0580 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum176.graph) (2-2/11) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum280.graph) (2-2/11) := by
  have hs := DegreeOneSmallSpectrum280.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum176.actual_graph_bounds.2
  linarith
#print axioms comparison0580
theorem comparison0581 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum434.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum433.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum433.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum434.actual_graph_bounds.2
  linarith
#print axioms comparison0581
theorem comparison0582 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum871.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1112.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1112.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum871.actual_graph_bounds.2
  linarith
#print axioms comparison0582
theorem comparison0583 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum434.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum703.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum703.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum434.actual_graph_bounds.2
  linarith
#print axioms comparison0583
theorem comparison0584 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum871.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1109.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1109.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum871.actual_graph_bounds.2
  linarith
#print axioms comparison0584
theorem comparison0585 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum115.graph) (2-2/10) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum113.graph) (2-2/10) := by
  have hs := DegreeOneSmallSpectrum113.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum115.actual_graph_bounds.2
  linarith
#print axioms comparison0585
theorem comparison0586 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum177.graph) (2-2/11) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum290.graph) (2-2/11) := by
  have hs := DegreeOneSmallSpectrum290.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum177.actual_graph_bounds.2
  linarith
#print axioms comparison0586
theorem comparison0587 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum440.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum439.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum439.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum440.actual_graph_bounds.2
  linarith
#print axioms comparison0587
theorem comparison0588 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum872.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1135.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1135.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum872.actual_graph_bounds.2
  linarith
#print axioms comparison0588
theorem comparison0589 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum440.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum723.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum723.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum440.actual_graph_bounds.2
  linarith
#print axioms comparison0589
theorem comparison0590 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum872.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1132.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1132.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum872.actual_graph_bounds.2
  linarith
#print axioms comparison0590
theorem comparison0591 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum121.graph) (2-2/10) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum116.graph) (2-2/10) := by
  have hs := DegreeOneSmallSpectrum116.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum121.actual_graph_bounds.2
  linarith
#print axioms comparison0591
theorem comparison0592 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum178.graph) (2-2/11) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum298.graph) (2-2/11) := by
  have hs := DegreeOneSmallSpectrum298.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum178.actual_graph_bounds.2
  linarith
#print axioms comparison0592
theorem comparison0593 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum446.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum445.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum445.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum446.actual_graph_bounds.2
  linarith
#print axioms comparison0593
theorem comparison0594 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum873.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1158.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1158.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum873.actual_graph_bounds.2
  linarith
#print axioms comparison0594
theorem comparison0595 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum446.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum735.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum735.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum446.actual_graph_bounds.2
  linarith
#print axioms comparison0595
theorem comparison0596 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum873.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1155.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1155.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum873.actual_graph_bounds.2
  linarith
#print axioms comparison0596
theorem comparison0597 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum128.graph) (2-2/10) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum109.graph) (2-2/10) := by
  have hs := DegreeOneSmallSpectrum109.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum128.actual_graph_bounds.2
  linarith
#print axioms comparison0597
theorem comparison0598 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum183.graph) (2-2/11) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum310.graph) (2-2/11) := by
  have hs := DegreeOneSmallSpectrum310.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum183.actual_graph_bounds.2
  linarith
#print axioms comparison0598
theorem comparison0599 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum464.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum463.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum463.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum464.actual_graph_bounds.2
  linarith
#print axioms comparison0599
end Gebendorfer.RadenkovicGutman.DegreeOneSmallComparisons
