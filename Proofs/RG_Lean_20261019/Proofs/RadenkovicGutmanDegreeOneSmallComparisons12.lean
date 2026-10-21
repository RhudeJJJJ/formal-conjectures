/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum110
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum113
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum114
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum118
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum119
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1208
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1211
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1223
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1226
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum123
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum129
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1310
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1313
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1328
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum133
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1331
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1361
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1364
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum137
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1377
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1380
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1411
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1414
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum142
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1421
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1424
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum144
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum145
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum146
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1463
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum147
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum184
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum198
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum199
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum204
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum208
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum209
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum218
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum311
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum323
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum328
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum336
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum339
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum340
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum341
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum464
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum468
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum469
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum504
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum505
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum509
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum510
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum527
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum528
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum539
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum540
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum543
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum544
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum562
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum563
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum754
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum755
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum784
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum788
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum791
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum792
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum793
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum794
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum880
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum881
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum909
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum910
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum916
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum917
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum923
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum924
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum945
import Proofs.RadenkovicGutmanSmallGeFourSpectrum018
import Proofs.RadenkovicGutmanSmallGeFourSpectrum022
import Proofs.RadenkovicGutmanSmallGeFourSpectrum038
import Proofs.RadenkovicGutmanSmallGeFourSpectrum064
import Proofs.RadenkovicGutmanSmallGeFourSpectrum103
import Proofs.RadenkovicGutmanSmallGeFourSpectrum104
import Proofs.RadenkovicGutmanSmallGeFourSpectrum176
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallComparisons
set_option maxHeartbeats 0
theorem comparison0600 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum880.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1211.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1211.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum880.actual_graph_bounds.2
  linarith
#print axioms comparison0600
theorem comparison0601 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum464.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum754.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum754.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum464.actual_graph_bounds.2
  linarith
#print axioms comparison0601
theorem comparison0602 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum880.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1208.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1208.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum880.actual_graph_bounds.2
  linarith
#print axioms comparison0602
theorem comparison0603 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum129.graph) (2-2/10) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum113.graph) (2-2/10) := by
  have hs := DegreeOneSmallSpectrum113.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum129.actual_graph_bounds.2
  linarith
#print axioms comparison0603
theorem comparison0604 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum184.graph) (2-2/11) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum311.graph) (2-2/11) := by
  have hs := DegreeOneSmallSpectrum311.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum184.actual_graph_bounds.2
  linarith
#print axioms comparison0604
theorem comparison0605 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum469.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum468.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum468.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum469.actual_graph_bounds.2
  linarith
#print axioms comparison0605
theorem comparison0606 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum881.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1226.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1226.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum881.actual_graph_bounds.2
  linarith
#print axioms comparison0606
theorem comparison0607 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum469.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum755.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum755.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum469.actual_graph_bounds.2
  linarith
#print axioms comparison0607
theorem comparison0608 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum881.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1223.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1223.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum881.actual_graph_bounds.2
  linarith
#print axioms comparison0608
theorem comparison0609 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum133.graph) (2-2/10) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum123.graph) (2-2/10) := by
  have hs := DegreeOneSmallSpectrum123.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum133.actual_graph_bounds.2
  linarith
#print axioms comparison0609
theorem comparison0610 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum198.graph) (2-2/11) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum323.graph) (2-2/11) := by
  have hs := DegreeOneSmallSpectrum323.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum198.actual_graph_bounds.2
  linarith
#print axioms comparison0610
theorem comparison0611 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum505.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum504.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum504.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum505.actual_graph_bounds.2
  linarith
#print axioms comparison0611
theorem comparison0612 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum909.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1313.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1313.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum909.actual_graph_bounds.2
  linarith
#print axioms comparison0612
theorem comparison0613 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum505.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum784.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum784.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum505.actual_graph_bounds.2
  linarith
#print axioms comparison0613
theorem comparison0614 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum909.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1310.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1310.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum909.actual_graph_bounds.2
  linarith
#print axioms comparison0614
theorem comparison0615 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum137.graph) (2-2/10) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum118.graph) (2-2/10) := by
  have hs := DegreeOneSmallSpectrum118.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum137.actual_graph_bounds.2
  linarith
#print axioms comparison0615
theorem comparison0616 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum199.graph) (2-2/11) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum328.graph) (2-2/11) := by
  have hs := DegreeOneSmallSpectrum328.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum199.actual_graph_bounds.2
  linarith
#print axioms comparison0616
theorem comparison0617 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum510.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum509.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum509.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum510.actual_graph_bounds.2
  linarith
#print axioms comparison0617
theorem comparison0618 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum910.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1331.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1331.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum910.actual_graph_bounds.2
  linarith
#print axioms comparison0618
theorem comparison0619 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum510.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum788.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum788.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum510.actual_graph_bounds.2
  linarith
#print axioms comparison0619
theorem comparison0620 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum910.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1328.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1328.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum910.actual_graph_bounds.2
  linarith
#print axioms comparison0620
theorem comparison0621 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum022.graph) (2-2/10) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum018.graph) (2-2/10) := by
  have hs := SmallGeFourSpectrum018.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum022.actual_graph_bounds.2
  linarith
#print axioms comparison0621
theorem comparison0622 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum038.graph) (2-2/11) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum064.graph) (2-2/11) := by
  have hs := SmallGeFourSpectrum064.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum038.actual_graph_bounds.2
  linarith
#print axioms comparison0622
theorem comparison0623 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum104.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum103.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum103.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum104.actual_graph_bounds.2
  linarith
#print axioms comparison0623
theorem comparison0624 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum916.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1364.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1364.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum916.actual_graph_bounds.2
  linarith
#print axioms comparison0624
theorem comparison0625 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum104.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum176.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum176.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum104.actual_graph_bounds.2
  linarith
#print axioms comparison0625
theorem comparison0626 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum916.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1361.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1361.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum916.actual_graph_bounds.2
  linarith
#print axioms comparison0626
theorem comparison0627 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum142.graph) (2-2/10) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum119.graph) (2-2/10) := by
  have hs := DegreeOneSmallSpectrum119.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum142.actual_graph_bounds.2
  linarith
#print axioms comparison0627
theorem comparison0628 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum204.graph) (2-2/11) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum336.graph) (2-2/11) := by
  have hs := DegreeOneSmallSpectrum336.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum204.actual_graph_bounds.2
  linarith
#print axioms comparison0628
theorem comparison0629 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum528.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum527.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum527.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum528.actual_graph_bounds.2
  linarith
#print axioms comparison0629
theorem comparison0630 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum917.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1380.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1380.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum917.actual_graph_bounds.2
  linarith
#print axioms comparison0630
theorem comparison0631 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum528.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum791.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum791.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum528.actual_graph_bounds.2
  linarith
#print axioms comparison0631
theorem comparison0632 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum917.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1377.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1377.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum917.actual_graph_bounds.2
  linarith
#print axioms comparison0632
theorem comparison0633 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum144.graph) (2-2/10) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum110.graph) (2-2/10) := by
  have hs := DegreeOneSmallSpectrum110.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum144.actual_graph_bounds.2
  linarith
#print axioms comparison0633
theorem comparison0634 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum208.graph) (2-2/11) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum339.graph) (2-2/11) := by
  have hs := DegreeOneSmallSpectrum339.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum208.actual_graph_bounds.2
  linarith
#print axioms comparison0634
theorem comparison0635 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum540.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum539.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum539.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum540.actual_graph_bounds.2
  linarith
#print axioms comparison0635
theorem comparison0636 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum923.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1414.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1414.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum923.actual_graph_bounds.2
  linarith
#print axioms comparison0636
theorem comparison0637 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum540.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum792.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum792.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum540.actual_graph_bounds.2
  linarith
#print axioms comparison0637
theorem comparison0638 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum923.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1411.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1411.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum923.actual_graph_bounds.2
  linarith
#print axioms comparison0638
theorem comparison0639 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum145.graph) (2-2/10) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum114.graph) (2-2/10) := by
  have hs := DegreeOneSmallSpectrum114.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum145.actual_graph_bounds.2
  linarith
#print axioms comparison0639
theorem comparison0640 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum209.graph) (2-2/11) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum340.graph) (2-2/11) := by
  have hs := DegreeOneSmallSpectrum340.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum209.actual_graph_bounds.2
  linarith
#print axioms comparison0640
theorem comparison0641 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum544.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum543.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum543.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum544.actual_graph_bounds.2
  linarith
#print axioms comparison0641
theorem comparison0642 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum924.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1424.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1424.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum924.actual_graph_bounds.2
  linarith
#print axioms comparison0642
theorem comparison0643 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum544.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum793.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum793.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum544.actual_graph_bounds.2
  linarith
#print axioms comparison0643
theorem comparison0644 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum924.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1421.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1421.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum924.actual_graph_bounds.2
  linarith
#print axioms comparison0644
theorem comparison0645 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum146.graph) (2-2/10) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum147.graph) (2-2/10) := by
  have hs := DegreeOneSmallSpectrum147.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum146.actual_graph_bounds.2
  linarith
#print axioms comparison0645
theorem comparison0646 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum218.graph) (2-2/11) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum341.graph) (2-2/11) := by
  have hs := DegreeOneSmallSpectrum341.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum218.actual_graph_bounds.2
  linarith
#print axioms comparison0646
theorem comparison0647 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum563.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum562.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum562.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum563.actual_graph_bounds.2
  linarith
#print axioms comparison0647
theorem comparison0648 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum945.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1463.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1463.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum945.actual_graph_bounds.2
  linarith
#print axioms comparison0648
theorem comparison0649 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum563.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum794.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum794.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum563.actual_graph_bounds.2
  linarith
#print axioms comparison0649
end Gebendorfer.RadenkovicGutman.DegreeOneSmallComparisons
