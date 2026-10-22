/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1013
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1019
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1099
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1105
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1106
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1107
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1122
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1128
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1129
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1130
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1207
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1222
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1304
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1307
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1308
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1317
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1321
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1324
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1325
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1326
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1333
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1334
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1336
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1337
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1343
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1345
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1351
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1356
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1359
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1368
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1372
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1375
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1381
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1382
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1388
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1390
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1396
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1401
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1406
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1409
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1410
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1416
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1419
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1420
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1430
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1432
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1440
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1446
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1449
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1615
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1628
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1634
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1635
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1645
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1651
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1652
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1663
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1664
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1665
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1685
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1686
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1687
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1688
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1689
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1690
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum941
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum942
import Proofs.RadenkovicGutmanDegreeTwoThreeSpectrum1091
import Proofs.RadenkovicGutmanDegreeTwoThreeSpectrum1137
import Proofs.RadenkovicGutmanDegreeTwoThreeSpectrum1153
import Proofs.RadenkovicGutmanDegreeTwoThreeSpectrum1390
import Proofs.RadenkovicGutmanDegreeTwoThreeSpectrum1414
import Proofs.RadenkovicGutmanDegreeTwoThreeSpectrum1430
import Proofs.RadenkovicGutmanDegreeTwoThreeSpectrum1433
import Proofs.RadenkovicGutmanDegreeTwoThreeSpectrum1434
import Proofs.RadenkovicGutmanDegreeTwoThreeSpectrum1462
import Proofs.RadenkovicGutmanDegreeTwoThreeSpectrum1466
import Proofs.RadenkovicGutmanDegreeTwoThreeSpectrum1467
import Proofs.RadenkovicGutmanDegreeTwoThreeSpectrum1468
import Proofs.RadenkovicGutmanDegreeTwoThreeSpectrum1469
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteComparisons
set_option maxHeartbeats 0
theorem comparison0600 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1304.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeTwoThreeSpectrum1462.graph) (2-2/13) := by
  have hs := DegreeTwoThreeSpectrum1462.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum1304.actual_graph_bounds.2
  linarith
#print axioms comparison0600
theorem comparison0601 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1308.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeTwoThreeSpectrum1430.graph) (2-2/13) := by
  have hs := DegreeTwoThreeSpectrum1430.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum1308.actual_graph_bounds.2
  linarith
#print axioms comparison0601
theorem comparison0602 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1307.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeTwoThreeSpectrum1091.graph) (2-2/13) := by
  have hs := DegreeTwoThreeSpectrum1091.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum1307.actual_graph_bounds.2
  linarith
#print axioms comparison0602
theorem comparison0603 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1317.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1685.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1685.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum1317.actual_graph_bounds.2
  linarith
#print axioms comparison0603
theorem comparison0604 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1321.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1686.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1686.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum1321.actual_graph_bounds.2
  linarith
#print axioms comparison0604
theorem comparison0605 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1326.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1663.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1663.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum1326.actual_graph_bounds.2
  linarith
#print axioms comparison0605
theorem comparison0606 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1324.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1325.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1325.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum1324.actual_graph_bounds.2
  linarith
#print axioms comparison0606
theorem comparison0607 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1336.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1634.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1634.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum1336.actual_graph_bounds.2
  linarith
#print axioms comparison0607
theorem comparison0608 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1337.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1651.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1651.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum1337.actual_graph_bounds.2
  linarith
#print axioms comparison0608
theorem comparison0609 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1324.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1334.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1334.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum1324.actual_graph_bounds.2
  linarith
#print axioms comparison0609
theorem comparison0610 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1343.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1345.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1345.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum1343.actual_graph_bounds.2
  linarith
#print axioms comparison0610
theorem comparison0611 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1105.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1128.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1128.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum1105.actual_graph_bounds.2
  linarith
#print axioms comparison0611
theorem comparison0612 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1351.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeTwoThreeSpectrum1466.graph) (2-2/13) := by
  have hs := DegreeTwoThreeSpectrum1466.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum1351.actual_graph_bounds.2
  linarith
#print axioms comparison0612
theorem comparison0613 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1356.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeTwoThreeSpectrum1467.graph) (2-2/13) := by
  have hs := DegreeTwoThreeSpectrum1467.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum1356.actual_graph_bounds.2
  linarith
#print axioms comparison0613
theorem comparison0614 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1359.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeTwoThreeSpectrum1433.graph) (2-2/13) := by
  have hs := DegreeTwoThreeSpectrum1433.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum1359.actual_graph_bounds.2
  linarith
#print axioms comparison0614
theorem comparison0615 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1333.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeTwoThreeSpectrum1137.graph) (2-2/13) := by
  have hs := DegreeTwoThreeSpectrum1137.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum1333.actual_graph_bounds.2
  linarith
#print axioms comparison0615
theorem comparison0616 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1368.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeTwoThreeSpectrum1468.graph) (2-2/13) := by
  have hs := DegreeTwoThreeSpectrum1468.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum1368.actual_graph_bounds.2
  linarith
#print axioms comparison0616
theorem comparison0617 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1372.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeTwoThreeSpectrum1469.graph) (2-2/13) := by
  have hs := DegreeTwoThreeSpectrum1469.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum1372.actual_graph_bounds.2
  linarith
#print axioms comparison0617
theorem comparison0618 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1375.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeTwoThreeSpectrum1434.graph) (2-2/13) := by
  have hs := DegreeTwoThreeSpectrum1434.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum1375.actual_graph_bounds.2
  linarith
#print axioms comparison0618
theorem comparison0619 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1334.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeTwoThreeSpectrum1153.graph) (2-2/13) := by
  have hs := DegreeTwoThreeSpectrum1153.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum1334.actual_graph_bounds.2
  linarith
#print axioms comparison0619
theorem comparison0620 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1381.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeTwoThreeSpectrum1390.graph) (2-2/13) := by
  have hs := DegreeTwoThreeSpectrum1390.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum1381.actual_graph_bounds.2
  linarith
#print axioms comparison0620
theorem comparison0621 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1382.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeTwoThreeSpectrum1414.graph) (2-2/13) := by
  have hs := DegreeTwoThreeSpectrum1414.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum1382.actual_graph_bounds.2
  linarith
#print axioms comparison0621
theorem comparison0622 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1325.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeTwoThreeSpectrum1153.graph) (2-2/13) := by
  have hs := DegreeTwoThreeSpectrum1153.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum1325.actual_graph_bounds.2
  linarith
#print axioms comparison0622
theorem comparison0623 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1388.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1390.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1390.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum1388.actual_graph_bounds.2
  linarith
#print axioms comparison0623
theorem comparison0624 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1106.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1129.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1129.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum1106.actual_graph_bounds.2
  linarith
#print axioms comparison0624
theorem comparison0625 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1396.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1687.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1687.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum1396.actual_graph_bounds.2
  linarith
#print axioms comparison0625
theorem comparison0626 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1401.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1688.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1688.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum1401.actual_graph_bounds.2
  linarith
#print axioms comparison0626
theorem comparison0627 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1406.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1689.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1689.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum1406.actual_graph_bounds.2
  linarith
#print axioms comparison0627
theorem comparison0628 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1409.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1664.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1664.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum1409.actual_graph_bounds.2
  linarith
#print axioms comparison0628
theorem comparison0629 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1336.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1381.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1381.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum1336.actual_graph_bounds.2
  linarith
#print axioms comparison0629
theorem comparison0630 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1416.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1690.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1690.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum1416.actual_graph_bounds.2
  linarith
#print axioms comparison0630
theorem comparison0631 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1419.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1665.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1665.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum1419.actual_graph_bounds.2
  linarith
#print axioms comparison0631
theorem comparison0632 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1337.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1382.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1382.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum1337.actual_graph_bounds.2
  linarith
#print axioms comparison0632
theorem comparison0633 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1409.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1635.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1635.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum1409.actual_graph_bounds.2
  linarith
#print axioms comparison0633
theorem comparison0634 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1419.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1652.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1652.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum1419.actual_graph_bounds.2
  linarith
#print axioms comparison0634
theorem comparison0635 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1326.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1375.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1375.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum1326.actual_graph_bounds.2
  linarith
#print axioms comparison0635
theorem comparison0636 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1430.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1432.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1432.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum1430.actual_graph_bounds.2
  linarith
#print axioms comparison0636
theorem comparison0637 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1107.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1130.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1130.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum1107.actual_graph_bounds.2
  linarith
#print axioms comparison0637
theorem comparison0638 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1396.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1440.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1440.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum1396.actual_graph_bounds.2
  linarith
#print axioms comparison0638
theorem comparison0639 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1401.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1615.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1615.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum1401.actual_graph_bounds.2
  linarith
#print axioms comparison0639
theorem comparison0640 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1406.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1628.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1628.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum1406.actual_graph_bounds.2
  linarith
#print axioms comparison0640
theorem comparison0641 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1317.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1368.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1368.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum1317.actual_graph_bounds.2
  linarith
#print axioms comparison0641
theorem comparison0642 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1416.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1645.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1645.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum1416.actual_graph_bounds.2
  linarith
#print axioms comparison0642
theorem comparison0643 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1321.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1372.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1372.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum1321.actual_graph_bounds.2
  linarith
#print axioms comparison0643
theorem comparison0644 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1446.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1449.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1449.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum1446.actual_graph_bounds.2
  linarith
#print axioms comparison0644
theorem comparison0645 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1099.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1122.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1122.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum1099.actual_graph_bounds.2
  linarith
#print axioms comparison0645
theorem comparison0646 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum941.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum942.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum942.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum941.actual_graph_bounds.2
  linarith
#print axioms comparison0646
theorem comparison0647 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1207.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1222.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1222.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum1207.actual_graph_bounds.2
  linarith
#print axioms comparison0647
theorem comparison0648 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1410.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1420.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1420.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum1410.actual_graph_bounds.2
  linarith
#print axioms comparison0648
theorem comparison0649 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1013.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1019.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1019.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum1013.actual_graph_bounds.2
  linarith
#print axioms comparison0649
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteComparisons
