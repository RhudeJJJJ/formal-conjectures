/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum093
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum097
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum098
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1011
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1015
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1017
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1021
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum107
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum108
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1084
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1088
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1460
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum147
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1472
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1475
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum148
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1482
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1485
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1487
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1497
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum154
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1552
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum156
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum157
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum158
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1584
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum159
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1636
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1653
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1721
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum219
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum220
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum238
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum239
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum248
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum249
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum252
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum253
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum269
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum270
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum342
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum343
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum399
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum405
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum406
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum428
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum566
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum567
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum570
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum571
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum615
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum617
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum638
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum640
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum647
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum649
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum680
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum683
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum795
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum796
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum945
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum946
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum947
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum952
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum981
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum985
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum988
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum992
import Proofs.RadenkovicGutmanSmallGeFourSpectrum015
import Proofs.RadenkovicGutmanSmallGeFourSpectrum017
import Proofs.RadenkovicGutmanSmallGeFourSpectrum023
import Proofs.RadenkovicGutmanSmallGeFourSpectrum028
import Proofs.RadenkovicGutmanSmallGeFourSpectrum039
import Proofs.RadenkovicGutmanSmallGeFourSpectrum043
import Proofs.RadenkovicGutmanSmallGeFourSpectrum044
import Proofs.RadenkovicGutmanSmallGeFourSpectrum066
import Proofs.RadenkovicGutmanSmallGeFourSpectrum093
import Proofs.RadenkovicGutmanSmallGeFourSpectrum109
import Proofs.RadenkovicGutmanSmallGeFourSpectrum110
import Proofs.RadenkovicGutmanSmallGeFourSpectrum125
import Proofs.RadenkovicGutmanSmallGeFourSpectrum128
import Proofs.RadenkovicGutmanSmallGeFourSpectrum177
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallComparisons
set_option maxHeartbeats 0
theorem comparison0650 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum945.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1460.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1460.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum945.actual_graph_bounds.2
  linarith
#print axioms comparison0650
theorem comparison0651 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum147.graph) (2-2/10) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum107.graph) (2-2/10) := by
  have hs := DegreeOneSmallSpectrum107.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum147.actual_graph_bounds.2
  linarith
#print axioms comparison0651
theorem comparison0652 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum219.graph) (2-2/11) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum342.graph) (2-2/11) := by
  have hs := DegreeOneSmallSpectrum342.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum219.actual_graph_bounds.2
  linarith
#print axioms comparison0652
theorem comparison0653 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum567.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum566.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum566.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum567.actual_graph_bounds.2
  linarith
#print axioms comparison0653
theorem comparison0654 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum946.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1475.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1475.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum946.actual_graph_bounds.2
  linarith
#print axioms comparison0654
theorem comparison0655 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum567.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum795.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum795.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum567.actual_graph_bounds.2
  linarith
#print axioms comparison0655
theorem comparison0656 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum946.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1472.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1472.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum946.actual_graph_bounds.2
  linarith
#print axioms comparison0656
theorem comparison0657 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum148.graph) (2-2/10) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum108.graph) (2-2/10) := by
  have hs := DegreeOneSmallSpectrum108.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum148.actual_graph_bounds.2
  linarith
#print axioms comparison0657
theorem comparison0658 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum220.graph) (2-2/11) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum343.graph) (2-2/11) := by
  have hs := DegreeOneSmallSpectrum343.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum220.actual_graph_bounds.2
  linarith
#print axioms comparison0658
theorem comparison0659 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum571.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum570.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum570.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum571.actual_graph_bounds.2
  linarith
#print axioms comparison0659
theorem comparison0660 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum947.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1485.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1485.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum947.actual_graph_bounds.2
  linarith
#print axioms comparison0660
theorem comparison0661 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum571.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum796.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum796.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum571.actual_graph_bounds.2
  linarith
#print axioms comparison0661
theorem comparison0662 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum947.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1482.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1482.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum947.actual_graph_bounds.2
  linarith
#print axioms comparison0662
theorem comparison0663 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum023.graph) (2-2/10) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum017.graph) (2-2/10) := by
  have hs := SmallGeFourSpectrum017.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum023.actual_graph_bounds.2
  linarith
#print axioms comparison0663
theorem comparison0664 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum039.graph) (2-2/11) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum066.graph) (2-2/11) := by
  have hs := SmallGeFourSpectrum066.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum039.actual_graph_bounds.2
  linarith
#print axioms comparison0664
theorem comparison0665 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum110.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum109.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum109.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum110.actual_graph_bounds.2
  linarith
#print axioms comparison0665
theorem comparison0666 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum952.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1497.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1497.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum952.actual_graph_bounds.2
  linarith
#print axioms comparison0666
theorem comparison0667 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum110.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum177.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum177.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum110.actual_graph_bounds.2
  linarith
#print axioms comparison0667
theorem comparison0668 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum952.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1487.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1487.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum952.actual_graph_bounds.2
  linarith
#print axioms comparison0668
theorem comparison0669 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum015.graph) (2-2/10) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum028.graph) (2-2/10) := by
  have hs := SmallGeFourSpectrum028.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum015.actual_graph_bounds.2
  linarith
#print axioms comparison0669
theorem comparison0670 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum044.graph) (2-2/11) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum043.graph) (2-2/11) := by
  have hs := SmallGeFourSpectrum043.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum044.actual_graph_bounds.2
  linarith
#print axioms comparison0670
theorem comparison0671 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum093.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum128.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum128.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum093.actual_graph_bounds.2
  linarith
#print axioms comparison0671
theorem comparison0672 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum985.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum981.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum981.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum985.actual_graph_bounds.2
  linarith
#print axioms comparison0672
theorem comparison0673 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum093.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum125.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum125.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum093.actual_graph_bounds.2
  linarith
#print axioms comparison0673
theorem comparison0674 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum985.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1552.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1552.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum985.actual_graph_bounds.2
  linarith
#print axioms comparison0674
theorem comparison0675 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum093.graph) (2-2/10) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum154.graph) (2-2/10) := by
  have hs := DegreeOneSmallSpectrum154.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum093.actual_graph_bounds.2
  linarith
#print axioms comparison0675
theorem comparison0676 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum239.graph) (2-2/11) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum238.graph) (2-2/11) := by
  have hs := DegreeOneSmallSpectrum238.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum239.actual_graph_bounds.2
  linarith
#print axioms comparison0676
theorem comparison0677 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum399.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum617.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum617.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum399.actual_graph_bounds.2
  linarith
#print axioms comparison0677
theorem comparison0678 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum992.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum988.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum988.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum992.actual_graph_bounds.2
  linarith
#print axioms comparison0678
theorem comparison0679 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum399.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum615.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum615.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum399.actual_graph_bounds.2
  linarith
#print axioms comparison0679
theorem comparison0680 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum992.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1584.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1584.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum992.actual_graph_bounds.2
  linarith
#print axioms comparison0680
theorem comparison0681 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum097.graph) (2-2/10) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum156.graph) (2-2/10) := by
  have hs := DegreeOneSmallSpectrum156.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum097.actual_graph_bounds.2
  linarith
#print axioms comparison0681
theorem comparison0682 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum249.graph) (2-2/11) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum248.graph) (2-2/11) := by
  have hs := DegreeOneSmallSpectrum248.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum249.actual_graph_bounds.2
  linarith
#print axioms comparison0682
theorem comparison0683 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum405.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum640.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum640.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum405.actual_graph_bounds.2
  linarith
#print axioms comparison0683
theorem comparison0684 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1015.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1011.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1011.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum1015.actual_graph_bounds.2
  linarith
#print axioms comparison0684
theorem comparison0685 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum405.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum638.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum638.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum405.actual_graph_bounds.2
  linarith
#print axioms comparison0685
theorem comparison0686 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1015.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1636.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1636.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum1015.actual_graph_bounds.2
  linarith
#print axioms comparison0686
theorem comparison0687 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum098.graph) (2-2/10) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum157.graph) (2-2/10) := by
  have hs := DegreeOneSmallSpectrum157.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum098.actual_graph_bounds.2
  linarith
#print axioms comparison0687
theorem comparison0688 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum253.graph) (2-2/11) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum252.graph) (2-2/11) := by
  have hs := DegreeOneSmallSpectrum252.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum253.actual_graph_bounds.2
  linarith
#print axioms comparison0688
theorem comparison0689 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum406.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum649.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum649.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum406.actual_graph_bounds.2
  linarith
#print axioms comparison0689
theorem comparison0690 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1021.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1017.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1017.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum1021.actual_graph_bounds.2
  linarith
#print axioms comparison0690
theorem comparison0691 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum406.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum647.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum647.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum406.actual_graph_bounds.2
  linarith
#print axioms comparison0691
theorem comparison0692 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1021.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1653.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1653.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum1021.actual_graph_bounds.2
  linarith
#print axioms comparison0692
theorem comparison0693 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum107.graph) (2-2/10) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum158.graph) (2-2/10) := by
  have hs := DegreeOneSmallSpectrum158.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum107.actual_graph_bounds.2
  linarith
#print axioms comparison0693
theorem comparison0694 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum270.graph) (2-2/11) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum269.graph) (2-2/11) := by
  have hs := DegreeOneSmallSpectrum269.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum270.actual_graph_bounds.2
  linarith
#print axioms comparison0694
theorem comparison0695 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum428.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum683.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum683.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum428.actual_graph_bounds.2
  linarith
#print axioms comparison0695
theorem comparison0696 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1088.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1084.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1084.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum1088.actual_graph_bounds.2
  linarith
#print axioms comparison0696
theorem comparison0697 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum428.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum680.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum680.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum428.actual_graph_bounds.2
  linarith
#print axioms comparison0697
theorem comparison0698 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1088.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1721.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1721.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum1088.actual_graph_bounds.2
  linarith
#print axioms comparison0698
theorem comparison0699 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum108.graph) (2-2/10) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum159.graph) (2-2/10) := by
  have hs := DegreeOneSmallSpectrum159.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum108.actual_graph_bounds.2
  linarith
#print axioms comparison0699
end Gebendorfer.RadenkovicGutman.DegreeOneSmallComparisons
