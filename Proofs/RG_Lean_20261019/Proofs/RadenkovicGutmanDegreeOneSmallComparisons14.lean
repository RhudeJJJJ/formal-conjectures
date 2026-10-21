/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1091
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1095
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1114
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1118
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1293
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1296
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1298
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum130
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1301
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1350
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1353
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1522
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1526
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum160
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum161
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum164
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum165
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum166
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum168
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1753
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1792
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum189
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1896
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1906
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum193
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1938
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum196
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum274
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum275
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum284
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum317
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum318
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum369
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum375
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum378
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum383
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum384
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum386
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum392
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum429
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum500
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum694
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum697
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum715
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum718
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum775
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum777
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum856
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum857
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum858
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum861
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum896
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum904
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum912
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum915
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum940
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum962
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum979
import Proofs.RadenkovicGutmanSmallGeFourSpectrum017
import Proofs.RadenkovicGutmanSmallGeFourSpectrum019
import Proofs.RadenkovicGutmanSmallGeFourSpectrum020
import Proofs.RadenkovicGutmanSmallGeFourSpectrum025
import Proofs.RadenkovicGutmanSmallGeFourSpectrum026
import Proofs.RadenkovicGutmanSmallGeFourSpectrum031
import Proofs.RadenkovicGutmanSmallGeFourSpectrum032
import Proofs.RadenkovicGutmanSmallGeFourSpectrum040
import Proofs.RadenkovicGutmanSmallGeFourSpectrum049
import Proofs.RadenkovicGutmanSmallGeFourSpectrum057
import Proofs.RadenkovicGutmanSmallGeFourSpectrum058
import Proofs.RadenkovicGutmanSmallGeFourSpectrum061
import Proofs.RadenkovicGutmanSmallGeFourSpectrum062
import Proofs.RadenkovicGutmanSmallGeFourSpectrum074
import Proofs.RadenkovicGutmanSmallGeFourSpectrum095
import Proofs.RadenkovicGutmanSmallGeFourSpectrum099
import Proofs.RadenkovicGutmanSmallGeFourSpectrum100
import Proofs.RadenkovicGutmanSmallGeFourSpectrum113
import Proofs.RadenkovicGutmanSmallGeFourSpectrum116
import Proofs.RadenkovicGutmanSmallGeFourSpectrum170
import Proofs.RadenkovicGutmanSmallGeFourSpectrum173
import Proofs.RadenkovicGutmanSmallGeFourSpectrum175
import Proofs.RadenkovicGutmanSmallGeFourSpectrum183
import Proofs.RadenkovicGutmanSmallGeFourSpectrum206
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallComparisons
set_option maxHeartbeats 0
theorem comparison0700 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum275.graph) (2-2/11) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum274.graph) (2-2/11) := by
  have hs := DegreeOneSmallSpectrum274.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum275.actual_graph_bounds.2
  linarith
#print axioms comparison0700
theorem comparison0701 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum429.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum697.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum697.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum429.actual_graph_bounds.2
  linarith
#print axioms comparison0701
theorem comparison0702 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1095.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1091.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1091.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum1095.actual_graph_bounds.2
  linarith
#print axioms comparison0702
theorem comparison0703 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum429.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum694.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum694.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum429.actual_graph_bounds.2
  linarith
#print axioms comparison0703
theorem comparison0704 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1095.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1753.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1753.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum1095.actual_graph_bounds.2
  linarith
#print axioms comparison0704
theorem comparison0705 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum017.graph) (2-2/10) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum160.graph) (2-2/10) := by
  have hs := DegreeOneSmallSpectrum160.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum017.actual_graph_bounds.2
  linarith
#print axioms comparison0705
theorem comparison0706 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum049.graph) (2-2/11) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum284.graph) (2-2/11) := by
  have hs := DegreeOneSmallSpectrum284.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum049.actual_graph_bounds.2
  linarith
#print axioms comparison0706
theorem comparison0707 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum095.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum718.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum718.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum095.actual_graph_bounds.2
  linarith
#print axioms comparison0707
theorem comparison0708 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1118.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1114.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1114.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum1118.actual_graph_bounds.2
  linarith
#print axioms comparison0708
theorem comparison0709 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum095.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum715.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum715.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum095.actual_graph_bounds.2
  linarith
#print axioms comparison0709
theorem comparison0710 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1118.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1792.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1792.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum1118.actual_graph_bounds.2
  linarith
#print axioms comparison0710
theorem comparison0711 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum130.graph) (2-2/10) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum161.graph) (2-2/10) := by
  have hs := DegreeOneSmallSpectrum161.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum130.actual_graph_bounds.2
  linarith
#print axioms comparison0711
theorem comparison0712 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum318.graph) (2-2/11) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum317.graph) (2-2/11) := by
  have hs := DegreeOneSmallSpectrum317.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum318.actual_graph_bounds.2
  linarith
#print axioms comparison0712
theorem comparison0713 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum500.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum777.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum777.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum500.actual_graph_bounds.2
  linarith
#print axioms comparison0713
theorem comparison0714 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1296.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1293.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1293.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum1296.actual_graph_bounds.2
  linarith
#print axioms comparison0714
theorem comparison0715 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum500.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum775.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum775.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum500.actual_graph_bounds.2
  linarith
#print axioms comparison0715
theorem comparison0716 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1296.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1896.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1896.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum1296.actual_graph_bounds.2
  linarith
#print axioms comparison0716
theorem comparison0717 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum019.graph) (2-2/10) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum031.graph) (2-2/10) := by
  have hs := SmallGeFourSpectrum031.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum019.actual_graph_bounds.2
  linarith
#print axioms comparison0717
theorem comparison0718 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum058.graph) (2-2/11) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum057.graph) (2-2/11) := by
  have hs := SmallGeFourSpectrum057.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum058.actual_graph_bounds.2
  linarith
#print axioms comparison0718
theorem comparison0719 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum099.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum173.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum173.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum099.actual_graph_bounds.2
  linarith
#print axioms comparison0719
theorem comparison0720 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1301.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1298.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1298.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum1301.actual_graph_bounds.2
  linarith
#print axioms comparison0720
theorem comparison0721 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum099.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum170.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum170.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum099.actual_graph_bounds.2
  linarith
#print axioms comparison0721
theorem comparison0722 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1301.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1906.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1906.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum1301.actual_graph_bounds.2
  linarith
#print axioms comparison0722
theorem comparison0723 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum020.graph) (2-2/10) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum032.graph) (2-2/10) := by
  have hs := SmallGeFourSpectrum032.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum020.actual_graph_bounds.2
  linarith
#print axioms comparison0723
theorem comparison0724 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum062.graph) (2-2/11) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum061.graph) (2-2/11) := by
  have hs := SmallGeFourSpectrum061.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum062.actual_graph_bounds.2
  linarith
#print axioms comparison0724
theorem comparison0725 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum100.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum183.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum183.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum100.actual_graph_bounds.2
  linarith
#print axioms comparison0725
theorem comparison0726 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1353.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1350.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1350.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum1353.actual_graph_bounds.2
  linarith
#print axioms comparison0726
theorem comparison0727 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum100.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum175.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum175.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum100.actual_graph_bounds.2
  linarith
#print axioms comparison0727
theorem comparison0728 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1353.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1938.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1938.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum1353.actual_graph_bounds.2
  linarith
#print axioms comparison0728
theorem comparison0729 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum026.graph) (2-2/10) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum025.graph) (2-2/10) := by
  have hs := SmallGeFourSpectrum025.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum026.actual_graph_bounds.2
  linarith
#print axioms comparison0729
theorem comparison0730 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum040.graph) (2-2/11) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum074.graph) (2-2/11) := by
  have hs := SmallGeFourSpectrum074.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum040.actual_graph_bounds.2
  linarith
#print axioms comparison0730
theorem comparison0731 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum116.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum113.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum113.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum116.actual_graph_bounds.2
  linarith
#print axioms comparison0731
theorem comparison0732 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum979.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1526.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1526.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum979.actual_graph_bounds.2
  linarith
#print axioms comparison0732
theorem comparison0733 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum116.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum206.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum206.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum116.actual_graph_bounds.2
  linarith
#print axioms comparison0733
theorem comparison0734 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum979.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1522.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1522.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum979.actual_graph_bounds.2
  linarith
#print axioms comparison0734
theorem comparison0735 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum168.graph) (2-2/11) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum164.graph) (2-2/11) := by
  have hs := DegreeOneSmallSpectrum164.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum168.actual_graph_bounds.2
  linarith
#print axioms comparison0735
theorem comparison0736 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum369.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum386.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum386.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum369.actual_graph_bounds.2
  linarith
#print axioms comparison0736
theorem comparison0737 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum861.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum858.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum858.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum861.actual_graph_bounds.2
  linarith
#print axioms comparison0737
theorem comparison0738 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum861.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum915.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum915.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum861.actual_graph_bounds.2
  linarith
#print axioms comparison0738
theorem comparison0739 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum164.graph) (2-2/11) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum189.graph) (2-2/11) := by
  have hs := DegreeOneSmallSpectrum189.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum164.actual_graph_bounds.2
  linarith
#print axioms comparison0739
theorem comparison0740 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum378.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum375.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum375.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum378.actual_graph_bounds.2
  linarith
#print axioms comparison0740
theorem comparison0741 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum856.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum904.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum904.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum856.actual_graph_bounds.2
  linarith
#print axioms comparison0741
theorem comparison0742 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum856.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum896.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum896.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum856.actual_graph_bounds.2
  linarith
#print axioms comparison0742
theorem comparison0743 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum165.graph) (2-2/11) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum193.graph) (2-2/11) := by
  have hs := DegreeOneSmallSpectrum193.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum165.actual_graph_bounds.2
  linarith
#print axioms comparison0743
theorem comparison0744 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum386.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum383.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum383.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum386.actual_graph_bounds.2
  linarith
#print axioms comparison0744
theorem comparison0745 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum857.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum940.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum940.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum857.actual_graph_bounds.2
  linarith
#print axioms comparison0745
theorem comparison0746 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum857.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum912.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum912.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum857.actual_graph_bounds.2
  linarith
#print axioms comparison0746
theorem comparison0747 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum166.graph) (2-2/11) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum196.graph) (2-2/11) := by
  have hs := DegreeOneSmallSpectrum196.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum166.actual_graph_bounds.2
  linarith
#print axioms comparison0747
theorem comparison0748 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum392.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum384.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum384.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum392.actual_graph_bounds.2
  linarith
#print axioms comparison0748
theorem comparison0749 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum858.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum962.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum962.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum858.actual_graph_bounds.2
  linarith
#print axioms comparison0749
end Gebendorfer.RadenkovicGutman.DegreeOneSmallComparisons
