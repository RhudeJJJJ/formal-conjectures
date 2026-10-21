/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1069
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1166
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1231
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1256
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1257
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1332
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1335
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1338
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1339
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum166
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum167
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum172
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum175
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum179
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum180
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum182
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum185
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum186
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum188
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum190
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum191
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum192
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum196
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum197
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum202
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum207
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum212
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum216
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum217
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum370
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum371
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum372
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum373
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum377
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum379
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum380
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum381
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum382
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum385
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum396
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum397
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum423
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum453
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum475
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum489
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum490
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum514
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum530
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum546
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum551
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum858
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum859
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum860
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum868
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum870
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum877
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum879
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum885
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum887
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum892
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum894
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum903
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum908
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum910
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum911
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum913
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum914
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum915
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum920
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum922
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum927
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum929
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum933
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum935
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum961
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum965
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum966
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallComparisons
set_option maxHeartbeats 0
theorem comparison0750 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum858.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum913.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum913.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum858.actual_graph_bounds.2
  linarith
#print axioms comparison0750
theorem comparison0751 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum167.graph) (2-2/11) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum197.graph) (2-2/11) := by
  have hs := DegreeOneSmallSpectrum197.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum167.actual_graph_bounds.2
  linarith
#print axioms comparison0751
theorem comparison0752 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum396.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum385.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum385.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum396.actual_graph_bounds.2
  linarith
#print axioms comparison0752
theorem comparison0753 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum859.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum965.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum965.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum859.actual_graph_bounds.2
  linarith
#print axioms comparison0753
theorem comparison0754 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum859.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum914.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum914.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum859.actual_graph_bounds.2
  linarith
#print axioms comparison0754
theorem comparison0755 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum167.graph) (2-2/11) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum188.graph) (2-2/11) := by
  have hs := DegreeOneSmallSpectrum188.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum167.actual_graph_bounds.2
  linarith
#print axioms comparison0755
theorem comparison0756 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum397.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum382.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum382.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum397.actual_graph_bounds.2
  linarith
#print axioms comparison0756
theorem comparison0757 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum860.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum966.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum966.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum860.actual_graph_bounds.2
  linarith
#print axioms comparison0757
theorem comparison0758 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum860.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum911.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum911.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum860.actual_graph_bounds.2
  linarith
#print axioms comparison0758
theorem comparison0759 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum166.graph) (2-2/11) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum182.graph) (2-2/11) := by
  have hs := DegreeOneSmallSpectrum182.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum166.actual_graph_bounds.2
  linarith
#print axioms comparison0759
theorem comparison0760 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum396.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum381.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum381.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum396.actual_graph_bounds.2
  linarith
#print axioms comparison0760
theorem comparison0761 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum860.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum961.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum961.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum860.actual_graph_bounds.2
  linarith
#print axioms comparison0761
theorem comparison0762 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum860.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum910.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum910.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum860.actual_graph_bounds.2
  linarith
#print axioms comparison0762
theorem comparison0763 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum175.graph) (2-2/11) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum172.graph) (2-2/11) := by
  have hs := DegreeOneSmallSpectrum172.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum175.actual_graph_bounds.2
  linarith
#print axioms comparison0763
theorem comparison0764 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum370.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum423.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum423.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum370.actual_graph_bounds.2
  linarith
#print axioms comparison0764
theorem comparison0765 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum870.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum868.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum868.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum870.actual_graph_bounds.2
  linarith
#print axioms comparison0765
theorem comparison0766 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum870.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1069.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1069.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum870.actual_graph_bounds.2
  linarith
#print axioms comparison0766
theorem comparison0767 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum182.graph) (2-2/11) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum179.graph) (2-2/11) := by
  have hs := DegreeOneSmallSpectrum179.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum182.actual_graph_bounds.2
  linarith
#print axioms comparison0767
theorem comparison0768 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum371.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum453.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum453.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum371.actual_graph_bounds.2
  linarith
#print axioms comparison0768
theorem comparison0769 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum879.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum877.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum877.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum879.actual_graph_bounds.2
  linarith
#print axioms comparison0769
theorem comparison0770 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum879.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1166.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1166.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum879.actual_graph_bounds.2
  linarith
#print axioms comparison0770
theorem comparison0771 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum188.graph) (2-2/11) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum185.graph) (2-2/11) := by
  have hs := DegreeOneSmallSpectrum185.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum188.actual_graph_bounds.2
  linarith
#print axioms comparison0771
theorem comparison0772 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum372.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum475.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum475.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum372.actual_graph_bounds.2
  linarith
#print axioms comparison0772
theorem comparison0773 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum887.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum885.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum885.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum887.actual_graph_bounds.2
  linarith
#print axioms comparison0773
theorem comparison0774 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum887.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1231.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1231.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum887.actual_graph_bounds.2
  linarith
#print axioms comparison0774
theorem comparison0775 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum197.graph) (2-2/11) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum185.graph) (2-2/11) := by
  have hs := DegreeOneSmallSpectrum185.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum197.actual_graph_bounds.2
  linarith
#print axioms comparison0775
theorem comparison0776 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum373.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum490.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum490.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum373.actual_graph_bounds.2
  linarith
#print axioms comparison0776
theorem comparison0777 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum894.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum892.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum892.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum894.actual_graph_bounds.2
  linarith
#print axioms comparison0777
theorem comparison0778 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum894.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1257.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1257.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum894.actual_graph_bounds.2
  linarith
#print axioms comparison0778
theorem comparison0779 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum196.graph) (2-2/11) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum179.graph) (2-2/11) := by
  have hs := DegreeOneSmallSpectrum179.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum196.actual_graph_bounds.2
  linarith
#print axioms comparison0779
theorem comparison0780 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum377.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum489.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum489.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum377.actual_graph_bounds.2
  linarith
#print axioms comparison0780
theorem comparison0781 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum908.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum903.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum903.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum908.actual_graph_bounds.2
  linarith
#print axioms comparison0781
theorem comparison0782 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum908.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1256.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1256.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum908.actual_graph_bounds.2
  linarith
#print axioms comparison0782
theorem comparison0783 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum202.graph) (2-2/11) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum190.graph) (2-2/11) := by
  have hs := DegreeOneSmallSpectrum190.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum202.actual_graph_bounds.2
  linarith
#print axioms comparison0783
theorem comparison0784 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum379.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum514.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum514.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum379.actual_graph_bounds.2
  linarith
#print axioms comparison0784
theorem comparison0785 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum915.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum913.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum913.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum915.actual_graph_bounds.2
  linarith
#print axioms comparison0785
theorem comparison0786 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum915.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1332.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1332.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum915.actual_graph_bounds.2
  linarith
#print axioms comparison0786
theorem comparison0787 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum207.graph) (2-2/11) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum191.graph) (2-2/11) := by
  have hs := DegreeOneSmallSpectrum191.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum207.actual_graph_bounds.2
  linarith
#print axioms comparison0787
theorem comparison0788 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum380.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum530.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum530.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum380.actual_graph_bounds.2
  linarith
#print axioms comparison0788
theorem comparison0789 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum922.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum920.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum920.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum922.actual_graph_bounds.2
  linarith
#print axioms comparison0789
theorem comparison0790 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum922.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1335.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1335.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum922.actual_graph_bounds.2
  linarith
#print axioms comparison0790
theorem comparison0791 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum212.graph) (2-2/11) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum192.graph) (2-2/11) := by
  have hs := DegreeOneSmallSpectrum192.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum212.actual_graph_bounds.2
  linarith
#print axioms comparison0791
theorem comparison0792 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum381.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum546.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum546.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum381.actual_graph_bounds.2
  linarith
#print axioms comparison0792
theorem comparison0793 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum929.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum927.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum927.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum929.actual_graph_bounds.2
  linarith
#print axioms comparison0793
theorem comparison0794 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum929.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1338.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1338.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum929.actual_graph_bounds.2
  linarith
#print axioms comparison0794
theorem comparison0795 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum217.graph) (2-2/11) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum186.graph) (2-2/11) := by
  have hs := DegreeOneSmallSpectrum186.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum217.actual_graph_bounds.2
  linarith
#print axioms comparison0795
theorem comparison0796 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum382.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum551.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum551.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum382.actual_graph_bounds.2
  linarith
#print axioms comparison0796
theorem comparison0797 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum935.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum933.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum933.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum935.actual_graph_bounds.2
  linarith
#print axioms comparison0797
theorem comparison0798 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum935.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1339.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1339.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum935.actual_graph_bounds.2
  linarith
#print axioms comparison0798
theorem comparison0799 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum216.graph) (2-2/11) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum180.graph) (2-2/11) := by
  have hs := DegreeOneSmallSpectrum180.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum216.actual_graph_bounds.2
  linarith
#print axioms comparison0799
end Gebendorfer.RadenkovicGutman.DegreeOneSmallComparisons
