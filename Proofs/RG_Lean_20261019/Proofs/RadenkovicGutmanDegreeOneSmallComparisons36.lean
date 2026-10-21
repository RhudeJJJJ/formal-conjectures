/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1001
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1030
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1052
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1063
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1066
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1067
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1104
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1127
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1150
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1159
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1162
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1163
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1166
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1169
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1203
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1218
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1227
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1228
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1231
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1234
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1237
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1248
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1249
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1253
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1256
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1257
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1260
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1263
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1264
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1268
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1270
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1271
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum862
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum863
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum864
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum865
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum868
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum869
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum871
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum872
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum873
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum874
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum877
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum878
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum880
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum881
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum882
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum885
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum886
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum888
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum889
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum892
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum893
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum901
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum902
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum903
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum905
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum906
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum909
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum910
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum911
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum913
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum914
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum916
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum917
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum918
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum920
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum921
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum923
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum924
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum925
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum928
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum951
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum956
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum961
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum965
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum966
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum971
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum974
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum976
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum977
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum978
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallComparisons
set_option maxHeartbeats 0
theorem comparison1800 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum965.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum878.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum878.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum965.actual_graph_bounds.2
  linarith
#print axioms comparison1800
theorem comparison1801 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum977.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum888.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum888.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum977.actual_graph_bounds.2
  linarith
#print axioms comparison1801
theorem comparison1802 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum978.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum889.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum889.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum978.actual_graph_bounds.2
  linarith
#print axioms comparison1802
theorem comparison1803 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum976.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum882.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum882.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum976.actual_graph_bounds.2
  linarith
#print axioms comparison1803
theorem comparison1804 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum966.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum874.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum874.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum966.actual_graph_bounds.2
  linarith
#print axioms comparison1804
theorem comparison1805 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum971.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum880.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum880.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum971.actual_graph_bounds.2
  linarith
#print axioms comparison1805
theorem comparison1806 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum974.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum881.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum881.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum974.actual_graph_bounds.2
  linarith
#print axioms comparison1806
theorem comparison1807 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum961.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum873.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum873.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum961.actual_graph_bounds.2
  linarith
#print axioms comparison1807
theorem comparison1808 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum951.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum871.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum871.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum951.actual_graph_bounds.2
  linarith
#print axioms comparison1808
theorem comparison1809 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum956.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum872.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum872.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum956.actual_graph_bounds.2
  linarith
#print axioms comparison1809
theorem comparison1810 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum862.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1001.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1001.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum862.actual_graph_bounds.2
  linarith
#print axioms comparison1810
theorem comparison1811 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum863.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1030.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1030.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum863.actual_graph_bounds.2
  linarith
#print axioms comparison1811
theorem comparison1812 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum864.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1052.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1052.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum864.actual_graph_bounds.2
  linarith
#print axioms comparison1812
theorem comparison1813 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum865.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1067.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1067.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum865.actual_graph_bounds.2
  linarith
#print axioms comparison1813
theorem comparison1814 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum869.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1066.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1066.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum869.actual_graph_bounds.2
  linarith
#print axioms comparison1814
theorem comparison1815 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum868.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1063.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1063.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum868.actual_graph_bounds.2
  linarith
#print axioms comparison1815
theorem comparison1816 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum871.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1104.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1104.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum871.actual_graph_bounds.2
  linarith
#print axioms comparison1816
theorem comparison1817 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum872.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1127.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1127.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum872.actual_graph_bounds.2
  linarith
#print axioms comparison1817
theorem comparison1818 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum873.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1150.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1150.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum873.actual_graph_bounds.2
  linarith
#print axioms comparison1818
theorem comparison1819 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum874.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1163.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1163.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum874.actual_graph_bounds.2
  linarith
#print axioms comparison1819
theorem comparison1820 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum878.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1162.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1162.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum878.actual_graph_bounds.2
  linarith
#print axioms comparison1820
theorem comparison1821 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum877.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1159.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1159.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum877.actual_graph_bounds.2
  linarith
#print axioms comparison1821
theorem comparison1822 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum880.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1203.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1203.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum880.actual_graph_bounds.2
  linarith
#print axioms comparison1822
theorem comparison1823 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum881.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1218.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1218.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum881.actual_graph_bounds.2
  linarith
#print axioms comparison1823
theorem comparison1824 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum882.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1228.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1228.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum882.actual_graph_bounds.2
  linarith
#print axioms comparison1824
theorem comparison1825 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum886.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1227.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1227.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum886.actual_graph_bounds.2
  linarith
#print axioms comparison1825
theorem comparison1826 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum885.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1162.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1162.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum885.actual_graph_bounds.2
  linarith
#print axioms comparison1826
theorem comparison1827 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum888.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1248.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1248.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum888.actual_graph_bounds.2
  linarith
#print axioms comparison1827
theorem comparison1828 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum889.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1249.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1249.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum889.actual_graph_bounds.2
  linarith
#print axioms comparison1828
theorem comparison1829 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum893.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1228.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1228.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum893.actual_graph_bounds.2
  linarith
#print axioms comparison1829
theorem comparison1830 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum892.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1163.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1163.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum892.actual_graph_bounds.2
  linarith
#print axioms comparison1830
theorem comparison1831 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum905.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1203.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1203.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum905.actual_graph_bounds.2
  linarith
#print axioms comparison1831
theorem comparison1832 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum906.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1218.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1218.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum906.actual_graph_bounds.2
  linarith
#print axioms comparison1832
theorem comparison1833 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum903.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1150.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1150.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum903.actual_graph_bounds.2
  linarith
#print axioms comparison1833
theorem comparison1834 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum901.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1104.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1104.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum901.actual_graph_bounds.2
  linarith
#print axioms comparison1834
theorem comparison1835 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum902.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1127.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1127.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum902.actual_graph_bounds.2
  linarith
#print axioms comparison1835
theorem comparison1836 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum909.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1253.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1253.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum909.actual_graph_bounds.2
  linarith
#print axioms comparison1836
theorem comparison1837 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum910.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1256.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1256.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum910.actual_graph_bounds.2
  linarith
#print axioms comparison1837
theorem comparison1838 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum911.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1257.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1257.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum911.actual_graph_bounds.2
  linarith
#print axioms comparison1838
theorem comparison1839 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum914.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1231.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1231.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum914.actual_graph_bounds.2
  linarith
#print axioms comparison1839
theorem comparison1840 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum913.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1166.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1166.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum913.actual_graph_bounds.2
  linarith
#print axioms comparison1840
theorem comparison1841 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum916.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1260.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1260.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum916.actual_graph_bounds.2
  linarith
#print axioms comparison1841
theorem comparison1842 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum917.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1263.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1263.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum917.actual_graph_bounds.2
  linarith
#print axioms comparison1842
theorem comparison1843 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum918.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1264.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1264.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum918.actual_graph_bounds.2
  linarith
#print axioms comparison1843
theorem comparison1844 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum921.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1234.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1234.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum921.actual_graph_bounds.2
  linarith
#print axioms comparison1844
theorem comparison1845 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum920.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1169.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1169.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum920.actual_graph_bounds.2
  linarith
#print axioms comparison1845
theorem comparison1846 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum923.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1268.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1268.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum923.actual_graph_bounds.2
  linarith
#print axioms comparison1846
theorem comparison1847 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum924.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1270.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1270.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum924.actual_graph_bounds.2
  linarith
#print axioms comparison1847
theorem comparison1848 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum925.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1271.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1271.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum925.actual_graph_bounds.2
  linarith
#print axioms comparison1848
theorem comparison1849 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum928.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1237.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1237.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum928.actual_graph_bounds.2
  linarith
#print axioms comparison1849
end Gebendorfer.RadenkovicGutman.DegreeOneSmallComparisons
