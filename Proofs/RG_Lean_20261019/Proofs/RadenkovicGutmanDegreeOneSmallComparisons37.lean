/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1101
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1108
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1111
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1112
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1124
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1131
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1134
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1135
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1142
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1147
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1154
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1157
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1158
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1172
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1173
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1177
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1179
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1180
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1181
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1182
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1189
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1195
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1201
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1207
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1210
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1211
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1216
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1222
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1225
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1226
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1238
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1242
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1244
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1245
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1246
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1247
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1272
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1273
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1275
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1278
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1281
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1282
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1284
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1285
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1286
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1287
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1288
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1289
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1290
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1291
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum927
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum930
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum931
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum933
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum934
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum937
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum938
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum939
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum941
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum942
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum945
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum946
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum947
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum948
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum949
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum950
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum952
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum953
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum954
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum955
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum957
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum958
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum959
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum960
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum963
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum964
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum967
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum968
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum969
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum970
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum972
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum973
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallComparisons
set_option maxHeartbeats 0
theorem comparison1850 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum927.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1172.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1172.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum927.actual_graph_bounds.2
  linarith
#print axioms comparison1850
theorem comparison1851 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum930.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1272.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1272.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum930.actual_graph_bounds.2
  linarith
#print axioms comparison1851
theorem comparison1852 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum931.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1273.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1273.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum931.actual_graph_bounds.2
  linarith
#print axioms comparison1852
theorem comparison1853 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum934.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1238.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1238.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum934.actual_graph_bounds.2
  linarith
#print axioms comparison1853
theorem comparison1854 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum933.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1173.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1173.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum933.actual_graph_bounds.2
  linarith
#print axioms comparison1854
theorem comparison1855 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum941.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1207.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1207.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum941.actual_graph_bounds.2
  linarith
#print axioms comparison1855
theorem comparison1856 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum942.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1222.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1222.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum942.actual_graph_bounds.2
  linarith
#print axioms comparison1856
theorem comparison1857 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum939.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1154.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1154.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum939.actual_graph_bounds.2
  linarith
#print axioms comparison1857
theorem comparison1858 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum937.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1108.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1108.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum937.actual_graph_bounds.2
  linarith
#print axioms comparison1858
theorem comparison1859 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum938.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1131.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1131.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum938.actual_graph_bounds.2
  linarith
#print axioms comparison1859
theorem comparison1860 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum945.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1275.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1275.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum945.actual_graph_bounds.2
  linarith
#print axioms comparison1860
theorem comparison1861 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum946.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1278.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1278.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum946.actual_graph_bounds.2
  linarith
#print axioms comparison1861
theorem comparison1862 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum947.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1281.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1281.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum947.actual_graph_bounds.2
  linarith
#print axioms comparison1862
theorem comparison1863 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum948.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1282.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1282.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum948.actual_graph_bounds.2
  linarith
#print axioms comparison1863
theorem comparison1864 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum950.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1242.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1242.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum950.actual_graph_bounds.2
  linarith
#print axioms comparison1864
theorem comparison1865 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum949.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1177.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1177.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum949.actual_graph_bounds.2
  linarith
#print axioms comparison1865
theorem comparison1866 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum952.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1284.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1284.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum952.actual_graph_bounds.2
  linarith
#print axioms comparison1866
theorem comparison1867 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum953.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1285.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1285.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum953.actual_graph_bounds.2
  linarith
#print axioms comparison1867
theorem comparison1868 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum955.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1244.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1244.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum955.actual_graph_bounds.2
  linarith
#print axioms comparison1868
theorem comparison1869 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum954.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1179.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1179.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum954.actual_graph_bounds.2
  linarith
#print axioms comparison1869
theorem comparison1870 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum957.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1286.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1286.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum957.actual_graph_bounds.2
  linarith
#print axioms comparison1870
theorem comparison1871 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum958.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1287.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1287.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum958.actual_graph_bounds.2
  linarith
#print axioms comparison1871
theorem comparison1872 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum960.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1245.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1245.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum960.actual_graph_bounds.2
  linarith
#print axioms comparison1872
theorem comparison1873 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum959.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1180.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1180.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum959.actual_graph_bounds.2
  linarith
#print axioms comparison1873
theorem comparison1874 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum963.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1210.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1210.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum963.actual_graph_bounds.2
  linarith
#print axioms comparison1874
theorem comparison1875 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum964.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1225.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1225.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum964.actual_graph_bounds.2
  linarith
#print axioms comparison1875
theorem comparison1876 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum959.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1157.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1157.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum959.actual_graph_bounds.2
  linarith
#print axioms comparison1876
theorem comparison1877 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum949.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1111.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1111.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum949.actual_graph_bounds.2
  linarith
#print axioms comparison1877
theorem comparison1878 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum954.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1134.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1134.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum954.actual_graph_bounds.2
  linarith
#print axioms comparison1878
theorem comparison1879 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum967.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1288.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1288.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum967.actual_graph_bounds.2
  linarith
#print axioms comparison1879
theorem comparison1880 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum968.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1289.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1289.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum968.actual_graph_bounds.2
  linarith
#print axioms comparison1880
theorem comparison1881 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum969.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1290.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1290.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum969.actual_graph_bounds.2
  linarith
#print axioms comparison1881
theorem comparison1882 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum970.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1246.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1246.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum970.actual_graph_bounds.2
  linarith
#print axioms comparison1882
theorem comparison1883 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum963.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1181.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1181.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum963.actual_graph_bounds.2
  linarith
#print axioms comparison1883
theorem comparison1884 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum972.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1291.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1291.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum972.actual_graph_bounds.2
  linarith
#print axioms comparison1884
theorem comparison1885 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum973.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1247.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1247.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum973.actual_graph_bounds.2
  linarith
#print axioms comparison1885
theorem comparison1886 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum964.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1182.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1182.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum964.actual_graph_bounds.2
  linarith
#print axioms comparison1886
theorem comparison1887 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum970.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1211.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1211.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum970.actual_graph_bounds.2
  linarith
#print axioms comparison1887
theorem comparison1888 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum973.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1226.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1226.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum973.actual_graph_bounds.2
  linarith
#print axioms comparison1888
theorem comparison1889 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum960.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1158.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1158.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum960.actual_graph_bounds.2
  linarith
#print axioms comparison1889
theorem comparison1890 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum950.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1112.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1112.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum950.actual_graph_bounds.2
  linarith
#print axioms comparison1890
theorem comparison1891 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum955.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1135.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1135.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum955.actual_graph_bounds.2
  linarith
#print axioms comparison1891
theorem comparison1892 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum967.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1189.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1189.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum967.actual_graph_bounds.2
  linarith
#print axioms comparison1892
theorem comparison1893 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum968.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1195.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1195.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum968.actual_graph_bounds.2
  linarith
#print axioms comparison1893
theorem comparison1894 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum969.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1201.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1201.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum969.actual_graph_bounds.2
  linarith
#print axioms comparison1894
theorem comparison1895 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum957.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1142.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1142.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum957.actual_graph_bounds.2
  linarith
#print axioms comparison1895
theorem comparison1896 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum972.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1216.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1216.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum972.actual_graph_bounds.2
  linarith
#print axioms comparison1896
theorem comparison1897 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum958.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1147.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1147.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum958.actual_graph_bounds.2
  linarith
#print axioms comparison1897
theorem comparison1898 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum948.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1101.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1101.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum948.actual_graph_bounds.2
  linarith
#print axioms comparison1898
theorem comparison1899 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum953.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1124.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1124.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum953.actual_graph_bounds.2
  linarith
#print axioms comparison1899
end Gebendorfer.RadenkovicGutman.DegreeOneSmallComparisons
