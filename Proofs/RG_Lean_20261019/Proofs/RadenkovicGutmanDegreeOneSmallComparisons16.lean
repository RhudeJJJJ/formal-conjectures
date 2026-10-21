/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1002
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1007
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1031
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1036
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1058
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1319
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1323
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1327
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1330
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1331
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1343
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1345
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1346
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1347
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1348
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum170
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum171
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum176
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum177
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum178
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum181
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum183
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum184
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum187
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum194
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum195
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum222
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum225
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum226
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum227
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum228
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum229
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum241
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum255
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum262
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum385
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum387
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum388
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum389
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum391
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum393
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum394
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum395
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum402
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum409
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum411
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum415
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum417
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum540
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum544
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum546
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum549
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum550
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum555
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum557
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum558
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum559
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum560
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum862
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum863
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum864
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum939
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum944
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum949
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum951
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum954
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum956
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum957
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum958
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum959
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum960
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum961
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum963
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum964
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum966
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum971
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum974
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum976
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum977
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum978
import Proofs.RadenkovicGutmanSmallGeFourSpectrum037
import Proofs.RadenkovicGutmanSmallGeFourSpectrum094
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallComparisons
set_option maxHeartbeats 0
theorem comparison0800 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum385.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum546.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum546.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum385.actual_graph_bounds.2
  linarith
#print axioms comparison0800
theorem comparison0801 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum944.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum939.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum939.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum944.actual_graph_bounds.2
  linarith
#print axioms comparison0801
theorem comparison0802 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum944.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1327.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1327.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum944.actual_graph_bounds.2
  linarith
#print axioms comparison0802
theorem comparison0803 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum222.graph) (2-2/11) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum194.graph) (2-2/11) := by
  have hs := DegreeOneSmallSpectrum194.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum222.actual_graph_bounds.2
  linarith
#print axioms comparison0803
theorem comparison0804 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum387.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum555.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum555.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum387.actual_graph_bounds.2
  linarith
#print axioms comparison0804
theorem comparison0805 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum951.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum949.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum949.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum951.actual_graph_bounds.2
  linarith
#print axioms comparison0805
theorem comparison0806 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum951.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1343.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1343.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum951.actual_graph_bounds.2
  linarith
#print axioms comparison0806
theorem comparison0807 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum225.graph) (2-2/11) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum195.graph) (2-2/11) := by
  have hs := DegreeOneSmallSpectrum195.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum225.actual_graph_bounds.2
  linarith
#print axioms comparison0807
theorem comparison0808 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum388.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum557.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum557.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum388.actual_graph_bounds.2
  linarith
#print axioms comparison0808
theorem comparison0809 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum956.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum954.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum954.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum956.actual_graph_bounds.2
  linarith
#print axioms comparison0809
theorem comparison0810 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum956.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1345.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1345.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum956.actual_graph_bounds.2
  linarith
#print axioms comparison0810
theorem comparison0811 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum227.graph) (2-2/11) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum187.graph) (2-2/11) := by
  have hs := DegreeOneSmallSpectrum187.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum227.actual_graph_bounds.2
  linarith
#print axioms comparison0811
theorem comparison0812 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum389.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum558.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum558.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum389.actual_graph_bounds.2
  linarith
#print axioms comparison0812
theorem comparison0813 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum961.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum959.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum959.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum961.actual_graph_bounds.2
  linarith
#print axioms comparison0813
theorem comparison0814 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum961.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1346.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1346.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum961.actual_graph_bounds.2
  linarith
#print axioms comparison0814
theorem comparison0815 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum226.graph) (2-2/11) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum181.graph) (2-2/11) := by
  have hs := DegreeOneSmallSpectrum181.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum226.actual_graph_bounds.2
  linarith
#print axioms comparison0815
theorem comparison0816 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum391.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum549.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum549.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum391.actual_graph_bounds.2
  linarith
#print axioms comparison0816
theorem comparison0817 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum966.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum959.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum959.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum966.actual_graph_bounds.2
  linarith
#print axioms comparison0817
theorem comparison0818 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum966.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1330.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1330.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum966.actual_graph_bounds.2
  linarith
#print axioms comparison0818
theorem comparison0819 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum228.graph) (2-2/11) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum183.graph) (2-2/11) := by
  have hs := DegreeOneSmallSpectrum183.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum228.actual_graph_bounds.2
  linarith
#print axioms comparison0819
theorem comparison0820 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum393.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum559.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum559.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum393.actual_graph_bounds.2
  linarith
#print axioms comparison0820
theorem comparison0821 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum971.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum963.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum963.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum971.actual_graph_bounds.2
  linarith
#print axioms comparison0821
theorem comparison0822 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum971.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1347.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1347.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum971.actual_graph_bounds.2
  linarith
#print axioms comparison0822
theorem comparison0823 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum229.graph) (2-2/11) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum184.graph) (2-2/11) := by
  have hs := DegreeOneSmallSpectrum184.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum229.actual_graph_bounds.2
  linarith
#print axioms comparison0823
theorem comparison0824 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum394.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum560.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum560.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum394.actual_graph_bounds.2
  linarith
#print axioms comparison0824
theorem comparison0825 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum974.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum964.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum964.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum974.actual_graph_bounds.2
  linarith
#print axioms comparison0825
theorem comparison0826 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum974.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1348.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1348.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum974.actual_graph_bounds.2
  linarith
#print axioms comparison0826
theorem comparison0827 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum227.graph) (2-2/11) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum178.graph) (2-2/11) := by
  have hs := DegreeOneSmallSpectrum178.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum227.actual_graph_bounds.2
  linarith
#print axioms comparison0827
theorem comparison0828 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum395.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum550.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum550.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum395.actual_graph_bounds.2
  linarith
#print axioms comparison0828
theorem comparison0829 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum976.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum960.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum960.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum976.actual_graph_bounds.2
  linarith
#print axioms comparison0829
theorem comparison0830 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum976.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1331.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1331.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum976.actual_graph_bounds.2
  linarith
#print axioms comparison0830
theorem comparison0831 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum222.graph) (2-2/11) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum176.graph) (2-2/11) := by
  have hs := DegreeOneSmallSpectrum176.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum222.actual_graph_bounds.2
  linarith
#print axioms comparison0831
theorem comparison0832 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum393.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum540.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum540.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum393.actual_graph_bounds.2
  linarith
#print axioms comparison0832
theorem comparison0833 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum977.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum957.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum957.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum977.actual_graph_bounds.2
  linarith
#print axioms comparison0833
theorem comparison0834 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum977.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1319.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1319.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum977.actual_graph_bounds.2
  linarith
#print axioms comparison0834
theorem comparison0835 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum225.graph) (2-2/11) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum177.graph) (2-2/11) := by
  have hs := DegreeOneSmallSpectrum177.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum225.actual_graph_bounds.2
  linarith
#print axioms comparison0835
theorem comparison0836 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum394.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum544.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum544.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum394.actual_graph_bounds.2
  linarith
#print axioms comparison0836
theorem comparison0837 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum978.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum958.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum958.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum978.actual_graph_bounds.2
  linarith
#print axioms comparison0837
theorem comparison0838 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum978.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1323.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1323.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum978.actual_graph_bounds.2
  linarith
#print axioms comparison0838
theorem comparison0839 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum037.graph) (2-2/11) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum241.graph) (2-2/11) := by
  have hs := DegreeOneSmallSpectrum241.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum037.actual_graph_bounds.2
  linarith
#print axioms comparison0839
theorem comparison0840 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum094.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum402.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum402.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum094.actual_graph_bounds.2
  linarith
#print axioms comparison0840
theorem comparison0841 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum862.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1007.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1007.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum862.actual_graph_bounds.2
  linarith
#print axioms comparison0841
theorem comparison0842 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum862.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1002.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1002.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum862.actual_graph_bounds.2
  linarith
#print axioms comparison0842
theorem comparison0843 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum170.graph) (2-2/11) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum255.graph) (2-2/11) := by
  have hs := DegreeOneSmallSpectrum255.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum170.actual_graph_bounds.2
  linarith
#print axioms comparison0843
theorem comparison0844 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum411.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum409.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum409.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum411.actual_graph_bounds.2
  linarith
#print axioms comparison0844
theorem comparison0845 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum863.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1036.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1036.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum863.actual_graph_bounds.2
  linarith
#print axioms comparison0845
theorem comparison0846 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum863.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1031.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1031.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum863.actual_graph_bounds.2
  linarith
#print axioms comparison0846
theorem comparison0847 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum171.graph) (2-2/11) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum262.graph) (2-2/11) := by
  have hs := DegreeOneSmallSpectrum262.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum171.actual_graph_bounds.2
  linarith
#print axioms comparison0847
theorem comparison0848 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum417.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum415.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum415.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum417.actual_graph_bounds.2
  linarith
#print axioms comparison0848
theorem comparison0849 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum864.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1058.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1058.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum864.actual_graph_bounds.2
  linarith
#print axioms comparison0849
end Gebendorfer.RadenkovicGutman.DegreeOneSmallComparisons
