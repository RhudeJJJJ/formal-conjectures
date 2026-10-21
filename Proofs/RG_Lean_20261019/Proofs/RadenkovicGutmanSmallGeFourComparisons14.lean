/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanSmallGeFourSpectrum197
import Proofs.RadenkovicGutmanSmallGeFourSpectrum198
import Proofs.RadenkovicGutmanSmallGeFourSpectrum225
import Proofs.RadenkovicGutmanSmallGeFourSpectrum226
import Proofs.RadenkovicGutmanSmallGeFourSpectrum227
import Proofs.RadenkovicGutmanSmallGeFourSpectrum228
import Proofs.RadenkovicGutmanSmallGeFourSpectrum229
import Proofs.RadenkovicGutmanSmallGeFourSpectrum230
import Proofs.RadenkovicGutmanSmallGeFourSpectrum231
import Proofs.RadenkovicGutmanSmallGeFourSpectrum232
import Proofs.RadenkovicGutmanSmallGeFourSpectrum233
namespace Gebendorfer.RadenkovicGutman.SmallGeFourComparisons
set_option maxHeartbeats 0
theorem comparison238 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum225.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum226.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum226.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum225.actual_graph_bounds.2
  linarith
#print axioms comparison238
theorem comparison239 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum226.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum227.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum227.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum226.actual_graph_bounds.2
  linarith
#print axioms comparison239
theorem comparison240 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum227.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum228.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum228.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum227.actual_graph_bounds.2
  linarith
#print axioms comparison240
theorem comparison241 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum228.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum198.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum198.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum228.actual_graph_bounds.2
  linarith
#print axioms comparison241
theorem comparison242 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum229.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum230.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum230.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum229.actual_graph_bounds.2
  linarith
#print axioms comparison242
theorem comparison243 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum230.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum231.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum231.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum230.actual_graph_bounds.2
  linarith
#print axioms comparison243
theorem comparison244 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum231.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum232.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum232.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum231.actual_graph_bounds.2
  linarith
#print axioms comparison244
theorem comparison245 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum232.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum197.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum197.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum232.actual_graph_bounds.2
  linarith
#print axioms comparison245
theorem comparison246 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum197.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum233.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum233.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum197.actual_graph_bounds.2
  linarith
#print axioms comparison246
end Gebendorfer.RadenkovicGutman.SmallGeFourComparisons
