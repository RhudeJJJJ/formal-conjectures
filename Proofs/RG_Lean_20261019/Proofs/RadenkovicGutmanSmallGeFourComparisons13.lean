/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanSmallGeFourSpectrum131
import Proofs.RadenkovicGutmanSmallGeFourSpectrum132
import Proofs.RadenkovicGutmanSmallGeFourSpectrum140
import Proofs.RadenkovicGutmanSmallGeFourSpectrum141
import Proofs.RadenkovicGutmanSmallGeFourSpectrum146
import Proofs.RadenkovicGutmanSmallGeFourSpectrum163
import Proofs.RadenkovicGutmanSmallGeFourSpectrum164
import Proofs.RadenkovicGutmanSmallGeFourSpectrum167
import Proofs.RadenkovicGutmanSmallGeFourSpectrum178
import Proofs.RadenkovicGutmanSmallGeFourSpectrum195
import Proofs.RadenkovicGutmanSmallGeFourSpectrum196
import Proofs.RadenkovicGutmanSmallGeFourSpectrum199
import Proofs.RadenkovicGutmanSmallGeFourSpectrum200
import Proofs.RadenkovicGutmanSmallGeFourSpectrum203
import Proofs.RadenkovicGutmanSmallGeFourSpectrum208
import Proofs.RadenkovicGutmanSmallGeFourSpectrum214
import Proofs.RadenkovicGutmanSmallGeFourSpectrum215
import Proofs.RadenkovicGutmanSmallGeFourSpectrum216
import Proofs.RadenkovicGutmanSmallGeFourSpectrum217
import Proofs.RadenkovicGutmanSmallGeFourSpectrum218
import Proofs.RadenkovicGutmanSmallGeFourSpectrum219
import Proofs.RadenkovicGutmanSmallGeFourSpectrum220
import Proofs.RadenkovicGutmanSmallGeFourSpectrum221
import Proofs.RadenkovicGutmanSmallGeFourSpectrum222
import Proofs.RadenkovicGutmanSmallGeFourSpectrum223
import Proofs.RadenkovicGutmanSmallGeFourSpectrum224
namespace Gebendorfer.RadenkovicGutman.SmallGeFourComparisons
set_option maxHeartbeats 0
theorem comparison221 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum195.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum196.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum196.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum195.actual_graph_bounds.2
  linarith
#print axioms comparison221
theorem comparison222 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum131.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum132.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum132.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum131.actual_graph_bounds.2
  linarith
#print axioms comparison222
theorem comparison223 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum140.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum141.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum141.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum140.actual_graph_bounds.2
  linarith
#print axioms comparison223
theorem comparison224 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum141.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum146.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum146.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum141.actual_graph_bounds.2
  linarith
#print axioms comparison224
theorem comparison225 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum163.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum164.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum164.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum163.actual_graph_bounds.2
  linarith
#print axioms comparison225
theorem comparison226 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum164.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum167.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum167.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum164.actual_graph_bounds.2
  linarith
#print axioms comparison226
theorem comparison227 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum167.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum178.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum178.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum167.actual_graph_bounds.2
  linarith
#print axioms comparison227
theorem comparison228 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum178.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum199.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum199.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum178.actual_graph_bounds.2
  linarith
#print axioms comparison228
theorem comparison229 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum214.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum208.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum208.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum214.actual_graph_bounds.2
  linarith
#print axioms comparison229
theorem comparison230 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum215.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum216.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum216.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum215.actual_graph_bounds.2
  linarith
#print axioms comparison230
theorem comparison231 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum216.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum203.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum203.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum216.actual_graph_bounds.2
  linarith
#print axioms comparison231
theorem comparison232 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum217.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum218.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum218.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum217.actual_graph_bounds.2
  linarith
#print axioms comparison232
theorem comparison233 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum219.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum220.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum220.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum219.actual_graph_bounds.2
  linarith
#print axioms comparison233
theorem comparison234 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum220.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum221.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum221.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum220.actual_graph_bounds.2
  linarith
#print axioms comparison234
theorem comparison235 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum221.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum200.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum200.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum221.actual_graph_bounds.2
  linarith
#print axioms comparison235
theorem comparison236 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum222.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum223.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum223.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum222.actual_graph_bounds.2
  linarith
#print axioms comparison236
theorem comparison237 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum223.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum224.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum224.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum223.actual_graph_bounds.2
  linarith
#print axioms comparison237
end Gebendorfer.RadenkovicGutman.SmallGeFourComparisons
