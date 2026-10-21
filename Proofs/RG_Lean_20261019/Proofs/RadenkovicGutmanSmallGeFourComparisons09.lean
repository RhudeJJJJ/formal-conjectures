/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanSmallGeFourSpectrum069
import Proofs.RadenkovicGutmanSmallGeFourSpectrum070
import Proofs.RadenkovicGutmanSmallGeFourSpectrum085
import Proofs.RadenkovicGutmanSmallGeFourSpectrum086
import Proofs.RadenkovicGutmanSmallGeFourSpectrum087
import Proofs.RadenkovicGutmanSmallGeFourSpectrum088
import Proofs.RadenkovicGutmanSmallGeFourSpectrum089
import Proofs.RadenkovicGutmanSmallGeFourSpectrum090
import Proofs.RadenkovicGutmanSmallGeFourSpectrum091
import Proofs.RadenkovicGutmanSmallGeFourSpectrum092
import Proofs.RadenkovicGutmanSmallGeFourSpectrum139
import Proofs.RadenkovicGutmanSmallGeFourSpectrum140
import Proofs.RadenkovicGutmanSmallGeFourSpectrum141
import Proofs.RadenkovicGutmanSmallGeFourSpectrum146
import Proofs.RadenkovicGutmanSmallGeFourSpectrum163
import Proofs.RadenkovicGutmanSmallGeFourSpectrum164
import Proofs.RadenkovicGutmanSmallGeFourSpectrum167
import Proofs.RadenkovicGutmanSmallGeFourSpectrum178
import Proofs.RadenkovicGutmanSmallGeFourSpectrum197
import Proofs.RadenkovicGutmanSmallGeFourSpectrum199
import Proofs.RadenkovicGutmanSmallGeFourSpectrum223
import Proofs.RadenkovicGutmanSmallGeFourSpectrum226
import Proofs.RadenkovicGutmanSmallGeFourSpectrum227
import Proofs.RadenkovicGutmanSmallGeFourSpectrum228
import Proofs.RadenkovicGutmanSmallGeFourSpectrum229
import Proofs.RadenkovicGutmanSmallGeFourSpectrum230
import Proofs.RadenkovicGutmanSmallGeFourSpectrum231
import Proofs.RadenkovicGutmanSmallGeFourSpectrum232
namespace Gebendorfer.RadenkovicGutman.SmallGeFourComparisons
set_option maxHeartbeats 0
theorem comparison153 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum139.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum223.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum223.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum139.actual_graph_bounds.2
  linarith
#print axioms comparison153
theorem comparison154 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum085.graph) (2-2/11) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum086.graph) (2-2/11) := by
  have hs := SmallGeFourSpectrum086.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum085.actual_graph_bounds.2
  linarith
#print axioms comparison154
theorem comparison155 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum140.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum226.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum226.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum140.actual_graph_bounds.2
  linarith
#print axioms comparison155
theorem comparison156 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum086.graph) (2-2/11) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum087.graph) (2-2/11) := by
  have hs := SmallGeFourSpectrum087.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum086.actual_graph_bounds.2
  linarith
#print axioms comparison156
theorem comparison157 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum141.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum227.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum227.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum141.actual_graph_bounds.2
  linarith
#print axioms comparison157
theorem comparison158 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum087.graph) (2-2/11) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum070.graph) (2-2/11) := by
  have hs := SmallGeFourSpectrum070.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum087.actual_graph_bounds.2
  linarith
#print axioms comparison158
theorem comparison159 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum146.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum228.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum228.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum146.actual_graph_bounds.2
  linarith
#print axioms comparison159
theorem comparison160 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum088.graph) (2-2/11) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum089.graph) (2-2/11) := by
  have hs := SmallGeFourSpectrum089.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum088.actual_graph_bounds.2
  linarith
#print axioms comparison160
theorem comparison161 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum163.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum229.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum229.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum163.actual_graph_bounds.2
  linarith
#print axioms comparison161
theorem comparison162 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum089.graph) (2-2/11) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum090.graph) (2-2/11) := by
  have hs := SmallGeFourSpectrum090.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum089.actual_graph_bounds.2
  linarith
#print axioms comparison162
theorem comparison163 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum164.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum230.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum230.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum164.actual_graph_bounds.2
  linarith
#print axioms comparison163
theorem comparison164 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum090.graph) (2-2/11) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum091.graph) (2-2/11) := by
  have hs := SmallGeFourSpectrum091.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum090.actual_graph_bounds.2
  linarith
#print axioms comparison164
theorem comparison165 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum167.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum231.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum231.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum167.actual_graph_bounds.2
  linarith
#print axioms comparison165
theorem comparison166 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum091.graph) (2-2/11) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum069.graph) (2-2/11) := by
  have hs := SmallGeFourSpectrum069.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum091.actual_graph_bounds.2
  linarith
#print axioms comparison166
theorem comparison167 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum178.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum232.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum232.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum178.actual_graph_bounds.2
  linarith
#print axioms comparison167
theorem comparison168 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum069.graph) (2-2/11) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum092.graph) (2-2/11) := by
  have hs := SmallGeFourSpectrum092.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum069.actual_graph_bounds.2
  linarith
#print axioms comparison168
theorem comparison169 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum199.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum197.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum197.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum199.actual_graph_bounds.2
  linarith
#print axioms comparison169
end Gebendorfer.RadenkovicGutman.SmallGeFourComparisons
