/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanSmallGeFourSpectrum107
import Proofs.RadenkovicGutmanSmallGeFourSpectrum108
import Proofs.RadenkovicGutmanSmallGeFourSpectrum112
import Proofs.RadenkovicGutmanSmallGeFourSpectrum113
import Proofs.RadenkovicGutmanSmallGeFourSpectrum117
import Proofs.RadenkovicGutmanSmallGeFourSpectrum118
import Proofs.RadenkovicGutmanSmallGeFourSpectrum130
import Proofs.RadenkovicGutmanSmallGeFourSpectrum134
import Proofs.RadenkovicGutmanSmallGeFourSpectrum135
import Proofs.RadenkovicGutmanSmallGeFourSpectrum136
import Proofs.RadenkovicGutmanSmallGeFourSpectrum144
import Proofs.RadenkovicGutmanSmallGeFourSpectrum145
import Proofs.RadenkovicGutmanSmallGeFourSpectrum149
import Proofs.RadenkovicGutmanSmallGeFourSpectrum150
import Proofs.RadenkovicGutmanSmallGeFourSpectrum151
import Proofs.RadenkovicGutmanSmallGeFourSpectrum152
import Proofs.RadenkovicGutmanSmallGeFourSpectrum166
import Proofs.RadenkovicGutmanSmallGeFourSpectrum169
import Proofs.RadenkovicGutmanSmallGeFourSpectrum173
import Proofs.RadenkovicGutmanSmallGeFourSpectrum180
import Proofs.RadenkovicGutmanSmallGeFourSpectrum183
import Proofs.RadenkovicGutmanSmallGeFourSpectrum187
import Proofs.RadenkovicGutmanSmallGeFourSpectrum188
import Proofs.RadenkovicGutmanSmallGeFourSpectrum204
import Proofs.RadenkovicGutmanSmallGeFourSpectrum205
import Proofs.RadenkovicGutmanSmallGeFourSpectrum209
import Proofs.RadenkovicGutmanSmallGeFourSpectrum210
import Proofs.RadenkovicGutmanSmallGeFourSpectrum211
import Proofs.RadenkovicGutmanSmallGeFourSpectrum212
namespace Gebendorfer.RadenkovicGutman.SmallGeFourComparisons
set_option maxHeartbeats 0
theorem comparison187 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum187.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum117.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum117.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum187.actual_graph_bounds.2
  linarith
#print axioms comparison187
theorem comparison188 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum188.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum118.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum118.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum188.actual_graph_bounds.2
  linarith
#print axioms comparison188
theorem comparison189 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum173.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum183.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum183.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum173.actual_graph_bounds.2
  linarith
#print axioms comparison189
theorem comparison190 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum183.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum113.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum113.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum183.actual_graph_bounds.2
  linarith
#print axioms comparison190
theorem comparison191 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum107.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum108.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum108.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum107.actual_graph_bounds.2
  linarith
#print axioms comparison191
theorem comparison192 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum144.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum149.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum149.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum144.actual_graph_bounds.2
  linarith
#print axioms comparison192
theorem comparison193 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum166.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum169.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum169.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum166.actual_graph_bounds.2
  linarith
#print axioms comparison193
theorem comparison194 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum169.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum180.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum180.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum169.actual_graph_bounds.2
  linarith
#print axioms comparison194
theorem comparison195 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum180.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum112.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum112.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum180.actual_graph_bounds.2
  linarith
#print axioms comparison195
theorem comparison196 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum130.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum209.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum209.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum130.actual_graph_bounds.2
  linarith
#print axioms comparison196
theorem comparison197 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum134.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum210.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum210.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum134.actual_graph_bounds.2
  linarith
#print axioms comparison197
theorem comparison198 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum135.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum136.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum136.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum135.actual_graph_bounds.2
  linarith
#print axioms comparison198
theorem comparison199 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum136.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum204.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum204.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum136.actual_graph_bounds.2
  linarith
#print axioms comparison199
theorem comparison200 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum145.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum211.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum211.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum145.actual_graph_bounds.2
  linarith
#print axioms comparison200
theorem comparison201 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum150.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum212.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum212.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum150.actual_graph_bounds.2
  linarith
#print axioms comparison201
theorem comparison202 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum151.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum152.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum152.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum151.actual_graph_bounds.2
  linarith
#print axioms comparison202
theorem comparison203 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum152.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum205.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum205.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum152.actual_graph_bounds.2
  linarith
#print axioms comparison203
end Gebendorfer.RadenkovicGutman.SmallGeFourComparisons
