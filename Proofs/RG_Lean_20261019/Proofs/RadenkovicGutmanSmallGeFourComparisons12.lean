/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanSmallGeFourSpectrum142
import Proofs.RadenkovicGutmanSmallGeFourSpectrum143
import Proofs.RadenkovicGutmanSmallGeFourSpectrum147
import Proofs.RadenkovicGutmanSmallGeFourSpectrum148
import Proofs.RadenkovicGutmanSmallGeFourSpectrum155
import Proofs.RadenkovicGutmanSmallGeFourSpectrum156
import Proofs.RadenkovicGutmanSmallGeFourSpectrum158
import Proofs.RadenkovicGutmanSmallGeFourSpectrum161
import Proofs.RadenkovicGutmanSmallGeFourSpectrum162
import Proofs.RadenkovicGutmanSmallGeFourSpectrum165
import Proofs.RadenkovicGutmanSmallGeFourSpectrum168
import Proofs.RadenkovicGutmanSmallGeFourSpectrum170
import Proofs.RadenkovicGutmanSmallGeFourSpectrum171
import Proofs.RadenkovicGutmanSmallGeFourSpectrum174
import Proofs.RadenkovicGutmanSmallGeFourSpectrum175
import Proofs.RadenkovicGutmanSmallGeFourSpectrum179
import Proofs.RadenkovicGutmanSmallGeFourSpectrum181
import Proofs.RadenkovicGutmanSmallGeFourSpectrum184
import Proofs.RadenkovicGutmanSmallGeFourSpectrum190
import Proofs.RadenkovicGutmanSmallGeFourSpectrum191
import Proofs.RadenkovicGutmanSmallGeFourSpectrum194
import Proofs.RadenkovicGutmanSmallGeFourSpectrum195
import Proofs.RadenkovicGutmanSmallGeFourSpectrum201
import Proofs.RadenkovicGutmanSmallGeFourSpectrum202
import Proofs.RadenkovicGutmanSmallGeFourSpectrum206
import Proofs.RadenkovicGutmanSmallGeFourSpectrum207
import Proofs.RadenkovicGutmanSmallGeFourSpectrum213
import Proofs.RadenkovicGutmanSmallGeFourSpectrum214
namespace Gebendorfer.RadenkovicGutman.SmallGeFourComparisons
set_option maxHeartbeats 0
theorem comparison204 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum161.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum162.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum162.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum161.actual_graph_bounds.2
  linarith
#print axioms comparison204
theorem comparison205 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum142.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum147.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum147.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum142.actual_graph_bounds.2
  linarith
#print axioms comparison205
theorem comparison206 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum155.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum156.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum156.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum155.actual_graph_bounds.2
  linarith
#print axioms comparison206
theorem comparison207 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum156.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum158.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum158.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum156.actual_graph_bounds.2
  linarith
#print axioms comparison207
theorem comparison208 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum158.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum201.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum201.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum158.actual_graph_bounds.2
  linarith
#print axioms comparison208
theorem comparison209 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum174.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum213.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum213.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum174.actual_graph_bounds.2
  linarith
#print axioms comparison209
theorem comparison210 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum170.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum175.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum175.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum170.actual_graph_bounds.2
  linarith
#print axioms comparison210
theorem comparison211 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum175.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum206.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum206.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum175.actual_graph_bounds.2
  linarith
#print axioms comparison211
theorem comparison212 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum184.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum214.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum214.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum184.actual_graph_bounds.2
  linarith
#print axioms comparison212
theorem comparison213 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum171.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum181.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum181.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum171.actual_graph_bounds.2
  linarith
#print axioms comparison213
theorem comparison214 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum181.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum207.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum207.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum181.actual_graph_bounds.2
  linarith
#print axioms comparison214
theorem comparison215 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum190.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum191.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum191.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum190.actual_graph_bounds.2
  linarith
#print axioms comparison215
theorem comparison216 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum143.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum148.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum148.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum143.actual_graph_bounds.2
  linarith
#print axioms comparison216
theorem comparison217 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum165.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum168.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum168.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum165.actual_graph_bounds.2
  linarith
#print axioms comparison217
theorem comparison218 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum168.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum179.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum179.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum168.actual_graph_bounds.2
  linarith
#print axioms comparison218
theorem comparison219 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum179.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum202.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum202.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum179.actual_graph_bounds.2
  linarith
#print axioms comparison219
theorem comparison220 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum194.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum195.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum195.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum194.actual_graph_bounds.2
  linarith
#print axioms comparison220
end Gebendorfer.RadenkovicGutman.SmallGeFourComparisons
