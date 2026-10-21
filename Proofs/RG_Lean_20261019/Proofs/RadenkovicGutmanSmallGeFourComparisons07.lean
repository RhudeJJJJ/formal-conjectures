/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanSmallGeFourSpectrum046
import Proofs.RadenkovicGutmanSmallGeFourSpectrum050
import Proofs.RadenkovicGutmanSmallGeFourSpectrum051
import Proofs.RadenkovicGutmanSmallGeFourSpectrum052
import Proofs.RadenkovicGutmanSmallGeFourSpectrum057
import Proofs.RadenkovicGutmanSmallGeFourSpectrum059
import Proofs.RadenkovicGutmanSmallGeFourSpectrum061
import Proofs.RadenkovicGutmanSmallGeFourSpectrum063
import Proofs.RadenkovicGutmanSmallGeFourSpectrum073
import Proofs.RadenkovicGutmanSmallGeFourSpectrum074
import Proofs.RadenkovicGutmanSmallGeFourSpectrum076
import Proofs.RadenkovicGutmanSmallGeFourSpectrum077
import Proofs.RadenkovicGutmanSmallGeFourSpectrum078
import Proofs.RadenkovicGutmanSmallGeFourSpectrum079
import Proofs.RadenkovicGutmanSmallGeFourSpectrum108
import Proofs.RadenkovicGutmanSmallGeFourSpectrum136
import Proofs.RadenkovicGutmanSmallGeFourSpectrum138
import Proofs.RadenkovicGutmanSmallGeFourSpectrum152
import Proofs.RadenkovicGutmanSmallGeFourSpectrum154
import Proofs.RadenkovicGutmanSmallGeFourSpectrum156
import Proofs.RadenkovicGutmanSmallGeFourSpectrum158
import Proofs.RadenkovicGutmanSmallGeFourSpectrum161
import Proofs.RadenkovicGutmanSmallGeFourSpectrum162
import Proofs.RadenkovicGutmanSmallGeFourSpectrum168
import Proofs.RadenkovicGutmanSmallGeFourSpectrum175
import Proofs.RadenkovicGutmanSmallGeFourSpectrum177
import Proofs.RadenkovicGutmanSmallGeFourSpectrum179
import Proofs.RadenkovicGutmanSmallGeFourSpectrum180
import Proofs.RadenkovicGutmanSmallGeFourSpectrum181
import Proofs.RadenkovicGutmanSmallGeFourSpectrum189
import Proofs.RadenkovicGutmanSmallGeFourSpectrum190
import Proofs.RadenkovicGutmanSmallGeFourSpectrum191
namespace Gebendorfer.RadenkovicGutman.SmallGeFourComparisons
set_option maxHeartbeats 0
theorem comparison119 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum108.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum180.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum180.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum108.actual_graph_bounds.2
  linarith
#print axioms comparison119
theorem comparison120 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum046.graph) (2-2/11) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum076.graph) (2-2/11) := by
  have hs := SmallGeFourSpectrum076.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum046.actual_graph_bounds.2
  linarith
#print axioms comparison120
theorem comparison121 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum138.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum136.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum136.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum138.actual_graph_bounds.2
  linarith
#print axioms comparison121
theorem comparison122 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum050.graph) (2-2/11) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum077.graph) (2-2/11) := by
  have hs := SmallGeFourSpectrum077.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum050.actual_graph_bounds.2
  linarith
#print axioms comparison122
theorem comparison123 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum154.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum152.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum152.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum154.actual_graph_bounds.2
  linarith
#print axioms comparison123
theorem comparison124 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum051.graph) (2-2/11) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum052.graph) (2-2/11) := by
  have hs := SmallGeFourSpectrum052.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum051.actual_graph_bounds.2
  linarith
#print axioms comparison124
theorem comparison125 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum161.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum156.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum156.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum161.actual_graph_bounds.2
  linarith
#print axioms comparison125
theorem comparison126 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum052.graph) (2-2/11) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum073.graph) (2-2/11) := by
  have hs := SmallGeFourSpectrum073.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum052.actual_graph_bounds.2
  linarith
#print axioms comparison126
theorem comparison127 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum162.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum158.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum158.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum162.actual_graph_bounds.2
  linarith
#print axioms comparison127
theorem comparison128 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum059.graph) (2-2/11) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum078.graph) (2-2/11) := by
  have hs := SmallGeFourSpectrum078.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum059.actual_graph_bounds.2
  linarith
#print axioms comparison128
theorem comparison129 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum177.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum175.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum175.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum177.actual_graph_bounds.2
  linarith
#print axioms comparison129
theorem comparison130 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum063.graph) (2-2/11) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum079.graph) (2-2/11) := by
  have hs := SmallGeFourSpectrum079.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum063.actual_graph_bounds.2
  linarith
#print axioms comparison130
theorem comparison131 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum189.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum181.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum181.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum189.actual_graph_bounds.2
  linarith
#print axioms comparison131
theorem comparison132 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum057.graph) (2-2/11) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum061.graph) (2-2/11) := by
  have hs := SmallGeFourSpectrum061.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum057.actual_graph_bounds.2
  linarith
#print axioms comparison132
theorem comparison133 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum190.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum168.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum168.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum190.actual_graph_bounds.2
  linarith
#print axioms comparison133
theorem comparison134 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum061.graph) (2-2/11) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum074.graph) (2-2/11) := by
  have hs := SmallGeFourSpectrum074.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum061.actual_graph_bounds.2
  linarith
#print axioms comparison134
theorem comparison135 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum191.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum179.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum179.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum191.actual_graph_bounds.2
  linarith
#print axioms comparison135
end Gebendorfer.RadenkovicGutman.SmallGeFourComparisons
