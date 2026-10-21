/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanSmallGeFourSpectrum047
import Proofs.RadenkovicGutmanSmallGeFourSpectrum048
import Proofs.RadenkovicGutmanSmallGeFourSpectrum055
import Proofs.RadenkovicGutmanSmallGeFourSpectrum056
import Proofs.RadenkovicGutmanSmallGeFourSpectrum060
import Proofs.RadenkovicGutmanSmallGeFourSpectrum067
import Proofs.RadenkovicGutmanSmallGeFourSpectrum068
import Proofs.RadenkovicGutmanSmallGeFourSpectrum071
import Proofs.RadenkovicGutmanSmallGeFourSpectrum072
import Proofs.RadenkovicGutmanSmallGeFourSpectrum075
import Proofs.RadenkovicGutmanSmallGeFourSpectrum080
import Proofs.RadenkovicGutmanSmallGeFourSpectrum081
import Proofs.RadenkovicGutmanSmallGeFourSpectrum082
import Proofs.RadenkovicGutmanSmallGeFourSpectrum083
import Proofs.RadenkovicGutmanSmallGeFourSpectrum084
import Proofs.RadenkovicGutmanSmallGeFourSpectrum129
import Proofs.RadenkovicGutmanSmallGeFourSpectrum131
import Proofs.RadenkovicGutmanSmallGeFourSpectrum132
import Proofs.RadenkovicGutmanSmallGeFourSpectrum141
import Proofs.RadenkovicGutmanSmallGeFourSpectrum164
import Proofs.RadenkovicGutmanSmallGeFourSpectrum167
import Proofs.RadenkovicGutmanSmallGeFourSpectrum178
import Proofs.RadenkovicGutmanSmallGeFourSpectrum192
import Proofs.RadenkovicGutmanSmallGeFourSpectrum193
import Proofs.RadenkovicGutmanSmallGeFourSpectrum194
import Proofs.RadenkovicGutmanSmallGeFourSpectrum195
import Proofs.RadenkovicGutmanSmallGeFourSpectrum196
import Proofs.RadenkovicGutmanSmallGeFourSpectrum216
import Proofs.RadenkovicGutmanSmallGeFourSpectrum220
import Proofs.RadenkovicGutmanSmallGeFourSpectrum221
namespace Gebendorfer.RadenkovicGutman.SmallGeFourComparisons
set_option maxHeartbeats 0
theorem comparison136 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum067.graph) (2-2/11) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum068.graph) (2-2/11) := by
  have hs := SmallGeFourSpectrum068.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum067.actual_graph_bounds.2
  linarith
#print axioms comparison136
theorem comparison137 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum192.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum195.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum195.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum192.actual_graph_bounds.2
  linarith
#print axioms comparison137
theorem comparison138 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum047.graph) (2-2/11) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum048.graph) (2-2/11) := by
  have hs := SmallGeFourSpectrum048.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum047.actual_graph_bounds.2
  linarith
#print axioms comparison138
theorem comparison139 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum193.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum141.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum141.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum193.actual_graph_bounds.2
  linarith
#print axioms comparison139
theorem comparison140 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum055.graph) (2-2/11) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum056.graph) (2-2/11) := by
  have hs := SmallGeFourSpectrum056.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum055.actual_graph_bounds.2
  linarith
#print axioms comparison140
theorem comparison141 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum194.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum164.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum164.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum194.actual_graph_bounds.2
  linarith
#print axioms comparison141
theorem comparison142 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum056.graph) (2-2/11) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum060.graph) (2-2/11) := by
  have hs := SmallGeFourSpectrum060.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum056.actual_graph_bounds.2
  linarith
#print axioms comparison142
theorem comparison143 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum195.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum167.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum167.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum195.actual_graph_bounds.2
  linarith
#print axioms comparison143
theorem comparison144 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum060.graph) (2-2/11) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum071.graph) (2-2/11) := by
  have hs := SmallGeFourSpectrum071.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum060.actual_graph_bounds.2
  linarith
#print axioms comparison144
theorem comparison145 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum196.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum178.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum178.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum196.actual_graph_bounds.2
  linarith
#print axioms comparison145
theorem comparison146 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum080.graph) (2-2/11) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum075.graph) (2-2/11) := by
  have hs := SmallGeFourSpectrum075.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum080.actual_graph_bounds.2
  linarith
#print axioms comparison146
theorem comparison147 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum129.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum216.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum216.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum129.actual_graph_bounds.2
  linarith
#print axioms comparison147
theorem comparison148 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum081.graph) (2-2/11) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum082.graph) (2-2/11) := by
  have hs := SmallGeFourSpectrum082.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum081.actual_graph_bounds.2
  linarith
#print axioms comparison148
theorem comparison149 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum131.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum220.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum220.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum131.actual_graph_bounds.2
  linarith
#print axioms comparison149
theorem comparison150 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum082.graph) (2-2/11) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum072.graph) (2-2/11) := by
  have hs := SmallGeFourSpectrum072.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum082.actual_graph_bounds.2
  linarith
#print axioms comparison150
theorem comparison151 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum132.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum221.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum221.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum132.actual_graph_bounds.2
  linarith
#print axioms comparison151
theorem comparison152 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum083.graph) (2-2/11) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum084.graph) (2-2/11) := by
  have hs := SmallGeFourSpectrum084.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum083.actual_graph_bounds.2
  linarith
#print axioms comparison152
end Gebendorfer.RadenkovicGutman.SmallGeFourComparisons
