/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanSmallGeFourSpectrum093
import Proofs.RadenkovicGutmanSmallGeFourSpectrum097
import Proofs.RadenkovicGutmanSmallGeFourSpectrum099
import Proofs.RadenkovicGutmanSmallGeFourSpectrum100
import Proofs.RadenkovicGutmanSmallGeFourSpectrum101
import Proofs.RadenkovicGutmanSmallGeFourSpectrum102
import Proofs.RadenkovicGutmanSmallGeFourSpectrum103
import Proofs.RadenkovicGutmanSmallGeFourSpectrum104
import Proofs.RadenkovicGutmanSmallGeFourSpectrum114
import Proofs.RadenkovicGutmanSmallGeFourSpectrum115
import Proofs.RadenkovicGutmanSmallGeFourSpectrum116
import Proofs.RadenkovicGutmanSmallGeFourSpectrum119
import Proofs.RadenkovicGutmanSmallGeFourSpectrum120
import Proofs.RadenkovicGutmanSmallGeFourSpectrum121
import Proofs.RadenkovicGutmanSmallGeFourSpectrum122
import Proofs.RadenkovicGutmanSmallGeFourSpectrum123
import Proofs.RadenkovicGutmanSmallGeFourSpectrum124
import Proofs.RadenkovicGutmanSmallGeFourSpectrum125
import Proofs.RadenkovicGutmanSmallGeFourSpectrum126
import Proofs.RadenkovicGutmanSmallGeFourSpectrum127
import Proofs.RadenkovicGutmanSmallGeFourSpectrum128
import Proofs.RadenkovicGutmanSmallGeFourSpectrum137
import Proofs.RadenkovicGutmanSmallGeFourSpectrum153
import Proofs.RadenkovicGutmanSmallGeFourSpectrum157
import Proofs.RadenkovicGutmanSmallGeFourSpectrum159
import Proofs.RadenkovicGutmanSmallGeFourSpectrum160
import Proofs.RadenkovicGutmanSmallGeFourSpectrum172
import Proofs.RadenkovicGutmanSmallGeFourSpectrum176
import Proofs.RadenkovicGutmanSmallGeFourSpectrum182
import Proofs.RadenkovicGutmanSmallGeFourSpectrum185
import Proofs.RadenkovicGutmanSmallGeFourSpectrum186
namespace Gebendorfer.RadenkovicGutman.SmallGeFourComparisons
set_option maxHeartbeats 0
theorem comparison170 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum104.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum093.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum093.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum104.actual_graph_bounds.2
  linarith
#print axioms comparison170
theorem comparison171 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum097.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum124.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum124.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum097.actual_graph_bounds.2
  linarith
#print axioms comparison171
theorem comparison172 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum102.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum127.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum127.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum102.actual_graph_bounds.2
  linarith
#print axioms comparison172
theorem comparison173 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum103.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum128.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum128.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum103.actual_graph_bounds.2
  linarith
#print axioms comparison173
theorem comparison174 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum101.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum121.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum121.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum101.actual_graph_bounds.2
  linarith
#print axioms comparison174
theorem comparison175 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum099.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum100.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum100.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum099.actual_graph_bounds.2
  linarith
#print axioms comparison175
theorem comparison176 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum100.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum116.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum116.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum100.actual_graph_bounds.2
  linarith
#print axioms comparison176
theorem comparison177 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum137.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum122.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum122.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum137.actual_graph_bounds.2
  linarith
#print axioms comparison177
theorem comparison178 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum153.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum123.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum123.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum153.actual_graph_bounds.2
  linarith
#print axioms comparison178
theorem comparison179 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum160.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum119.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum119.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum160.actual_graph_bounds.2
  linarith
#print axioms comparison179
theorem comparison180 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum157.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum159.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum159.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum157.actual_graph_bounds.2
  linarith
#print axioms comparison180
theorem comparison181 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum159.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum114.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum114.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum159.actual_graph_bounds.2
  linarith
#print axioms comparison181
theorem comparison182 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum176.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum125.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum125.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum176.actual_graph_bounds.2
  linarith
#print axioms comparison182
theorem comparison183 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum185.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum126.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum126.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum185.actual_graph_bounds.2
  linarith
#print axioms comparison183
theorem comparison184 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum186.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum120.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum120.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum186.actual_graph_bounds.2
  linarith
#print axioms comparison184
theorem comparison185 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum172.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum182.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum182.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum172.actual_graph_bounds.2
  linarith
#print axioms comparison185
theorem comparison186 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum182.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum115.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum115.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum182.actual_graph_bounds.2
  linarith
#print axioms comparison186
end Gebendorfer.RadenkovicGutman.SmallGeFourComparisons
