/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanSmallGeFourSpectrum024
import Proofs.RadenkovicGutmanSmallGeFourSpectrum036
import Proofs.RadenkovicGutmanSmallGeFourSpectrum038
import Proofs.RadenkovicGutmanSmallGeFourSpectrum040
import Proofs.RadenkovicGutmanSmallGeFourSpectrum041
import Proofs.RadenkovicGutmanSmallGeFourSpectrum042
import Proofs.RadenkovicGutmanSmallGeFourSpectrum043
import Proofs.RadenkovicGutmanSmallGeFourSpectrum044
import Proofs.RadenkovicGutmanSmallGeFourSpectrum053
import Proofs.RadenkovicGutmanSmallGeFourSpectrum058
import Proofs.RadenkovicGutmanSmallGeFourSpectrum062
import Proofs.RadenkovicGutmanSmallGeFourSpectrum064
import Proofs.RadenkovicGutmanSmallGeFourSpectrum065
import Proofs.RadenkovicGutmanSmallGeFourSpectrum069
import Proofs.RadenkovicGutmanSmallGeFourSpectrum071
import Proofs.RadenkovicGutmanSmallGeFourSpectrum098
import Proofs.RadenkovicGutmanSmallGeFourSpectrum100
import Proofs.RadenkovicGutmanSmallGeFourSpectrum106
import Proofs.RadenkovicGutmanSmallGeFourSpectrum107
import Proofs.RadenkovicGutmanSmallGeFourSpectrum109
import Proofs.RadenkovicGutmanSmallGeFourSpectrum110
import Proofs.RadenkovicGutmanSmallGeFourSpectrum112
import Proofs.RadenkovicGutmanSmallGeFourSpectrum159
import Proofs.RadenkovicGutmanSmallGeFourSpectrum169
import Proofs.RadenkovicGutmanSmallGeFourSpectrum178
import Proofs.RadenkovicGutmanSmallGeFourSpectrum180
import Proofs.RadenkovicGutmanSmallGeFourSpectrum182
import Proofs.RadenkovicGutmanSmallGeFourSpectrum183
import Proofs.RadenkovicGutmanSmallGeFourSpectrum199
import Proofs.RadenkovicGutmanSmallGeFourSpectrum231
import Proofs.RadenkovicGutmanSmallGeFourSpectrum232
namespace Gebendorfer.RadenkovicGutman.SmallGeFourComparisons
set_option maxHeartbeats 0
theorem comparison102 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum180.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum178.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum178.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum180.actual_graph_bounds.2
  linarith
#print axioms comparison102
theorem comparison103 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum180.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum231.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum231.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum180.actual_graph_bounds.2
  linarith
#print axioms comparison103
theorem comparison104 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum024.graph) (2-2/10) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum036.graph) (2-2/10) := by
  have hs := SmallGeFourSpectrum036.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum024.actual_graph_bounds.2
  linarith
#print axioms comparison104
theorem comparison105 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum071.graph) (2-2/11) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum069.graph) (2-2/11) := by
  have hs := SmallGeFourSpectrum069.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum071.actual_graph_bounds.2
  linarith
#print axioms comparison105
theorem comparison106 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum112.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum199.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum199.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum112.actual_graph_bounds.2
  linarith
#print axioms comparison106
theorem comparison107 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum112.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum232.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum232.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum112.actual_graph_bounds.2
  linarith
#print axioms comparison107
theorem comparison108 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum038.graph) (2-2/11) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum044.graph) (2-2/11) := by
  have hs := SmallGeFourSpectrum044.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum038.actual_graph_bounds.2
  linarith
#print axioms comparison108
theorem comparison109 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum110.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum100.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum100.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum110.actual_graph_bounds.2
  linarith
#print axioms comparison109
theorem comparison110 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum053.graph) (2-2/11) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum042.graph) (2-2/11) := by
  have hs := SmallGeFourSpectrum042.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum053.actual_graph_bounds.2
  linarith
#print axioms comparison110
theorem comparison111 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum098.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum159.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum159.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum098.actual_graph_bounds.2
  linarith
#print axioms comparison111
theorem comparison112 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum064.graph) (2-2/11) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum043.graph) (2-2/11) := by
  have hs := SmallGeFourSpectrum043.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum064.actual_graph_bounds.2
  linarith
#print axioms comparison112
theorem comparison113 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum106.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum182.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum182.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum106.actual_graph_bounds.2
  linarith
#print axioms comparison113
theorem comparison114 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum065.graph) (2-2/11) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum041.graph) (2-2/11) := by
  have hs := SmallGeFourSpectrum041.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum065.actual_graph_bounds.2
  linarith
#print axioms comparison114
theorem comparison115 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum109.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum183.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum183.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum109.actual_graph_bounds.2
  linarith
#print axioms comparison115
theorem comparison116 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum058.graph) (2-2/11) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum062.graph) (2-2/11) := by
  have hs := SmallGeFourSpectrum062.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum058.actual_graph_bounds.2
  linarith
#print axioms comparison116
theorem comparison117 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum107.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum169.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum169.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum107.actual_graph_bounds.2
  linarith
#print axioms comparison117
theorem comparison118 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum062.graph) (2-2/11) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum040.graph) (2-2/11) := by
  have hs := SmallGeFourSpectrum040.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum062.actual_graph_bounds.2
  linarith
#print axioms comparison118
end Gebendorfer.RadenkovicGutman.SmallGeFourComparisons
