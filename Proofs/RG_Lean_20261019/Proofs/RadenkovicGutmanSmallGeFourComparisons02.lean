/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanSmallGeFourSpectrum008
import Proofs.RadenkovicGutmanSmallGeFourSpectrum009
import Proofs.RadenkovicGutmanSmallGeFourSpectrum011
import Proofs.RadenkovicGutmanSmallGeFourSpectrum012
import Proofs.RadenkovicGutmanSmallGeFourSpectrum013
import Proofs.RadenkovicGutmanSmallGeFourSpectrum017
import Proofs.RadenkovicGutmanSmallGeFourSpectrum019
import Proofs.RadenkovicGutmanSmallGeFourSpectrum020
import Proofs.RadenkovicGutmanSmallGeFourSpectrum032
import Proofs.RadenkovicGutmanSmallGeFourSpectrum034
import Proofs.RadenkovicGutmanSmallGeFourSpectrum035
import Proofs.RadenkovicGutmanSmallGeFourSpectrum039
import Proofs.RadenkovicGutmanSmallGeFourSpectrum048
import Proofs.RadenkovicGutmanSmallGeFourSpectrum049
import Proofs.RadenkovicGutmanSmallGeFourSpectrum056
import Proofs.RadenkovicGutmanSmallGeFourSpectrum058
import Proofs.RadenkovicGutmanSmallGeFourSpectrum060
import Proofs.RadenkovicGutmanSmallGeFourSpectrum062
import Proofs.RadenkovicGutmanSmallGeFourSpectrum086
import Proofs.RadenkovicGutmanSmallGeFourSpectrum089
import Proofs.RadenkovicGutmanSmallGeFourSpectrum095
import Proofs.RadenkovicGutmanSmallGeFourSpectrum099
import Proofs.RadenkovicGutmanSmallGeFourSpectrum110
import Proofs.RadenkovicGutmanSmallGeFourSpectrum141
import Proofs.RadenkovicGutmanSmallGeFourSpectrum149
import Proofs.RadenkovicGutmanSmallGeFourSpectrum164
import Proofs.RadenkovicGutmanSmallGeFourSpectrum169
import Proofs.RadenkovicGutmanSmallGeFourSpectrum195
namespace Gebendorfer.RadenkovicGutman.SmallGeFourComparisons
set_option maxHeartbeats 0
theorem comparison034 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum039.graph) (2-2/11) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum056.graph) (2-2/11) := by
  have hs := SmallGeFourSpectrum056.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum039.actual_graph_bounds.2
  linarith
#print axioms comparison034
theorem comparison035 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum110.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum195.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum195.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum110.actual_graph_bounds.2
  linarith
#print axioms comparison035
theorem comparison036 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum011.graph) (2-2/9) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum009.graph) (2-2/9) := by
  have hs := SmallGeFourSpectrum009.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum011.actual_graph_bounds.2
  linarith
#print axioms comparison036
theorem comparison037 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum017.graph) (2-2/10) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum032.graph) (2-2/10) := by
  have hs := SmallGeFourSpectrum032.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum017.actual_graph_bounds.2
  linarith
#print axioms comparison037
theorem comparison038 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum049.graph) (2-2/11) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum048.graph) (2-2/11) := by
  have hs := SmallGeFourSpectrum048.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum049.actual_graph_bounds.2
  linarith
#print axioms comparison038
theorem comparison039 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum095.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum149.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum149.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum095.actual_graph_bounds.2
  linarith
#print axioms comparison039
theorem comparison040 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum049.graph) (2-2/11) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum086.graph) (2-2/11) := by
  have hs := SmallGeFourSpectrum086.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum049.actual_graph_bounds.2
  linarith
#print axioms comparison040
theorem comparison041 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum095.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum141.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum141.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum095.actual_graph_bounds.2
  linarith
#print axioms comparison041
theorem comparison042 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum012.graph) (2-2/9) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum013.graph) (2-2/9) := by
  have hs := SmallGeFourSpectrum013.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum012.actual_graph_bounds.2
  linarith
#print axioms comparison042
theorem comparison043 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum019.graph) (2-2/10) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum034.graph) (2-2/10) := by
  have hs := SmallGeFourSpectrum034.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum019.actual_graph_bounds.2
  linarith
#print axioms comparison043
theorem comparison044 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum058.graph) (2-2/11) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum056.graph) (2-2/11) := by
  have hs := SmallGeFourSpectrum056.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum058.actual_graph_bounds.2
  linarith
#print axioms comparison044
theorem comparison045 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum099.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum169.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum169.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum099.actual_graph_bounds.2
  linarith
#print axioms comparison045
theorem comparison046 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum058.graph) (2-2/11) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum089.graph) (2-2/11) := by
  have hs := SmallGeFourSpectrum089.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum058.actual_graph_bounds.2
  linarith
#print axioms comparison046
theorem comparison047 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum099.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum164.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum164.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum099.actual_graph_bounds.2
  linarith
#print axioms comparison047
theorem comparison048 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum013.graph) (2-2/9) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum008.graph) (2-2/9) := by
  have hs := SmallGeFourSpectrum008.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum013.actual_graph_bounds.2
  linarith
#print axioms comparison048
theorem comparison049 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum020.graph) (2-2/10) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum035.graph) (2-2/10) := by
  have hs := SmallGeFourSpectrum035.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum020.actual_graph_bounds.2
  linarith
#print axioms comparison049
theorem comparison050 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum062.graph) (2-2/11) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum060.graph) (2-2/11) := by
  have hs := SmallGeFourSpectrum060.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum062.actual_graph_bounds.2
  linarith
#print axioms comparison050
end Gebendorfer.RadenkovicGutman.SmallGeFourComparisons
