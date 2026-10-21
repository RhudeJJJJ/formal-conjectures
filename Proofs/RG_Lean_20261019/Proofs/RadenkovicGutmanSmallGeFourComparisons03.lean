/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanSmallGeFourSpectrum008
import Proofs.RadenkovicGutmanSmallGeFourSpectrum014
import Proofs.RadenkovicGutmanSmallGeFourSpectrum015
import Proofs.RadenkovicGutmanSmallGeFourSpectrum018
import Proofs.RadenkovicGutmanSmallGeFourSpectrum022
import Proofs.RadenkovicGutmanSmallGeFourSpectrum024
import Proofs.RadenkovicGutmanSmallGeFourSpectrum026
import Proofs.RadenkovicGutmanSmallGeFourSpectrum028
import Proofs.RadenkovicGutmanSmallGeFourSpectrum039
import Proofs.RadenkovicGutmanSmallGeFourSpectrum040
import Proofs.RadenkovicGutmanSmallGeFourSpectrum052
import Proofs.RadenkovicGutmanSmallGeFourSpectrum054
import Proofs.RadenkovicGutmanSmallGeFourSpectrum062
import Proofs.RadenkovicGutmanSmallGeFourSpectrum071
import Proofs.RadenkovicGutmanSmallGeFourSpectrum090
import Proofs.RadenkovicGutmanSmallGeFourSpectrum091
import Proofs.RadenkovicGutmanSmallGeFourSpectrum096
import Proofs.RadenkovicGutmanSmallGeFourSpectrum100
import Proofs.RadenkovicGutmanSmallGeFourSpectrum108
import Proofs.RadenkovicGutmanSmallGeFourSpectrum111
import Proofs.RadenkovicGutmanSmallGeFourSpectrum112
import Proofs.RadenkovicGutmanSmallGeFourSpectrum116
import Proofs.RadenkovicGutmanSmallGeFourSpectrum156
import Proofs.RadenkovicGutmanSmallGeFourSpectrum162
import Proofs.RadenkovicGutmanSmallGeFourSpectrum167
import Proofs.RadenkovicGutmanSmallGeFourSpectrum169
import Proofs.RadenkovicGutmanSmallGeFourSpectrum178
import Proofs.RadenkovicGutmanSmallGeFourSpectrum180
namespace Gebendorfer.RadenkovicGutman.SmallGeFourComparisons
set_option maxHeartbeats 0
theorem comparison051 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum100.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum180.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum180.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum100.actual_graph_bounds.2
  linarith
#print axioms comparison051
theorem comparison052 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum062.graph) (2-2/11) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum090.graph) (2-2/11) := by
  have hs := SmallGeFourSpectrum090.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum062.actual_graph_bounds.2
  linarith
#print axioms comparison052
theorem comparison053 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum100.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum167.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum167.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum100.actual_graph_bounds.2
  linarith
#print axioms comparison053
theorem comparison054 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum008.graph) (2-2/9) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum014.graph) (2-2/9) := by
  have hs := SmallGeFourSpectrum014.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum008.actual_graph_bounds.2
  linarith
#print axioms comparison054
theorem comparison055 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum026.graph) (2-2/10) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum024.graph) (2-2/10) := by
  have hs := SmallGeFourSpectrum024.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum026.actual_graph_bounds.2
  linarith
#print axioms comparison055
theorem comparison056 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum040.graph) (2-2/11) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum071.graph) (2-2/11) := by
  have hs := SmallGeFourSpectrum071.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum040.actual_graph_bounds.2
  linarith
#print axioms comparison056
theorem comparison057 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum116.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum112.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum112.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum116.actual_graph_bounds.2
  linarith
#print axioms comparison057
theorem comparison058 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum040.graph) (2-2/11) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum091.graph) (2-2/11) := by
  have hs := SmallGeFourSpectrum091.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum040.actual_graph_bounds.2
  linarith
#print axioms comparison058
theorem comparison059 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum116.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum178.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum178.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum116.actual_graph_bounds.2
  linarith
#print axioms comparison059
theorem comparison060 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum022.graph) (2-2/10) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum015.graph) (2-2/10) := by
  have hs := SmallGeFourSpectrum015.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum022.actual_graph_bounds.2
  linarith
#print axioms comparison060
theorem comparison061 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum039.graph) (2-2/11) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum062.graph) (2-2/11) := by
  have hs := SmallGeFourSpectrum062.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum039.actual_graph_bounds.2
  linarith
#print axioms comparison061
theorem comparison062 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum111.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum108.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum108.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum111.actual_graph_bounds.2
  linarith
#print axioms comparison062
theorem comparison063 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum111.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum169.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum169.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum111.actual_graph_bounds.2
  linarith
#print axioms comparison063
theorem comparison064 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum018.graph) (2-2/10) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum028.graph) (2-2/10) := by
  have hs := SmallGeFourSpectrum028.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum018.actual_graph_bounds.2
  linarith
#print axioms comparison064
theorem comparison065 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum054.graph) (2-2/11) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum052.graph) (2-2/11) := by
  have hs := SmallGeFourSpectrum052.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum054.actual_graph_bounds.2
  linarith
#print axioms comparison065
theorem comparison066 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum096.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum162.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum162.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum096.actual_graph_bounds.2
  linarith
#print axioms comparison066
theorem comparison067 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum096.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum156.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum156.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum096.actual_graph_bounds.2
  linarith
#print axioms comparison067
end Gebendorfer.RadenkovicGutman.SmallGeFourComparisons
