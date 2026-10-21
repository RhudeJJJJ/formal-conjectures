/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanSmallGeFourSpectrum002
import Proofs.RadenkovicGutmanSmallGeFourSpectrum005
import Proofs.RadenkovicGutmanSmallGeFourSpectrum007
import Proofs.RadenkovicGutmanSmallGeFourSpectrum008
import Proofs.RadenkovicGutmanSmallGeFourSpectrum010
import Proofs.RadenkovicGutmanSmallGeFourSpectrum015
import Proofs.RadenkovicGutmanSmallGeFourSpectrum020
import Proofs.RadenkovicGutmanSmallGeFourSpectrum022
import Proofs.RadenkovicGutmanSmallGeFourSpectrum023
import Proofs.RadenkovicGutmanSmallGeFourSpectrum026
import Proofs.RadenkovicGutmanSmallGeFourSpectrum034
import Proofs.RadenkovicGutmanSmallGeFourSpectrum035
import Proofs.RadenkovicGutmanSmallGeFourSpectrum038
import Proofs.RadenkovicGutmanSmallGeFourSpectrum039
import Proofs.RadenkovicGutmanSmallGeFourSpectrum040
import Proofs.RadenkovicGutmanSmallGeFourSpectrum044
import Proofs.RadenkovicGutmanSmallGeFourSpectrum056
import Proofs.RadenkovicGutmanSmallGeFourSpectrum060
import Proofs.RadenkovicGutmanSmallGeFourSpectrum068
import Proofs.RadenkovicGutmanSmallGeFourSpectrum093
import Proofs.RadenkovicGutmanSmallGeFourSpectrum104
import Proofs.RadenkovicGutmanSmallGeFourSpectrum108
import Proofs.RadenkovicGutmanSmallGeFourSpectrum110
import Proofs.RadenkovicGutmanSmallGeFourSpectrum116
import Proofs.RadenkovicGutmanSmallGeFourSpectrum169
import Proofs.RadenkovicGutmanSmallGeFourSpectrum180
import Proofs.RadenkovicGutmanSmallGeFourSpectrum195
import Proofs.RadenkovicGutmanSmallGeFourSpectrum196
namespace Gebendorfer.RadenkovicGutman.SmallGeFourComparisons
set_option maxHeartbeats 0
theorem comparison017 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum022.graph) (2-2/10) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum034.graph) (2-2/10) := by
  have hs := SmallGeFourSpectrum034.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum022.actual_graph_bounds.2
  linarith
#print axioms comparison017
theorem comparison018 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum038.graph) (2-2/11) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum056.graph) (2-2/11) := by
  have hs := SmallGeFourSpectrum056.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum038.actual_graph_bounds.2
  linarith
#print axioms comparison018
theorem comparison019 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum104.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum169.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum169.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum104.actual_graph_bounds.2
  linarith
#print axioms comparison019
theorem comparison020 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum104.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum195.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum195.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum104.actual_graph_bounds.2
  linarith
#print axioms comparison020
theorem comparison021 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum002.graph) (2-2/8) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum005.graph) (2-2/8) := by
  have hs := SmallGeFourSpectrum005.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum002.actual_graph_bounds.2
  linarith
#print axioms comparison021
theorem comparison022 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum010.graph) (2-2/9) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum008.graph) (2-2/9) := by
  have hs := SmallGeFourSpectrum008.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum010.actual_graph_bounds.2
  linarith
#print axioms comparison022
theorem comparison023 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum015.graph) (2-2/10) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum026.graph) (2-2/10) := by
  have hs := SmallGeFourSpectrum026.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum015.actual_graph_bounds.2
  linarith
#print axioms comparison023
theorem comparison024 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum044.graph) (2-2/11) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum040.graph) (2-2/11) := by
  have hs := SmallGeFourSpectrum040.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum044.actual_graph_bounds.2
  linarith
#print axioms comparison024
theorem comparison025 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum093.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum116.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum116.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum093.actual_graph_bounds.2
  linarith
#print axioms comparison025
theorem comparison026 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum015.graph) (2-2/10) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum035.graph) (2-2/10) := by
  have hs := SmallGeFourSpectrum035.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum015.actual_graph_bounds.2
  linarith
#print axioms comparison026
theorem comparison027 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum044.graph) (2-2/11) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum060.graph) (2-2/11) := by
  have hs := SmallGeFourSpectrum060.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum044.actual_graph_bounds.2
  linarith
#print axioms comparison027
theorem comparison028 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum093.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum180.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum180.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum093.actual_graph_bounds.2
  linarith
#print axioms comparison028
theorem comparison029 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum093.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum196.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum196.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum093.actual_graph_bounds.2
  linarith
#print axioms comparison029
theorem comparison030 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum007.graph) (2-2/9) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum010.graph) (2-2/9) := by
  have hs := SmallGeFourSpectrum010.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum007.actual_graph_bounds.2
  linarith
#print axioms comparison030
theorem comparison031 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum023.graph) (2-2/10) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum020.graph) (2-2/10) := by
  have hs := SmallGeFourSpectrum020.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum023.actual_graph_bounds.2
  linarith
#print axioms comparison031
theorem comparison032 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum039.graph) (2-2/11) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum068.graph) (2-2/11) := by
  have hs := SmallGeFourSpectrum068.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum039.actual_graph_bounds.2
  linarith
#print axioms comparison032
theorem comparison033 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum110.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum108.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum108.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum110.actual_graph_bounds.2
  linarith
#print axioms comparison033
end Gebendorfer.RadenkovicGutman.SmallGeFourComparisons
