/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanSmallGeFourSpectrum024
import Proofs.RadenkovicGutmanSmallGeFourSpectrum025
import Proofs.RadenkovicGutmanSmallGeFourSpectrum032
import Proofs.RadenkovicGutmanSmallGeFourSpectrum033
import Proofs.RadenkovicGutmanSmallGeFourSpectrum034
import Proofs.RadenkovicGutmanSmallGeFourSpectrum035
import Proofs.RadenkovicGutmanSmallGeFourSpectrum047
import Proofs.RadenkovicGutmanSmallGeFourSpectrum048
import Proofs.RadenkovicGutmanSmallGeFourSpectrum055
import Proofs.RadenkovicGutmanSmallGeFourSpectrum056
import Proofs.RadenkovicGutmanSmallGeFourSpectrum060
import Proofs.RadenkovicGutmanSmallGeFourSpectrum086
import Proofs.RadenkovicGutmanSmallGeFourSpectrum087
import Proofs.RadenkovicGutmanSmallGeFourSpectrum089
import Proofs.RadenkovicGutmanSmallGeFourSpectrum090
import Proofs.RadenkovicGutmanSmallGeFourSpectrum091
import Proofs.RadenkovicGutmanSmallGeFourSpectrum141
import Proofs.RadenkovicGutmanSmallGeFourSpectrum144
import Proofs.RadenkovicGutmanSmallGeFourSpectrum146
import Proofs.RadenkovicGutmanSmallGeFourSpectrum149
import Proofs.RadenkovicGutmanSmallGeFourSpectrum164
import Proofs.RadenkovicGutmanSmallGeFourSpectrum166
import Proofs.RadenkovicGutmanSmallGeFourSpectrum167
import Proofs.RadenkovicGutmanSmallGeFourSpectrum169
import Proofs.RadenkovicGutmanSmallGeFourSpectrum226
import Proofs.RadenkovicGutmanSmallGeFourSpectrum227
import Proofs.RadenkovicGutmanSmallGeFourSpectrum229
import Proofs.RadenkovicGutmanSmallGeFourSpectrum230
namespace Gebendorfer.RadenkovicGutman.SmallGeFourComparisons
set_option maxHeartbeats 0
theorem comparison085 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum047.graph) (2-2/11) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum086.graph) (2-2/11) := by
  have hs := SmallGeFourSpectrum086.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum047.actual_graph_bounds.2
  linarith
#print axioms comparison085
theorem comparison086 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum144.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum141.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum141.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum144.actual_graph_bounds.2
  linarith
#print axioms comparison086
theorem comparison087 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum144.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum226.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum226.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum144.actual_graph_bounds.2
  linarith
#print axioms comparison087
theorem comparison088 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum032.graph) (2-2/10) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum025.graph) (2-2/10) := by
  have hs := SmallGeFourSpectrum025.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum032.actual_graph_bounds.2
  linarith
#print axioms comparison088
theorem comparison089 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum048.graph) (2-2/11) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum087.graph) (2-2/11) := by
  have hs := SmallGeFourSpectrum087.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum048.actual_graph_bounds.2
  linarith
#print axioms comparison089
theorem comparison090 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum149.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum146.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum146.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum149.actual_graph_bounds.2
  linarith
#print axioms comparison090
theorem comparison091 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum149.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum227.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum227.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum149.actual_graph_bounds.2
  linarith
#print axioms comparison091
theorem comparison092 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum033.graph) (2-2/10) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum034.graph) (2-2/10) := by
  have hs := SmallGeFourSpectrum034.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum033.actual_graph_bounds.2
  linarith
#print axioms comparison092
theorem comparison093 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum055.graph) (2-2/11) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum089.graph) (2-2/11) := by
  have hs := SmallGeFourSpectrum089.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum055.actual_graph_bounds.2
  linarith
#print axioms comparison093
theorem comparison094 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum166.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum164.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum164.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum166.actual_graph_bounds.2
  linarith
#print axioms comparison094
theorem comparison095 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum166.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum229.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum229.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum166.actual_graph_bounds.2
  linarith
#print axioms comparison095
theorem comparison096 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum034.graph) (2-2/10) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum035.graph) (2-2/10) := by
  have hs := SmallGeFourSpectrum035.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum034.actual_graph_bounds.2
  linarith
#print axioms comparison096
theorem comparison097 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum056.graph) (2-2/11) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum090.graph) (2-2/11) := by
  have hs := SmallGeFourSpectrum090.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum056.actual_graph_bounds.2
  linarith
#print axioms comparison097
theorem comparison098 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum169.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum167.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum167.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum169.actual_graph_bounds.2
  linarith
#print axioms comparison098
theorem comparison099 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum169.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum230.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum230.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum169.actual_graph_bounds.2
  linarith
#print axioms comparison099
theorem comparison100 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum035.graph) (2-2/10) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum024.graph) (2-2/10) := by
  have hs := SmallGeFourSpectrum024.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum035.actual_graph_bounds.2
  linarith
#print axioms comparison100
theorem comparison101 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum060.graph) (2-2/11) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum091.graph) (2-2/11) := by
  have hs := SmallGeFourSpectrum091.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum060.actual_graph_bounds.2
  linarith
#print axioms comparison101
end Gebendorfer.RadenkovicGutman.SmallGeFourComparisons
