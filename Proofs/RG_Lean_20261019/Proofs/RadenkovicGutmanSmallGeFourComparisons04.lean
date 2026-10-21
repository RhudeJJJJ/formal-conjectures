/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanSmallGeFourSpectrum019
import Proofs.RadenkovicGutmanSmallGeFourSpectrum020
import Proofs.RadenkovicGutmanSmallGeFourSpectrum021
import Proofs.RadenkovicGutmanSmallGeFourSpectrum026
import Proofs.RadenkovicGutmanSmallGeFourSpectrum027
import Proofs.RadenkovicGutmanSmallGeFourSpectrum029
import Proofs.RadenkovicGutmanSmallGeFourSpectrum030
import Proofs.RadenkovicGutmanSmallGeFourSpectrum031
import Proofs.RadenkovicGutmanSmallGeFourSpectrum032
import Proofs.RadenkovicGutmanSmallGeFourSpectrum045
import Proofs.RadenkovicGutmanSmallGeFourSpectrum056
import Proofs.RadenkovicGutmanSmallGeFourSpectrum060
import Proofs.RadenkovicGutmanSmallGeFourSpectrum061
import Proofs.RadenkovicGutmanSmallGeFourSpectrum066
import Proofs.RadenkovicGutmanSmallGeFourSpectrum067
import Proofs.RadenkovicGutmanSmallGeFourSpectrum068
import Proofs.RadenkovicGutmanSmallGeFourSpectrum082
import Proofs.RadenkovicGutmanSmallGeFourSpectrum105
import Proofs.RadenkovicGutmanSmallGeFourSpectrum107
import Proofs.RadenkovicGutmanSmallGeFourSpectrum108
import Proofs.RadenkovicGutmanSmallGeFourSpectrum132
import Proofs.RadenkovicGutmanSmallGeFourSpectrum133
import Proofs.RadenkovicGutmanSmallGeFourSpectrum164
import Proofs.RadenkovicGutmanSmallGeFourSpectrum167
import Proofs.RadenkovicGutmanSmallGeFourSpectrum168
import Proofs.RadenkovicGutmanSmallGeFourSpectrum191
import Proofs.RadenkovicGutmanSmallGeFourSpectrum195
import Proofs.RadenkovicGutmanSmallGeFourSpectrum196
import Proofs.RadenkovicGutmanSmallGeFourSpectrum220
namespace Gebendorfer.RadenkovicGutman.SmallGeFourComparisons
set_option maxHeartbeats 0
theorem comparison068 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum021.graph) (2-2/10) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum029.graph) (2-2/10) := by
  have hs := SmallGeFourSpectrum029.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum021.actual_graph_bounds.2
  linarith
#print axioms comparison068
theorem comparison069 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum066.graph) (2-2/11) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum061.graph) (2-2/11) := by
  have hs := SmallGeFourSpectrum061.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum066.actual_graph_bounds.2
  linarith
#print axioms comparison069
theorem comparison070 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum105.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum191.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum191.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum105.actual_graph_bounds.2
  linarith
#print axioms comparison070
theorem comparison071 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum105.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum168.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum168.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum105.actual_graph_bounds.2
  linarith
#print axioms comparison071
theorem comparison072 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum019.graph) (2-2/10) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum020.graph) (2-2/10) := by
  have hs := SmallGeFourSpectrum020.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum019.actual_graph_bounds.2
  linarith
#print axioms comparison072
theorem comparison073 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum067.graph) (2-2/11) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum056.graph) (2-2/11) := by
  have hs := SmallGeFourSpectrum056.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum067.actual_graph_bounds.2
  linarith
#print axioms comparison073
theorem comparison074 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum107.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum195.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum195.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum107.actual_graph_bounds.2
  linarith
#print axioms comparison074
theorem comparison075 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum107.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum164.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum164.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum107.actual_graph_bounds.2
  linarith
#print axioms comparison075
theorem comparison076 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum020.graph) (2-2/10) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum026.graph) (2-2/10) := by
  have hs := SmallGeFourSpectrum026.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum020.actual_graph_bounds.2
  linarith
#print axioms comparison076
theorem comparison077 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum068.graph) (2-2/11) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum060.graph) (2-2/11) := by
  have hs := SmallGeFourSpectrum060.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum068.actual_graph_bounds.2
  linarith
#print axioms comparison077
theorem comparison078 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum108.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum196.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum196.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum108.actual_graph_bounds.2
  linarith
#print axioms comparison078
theorem comparison079 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum108.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum167.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum167.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum108.actual_graph_bounds.2
  linarith
#print axioms comparison079
theorem comparison080 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum030.graph) (2-2/10) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum027.graph) (2-2/10) := by
  have hs := SmallGeFourSpectrum027.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum030.actual_graph_bounds.2
  linarith
#print axioms comparison080
theorem comparison081 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum045.graph) (2-2/11) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum082.graph) (2-2/11) := by
  have hs := SmallGeFourSpectrum082.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum045.actual_graph_bounds.2
  linarith
#print axioms comparison081
theorem comparison082 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum133.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum132.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum132.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum133.actual_graph_bounds.2
  linarith
#print axioms comparison082
theorem comparison083 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum133.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum220.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum220.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum133.actual_graph_bounds.2
  linarith
#print axioms comparison083
theorem comparison084 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum031.graph) (2-2/10) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum032.graph) (2-2/10) := by
  have hs := SmallGeFourSpectrum032.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum031.actual_graph_bounds.2
  linarith
#print axioms comparison084
end Gebendorfer.RadenkovicGutman.SmallGeFourComparisons
