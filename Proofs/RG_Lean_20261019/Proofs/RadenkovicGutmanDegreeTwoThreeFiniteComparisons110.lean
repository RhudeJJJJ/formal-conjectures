/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1021
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1095
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1296
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1481
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1964
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1974
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1979
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1981
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1983
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum370
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum870
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum922
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum924
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum947
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum952
import Proofs.RadenkovicGutmanSmallGeFourSpectrum110
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteComparisons
set_option maxHeartbeats 0
theorem comparison5500 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum924.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1964.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1964.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum924.actual_graph_bounds.2
  linarith
#print axioms comparison5500
theorem comparison5501 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum947.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1974.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1974.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum947.actual_graph_bounds.2
  linarith
#print axioms comparison5501
theorem comparison5502 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1021.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1979.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1979.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum1021.actual_graph_bounds.2
  linarith
#print axioms comparison5502
theorem comparison5503 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1095.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1981.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1981.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum1095.actual_graph_bounds.2
  linarith
#print axioms comparison5503
theorem comparison5504 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1296.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1983.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1983.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum1296.actual_graph_bounds.2
  linarith
#print axioms comparison5504
theorem comparison5505 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum370.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum110.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum110.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum370.actual_graph_bounds.2
  linarith
#print axioms comparison5505
theorem comparison5506 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum922.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1481.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1481.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum922.actual_graph_bounds.2
  linarith
#print axioms comparison5506
theorem comparison5507 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum870.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum952.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum952.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum870.actual_graph_bounds.2
  linarith
#print axioms comparison5507
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteComparisons
