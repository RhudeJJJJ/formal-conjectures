/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualSpectrum1715
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualSpectrum1749
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualSpectrum1956
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualSpectrum2356
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualSpectrum2357
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualSpectrum2358
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteComparisons
set_option maxHeartbeats 0
theorem comparison1200 :
    stopLoss (laplacianSpectrum DegreeOneMiddleResidualSpectrum1715.graph) (2-2/17) <
      stopLoss (laplacianSpectrum DegreeOneMiddleResidualSpectrum2356.graph) (2-2/17) := by
  have hs := DegreeOneMiddleResidualSpectrum2356.actual_graph_bounds.1
  have ht := DegreeOneMiddleResidualSpectrum1715.actual_graph_bounds.2
  linarith
#print axioms comparison1200
theorem comparison1201 :
    stopLoss (laplacianSpectrum DegreeOneMiddleResidualSpectrum1749.graph) (2-2/17) <
      stopLoss (laplacianSpectrum DegreeOneMiddleResidualSpectrum2357.graph) (2-2/17) := by
  have hs := DegreeOneMiddleResidualSpectrum2357.actual_graph_bounds.1
  have ht := DegreeOneMiddleResidualSpectrum1749.actual_graph_bounds.2
  linarith
#print axioms comparison1201
theorem comparison1202 :
    stopLoss (laplacianSpectrum DegreeOneMiddleResidualSpectrum1956.graph) (2-2/17) <
      stopLoss (laplacianSpectrum DegreeOneMiddleResidualSpectrum2358.graph) (2-2/17) := by
  have hs := DegreeOneMiddleResidualSpectrum2358.actual_graph_bounds.1
  have ht := DegreeOneMiddleResidualSpectrum1956.actual_graph_bounds.2
  linarith
#print axioms comparison1202
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteComparisons
