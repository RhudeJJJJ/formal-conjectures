/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanNoRuntimeSpectrum5531OriginalNamespace
import Proofs.RadenkovicGutmanNoRuntimeSpectrum5532OriginalNamespace
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteComparisons
set_option maxHeartbeats 0
theorem comparison3296 :
    stopLoss (laplacianSpectrum DegreeTwoThreeSpectrum5532.graph) (2-2/17) <
      stopLoss (laplacianSpectrum DegreeTwoThreeSpectrum5531.graph) (2-2/17) := by
  have hs := DegreeTwoThreeSpectrum5531.actual_graph_bounds.1
  have ht := DegreeTwoThreeSpectrum5532.actual_graph_bounds.2
  linarith
#print axioms comparison3296
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteComparisons
