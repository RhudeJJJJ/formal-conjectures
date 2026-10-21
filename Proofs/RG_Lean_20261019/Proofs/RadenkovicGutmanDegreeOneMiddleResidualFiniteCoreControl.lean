/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteCoreCoverage
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteKeys.CoreCoverage
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem control10 : coveredRange 10 1 8=true := by decide +kernel
#print axioms control10
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteKeys.CoreCoverage
