/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteCoreCoverage
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteKeys.CoreCoverage
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem checked5b000 : coveredRange 5 0 20=true := by decide +kernel
#print axioms checked5b000
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteKeys.CoreCoverage
