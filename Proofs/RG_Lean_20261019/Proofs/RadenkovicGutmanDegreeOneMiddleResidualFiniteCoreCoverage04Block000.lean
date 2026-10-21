/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteCoreCoverage
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteKeys.CoreCoverage
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem checked4b000 : coveredRange 4 0 9=true := by decide +kernel
#print axioms checked4b000
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteKeys.CoreCoverage
