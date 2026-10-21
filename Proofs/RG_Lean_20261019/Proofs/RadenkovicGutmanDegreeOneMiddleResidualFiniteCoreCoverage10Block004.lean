/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteCoreCoverage
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteKeys.CoreCoverage
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem checked10b004 : coveredRange 10 128 32=true := by decide +kernel
#print axioms checked10b004
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteKeys.CoreCoverage
