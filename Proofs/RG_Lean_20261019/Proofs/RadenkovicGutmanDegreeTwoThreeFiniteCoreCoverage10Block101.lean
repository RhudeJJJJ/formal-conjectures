/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteCoreCoverage
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys.CoreCoverage
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem checked10b101 : coveredRange 10 808 8=true := by decide +kernel
#print axioms checked10b101
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys.CoreCoverage
