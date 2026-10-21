/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteCoreCoverage
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys.CoreCoverage
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem checked7b008 : coveredRange 7 64 8=true := by decide +kernel
#print axioms checked7b008
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys.CoreCoverage
