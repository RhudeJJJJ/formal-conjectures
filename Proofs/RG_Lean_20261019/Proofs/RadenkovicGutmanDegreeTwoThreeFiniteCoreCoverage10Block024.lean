/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteCoreCoverage
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys.CoreCoverage
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem checked10b024 : coveredRange 10 192 8=true := by decide +kernel
#print axioms checked10b024
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys.CoreCoverage
