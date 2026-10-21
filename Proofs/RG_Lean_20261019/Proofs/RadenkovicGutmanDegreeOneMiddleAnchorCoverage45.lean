/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeOneMiddleAnchorData
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleAnchors
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem checked45 : checkAt 45=true := by decide +kernel
#print axioms checked45
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleAnchors
