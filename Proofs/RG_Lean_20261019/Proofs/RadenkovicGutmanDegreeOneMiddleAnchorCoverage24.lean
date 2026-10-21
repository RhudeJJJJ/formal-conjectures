/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeOneMiddleAnchorData
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleAnchors
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem checked24 : checkAt 24=true := by decide +kernel
#print axioms checked24
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleAnchors
