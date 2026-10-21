/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeOneMiddleAnchorData
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleAnchors
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem checked19 : checkAt 19=true := by decide +kernel
#print axioms checked19
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleAnchors
