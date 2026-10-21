/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeOneMiddleAnchorData
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleAnchors
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem checked17 : checkAt 17=true := by decide +kernel
#print axioms checked17
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleAnchors
