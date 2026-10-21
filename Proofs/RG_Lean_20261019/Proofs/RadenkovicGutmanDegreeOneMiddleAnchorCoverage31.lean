/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeOneMiddleAnchorData
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleAnchors
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem checked31 : checkAt 31=true := by decide +kernel
#print axioms checked31
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleAnchors
