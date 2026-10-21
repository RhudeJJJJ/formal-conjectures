/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeOneMiddleAnchorData
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleAnchors
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem checked23 : checkAt 23=true := by decide +kernel
#print axioms checked23
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleAnchors
