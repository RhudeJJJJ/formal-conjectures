/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeOneMiddleAnchorData
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleAnchors
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem checked35 : checkAt 35=true := by decide +kernel
#print axioms checked35
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleAnchors
