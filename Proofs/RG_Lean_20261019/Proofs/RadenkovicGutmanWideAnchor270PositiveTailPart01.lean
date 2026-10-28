/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor270PositiveTailPartsData
namespace Gebendorfer.RadenkovicGutman.WideAnchor270PositiveTailPart01
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
theorem checked : (0 : ℚ)<WideAnchor270PositiveTailPartsData.Y := by decide +kernel
#print axioms checked
end Gebendorfer.RadenkovicGutman.WideAnchor270PositiveTailPart01
