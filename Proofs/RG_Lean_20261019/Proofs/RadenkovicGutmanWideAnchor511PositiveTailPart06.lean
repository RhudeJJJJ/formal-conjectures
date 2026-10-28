/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor511PositiveTailPartsData
namespace Gebendorfer.RadenkovicGutman.WideAnchor511PositiveTailPart06
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
theorem checked : (0 : ℚ)<(ComputedPositiveTail.shifted WideAnchor511PositiveTailPartsData.data.E WideAnchor511PositiveTailPartsData.Y).headD 0 := by decide +kernel
#print axioms checked
end Gebendorfer.RadenkovicGutman.WideAnchor511PositiveTailPart06
