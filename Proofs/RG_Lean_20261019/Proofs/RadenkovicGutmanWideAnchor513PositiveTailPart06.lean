/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor513PositiveTailPartsData
namespace Gebendorfer.RadenkovicGutman.WideAnchor513PositiveTailPart06
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
theorem checked : (0 : ℚ)<(ComputedPositiveTail.shifted WideAnchor513PositiveTailPartsData.data.E WideAnchor513PositiveTailPartsData.Y).headD 0 := by decide +kernel
#print axioms checked
end Gebendorfer.RadenkovicGutman.WideAnchor513PositiveTailPart06
