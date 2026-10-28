/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor512PositiveTailPartsData
namespace Gebendorfer.RadenkovicGutman.WideAnchor512PositiveTailPart05
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
theorem checked : (0 : ℚ)<(ComputedPositiveTail.shifted WideAnchor512PositiveTailPartsData.data.N WideAnchor512PositiveTailPartsData.Y).headD 0 := by decide +kernel
#print axioms checked
end Gebendorfer.RadenkovicGutman.WideAnchor512PositiveTailPart05
