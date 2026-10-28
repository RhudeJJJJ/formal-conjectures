/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor271PositiveTailPartsData
namespace Gebendorfer.RadenkovicGutman.WideAnchor271PositiveTailPart02
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
theorem checked : ComputedHornerArithmetic.nonnegative (ComputedPositiveTail.shifted (ComputedPositiveTail.comparison WideAnchor271PositiveTailPartsData.data WideAnchor271PositiveTailPartsData.K) WideAnchor271PositiveTailPartsData.Y)=true := by decide +kernel
#print axioms checked
end Gebendorfer.RadenkovicGutman.WideAnchor271PositiveTailPart02
