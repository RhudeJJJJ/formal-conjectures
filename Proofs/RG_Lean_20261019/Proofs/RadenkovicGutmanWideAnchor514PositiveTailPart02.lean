/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor514PositiveTailPartsData
namespace Gebendorfer.RadenkovicGutman.WideAnchor514PositiveTailPart02
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
theorem checked : ComputedHornerArithmetic.nonnegative (ComputedPositiveTail.shifted (ComputedPositiveTail.comparison WideAnchor514PositiveTailPartsData.data WideAnchor514PositiveTailPartsData.K) WideAnchor514PositiveTailPartsData.Y)=true := by decide +kernel
#print axioms checked
end Gebendorfer.RadenkovicGutman.WideAnchor514PositiveTailPart02
