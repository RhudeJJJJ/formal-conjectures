/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor029PositiveTailPartsData
namespace Gebendorfer.RadenkovicGutman.WideAnchor029PositiveTailPart03
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
theorem checked : ComputedHornerArithmetic.nonnegative (ComputedPositiveTail.shifted WideAnchor029PositiveTailPartsData.data.N WideAnchor029PositiveTailPartsData.Y)=true := by decide +kernel
#print axioms checked
end Gebendorfer.RadenkovicGutman.WideAnchor029PositiveTailPart03
