/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPositiveTail
namespace Gebendorfer.RadenkovicGutman.WideAnchor030PositiveTailPartsData
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build ((51/26)) 9 39

def K : ℚ := (995871/500000)

def Y : ℚ := 128

def payment : ℚ := (63735744/8192995871)
#print axioms data
#print axioms K
#print axioms Y
#print axioms payment
end Gebendorfer.RadenkovicGutman.WideAnchor030PositiveTailPartsData
