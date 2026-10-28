/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPositiveTail
namespace Gebendorfer.RadenkovicGutman.WideAnchor270PositiveTailPartsData
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build ((51/26)) 0 46

def K : ℚ := (1991863/1000000)

def Y : ℚ := 128

def payment : ℚ := (127479232/16385991863)
#print axioms data
#print axioms K
#print axioms Y
#print axioms payment
end Gebendorfer.RadenkovicGutman.WideAnchor270PositiveTailPartsData
