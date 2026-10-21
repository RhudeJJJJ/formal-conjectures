/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeOneSmallKeyRanges
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem checked8b006 : coveredRange 8 192 32=true := by decide +kernel
#print axioms checked8b006
end Gebendorfer.RadenkovicGutman.DegreeOneSmallKeys
