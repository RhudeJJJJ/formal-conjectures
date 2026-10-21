/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeOneSmallKeyRanges
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem checked10b054 : coveredRange 10 1728 32=true := by decide +kernel
#print axioms checked10b054
end Gebendorfer.RadenkovicGutman.DegreeOneSmallKeys
