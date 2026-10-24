/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00IntegerLeaf03800Prepared
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00IntegerLeaf03800
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
theorem sign_checked : NestedInteger.bernsteinCheck 3 ![88,4,4] affine=true := by decide +kernel
#print axioms sign_checked
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00IntegerLeaf03800
