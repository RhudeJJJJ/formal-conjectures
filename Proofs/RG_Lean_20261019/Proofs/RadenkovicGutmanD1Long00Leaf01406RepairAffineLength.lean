/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01406RepairJoin00
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
theorem leaf01406_w_affine_length : leaf01406_w_affine.length=89 := by decide +kernel
#print axioms leaf01406_w_affine_length
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
