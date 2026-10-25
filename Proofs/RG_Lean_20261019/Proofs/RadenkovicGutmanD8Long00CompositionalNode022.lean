/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanNormProgramPack
namespace Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e022 : NestedArithmetic.Expr 3 := .indet 1
noncomputable def p022 : NestedHorner.Poly 3 := [[[],[1]]]
theorem h022 : NestedArithmetic.compile e022=p022 := by decide +kernel
#print axioms h022
end Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
