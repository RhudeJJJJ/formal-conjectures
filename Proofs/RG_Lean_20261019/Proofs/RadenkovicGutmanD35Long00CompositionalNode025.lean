/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanNormProgramPack
namespace Gebendorfer.RadenkovicGutman.FixedDegree35Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e025 : NestedArithmetic.Expr 3 := .indet 2
noncomputable def p025 : NestedHorner.Poly 3 := [[[0,1]]]
theorem h025 : NestedArithmetic.compile e025=p025 := by decide +kernel
#print axioms h025
end Gebendorfer.RadenkovicGutman.FixedDegree35Long00Compositional
